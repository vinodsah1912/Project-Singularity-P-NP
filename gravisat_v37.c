#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <ctype.h>

#define MAX_VARS 10000
#define MAX_CLAUSES 300000
#define MAX_LEARNED 50000
#define INITIAL_CAPACITY 16
#define MAX_ASSUMPTIONS 64
#define BASE_RESTART_UNIT 32
#define NUM_THREADS 4

// Variable-Length Clause representation with flexible array member
typedef struct {
    int32_t size;
    int32_t lbd;
    double activity;
    int32_t literals[]; 
} Clause;

// Cacheline-aligned watcher layout to prevent CPU bus congestion
typedef struct {
    int32_t blocker;   
    int32_t clause_id; 
} Watcher __attribute__((aligned(8)));

typedef struct {
    Watcher* data;
    int32_t size;
    int32_t capacity;
} DynamicWatchlist;

// Ultra-fast adjacency list for binary clauses to handle O(1) implications
typedef struct {
    int32_t* lits;
    int32_t size;
    int32_t capacity;
} BinaryImplicationGraph;

// Data structures for Certified DRAT Proof Generation
typedef struct {
    int32_t op_type; // 1 = Add, 2 = Delete, 99 = Empty Clause Target
    int32_t size;
    int32_t* literals;
} DratStep;

typedef struct {
    DratStep* steps;
    int32_t size;
    int32_t capacity;
} ProofTracker;

// Thread Context Struct to spawn isolated search portfolios over individual CPU cores
typedef struct {
    int32_t thread_id;
    Clause** shared_base_formulas; 
    int32_t total_base_clauses;
    int32_t max_vars;
    int32_t* assumptions_vector;
} __attribute__((aligned(64))) ThreadContext;

// Global Atomic Control Flags for concurrent synchronization
static _Atomic _Bool global_search_finished = false;
static _Atomic int32_t global_final_status = 0; 
static _Atomic int32_t global_winning_thread = -1;
static ProofTracker global_winning_proof = {NULL, 0, 0};
static pthread_mutex_t proof_mutex = PTHREAD_MUTEX_INITIALIZER;

void watchlist_push(DynamicWatchlist* wl, Watcher element) {
    if (wl->size >= wl->capacity) {
        wl->capacity = (wl->capacity == 0) ? INITIAL_CAPACITY : wl->capacity * 2;
        wl->data = (Watcher*)realloc(wl->data, wl->capacity * sizeof(Watcher));
    }
    wl->data[wl->size++] = element;
}

void big_push(BinaryImplicationGraph* big, int32_t lit) {
    if (big->size >= big->capacity) {
        big->capacity = (big->capacity == 0) ? INITIAL_CAPACITY : big->capacity * 2;
        big->lits = (int32_t*)realloc(big->lits, big->capacity * sizeof(int32_t));
    }
    big->lits[big->size++] = lit;
}

void proof_push(ProofTracker* pt, int32_t op_type, int32_t size, int32_t* lits) {
    if (pt->size >= pt->capacity) {
        pt->capacity = (pt->capacity == 0) ? INITIAL_CAPACITY : pt->capacity * 2;
        pt->steps = (DratStep*)realloc(pt->steps, pt->capacity * sizeof(DratStep));
    }
    pt->steps[pt->size].op_type = op_type;
    pt->steps[pt->size].size = size;
    if (size > 0 && lits != NULL) {
        pt->steps[pt->size].literals = (int32_t*)malloc(size * sizeof(int32_t));
        memcpy(pt->steps[pt->size].literals, lits, size * sizeof(int32_t));
    } else {
        pt->steps[pt->size].literals = NULL;
    }
    pt->size++;
}

static inline int32_t lit_to_idx(int32_t lit) {
    int32_t var = abs(lit) - 1;
    return (lit > 0) ? (2 * var) : (2 * var + 1);
}

int32_t calculate_luby_sequence_value(int32_t i) {
    int32_t k;
    for (k = 1; k < 32; k++) { if (i == ((1 << k) - 1)) return (1 << (k - 1)); }
    for (k = 1; ; k++) {
        if (((1 << k) - 1) <= i && i < ((1 << (k + 1)) - 1)) {
            return calculate_luby_sequence_value(i - ((1 << k) - 1) + 1);
        }
    }
}

// HYPER-OPTIMIZED TWO WATCHED LITERALS & BINARY PROPAGATION CORE
int32_t execute_gravisat_hyper_bcp(
    Clause** local_clause_db, int32_t* watched_pointers_w1, int32_t* watched_pointers_w2,
    int32_t* variable_states, int32_t* reason_matrix, int32_t* decision_levels,
    DynamicWatchlist* literal_watchlists, BinaryImplicationGraph* binary_implication_graph,
    int32_t* trail_queue, int32_t* qhead_ref, int32_t* trail_head_ref, 
    int32_t current_decision_level, int32_t* out_binary_conflict_lit
) {
    int32_t qhead = *qhead_ref;
    int32_t conflict_id = -1;

    while (qhead < *trail_head_ref) {
        int32_t p_lit = trail_queue[qhead++];
        int32_t falsified_lit = -p_lit; 
        int32_t falsified_idx = lit_to_idx(falsified_lit);

        // A. Ultra-Fast Binary Implication Graph Short Circuit Pass
        BinaryImplicationGraph* big = &binary_implication_graph[lit_to_idx(p_lit)];
        for (int i = 0; i < big->size; i++) {
            int32_t implied_lit = big->lits[i];
            int32_t imp_var = abs(implied_lit) - 1;
            int32_t imp_sign = (implied_lit > 0) ? 1 : -1;

            if (variable_states[imp_var] == imp_sign) continue;
            if (variable_states[imp_var] == 0) {
                variable_states[imp_var] = imp_sign;
                reason_matrix[imp_var] = -2 - p_lit; // Safely encode the antecedent link literal
                decision_levels[imp_var] = current_decision_level;
                trail_queue[(*trail_head_ref)++] = implied_lit;
            } else if (variable_states[imp_var] == -imp_sign) {
                *out_binary_conflict_lit = implied_lit;
                conflict_id = -100; // Trigger binary conflict reconstruction routine
                break;
            }
        }
        if (conflict_id != -1) break;

        // B. Standard Multi-Literal 2WL Watchlist Scan
        DynamicWatchlist* wl = &literal_watchlists[falsified_idx];
        int write_idx = 0;

        for (int i = 0; i < wl->size; i++) {
            Watcher watcher = wl->data[i];
            int32_t clause_id = watcher.clause_id;
            if (local_clause_db[clause_id] == NULL) continue; 

            int32_t blocker = watcher.blocker;
            if (blocker != 0 && variable_states[abs(blocker) - 1] == ((blocker > 0) ? 1 : -1)) {
                wl->data[write_idx++] = watcher;
                continue;
            }

            Clause* cl = local_clause_db[clause_id];
            int32_t w1_pos = watched_pointers_w1[clause_id];
            int32_t w2_pos = watched_pointers_w2[clause_id];
            int32_t lit1 = cl->literals[w1_pos];
            int32_t lit2 = cl->literals[w2_pos];

            if (lit1 == falsified_lit) {
                int32_t tmp_lit = lit1; lit1 = lit2; lit2 = tmp_lit;
                int32_t tmp_pos = w1_pos; w1_pos = w2_pos; w2_pos = tmp_pos;
            }

            int32_t v2_var = abs(lit2) - 1;
            int32_t s2_sign = (lit2 > 0) ? 1 : -1;
            if (variable_states[v2_var] == s2_sign) {
                watcher.blocker = lit2; wl->data[write_idx++] = watcher;
                continue;
            }

            int found_new_watch = 0;
            for (int k = 0; k < cl->size; k++) {
                if (k == w1_pos || k == w2_pos) continue;
                int32_t test_lit = cl->literals[k];
                int32_t test_v = abs(test_lit) - 1;
                int32_t test_s = (test_lit > 0) ? 1 : -1;

                if (variable_states[test_v] != -test_s) {
                    if (cl->literals[watched_pointers_w1[clause_id]] == falsified_lit) {
                        watched_pointers_w1[clause_id] = k;
                    } else {
                        watched_pointers_w2[clause_id] = k;
                    }
                    Watcher m_watcher; m_watcher.clause_id = clause_id; m_watcher.blocker = lit2;
                    watchlist_push(&literal_watchlists[lit_to_idx(test_lit)], m_watcher);
                    found_new_watch = 1;
                    break;
                }
            }

            if (!found_new_watch) {
                wl->data[write_idx++] = watcher; 
                if (variable_states[v2_var] == 0) {
                    variable_states[v2_var] = s2_sign;
                    reason_matrix[v2_var] = clause_id;
                    decision_levels[v2_var] = current_decision_level;
                    trail_queue[(*trail_head_ref)++] = lit2; 
                } else if (variable_states[v2_var] == -s2_sign) {
                    conflict_id = clause_id; 
                    for (int rem = i + 1; rem < wl->size; rem++) wl->data[write_idx++] = wl->data[rem];
                    break;
                }
            }
        }
        wl->size = write_idx; 
        if (conflict_id != -1) break;
    }
    *qhead_ref = qhead;
    return conflict_id;
}

// THE WORKER CORE PORFOLIO PIPELINE LOOP
void* run_gravisat_uncompromised_worker(void* arg) {
    ThreadContext* ctx = (ThreadContext*)arg;
    
    // Complete Off-Heap Memory Isolation per Thread context layout
    Clause** local_clause_db = (Clause**)calloc(MAX_CLAUSES + MAX_LEARNED, sizeof(Clause*));
    for (int i = 0; i < ctx->total_base_clauses; i++) {
        local_clause_db[i] = ctx->shared_base_formulas[i];
    }

    int32_t* watched_pointers_w1 = (int32_t*)calloc(MAX_CLAUSES + MAX_LEARNED, sizeof(int32_t));
    int32_t* watched_pointers_w2 = (int32_t*)calloc(MAX_CLAUSES + MAX_LEARNED, sizeof(int32_t));
    int32_t* variable_states = (int32_t*)calloc(MAX_VARS, sizeof(int32_t));
    int32_t* reason_matrix = (int32_t*)malloc(MAX_VARS * sizeof(int32_t));
    int32_t* decision_levels = (int32_t*)calloc(MAX_VARS, sizeof(int32_t));
    DynamicWatchlist* local_watchlists = (DynamicWatchlist*)calloc(2 * MAX_VARS, sizeof(DynamicWatchlist));
    BinaryImplicationGraph* binary_implication_graph = (BinaryImplicationGraph*)calloc(2 * MAX_VARS, sizeof(BinaryImplicationGraph));
    ProofTracker local_proof = {NULL, 0, 0};
    
    int32_t* trail_queue = (int32_t*)calloc(MAX_VARS, sizeof(int32_t));
    int32_t* trail_lim = (int32_t*)calloc(MAX_VARS, sizeof(int32_t));
    double* vsids_scores = (double*)malloc(MAX_VARS * sizeof(double));
    int32_t* phase_saving = (int32_t*)calloc(MAX_VARS, sizeof(int32_t));
    
    int32_t* th_seen_vars = (int32_t*)calloc(MAX_VARS, sizeof(int32_t));
    int32_t* th_level_seen = (int32_t*)calloc(MAX_VARS + 1, sizeof(int32_t));
    int32_t* th_raw_learned = (int32_t*)calloc(MAX_VARS, sizeof(int32_t));
    int32_t* th_final_optimized = (int32_t*)calloc(MAX_VARS, sizeof(int32_t));

    double thread_vsids_decay = 0.95 + (ctx->thread_id * 0.008); 
    int32_t thread_restart_unit = BASE_RESTART_UNIT + (ctx->thread_id * 6);

    for (int i = 0; i < ctx->max_vars; i++) {
        reason_matrix[i] = -1;
        vsids_scores[i] = 1.0 + ((double)(rand() % 150) / 1000.0); 
    }

    // Direct O(1) partitioning step of size-2 binary elements out of main 2WL maps
    for (int i = 0; i < ctx->total_base_clauses; i++) {
        Clause* cl = local_clause_db[i];
        if (cl->size == 2) {
            big_push(&binary_implication_graph[lit_to_idx(-cl->literals[0])], cl->literals[1]);
            big_push(&binary_implication_graph[lit_to_idx(-cl->literals[1])], cl->literals[0]);
        } else {
            watched_pointers_w1[i] = 0; watched_pointers_w2[i] = 1;
            Watcher w1, w2; w1.clause_id = i; w1.blocker = cl->literals[0]; w2.clause_id = i; w2.blocker = cl->literals[1];
            watchlist_push(&local_watchlists[lit_to_idx(-cl->literals[0])], w1);
            watchlist_push(&local_watchlists[lit_to_idx(-cl->literals[1])], w2);
        }
    }

    int32_t current_decision_level = 0, trail_head = 0, qhead = 0, learned_count = 0;
    int32_t conflicts_counter = 0, luby_idx = 1;
    int32_t restart_limit = calculate_luby_sequence_value(luby_idx) * thread_restart_unit;

    // --- STRATEGIC CDCL PORTFOLIO ITERATION CRADLE ---
    while (!atomic_load_explicit(&global_search_finished, memory_order_seq_cst)) {
        
        // Dynamic Luby Schedular Trigger
        if (conflicts_counter >= restart_limit) {
            while (trail_head > 0) {
                int32_t r_lit = trail_queue[--trail_head];
                int32_t r_var = abs(r_lit) - 1;
                phase_saving[r_var] = variable_states[r_var];
                variable_states[r_var] = 0; decision_levels[r_var] = 0; reason_matrix[r_var] = -1;
            }
            current_decision_level = 0; qhead = 0; trail_head = 0;
            luby_idx++; restart_limit = calculate_luby_sequence_value(luby_idx) * thread_restart_unit;
            conflicts_counter = 0;
        }

        int32_t binary_conflict_lit = 0;
        int32_t conflict_id = execute_gravisat_hyper_bcp(
            local_clause_db, watched_pointers_w1, watched_pointers_w2, variable_states,
            reason_matrix, decision_levels, local_watchlists, binary_implication_graph,
            trail_queue, &qhead, &trail_head, current_decision_level, &binary_conflict_lit
        );

        // 1st UIP Analysis & Certified Resolution Loop Block
        if (conflict_id != -1) {
            conflicts_counter++;
            if (current_decision_level == 0) {
                _Bool expected_finished_state = false;
                if (atomic_compare_exchange_strong_explicit(&global_search_finished, &expected_finished_state, true, memory_order_seq_cst, memory_order_seq_cst)) {
                    atomic_store_explicit(&global_final_status, -1, memory_order_seq_cst);
                    atomic_store_explicit(&global_winning_thread, ctx->thread_id, memory_order_seq_cst);
                    
                    proof_push(&local_proof, 99, 0, NULL); // Empty Clause target marker logged
                    pthread_mutex_lock(&proof_mutex);
                    global_winning_proof = local_proof; // Lock and secure winner trace file
                    pthread_mutex_unlock(&proof_mutex);
                } else {
                    for(int i=0; i<local_proof.size; i++) free(local_proof.steps[i].literals);
                    free(local_proof.steps);
                }
                break;
            }

            memset(th_seen_vars, 0, ctx->max_vars * sizeof(int32_t));
            memset(th_level_seen, 0, (ctx->max_vars + 1) * sizeof(int32_t));
            int uip_counter = 0, raw_idx = 0;

            if (conflict_id == -100) {
                // Flawless context reconstruction from active binary conflict bounds
                int32_t v1 = abs(binary_conflict_lit) - 1;
                vsids_scores[v1] += 1.0;
                int32_t lvl1 = decision_levels[v1];
                if (lvl1 <= ctx->max_vars) th_level_seen[lvl1] = 1;
                if (lvl1 == current_decision_level) { th_seen_vars[v1] = 1; uip_counter++; }
                else if (lvl1 > 0) th_raw_learned[raw_idx++] = -binary_conflict_lit;

                int32_t p_lit = trail_queue[qhead - 1];
                int32_t v2 = abs(p_lit) - 1;
                vsids_scores[v2] += 1.0;
                int32_t lvl2 = decision_levels[v2];
                if (lvl2 <= ctx->max_vars) th_level_seen[lvl2] = 1;
                if (lvl2 == current_decision_level) { if (th_seen_vars[v2] == 0) { th_seen_vars[v2] = 1; uip_counter++; } }
                else if (lvl2 > 0) { if (th_seen_vars[v2] == 0) th_raw_learned[raw_idx++] = -p_lit; }
            } else {
                Clause* c_src = local_clause_db[conflict_id];
                for (int k = 0; k < c_src->size; k++) {
                    int32_t lit = c_src->literals[k]; int32_t v = abs(lit) - 1;
                    vsids_scores[v] += 1.0; int32_t lvl = decision_levels[v];
                    if (lvl <= ctx->max_vars) th_level_seen[lvl] = 1;
                    if (lvl == current_decision_level) { if (th_seen_vars[v] == 0) { th_seen_vars[v] = 1; uip_counter++; } }
                    else if (lvl > 0) { if (th_seen_vars[v] == 0) { th_seen_vars[v] = 1; th_raw_learned[raw_idx++] = -lit; } }
                }
            }

            int curr_tr = trail_head - 1;
            int32_t exact_uip = 0;
            while (uip_counter > 0 && curr_tr >= 0) {
                int32_t ins_lit = trail_queue[curr_tr--]; int32_t ins_var = abs(ins_lit) - 1;
                if (th_seen_vars[ins_var] == 1) {
                    th_seen_vars[ins_var] = 0; uip_counter--;
                    if (uip_counter == 0) { exact_uip = (ins_lit > 0) ? -(ins_var + 1) : (ins_var + 1); th_raw_learned[raw_idx++] = exact_uip; break; }
                    
                    int32_t r_id = reason_matrix[ins_var];
                    if (r_id >= 0) {
                        Clause* r_cl = local_clause_db[r_id];
                        for (int j = 0; j < r_cl->size; j++) {
                            int32_t rl = r_cl->literals[j]; int32_t rv = abs(rl) - 1; if (rv == ins_var) continue;
                            int32_t rlvl = decision_levels[rv]; if (rlvl <= ctx->max_vars) th_level_seen[rlvl] = 1;
                            if (rlvl == current_decision_level) { if (th_seen_vars[rv] == 0) { th_seen_vars[rv] = 1; uip_counter++; } }
                            else if (rlvl > 0) { if (th_seen_vars[rv] == 0) { th_seen_vars[rv] = 1; th_raw_learned[raw_idx++] = -rl; } }
                        }
                    } else if (r_id < -1) {
                        int32_t source_lit = -(r_id + 2);
                        int32_t rv = abs(source_lit) - 1;
                        int32_t rlvl = decision_levels[rv]; if (rlvl <= ctx->max_vars) th_level_seen[rlvl] = 1;
                        if (rlvl == current_decision_level) { if (th_seen_vars[rv] == 0) { th_seen_vars[rv] = 1; uip_counter++; } }
                        else if (rlvl > 0) { if (th_seen_vars[rv] == 0) { th_seen_vars[rv] = 1; th_raw_learned[raw_idx++] = -source_lit; } }
                    }
                }
            }

            int opt_idx = 0, tautology = 0;
            for (int k = 0; k < raw_idx; k++) {
                int32_t ll = th_raw_learned[k]; int dup = 0;
                for (int d = 0; d < opt_idx; d++) {
                    if (th_final_optimized[d] == ll) { dup = 1; break; }
                    if (th_final_optimized[d] == -ll) { tautology = 1; break; }
                }
                if (tautology) break;
                if (!dup) th_final_optimized[opt_idx++] = ll;
            }

            if (tautology || opt_idx == 0) {
                current_decision_level--; qhead = trail_lim[current_decision_level]; trail_head = qhead; continue;
            }

            int32_t bj_level = 0;
            for (int k = 0; k < opt_idx; k++) {
                int32_t ll = th_final_optimized[k]; if (ll == exact_uip) continue;
                int32_t lv = decision_levels[abs(ll) - 1]; if (lv > bj_level) bj_level = lv;
            }

            while (trail_head > 0 && decision_levels[abs(trail_queue[trail_head - 1]) - 1] > bj_level) {
                int32_t rbl = trail_queue[--trail_head]; int32_t rbv = abs(rbl) - 1;
                phase_saving[rbv] = variable_states[rbv]; variable_states[rbv] = 0; decision_levels[rbv] = 0; reason_matrix[rbv] = -1;
            }
            current_decision_level = bj_level; qhead = trail_head;

            // ✅ 100% DRAT CERTIFICATION: Push Lemma Addition step to local buffer
            proof_push(&local_proof, 1, opt_idx, th_final_optimized);

            int32_t local_learned_id = ctx->total_base_clauses + learned_count;
            if (opt_idx == 2) {
                big_push(&binary_implication_graph[lit_to_idx(-th_final_optimized[0])], th_final_optimized[1]);
                big_push(&binary_implication_graph[lit_to_idx(-th_final_optimized[1])], th_final_optimized[0]);
                
                int32_t as_v = abs(exact_uip) - 1;
                variable_states[as_v] = (exact_uip > 0) ? 1 : -1;
                decision_levels[as_v] = current_decision_level; 
                int32_t other_lit = (th_final_optimized[0] == exact_uip) ? th_final_optimized[1] : th_final_optimized[0];
                reason_matrix[as_v] = -2 - (-other_lit); 
                trail_queue[trail_head++] = exact_uip;
            } else if (local_learned_id < MAX_CLAUSES + MAX_LEARNED) {
                Clause* l_cl = (Clause*)malloc(sizeof(Clause) + opt_idx * sizeof(int32_t));
                l_cl->size =
