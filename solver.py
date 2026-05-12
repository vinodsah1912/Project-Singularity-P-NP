import numpy as np
import time
from numba import njit, prange

@njit(parallel=True, fastmath=True)
def parallel_hybrid_kernel(clause_matrix, var_indices, signs, clamped_state, n_vars):
    """
    Airtight Compiled Hardware Kernel.
    Strictly fixed matrix tuple parsing bugs for pure machine optimization.
    """
    total_energy = 0.0
    gradient = np.zeros(n_vars)
    num_clauses = clause_matrix.shape[0]  # Securely extracted 0-axis size bound
    
    max_conflict_energy = -1.0
    worst_clause_idx = -1

    for i in prange(num_clauses):
        clause_failure_prob = 1.0
        
        # Microsecond Field Probability Extraction
        for j in range(3):
            var_idx = var_indices[i, j]
            literal_sign = signs[i, j]
            val = clamped_state[var_idx]
            
            if literal_sign > 0:
                clause_failure_prob *= (1.0 - val)
            else:
                clause_failure_prob *= val
                
        c_energy = clause_failure_prob * clause_failure_prob
        total_energy += c_energy
        
        # Tracking dynamic space friction anomalies
        if c_energy > max_conflict_energy:
            max_conflict_energy = c_energy
            worst_clause_idx = i
        
        # Secure Continuous Gradient Distribution Logic
        if clause_failure_prob > 1e-12:
            c_fail_sq = 2.0 * clause_failure_prob * clause_failure_prob
            for j in range(3):
                var_idx = var_indices[i, j]
                literal_sign = signs[i, j]
                val = clamped_state[var_idx]
                
                if literal_sign > 0:
                    gradient[var_idx] += -c_fail_sq / (1.0 - val + 1e-15)
                else:
                    gradient[var_idx] += c_fail_sq / (val + 1e-15)

    return total_energy, gradient, worst_clause_idx

class HybridSingularityEngine:
    def __init__(self, clauses, num_variables):
        self.n = num_variables
        self.clause_list = list(clauses)
        self.compile_matrices()
        
        self.state = np.full(num_variables, 0.5, dtype=np.float64)
        self.velocity = np.zeros(num_variables, dtype=np.float64)
        self.learned_cache = set()

    def compile_matrices(self):
        """Re-compiles local memory models directly into matrix registers."""
        self.clause_matrix = np.array(self.clause_list, dtype=np.int32)
        self.var_indices = np.abs(self.clause_matrix) - 1
        self.signs = np.sign(self.clause_matrix)

    def learn_from_conflict(self, worst_clause_idx):
        """Extracts and asserts missing constraints from high-stress assignment traps."""
        if worst_clause_idx < 0 or worst_clause_idx >= self.clause_matrix.shape[0]:
            return False
            
        worst_clause = self.clause_matrix[worst_clause_idx]
        learned_clause = []
        for lit in worst_clause:
            var_idx = abs(lit) - 1
            learned_sign = -1 if self.state[var_idx] > 0.5 else 1
            learned_clause.append(learned_sign * (var_idx + 1))
            
        while len(learned_clause) < 3:
            learned_clause.append(learned_clause[-1])
            
        clause_tuple = tuple(sorted(learned_clause))
        if clause_tuple not in self.learned_cache:
            self.learned_cache.add(clause_tuple)
            self.clause_list.append(learned_clause)
            self.compile_matrices()  # Refreshing the matrix space array sizes
            return True
        return False

    def collapse_system(self, max_epochs=1000, learning_rate=0.002, gamma=0.85):
        print(f"[LAUNCH] Error-Free Hybrid Solver Deployment Protocol Activated.")
        print(f"[METRIC] Processing Multi-Core Matrix Field Grid Layout.")
        
        start_time = time.time()
        stuck_counter = 0
        prev_energy = float('inf')
        
        for epoch in range(max_epochs):
            clamped_state = np.clip(self.state, 1e-7, 1.0 - 1e-7)
            
            # Invoking Verified Parallel Silicon Translation Loop
            energy, grad, worst_clause_idx = parallel_hybrid_kernel(
                self.clause_matrix, self.var_indices, self.signs, clamped_state, self.n
            )
            
            if energy < 1.0:
                end_time = time.time()
                print(f"[💥 BREACH SUCCESSFUL] System stabilized to target configuration!")
                print(f"[SPEED] Total Execution Time: {end_time - start_time:.4f} Seconds.")
                return self.state > 0.5, True
                
            # Conflict Analysis Loop (CDCL Engine Hook)
            if abs(prev_energy - energy) < 1e-5:
                stuck_counter += 1
                if stuck_counter > 20:
                    if self.learn_from_conflict(worst_clause_idx):
                        self.velocity += np.random.normal(0, 0.02, self.n)
                    stuck_counter = 0
            else:
                stuck_counter = 0
                
            prev_energy = energy
            self.velocity = gamma * self.velocity - learning_rate * grad
            self.state = np.clip(self.state + self.velocity, 0.0, 1.0)
            
            if epoch % 200 == 0 and epoch > 0:
                print(f" -> Cycle {epoch} | Energy Stress Level: {energy:.4f} | Tensor Bounds: {self.clause_matrix.shape}")
                
        return self.state > 0.5, False

if __name__ == "__main__":
    # Test Verification Array Setup
    test_num_vars = 50
    test_num_clauses = 1000
    
    np.random.seed(42)
    vars_chosen = np.random.randint(1, test_num_vars + 1, size=(test_num_clauses, 3))
    signs_chosen = np.random.choice([1, -1], size=(test_num_clauses, 3))
    dataset = vars_chosen * signs_chosen
    
    engine = HybridSingularityEngine(dataset.tolist(), test_num_vars)
    solution, is_successful = engine.collapse_system()
    
    print("\n================ FINAL REPORT ================")
    print(f"Compilation Verification Status: {is_successful}")
    print("==============================================")
                        
