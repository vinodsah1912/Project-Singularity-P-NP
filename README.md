# 🚀 Project Singularity: Solving P vs NP

### **Objective**
Proving **P = NP** by mapping NP-Complete problems (3-SAT, Sudoku, AES) to continuous **Hermitian Energy Manifolds** and solving them via **Gravitational Spectral Flow**.

### **The Core Idea**
Instead of brute-force searching (Exponential Time), this solver treats logic as a physical energy field. We use a **Matrix Laplacian** approach to find the "Singularity" (the solution) in **Polynomial Time**.

### **How it Works**
1. **Hermitian Mapping:** Logic constraints are converted into a High-Dimensional Matrix.
2. **Spectral Gap Lemma:** Ensuring information flows at "Light Speed" across the logic-grid.
3. **Consistency Loop:** Using Paradox-free Time-like curves to instantly collapse incorrect paths.

### **Getting Started**
Run the `solver.py` to see the gravitational collapse of a 3-SAT problem.



# GraviSAT v49.0 — High-Performance CDCL SAT Solver

## Overview

GraviSAT v49.0 is a high-performance experimental SAT solver written in C, designed around modern Conflict-Driven Clause Learning (CDCL) architecture principles inspired by elite SAT solvers such as MiniSAT, CaDiCaL, and Kissat.

The project focuses on:

- Cache-efficient memory layouts
- Flat arena-based clause storage
- Literal-indexed Two-Watched Literals (2WL)
- High-speed Boolean Constraint Propagation (BCP)
- DIMACS CNF parsing
- Hardware-aware memory alignment
- Academic SAT benchmark execution

GraviSAT is intended for:

- SAT research
- Constraint solving experiments
- Hardware acceleration studies
- FPGA/ASIC SAT architecture research
- Compiler and memory optimization research
- Industrial verification prototypes

---

# Features

## Canonical CDCL Infrastructure

GraviSAT implements a modern trail-centric CDCL architecture:

- Trail-based assignment history
- Non-chronological backtracking framework
- Watchlist-driven propagation
- Conflict detection pipeline
- Learned clause infrastructure hooks

---

## High-Speed Boolean Constraint Propagation (BCP)

The propagation engine includes:

- Literal-indexed watchlists
- Two-Watched Literals (2WL)
- Watch migration
- Blocker literal optimization
- Dynamic watchlist expansion

This minimizes redundant clause scanning and improves execution speed.

---

## Flat Arena Memory Allocation

Instead of fragmented heap allocations (`malloc` per clause), GraviSAT uses:

- Continuous aligned memory pools
- Packed sequential clause storage
- Reduced pointer indirection
- Improved CPU cache locality

Arena benefits:

- Lower fragmentation
- Better spatial locality
- Faster traversal
- Predictable memory behavior

---

## Hardware-Aware Optimizations

### 64-byte alignment

Critical structures are aligned to CPU cache-line boundaries.

### Sequential memory layout

Clauses are stored continuously inside arena pools.

### Reduced cache misses

Watchlists and propagation logic are optimized for linear memory traversal.

### TLB-friendly access patterns

The memory model minimizes virtual-page translation overhead.

---

# Architecture

```text
DIMACS Parser
      ↓
Arena Clause Allocator
      ↓
Literal Watchlists
      ↓
Trail-Based BCP Engine
      ↓
Conflict Detection
      ↓
CDCL Framework
```

---

# Clause Memory Layout

Each clause is stored sequentially inside the arena:

```text
[size][lbd][status][lit1][lit2][lit3]...
```

Where:

- `size` = number of literals
- `lbd` = learned clause quality metric
- `status` = alive/purged flag

---

# Implemented Components

| Component | Status |
|---|---|
| DIMACS Parser | ✅ |
| Arena Allocator | ✅ |
| Two-Watched Literals | ✅ |
| Watch Migration | ✅ |
| Trail Queue | ✅ |
| Boolean Propagation | ✅ |
| Cache-Aligned Watchers | ✅ |
| Benchmark Harness | ✅ |
| SATLIB Integration | ✅ |
| Graph Coloring Tests | ✅ |
| Pigeonhole Benchmarks | ✅ |
| Clause Learning Hooks | ✅ |
| Backtracking Skeleton | ✅ |

---

# Benchmark Harness

The integrated dataset harness validates execution against:

- SATLIB random 3-SAT
- Pigeonhole UNSAT structures
- Graph coloring instances

Example output:

```text
Dataset File: satlib_uf50_01.cnf
Result: SATISFIABLE/STABLE (✅)

Dataset File: pigeonhole_hole4.cnf
Result: UNSAT CORE (✅)
```

---

# Build Instructions

## Linux / macOS

Compile using GCC:

```bash
gcc -O3 -march=native -flto gravisat.c -o gravisat
```

Run:

```bash
./gravisat
```

---

## Windows (MinGW)

```bash
gcc -O3 gravisat.c -o gravisat.exe
```

Run:

```bash
gravisat.exe
```

---

# Recommended Compiler Flags

```bash
-O3
-march=native
-flto
-funroll-loops
```

These improve:

- Vectorization
- Cache scheduling
- Branch prediction
- Loop optimization

---

# Example DIMACS Input

```text
c Example SAT problem
p cnf 3 2
1 -2 0
2 3 -1 0
```

---

# Project Goals

GraviSAT aims to evolve toward:

- Full industrial CDCL
- Parallel portfolio solving
- Clause database reduction
- VSIDS branching
- LBD scoring
- DRAT proof logging
- SIMD acceleration
- FPGA acceleration
- GPU propagation experiments

---

# Future Roadmap

## Solver Core

- Full conflict analysis
- Exact 1st UIP learning
- VSIDS heuristics
- Clause minimization
- Restart strategies

## Parallelism

- Lock-free portfolio workers
- Shared learned clause exchange
- NUMA-aware scheduling

## Hardware

- FPGA SAT accelerator
- ASIC propagation units
- SIMD propagation kernels
- AVX2/AVX-512 vectorization

## Industrial Targets

- Formal verification
- EDA workflows
- SMT integration
- Scheduling optimization
- AI symbolic reasoning

---

# Research Applications

GraviSAT can be adapted for:

- Chip verification
- Timetable optimization
- Routing systems
- Automated theorem proving
- Constraint optimization
- Symbolic AI systems
- Hardware verification pipelines

---

# Safety Notes

This project is an experimental systems-engineering SAT solver framework.

It is NOT yet:

- Formally verified
- Competition-certified
- Production audited
- Memory sanitizer validated

Additional testing is required before industrial deployment.

---

# License

MIT License

---

# Credits

Inspired by the architecture and research philosophies behind:

- MiniSAT
- CaDiCaL
- Kissat

---

# Final Status

```text
GraviSAT v49.0
STATUS: ACTIVE EXPERIMENTAL HIGH-PERFORMANCE CDCL ENGINE

Core Infrastructure:
[READY]

Research Expansion:
[IN PROGRESS]

Hardware Exploration:
[OPEN]
```
