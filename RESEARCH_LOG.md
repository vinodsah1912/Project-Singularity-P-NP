# GraviSAT: Continuous Manifold Optimization for Non-Linear Cryptographic Puzzles

## 🔬 Project Status & Architectural Paradigm
This repository functions as an advanced academic research framework investigating the application of continuous relaxation and spectral gradient flow on discrete constraint satisfaction problems (such as SAT and cryptographic hash inversions). 

### 📐 Theoretical Foundations
Instead of deploying traditional discrete backtracking mechanisms (like CDCL in modern SAT solvers), GraviSAT translates boolean structures into a continuous energy landscape:
1. **State Space Relaxation:** Boolean bit states are mapped to a continuous field bounded between $0.0$ and $1.0$, initialized at the maximum uncertainty threshold ($0.5$).
2. **Hamiltonian Energy Function:** Constraints are formulated as differential equations where the global minimum sits at exactly $0.0$, representing a globally satisfying assignment.
3. **Relativistic Momentum & Friction Loop:** Incorporates dynamic velocity modifiers ($\beta$) to bypass geometric local minima traps without triggering exponential branching.

## 🛰️ Current Operational Scope
- **Computational Engine:** Optimized via Numba JIT and SIMD (Single Instruction, Multiple Data) parallel vector math executing at direct hardware register level.
- **Experimental Boundaries:** Validated on large-scale stochastic 3-SAT instances (up to 10 Million clauses). 
- **Cryptographic Modeling Notice:** Hash-function mapping utilizes circuit-to-CNF translation layouts. The current iteration serves as an exploration into partial pre-image attacks on reduced-round cryptographic structures rather than live multi-thread mainnet hash exploitation.
