import numpy as np
import time
# Importing both the powerful engines from your solver file
from solver import HybridSingularityEngine, GraviSAT_UltraEngine

class GraviSAT_MasterController:
    def __init__(self, clauses, num_variables):
        self.clauses = clauses
        self.n = num_variables
        self.num_clauses = len(clauses)

    def launch_optimal_engine(self):
        print("\n================= GraviSAT MISSION CONTROL =================")
        print(f"[SCAN] Total Constraints Loaded : {self.num_clauses:,}")
        print(f"[SCAN] Total Logic Variables    : {self.n:,}")
        
        # Calculate Clause-to-Variable Ratio to detect problem structure complexity
        ratio = self.num_clauses / self.n if self.n > 0 else 0
        print(f"[SCAN] Density Ratio Determined : {ratio:.2f}")

        # AUTOMATION LOGIC (Faisla):
        # 1. Agar data 50,000 se bada hai, toh raw hardware speed chahiye -> Select GraviSAT V4
        # 2. Agar data chota hai par density high hai (Uljhi hui problem), toh dimaag chahiye -> Select Hybrid CDCL
        if self.num_clauses >= 50000:
            print("[DECISION] Massive Scale Detected! Deploying GraviSAT V4 (Ultra-Silicon SIMD Core)...")
            time.sleep(1)
            engine = GraviSAT_UltraEngine(self.clauses, self.n)
            solution, success = engine.collapse_system()
            engine_name = "GraviSAT V4 (Raw Speed)"
        else:
            print("[DECISION] High Complexity / Small Scale Map! Deploying Hybrid CDCL-Matrix Engine...")
            time.sleep(1)
            engine = HybridSingularityEngine(self.clauses, self.n)
            solution, success = engine.collapse_system()
            engine_name = "Hybrid Engine (CDCL Brain)"

        print("\n=================== FINAL MISSION REPORT ===================")
        print(f"Engine Deployed : {engine_name}")
        print(f"Breach Status   : {'SUCCESS ✅' if success else 'TIMEOUT ❌'}")
        if success:
            # Display first 20 bits as sample if variable count is too large
            display_bits = solution.astype(int)
            if len(display_bits) > 20:
                print(f"Solution Vector (Sample) : {display_bits[:20]} ... [Truncated]")
            else:
                print(f"Solution Vector          : {display_bits}")
        print("============================================================")
        return solution, success

if __name__ == "__main__":
    # --- AUTOMATIC DEMO RUNNER ---
    # Scenario A: Creating a small but dense structured puzzle
    print("Testing Scenario A: Small Uljhi Hui Problem...")
    small_dense_dataset = [[1, -2, 3], [-1, 2, 4], [3, -4, -1], [-2, -3, 4]]
    controller_A = GraviSAT_MasterController(small_dense_dataset, num_variables=4)
    controller_A.launch_optimal_engine()

    print("\n" + "-"*60 + "\n")

    # Scenario B: Simulating a massive 1 Lakh dataset load
    print("Testing Scenario B: Massive Data Load...")
    np.random.seed(42)
    mega_vars = 500
    mega_clauses = 100000
    vars_chosen = np.random.randint(1, mega_vars + 1, size=(mega_clauses, 3))
    signs_chosen = np.random.choice([1, -1], size=(mega_clauses, 3))
    large_dataset = (vars_chosen * signs_chosen).tolist()

    controller_B = GraviSAT_MasterController(large_dataset, num_variables=mega_vars)
    controller_B.launch_optimal_engine()
    
