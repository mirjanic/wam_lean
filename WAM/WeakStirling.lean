import Mathlib.Data.Real.Basic -- For basic Real properties
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic -- For n!
import Mathlib.Analysis.SpecialFunctions.Log.Basic 


open Nat Real 


theorem weak_stirling {n : ℕ} (hn1 : n ≥ 1) : Real.log (Nat.factorial n) ≥ n * Real.log n - n + 1 := by 
  -- By induction on n ≥ 1
  refine Nat.le_induction (m := 1) ?base_case (fun k hk_ge_1 ih => ?inductive_step) n hn1
  case base_case => 
    simp only [factorial_one, cast_one, log_one, mul_zero, zero_sub, neg_add_cancel, ge_iff_le, le_refl]
  case inductive_step =>

    -- Define some commonly used terms and their positivity for logarithms and division
    let K : ℝ := k -- Cast k to Real
    let K_plus_1 : ℝ := K + 1 -- Cast (k+1) to Real. Note: (k:ℝ)+1 is defeq to ((k+1):ℕ):ℝ

    have h_K_pos : K > 0 := cast_pos'.mpr hk_ge_1
    have h_K_plus_1_pos : K_plus_1 > 0 := cast_add_one_pos k
    have h_fact_k_pos : (Nat.factorial k : ℝ) > 0 := Nat.cast_pos.mpr (Nat.factorial_pos k)

    -- Key inequality: K * Real.log (1 + 1/K) ≤ 1
    have key_ineq_log_approx : K * Real.log (1 + 1 / K) ≤ 1 := by
      suffices Real.log (1 + 1/K) ≤ 1 / K by
        . exact (le_mul_inv_iff₀' h_K_pos).mp this
      have h_one_div_K_pos : 1 / K > 0 := one_div_pos.mpr h_K_pos
      have h_X_pos : 1 + 1 / K > 0 := add_pos zero_lt_one h_one_div_K_pos
      apply le_trans (Real.log_le_sub_one_of_pos h_X_pos)
      exact add_tsub_le_left
    
     -- Start with LHS of P(k+1)
    calc Real.log (Nat.factorial (k + 1))
        = Real.log (↑(k + 1) * ↑(Nat.factorial k)) := by -- (k+1)! = (k+1) * k!
            rw [Nat.factorial_succ k, Nat.cast_mul]
      _ = Real.log K_plus_1 + Real.log (Nat.factorial k) := by -- log(a*b) = log a + log b for a,b > 0
            unfold K_plus_1 
            simp only [cast_add, cast_one]
            refine log_mul ?_ ?_ 
            . exact cast_add_one_ne_zero k 
            . exact Ne.symm (_root_.ne_of_lt h_fact_k_pos)
      _ ≥ Real.log K_plus_1 + (K * Real.log K - K + 1) := by -- Apply Inductive Hypothesis
            apply add_le_add_left ih
      _ ≥ K_plus_1 * Real.log K_plus_1 - K_plus_1 + 1 := by -- Final step using key_ineq_log_approx
        rw [ge_iff_le] 
        unfold K_plus_1 
        rw [add_mul K (1:ℝ) (Real.log (K + 1)), one_mul ] 
        suffices K * Real.log (K + 1) + Real.log (K + 1) - K ≤ Real.log (K + 1) + (K * Real.log K - K + 1) by linarith
        rw [add_comm (K * Real.log (K + 1)) (Real.log (K + 1))]
        suffices K * Real.log (K + 1) - K ≤ (K * Real.log K - K + 1) by linarith
        suffices K * Real.log (K + 1) ≤ K * Real.log K + 1 by linarith
        rw [← sub_le_iff_le_add']
        rw [← mul_sub K _ _]
        have h : Real.log (1 + 1 / K) = Real.log (K + 1) - Real.log K := by 
          calc Real.log (1 + 1 / K) = Real.log (K / K + 1 / K) := by 
                rw [(show K / K = 1 by exact div_self h_K_pos.ne')]
            _ = Real.log ((K + 1) / K) := by rw [@div_add_div_same]
            _ = Real.log (K + 1) - Real.log K := by
                rw [Real.log_div ?_ ?_]
                exact cast_add_one_ne_zero k
                exact Ne.symm (_root_.ne_of_lt h_K_pos)
        rw [← h]
        exact key_ineq_log_approx

    unfold K_plus_1 
    unfold K
    norm_cast

