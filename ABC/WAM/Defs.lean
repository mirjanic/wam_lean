import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.RingTheory.Ideal.Operations

import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Field.Basic

/- import Mathlib.NumberTheory.ArithmeticFunction -/

open Nat Finset PNat BigOperators Real ArithmeticFunction


namespace WAM.Helpers

  variable (n : ℕ)
  variable (s : ℝ)

  abbrev getPrimes : Finset ℕ := n.primeFactors

  abbrev getExponent (p : ℕ) : ℕ := n.factorization p

  noncomputable def termVal (p : ℕ) : ℝ := ((p : ℝ).log) ^ s

  noncomputable def denominator : ℝ := ∑ p ∈ getPrimes n, termVal s p

  noncomputable def numerator : ℝ := ∑ p ∈ getPrimes n, (getExponent n p : ℝ) * termVal s p


  -- The term (log p)^s is positive if p is a prime.
  lemma termVal_pos {s : ℝ} {p : ℕ} (hp_prime : p.Prime) :
    0 < termVal s p := by
    unfold termVal
    have hp_ge_two : p ≥ 2 := Nat.Prime.two_le hp_prime
    have hp_real_gt_one : (p : ℝ) > 1 := by exact_mod_cast Nat.lt_of_succ_le hp_ge_two
    have hlogp_pos : log (p : ℝ) > 0 := Real.log_pos hp_real_gt_one
    exact rpow_pos_of_pos hlogp_pos s

  -- The denominator of WAM is positive
  lemma denominator_pos (n : ℕ) (s : ℝ) (hn1 : n > 1) :
    denominator n s > 0 := by
    rw [denominator]
    rw [getPrimes]
    apply Finset.sum_pos
    . intro i
      intro h_in_support
      have h_prime : i.Prime := prime_of_mem_primeFactors h_in_support
      exact termVal_pos h_prime
    . simp_all only [gt_iff_lt, nonempty_primeFactors]

  -- The exponent is ≥ 1 for divisiors of n
  lemma divisor_exponent_ge_1
    (n p : ℕ) (hn1 : n > 1) (hp_mem : p ∈ getPrimes n) : 
    (getExponent n p ≥ 1) := by
    unfold getExponent
    unfold getPrimes at hp_mem
    convert_to 1 ≤ n.factorization p
    have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn1
    have h_prime : p.Prime := prime_of_mem_primeFactors hp_mem
    rw [<- Nat.Prime.dvd_iff_one_le_factorization h_prime hn0] 
    exact dvd_of_mem_primeFactors hp_mem

  -- The log term is 1 at s=0 
  lemma termVal_eq_1_at_s_0 (p : ℕ) : termVal 0 p = 1 := rpow_zero (Real.log ↑p)


end WAM.Helpers

noncomputable def WAM (n : ℕ) (s : ℝ) : ℝ := 
  (WAM.Helpers.numerator n s) / (WAM.Helpers.denominator n s)

-- Theorem: WAM(n,s) ≥ 1 for all n, s
theorem WAM_ge_1 (n : ℕ) (s : ℝ) (hn1 : n > 1) :
  WAM n s ≥ 1 := by

  let num := WAM.Helpers.numerator n s 
  let denom := WAM.Helpers.denominator n s 
  
  convert_to num / denom ≥ 1 
  
  have ineq : num ≥ denom := by
    unfold num denom WAM.Helpers.numerator WAM.Helpers.denominator
    apply Finset.sum_le_sum
    intro p hp_mem
    let term := WAM.Helpers.termVal s p 
    have h_term_pos : 0 < term := by 
      unfold term
      exact WAM.Helpers.termVal_pos (prime_of_mem_primeFactors hp_mem)
    rw [le_mul_iff_one_le_left h_term_pos]
    rw [Nat.one_le_cast]
    exact WAM.Helpers.divisor_exponent_ge_1 n p hn1 hp_mem

  let denom_pos : denom > 0 := WAM.Helpers.denominator_pos n s hn1
  
  exact (one_le_div₀ denom_pos).mpr ineq 


