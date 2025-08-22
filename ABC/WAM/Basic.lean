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

import ABC.WAM.Defs

open Nat Finset PNat BigOperators Real ArithmeticFunction

-- Theorem: WAM(n,s) = 1 if n is squarefree
theorem WAM_eq_1_for_squarefree
  (n : ℕ) (s : ℝ) (hn1 : n > 1) (hsq : Squarefree n) :
  WAM n s = 1 := by
    
    let num := WAM.Helpers.numerator n s 
    let denom := WAM.Helpers.denominator n s 

    convert_to num / denom = 1
    
    have eq : num = denom := by
      unfold num denom WAM.Helpers.numerator WAM.Helpers.denominator 

      apply Finset.sum_equiv (Equiv.refl ℕ)
      . exact fun i ↦ Eq.to_iff rfl 
      . intro p hp_mem
        have h_exple1 : n.factorization p ≤ 1 := by
          have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn1
          simp_all [Nat.squarefree_iff_factorization_le_one hn0]
        have h_expge1 : n.factorization p ≥ 1 := WAM.Helpers.divisor_exponent_ge_1 n p hn1 hp_mem  
        have h_exp1 : WAM.Helpers.getExponent n p = 1 := by
          unfold WAM.Helpers.getExponent
          exact Eq.symm (Nat.le_antisymm h_expge1 h_exple1)
        rw [h_exp1]
        simp

    let denom_pos : denom > 0 := WAM.Helpers.denominator_pos n s hn1
    
    refine (div_eq_one_iff_eq ?_).mpr eq
    exact Ne.symm (_root_.ne_of_lt denom_pos) 


-- Theorem: W(n^k,s) = k * W(n,s)
theorem WAM_exp_n 
  (n k : ℕ) (s : ℝ) (hn1 : n > 1) (hk0 : k > 0) :
  WAM (n^k) s = k * WAM n s := by 
    
    have h_k_ne_0 : k ≠ 0 := Nat.ne_zero_of_lt hk0
      
    let num_k := WAM.Helpers.numerator (n^k) s 
    let denom_k := WAM.Helpers.denominator (n^k) s

    let num := WAM.Helpers.numerator n s 
    let denom := WAM.Helpers.denominator n s 

    rw [show WAM n s = num / denom by rfl]
    rw [show WAM (n^k) s = num_k / denom_k by rfl]
    
    have hnk1 : n^k > 1 := by
      refine one_lt_pow ?_ hn1
      exact Nat.ne_zero_of_lt hk0

    have h_denom_pos : denom > 0 := WAM.Helpers.denominator_pos n s hn1
    have h_denom_n0 : denom ≠ 0 := Ne.symm (_root_.ne_of_lt h_denom_pos)

    have h_denom_k_pos : denom_k > 0 := WAM.Helpers.denominator_pos (n^k) s hnk1
    have h_denom_k_n0 : denom_k ≠ 0 := Ne.symm (_root_.ne_of_lt h_denom_k_pos)

    have h_same_primes : WAM.Helpers.getPrimes (n^k) = WAM.Helpers.getPrimes n := Nat.primeFactors_pow n h_k_ne_0 

    have h_exponents_k (p : ℕ) : k * WAM.Helpers.getExponent n p = WAM.Helpers.getExponent (n^k) p := by 
      unfold WAM.Helpers.getExponent 
      rw [Nat.factorization_pow n k]
      exact rfl

    have h_denom_same : denom = denom_k := by
      unfold denom denom_k WAM.Helpers.denominator 
      simp_all only [gt_iff_lt, ne_eq, denom_k, denom]
      
    have h_num_k : num_k = num * k := by
      unfold num_k num WAM.Helpers.numerator
      rw [h_same_primes, Finset.sum_mul] 
      apply Finset.sum_equiv (Equiv.refl ℕ)
      . exact fun i ↦ Eq.to_iff rfl
      . intro p hp_mem
        simp only [Equiv.refl_apply]
        rw [← h_exponents_k p]
        rw [cast_mul]
        exact mul_rotate (↑k) (↑(WAM.Helpers.getExponent n p)) (WAM.Helpers.termVal s p)
     
    rw [h_num_k, h_denom_same]
    ring_nf


-- Theorem: WAM(n^k,s) = k if k is squarefree
theorem WAM_for_squarefree_power
  (n k : ℕ) (s : ℝ) (hn1 : n > 1) (hk0 : k > 0) (hsq : Squarefree n) :
  WAM (n^k) s = k := by
     let h_wam : WAM n s = 1 := WAM_eq_1_for_squarefree n s hn1 hsq
     let h_wam_k : WAM (n^k) s = k * WAM n s := WAM_exp_n n k s hn1 hk0
     rw [h_wam_k, h_wam, mul_one]


-- Theorem: W(n,0) = Ω n / ω n 
theorem WAM_for_s_eq_0 (n : ℕ) : WAM n 0 = Ω n / ω n := by 
  
  let num := WAM.Helpers.numerator n 0 
  let denom := WAM.Helpers.denominator n 0 
  
  have h_num_Ω : num = Ω n := by 
    unfold num WAM.Helpers.numerator WAM.Helpers.getPrimes  
    conv =>
      lhs
      congr
      . rw [← n.toFinset_factors]
      . unfold WAM.Helpers.getExponent 
        simp only [WAM.Helpers.termVal_eq_1_at_s_0, nsmul_eq_mul, mul_one]
        intro p
        rw [← Nat.primeFactorsList_count_eq]
    rw [ArithmeticFunction.cardFactors_apply, ← cast_sum]
    norm_cast
    rw [List.sum_toFinset_count_eq_length n.primeFactorsList]

  have h_denom_ω : denom = ω n := by 
    unfold denom WAM.Helpers.denominator WAM.Helpers.getPrimes 
    conv =>
      lhs
      congr
      . skip
      . simp only [WAM.Helpers.termVal_eq_1_at_s_0]
    simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    rfl

  rw [← h_num_Ω, ← h_denom_ω]
  rfl

