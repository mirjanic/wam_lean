import Mathlib.Data.Nat.Basic
import Batteries.Data.Nat.Gcd
import Mathlib.Algebra.Group.Defs -- For one_mul
import Mathlib.Data.Finite.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Monotone.Basic

import WAM.Defs
import WAM.OmegaGrowth

open Nat Set Filter ArithmeticFunction 


lemma tendsto_inv_littleo {α : Type} {l : Filter α} {f g : α → ℝ} (hf : f > 0) (hg : g > 0) 
(h_tendsto_zero : Tendsto (fun x ↦ f x / g x) l (nhds 0)) : Tendsto (fun k ↦ g k / f k) l atTop  := by


  sorry



theorem wam_of_pow2_triples_diverges (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : 
atTop.Tendsto (λ k ↦ WAM (2^k * (2^k + 1)) s) atTop := by 

  unfold WAM 
  let pow2triple (k : ℕ) := 2^k * (2^k+1)
  have h_2 (k : ℕ) (hk : k ≠ 0) : (pow2triple k).factorization 2 = k := by 
    unfold pow2triple 
    rw [Nat.factorization_mul_apply_of_coprime]
    . rw [Nat.Prime.factorization_pow]
      . simp only [Finsupp.single_eq_same, Nat.add_eq_left]
        have h := factorization_eq_zero_of_remainder (2^(k-1)) (Nat.Prime.not_dvd_one prime_two) 
        rw [mul_comm,
            ← pow_succ 2 (k-1), 
            Nat.sub_add_cancel (show 1 ≤ k by exact one_le_iff_ne_zero.mpr hk)
            ] at h 
        exact h
      . exact prime_two
    . refine (coprime_add_iff_right ?_).mpr ?_
      . exact Nat.dvd_refl (2 ^ k)
      . exact gcd_pow_left_of_gcd_eq_one rfl
  have h_2inprimes (k : ℕ) : 2 ∈ WAM.Helpers.getPrimes (pow2triple k) := by 
    unfold WAM.Helpers.getPrimes
    rw [Nat.mem_primeFactors]
    constructor 
    . exact prime_two 
    constructor
    . unfold pow2triple
      cases k
      . exact Nat.dvd_mul_left 2 (2 ^ 0)
      . (expose_names; refine Nat.dvd_mul_right_of_dvd ?_ (2 ^ (n + 1) + 1))
        exact Dvd.intro_left (Nat.pow 2 n) rfl
    . exact Ne.symm (NeZero.ne' (pow2triple k))

  /-
  -- Define numerator and denominator 
  -/
  let num (k : ℕ) := WAM.Helpers.numerator (pow2triple k) s 
  have h_num_def (k : ℕ) : num k = WAM.Helpers.numerator (pow2triple k) s := rfl
  have h_num_pos (k : ℕ) : num k > 0 := by sorry 

  let denom (k : ℕ) := WAM.Helpers.denominator (pow2triple k) s 
  have h_denom_def (k : ℕ) : denom k = WAM.Helpers.denominator (pow2triple k) s := rfl
  have h_denom_pos (k : ℕ) : denom k > 0 := by sorry

  /-
  -- Simplify numerator and denominator exprs
  -/
  suffices atTop.Tendsto (λ k ↦ (num k) / (denom k)) atTop by 
    conv =>
      congr
      . intro k 
        congr 
        . rw [← h_num_def k]
        . rw [← h_denom_def k] 
      . skip
      . skip 
    exact this
  
  /-
  -- Divergence iff numerator grows strictly faster than denominator
  -/
  suffices denom =o[atTop] num by 
    -- Goal: Tendsto (fun k ↦ num k / denom k) atTop atTop 
    apply Asymptotics.IsLittleO.tendsto_div_nhds_zero at this 
    refine tendsto_inv_littleo ?_ ?_ this 
    . exact lt_of_strongLT h_denom_pos
    . exact lt_of_strongLT h_num_pos


  let linear (n : ℕ) : ℝ := n

  /-
  -- num k grows as fast as k
  -/
  have h_nom : linear =O[atTop] num := by 
    let c := (Real.log 2)^s 
    have hc : c > 0 := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) s
    suffices ∀ k ≠ 0, num k ≥ k * c by 
      rw [Asymptotics.isBigO_iff]
      use 1/c 
      rw [eventually_atTop]
      use 1 
      intro k hk
      simp only [Real.norm_eq_abs, abs_cast, one_div, linear] 
      suffices k * c ≤ num k by 
        simp only [abs_of_pos (h_num_pos k)]
        rw [← inv_mul_le_iff₀]
        simp only [inv_inv, linear]
        . rw [mul_comm]
          exact this 
        . simp only [inv_pos, linear]
          exact hc
      exact this k (Nat.ne_zero_of_lt hk)

    intro k hk
    unfold num WAM.Helpers.numerator 

    suffices (WAM.Helpers.getExponent (pow2triple k) 2) * WAM.Helpers.termVal s 2 = k * c by 
      rw [← this]
      let f (p : ℕ) := ↑(WAM.Helpers.getExponent (pow2triple k) p) * WAM.Helpers.termVal s p
      have hf (p : ℕ) : f p = ↑(WAM.Helpers.getExponent (pow2triple k) p) * WAM.Helpers.termVal s p := by rfl
      have hf0 (p : ℕ) (hp : p.Prime) : f p ≥ 0 := by 
        unfold f 
        simp [WAM.Helpers.termVal_pos hp]
      rw [← hf]
      conv =>
        congr 
        . congr 
          . skip
          . intro p 
            rw [← hf p]
        . skip
      rw [← Finset.add_sum_erase (WAM.Helpers.getPrimes (pow2triple k)) f (h_2inprimes k)]
      simp only [ge_iff_le, le_add_iff_nonneg_right, linear]
      refine Finset.sum_nonneg fun i a ↦ hf0 i ?_
      simp only [Finset.mem_erase, ne_eq, linear] at a
      obtain ⟨_, a⟩ := a 
      unfold WAM.Helpers.getPrimes at a 
      exact prime_of_mem_primeFactors a
    
    unfold WAM.Helpers.termVal c 
    simp only [cast_ofNat, mul_eq_mul_right_iff, Nat.cast_inj]
    left 
    exact h_2 k hk 

  /-
  -- denom k is o(k)
  -/
  have h_denom : denom =o[atTop] linear := by 
    

    let f (k : ℕ) := (ω (pow2triple k) : ℝ)^(1-s) * (Real.log (pow2triple k)^s)
    
    have hf : f =o[atTop] linear := by
      
      sorry  -- from h_omega_growth
    
    /-
    -- Now we only need to show that denom grows not faster than f
    -/
    suffices ∀ k ≠ 0, denom k < f k by 
      let h_omega_growth := omega_is_little_o_log_n
      unfold log_of_nat omega_real at h_omega_growth 
      
      sorry -- combine omega_growth and this

    

    sorry -- hardest

  exact Asymptotics.IsLittleO.trans_isBigO h_denom h_nom
