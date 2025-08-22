import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.PrimeCounting

import ABC.Primorials.Basic
import ABC.Asymptotics.WeakStirling

open Filter Topology Nat Real Asymptotics ArithmeticFunction

/-
  The function ω(n) (omega_real n), representing the number of distinct prime factors of n.
  The result is cast to ℝ for asymptotic comparison.
  Uses`ArithmeticFunction.cardDistinctPrimeFactors`.
-/
noncomputable def omega_real : ℕ → ℝ := Nat.cast ∘ ω

/-
  The natural logarithm of a natural number n, cast to ℝ.
  `Real.log x` is the natural logarithm of x.
  Note: By mathlib convention, `Real.log 0 = 0` and `Real.log 1 = 0`.
  This is acceptable for asymptotics using `Filter.atTop` as we are interested in large n,
  where n ≥ 2 and thus log (n : ℝ) > 0.
-/
noncomputable def log_of_nat (n : ℕ) : ℝ := Real.log (n : ℝ)


/- 
lemmas
-/

def log_gt_omega_fact (n : ℕ) := log_of_nat n ≥ log_of_nat (ω n)!
  
lemma h_log_gt_omega_factorial : ∀ᶠ (n : ℕ) in atTop, log_gt_omega_fact n := by 
  rw [eventually_atTop]
  unfold log_gt_omega_fact log_of_nat
  let a := 2
  use a 
  intro n hn 
  let k := ω n
  have hk : 0 < k := by 
    unfold k 
    rw [ArithmeticFunction.cardDistinctFactors_apply]
    have hn : 1 < n := by exact lt_of_add_left_lt hn
    rw [← Nat.nonempty_primeFactors] at hn 
    exact List.length_pos_iff_exists_mem.mpr hn

  let prim := primorial k
  have h_log_prim : n ≥ prim := primorial_omega_le_self hk 
  have h_prim_omega : prim > k.factorial := primorial_gt_factorial_for_n_ge_1 k hk
  have h_omegas : ω n = ω prim := by 
    convert_to k = ω (primorial k)
    exact Eq.symm (omega_primorial_eq_self k)

  have h : prim > (ω prim).factorial := lt_of_eq_of_lt (congrArg factorial (_root_.id (Eq.symm h_omegas))) h_prim_omega
  have h : n > (ω prim).factorial := Nat.lt_of_lt_of_le h h_log_prim
  have h : n > (ω n).factorial := Nat.lt_of_lt_of_le h_prim_omega h_log_prim
  have h : Real.log n > Real.log (ω n).factorial := by 
    rw [gt_iff_lt]
    rw [Real.log_lt_log_iff ?_ ?_]
    . exact cast_lt.mpr h
    . norm_cast
      exact factorial_pos (ω n)
    . norm_cast
      exact zero_lt_of_lt hn
  exact le_of_lt h


/-
  The theorem stating that ω(n) is little-o of log n as n tends to infinity.
  This means that the ratio ω(n) / log n tends to 0 as n → ∞.
  Formally, for every ε > 0, there exists an N such that for all n ≥ N,
  |ω(n)| ≤ ε * |log n|. Since ω(n) and log n (for n > 1) are positive,
  this simplifies to ω(n) ≤ ε * log n.
-/
theorem omega_is_little_o_log_n : omega_real =o[atTop] log_of_nat := by
  
  by_contra h_not_little_o
   
  simp only [IsLittleO, not_forall] at h_not_little_o
  rcases h_not_little_o with ⟨c, hc_pos, h_freq_norm⟩
  
  rw [isBigOWith_iff] at h_freq_norm
  rw [Filter.not_eventually] at h_freq_norm

  let log_lt_omega (n : ℕ) := c * log_of_nat n < omega_real n 

  conv at h_freq_norm =>
    congr
    . intro n 
      rw [not_le, norm_eq_abs, norm_eq_abs]
      unfold log_of_nat omega_real
      rw [abs_of_nonneg (log_natCast_nonneg n), ← log_of_nat]
      rw [abs_of_nonneg (cast_nonneg' (ω n)), ← omega_real]
      change log_lt_omega n
    . skip
  
  have h_omega_unbounded_with_constriant (N : ℕ): 
      ∃ᶠ (n : ℕ) in atTop, log_lt_omega n ∧ (ω n) > N := by
    by_contra h 
    rw [Filter.not_frequently] at h 
    simp [Filter.Eventually] at h 

    obtain ⟨n, h⟩ := h
    -- Use h_freq_gt_and_lt to show that there exists K > N, such that 
    -- K > n, log_lt_omega K, log_gt_omega_fact K 
    let x := 1 + n + Nat.ceil (Real.exp (N / c))
    have hx0 : x > 0 := pos_of_neZero x
    have hxn : x ≥ n := le_add_right_of_le (Nat.le_add_left n 1)
    simp [frequently_atTop] at h_freq_norm
    obtain ⟨K, hK, hltK⟩ := h_freq_norm x
    
    have hKn : K ≥ n := Nat.le_trans hxn hK 
    have hKN : ω K > N := by 
      unfold log_lt_omega at hltK 
      have h1 : c * log_of_nat x ≤ c * log_of_nat K := by 
        unfold log_of_nat 
        have h : Real.log x ≤ Real.log K := by 
           refine log_le_log ?_ ?_
           exact cast_pos'.mpr hx0
           exact cast_le.mpr hK
        exact (mul_le_mul_iff_of_pos_left hc_pos).mpr h
      have h2 : N < c * log_of_nat x := by 
        unfold log_of_nat x 
        have h (r : ℝ) : r < 1 + n + Nat.ceil r := by 
          convert_to r < n + (1 + Nat.ceil r) 
          . ring_nf 
          . refine lt_add_of_nonneg_of_lt n.cast_nonneg ?_
            calc r ≤ Nat.ceil r       := le_ceil r  -- Lemma: r ≤ ⌈r⌉₊
                 _ < (Nat.ceil r) + 1 := lt_add_one (Nat.ceil r : ℝ) -- Lemma: x < x + 1 for any x
                 _ = 1 + Nat.ceil r   := add_comm _ _ -- Lemma: a + b = b + a 
        have h : Real.exp (N / c) < 1 + n + Nat.ceil (Real.exp (N / c)) := h (Real.exp (N / c))
        rw [← Real.log_lt_log_iff] at h 
        . have h := mul_lt_mul_of_pos_left h hc_pos 
          simp at h 
          convert_to N < c * Real.log (1 + n + Nat.ceil (Real.exp (N / c))) at h
          . rw [div_eq_mul_inv]
            rw [mul_left_comm c N c⁻¹]
            rw [← div_eq_mul_inv c c]
            rw [div_self hc_pos.ne']
            rw [mul_one]
          norm_cast at h 
        . exact Real.exp_pos (N / c)
        . norm_cast
      have h : N < c * log_of_nat K := lt_of_lt_of_le h2 h1
      have h := lt_trans h hltK 
      unfold omega_real at h 
      rw [← gt_iff_lt] at h 
      exact Nat.cast_lt.mp h 

    exact (not_le_of_gt hKN) (h K hKn hltK)

  
  have h_mega (N : ℕ) : 
      ∃ᶠ (x : ℕ) in atTop, (log_lt_omega x ∧ ω x > N) ∧ log_gt_omega_fact x :=
    (h_omega_unbounded_with_constriant N).and_eventually h_log_gt_omega_factorial

  let N := Nat.ceil (Real.exp (1 + 1 / c))
  obtain ⟨n, hn, ⟨⟨hlt, homegaN⟩, hgt⟩⟩ := (frequently_atTop.mp (h_mega N)) N

  unfold log_lt_omega at hlt
  unfold log_gt_omega_fact at hgt
  
  have h_log_ceil_exp (x : ℝ) : x ≤ Real.log (Nat.ceil (Real.exp x)) := by 
    apply exp_le_exp.mp 
    rw [exp_log]
    . apply ceil_le.mp (Nat.le_refl ⌈rexp x⌉₊)
    . exact_mod_cast ceil_pos.mpr (exp_pos x)
  have hN0 : 0 < N := ceil_pos.mpr (exp_pos (1 + 1 / c))
  have hcN : 1 ≤ c * (log_of_nat N - 1) := by calc 
    1 ≤ c * ((1 + 1 / c) - 1) := by grind only 
    _ ≤ c * (Real.log (Nat.ceil (Real.exp (1 + 1 / c))) - 1) := by 
        rw [mul_le_mul_iff_of_pos_left hc_pos] 
        grind only
    _ = c * (log_of_nat N - 1) := by rfl

  contrapose! hcN
  
  rw [←mul_lt_mul_iff_of_pos_right (cast_pos.mpr (zero_lt_of_lt homegaN)), mul_assoc, ←lt_div_iff₀' hc_pos, one_mul]

  calc (log_of_nat N - 1) * ω n < (log_of_nat N - 1) * ω n + 1 := by grind only
    _ = ω n * (log_of_nat N) - ω n + 1 := by ring_nf
    _ ≤ (ω n) * log_of_nat (ω n) - (ω n) + 1 := by 
        suffices log_of_nat N < log_of_nat (ω n) by 
          simp only [add_le_add_iff_right, tsub_le_iff_right, sub_add_cancel, ge_iff_le]
          rw [mul_le_mul_iff_of_pos_left]
          . exact le_of_lt this
          . grind only [cast_pos]
        unfold log_of_nat 
        rw [log_lt_log_iff]
        . grind only [cast_lt]
        . grind only [cast_pos]
        . grind only [cast_pos] 
    _ ≤ log_of_nat (ω n)! := weak_stirling (one_le_of_lt homegaN)
    _ ≤ log_of_nat n := hgt
    _ < omega_real n  / c := (lt_div_iff₀' hc_pos).mpr hlt
  

theorem isLittleO_rpow {α : Type} {l : Filter α} {s : ℝ} {f g : α → ℝ} 
  (ho : f =o[l] g) (hs0 : 0 < s) (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : ∀ᶠ x in l, 0 ≤ g x) :
    (fun x => (f x) ^ s) =o[l] (fun x => (g x) ^ s) := by 
  rw [isLittleO_iff] at ho ⊢
  intro c hc 
  have hcs : 0 < c ^ (1 / s) := rpow_pos_of_pos hc (1 / s)
  obtain ho := ho hcs 
  filter_upwards [ho, hf, hg]
  intro x hx hf hg 
  have hfs : 0 ≤ f x ^ s := rpow_nonneg hf s
  have hgs : 0 ≤ g x ^ s := rpow_nonneg hg s 
  rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg hfs, abs_of_nonneg hgs]
  rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg] at hx
  calc f x ^ s ≤ (c ^ (1 / s) * g x)^s := by 
        rw [rpow_le_rpow_iff]
        . exact hx 
        . exact hf 
        . exact (mul_nonneg_iff_of_pos_left hcs).mpr hg
        . exact hs0
    _ = (c ^ (1 / s)) ^ s * g x ^ s := mul_rpow (le_of_lt hcs) hg
    _ = c ^ (1 / s * s) * g x ^ s := by 
      rw [rpow_mul]
      exact le_of_lt hc
    _ = c * g x ^ s := by 
      ring_nf 
      rw [mul_inv_cancel₀]
      . simp only [rpow_one] 
        exact CommMonoid.mul_comm c (g x ^ s)
      . exact Ne.symm (_root_.ne_of_lt hs0)

theorem omega_s_is_little_o_log_n_s {s : ℝ} (hs1 : s < 1) : 
    (fun x ↦ omega_real x ^ (1 - s)) =o[atTop] fun x ↦ log_of_nat x ^ (1 - s) := by 
  refine isLittleO_rpow omega_is_little_o_log_n (sub_pos.mpr hs1) ?_ ?_ 
  . apply Filter.Eventually.of_forall
    intro n 
    unfold omega_real 
    simp only [Function.comp_apply, cast_nonneg]
  . apply Filter.Eventually.of_forall 
    intro n 
    unfold log_of_nat 
    exact log_natCast_nonneg n
