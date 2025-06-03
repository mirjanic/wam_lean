import Mathlib.NumberTheory.ArithmeticFunction -- For ArithmeticFunction.cardDistinctPrimeFactors
import Mathlib.Analysis.Asymptotics.Defs -- For IsLittleO
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- For Real.log
import Mathlib.Data.Real.Basic -- For basic Real properties
/- import Mathlib.Topology.Instances.Real -- For Filter.atTop on ℕ, coercions to ℝ -/
import Mathlib.Data.Nat.Factorial.Basic -- For n!
import Mathlib.Analysis.SpecialFunctions.Stirling -- For log_factorial_ge_k_log_k_sub_k
import Mathlib.NumberTheory.PrimeCounting

import WAM.Primorial
import WAM.WeakStirling

open Filter Topology Nat Real Asymptotics ArithmeticFunction

/--
The function ω(n) (omega_real n), representing the number of distinct prime factors of n.
The result is cast to ℝ for asymptotic comparison.
Uses`ArithmeticFunction.cardDistinctPrimeFactors`.
-/
noncomputable def omega_real (n : ℕ) : ℝ := (ω n : ℝ)

/--
The natural logarithm of a natural number n, cast to ℝ.
`Real.log x` is the natural logarithm of x.
Note: By mathlib convention, `Real.log 0 = 0` and `Real.log 1 = 0`.
This is acceptable for asymptotics using `Filter.atTop` as we are interested in large n,
where n ≥ 2 and thus log (n : ℝ) > 0.
-/
noncomputable def log_of_nat (n : ℕ) : ℝ := Real.log (n : ℝ)

/--
The theorem stating that ω(n) is little-o of log n as n tends to infinity.
This means that the ratio ω(n) / log n tends to 0 as n → ∞.
Formally, for every ε > 0, there exists an N such that for all n ≥ N,
|ω(n)| ≤ ε * |log n|. Since ω(n) and log n (for n > 1) are positive,
this simplifies to ω(n) ≤ ε * log n.
-/
theorem omega_is_little_o_log_n : omega_real =o[atTop] log_of_nat := by
  
  let log_gt_omega_fact (n : ℕ) := log_of_nat n ≥ log_of_nat (ω n)!
  
  have h_log_gt_omega_factorial : ∀ᶠ (n : ℕ) in atTop, log_gt_omega_fact n := by 
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
    have h_log_prim : n ≥ prim := primorial_omega_le_self n 
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

  by_contra h_not_little_o
   
  simp only [IsLittleO, not_forall, not_eventually] at h_not_little_o
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
  
  have h_omega_unbounded_with_constriant: 
  ∀ (N : ℕ), (∃ᶠ (n : ℕ) in atTop, log_lt_omega n ∧ (ω n) > N) := by
    intro N
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
      have h : N < c * log_of_nat K := gt_of_ge_of_gt h1 h2
      have h := lt_trans h hltK 
      unfold omega_real at h 
      rw [← gt_iff_lt] at h 
      exact Nat.cast_lt.mp h 

    exact (not_le_of_gt hKN) (h K hKn hltK)

  
  have h_mega : 
  ∀ (N : ℕ), (∃ᶠ (x : ℕ) in atTop, (log_lt_omega x ∧ ω x > N) ∧ log_gt_omega_fact x) := by
    intro N 
    exact (h_omega_unbounded_with_constriant N).and_eventually h_log_gt_omega_factorial

  let N := Nat.ceil (Real.exp (2 + 1 / c))

  have h_bad_filter_at_big_n := h_mega N 

  rw [frequently_atTop] at h_bad_filter_at_big_n
  have h_bad_exists : ∃ n ≥ N, log_lt_omega n ∧ log_gt_omega_fact n ∧ ω n > N := by 
    have h := h_bad_filter_at_big_n N
    obtain ⟨n, hn, hcond⟩ := h 
    simp_all only [ge_iff_le, eventually_atTop, gt_iff_lt, one_div, ceil_le, log_gt_omega_fact, log_lt_omega, N]
    obtain ⟨w, h⟩ := h_log_gt_omega_factorial
    obtain ⟨left, right⟩ := hcond
    obtain ⟨left, right_1⟩ := left
    apply Exists.intro
    · apply And.intro
      on_goal 2 => apply And.intro
      on_goal 3 => apply And.intro
      on_goal 4 => {exact right_1
      }
      · simp_all only
      · simp_all only
      · simp_all only
  
  obtain ⟨n, hngtN, hlt, hgt, homegaN⟩ := h_bad_exists
  unfold log_lt_omega at hlt
  unfold log_gt_omega_fact at hgt

  have hlt : log_of_nat n < (omega_real n) / c := (lt_div_iff₀' hc_pos).mpr hlt
  have hltgt : (ω n) / c > log_of_nat (ω n)! := lt_of_le_of_lt hgt hlt
  have homegaN0 : ω n > 0 := zero_lt_of_lt homegaN 
  have hlogn : log_of_nat (ω n)! ≥ (ω n) * log_of_nat (ω n) - (ω n) + 1 := weak_stirling homegaN0 
  have hltgt : (ω n) / c > (ω n) * log_of_nat (ω n) - (ω n) + 1 := lt_of_le_of_lt hlogn hltgt
  have hlogomega : log_of_nat (ω n) > 2 + 1 / c := by 
    unfold N at homegaN 
    unfold log_of_nat
    have h : 0 < (ω n : ℝ) := cast_pos'.mpr homegaN0
    rw [gt_iff_lt, lt_log_iff_exp_lt h]
    have h : (ω n : ℝ) > ((Nat.ceil (Real.exp (2 + 1 / c))) : ℝ) := cast_lt.mpr homegaN
    exact lt_of_ceil_lt homegaN
  
  have h : (ω n) * log_of_nat (ω n) > (ω n) * (2 + 1/c) := (mul_lt_mul_left (cast_pos'.mpr homegaN0
)).mpr hlogomega

  have h :(ω n) * log_of_nat (ω n) - (ω n) + 1 > (ω n) * (2 + 1 / c) - (ω n) + 1 := by 
    rw [gt_iff_lt]
    rw [gt_iff_lt] at h
    have h := add_lt_add_right h (- (ω n) + 1)
    simp_all only [add_lt_add_iff_right, sub_lt_sub_iff_right]
  
  have h1 : (ω n) * (2 + 1 / c) - (ω n) + 1 > (ω n) + (ω n) / c := by 
      ring_nf
      simp only [gt_iff_lt, add_lt_add_iff_right, lt_add_iff_pos_left, zero_lt_one]

  have h : (ω n) * log_of_nat (ω n) - (ω n) + 1 > (ω n) + (ω n) / c := gt_trans h h1

  have hltgt : (ω n) / c > (ω n) / c := by 
    have h := gt_trans hltgt h 
    have g : (ω n) + (ω n) / c > (ω n) / c := by 
      simp_all only [lt_add_iff_pos_left, ofNat_pos, mul_pos_iff_of_pos_left, cast_pos]
    exact gt_trans h g

  exact (lt_self_iff_false (↑(ω n) / c)).mp hltgt

