import Mathlib.Data.Nat.Basic
import Batteries.Data.Nat.Gcd
import Mathlib.Algebra.Group.Defs -- For one_mul
import Mathlib.Data.Finite.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Monotone.Basic

import WAM.Defs
import WAM.OmegaGrowth

import Canonical

open Nat Set Filter ArithmeticFunction 

lemma tendsto_inv_littleo {α : Type} {l : Filter α} {f g : α → ℝ}
  (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 < g x) 
  (h_tendsto_zero : Tendsto (fun x ↦ f x / g x) l (nhds 0)) : 
  Tendsto (fun k ↦ g k / f k) l atTop  := by
  
  let fn (x : α) := f x / g x 
  have hfn (x : α) : fn x = f x / g x  := by rfl
  have hfnpos (x : α) : 0 < fn x := by 
    exact _root_.div_pos (hf x) (hg x) 
    
  suffices Tendsto fn⁻¹ l atTop by 
    conv at this =>
      congr
      . unfold fn 
        intro x 
        simp only [Pi.inv_apply, inv_div]
      . skip 
      . skip
    exact this

  have h_tendsto : Tendsto fn l (nhds 0) := by
    unfold fn 
    exact h_tendsto_zero
  
  clear_value fn 
  clear! h_tendsto_zero hfn hg hf 

  suffices Filter.Tendsto fn l (nhdsWithin 0 (Set.Ioi 0)) by 
    exact Filter.Tendsto.inv_tendsto_nhdsGT_zero this
  
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within fn h_tendsto ?_ 
  apply Filter.Eventually.of_forall hfnpos
  
lemma exp_s_concave {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : ConcaveOn ℝ {x : ℝ | 0 < x} (λ x ↦ x^s) := by 
  have hderiv : (deriv fun x ↦ x ^ s) = fun x ↦ s * x ^ (s-1) := by 
    sorry 
  have hderiv2 : (deriv^[2] (fun x ↦ x ^ s)) = fun x ↦ s * (s-1) * s ^ (s-2) := by sorry
  apply concaveOn_of_deriv2_nonpos
  . exact convex_Ioi 0 
  . suffices Continuous (fun x ↦ x ^ s) by 
      exact Continuous.continuousOn this
    exact Real.continuous_rpow_const (le_of_lt h0)
  . suffices DifferentiableOn ℝ (fun x : ℝ => x ^ s) {0}ᶜ by
      refine DifferentiableOn.mono this ?_
      refine subset_compl_singleton_iff.mpr ?_
      sorry 
    exact Real.differentiableOn_rpow_const s
    
  . sorry -- differentiable 2x 
  . intro x hx -- main concavity
    have h1 : s * (s - 1) < 0 := by sorry 
    have h2 : 0 < x ^ (s - 2) := by sorry 
    sorry



theorem wam_of_pow2_triples_diverges (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : 
atTop.Tendsto (λ k ↦ WAM (2^k * (2^k + 1)) s) atTop := by 

  unfold WAM

  let pow2triple (k : ℕ) := 2^k * (2^k+1)
  have hpown1 (k : ℕ) : 1 < pow2triple k := by 
    unfold pow2triple 
    refine Nat.one_lt_mul_iff.mpr ?_
    constructor 
    . exact Nat.two_pow_pos k
    constructor 
    . exact zero_lt_succ (2 ^ k)
    right 
    refine Nat.lt_add_of_pos_left ?_
    exact Nat.two_pow_pos k


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

  let denom (k : ℕ) := WAM.Helpers.denominator (pow2triple k) s 
  have h_denom_def (k : ℕ) : denom k = WAM.Helpers.denominator (pow2triple k) s := rfl

  have h_denom_pos (k : ℕ) : 0 < denom k := by 
    refine WAM.Helpers.denominator_pos (pow2triple k) s ?_
    exact hpown1 k

  have h_num_pos (k : ℕ) : num k > 0 := by 
    have h := WAM_ge_1 (pow2triple k) s (hpown1 k) 
    unfold WAM at h 
    rw [← h_num_def, ← h_denom_def] at h 
    suffices num k ≥ denom k by 
      exact gt_of_ge_of_gt this (h_denom_pos k)
    exact (one_le_div₀ (h_denom_pos k)).mp h
    
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
    exact tendsto_inv_littleo h_denom_pos h_num_pos this 


  let linear (n : ℕ) : ℝ := n

  /-
  -- num k grows as fast as k
  -/
  have h_num : linear =O[atTop] num := by 
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
     
    clear h_num h_num_pos h_num_def 
    clear_value num 

    let h_omega_growth := omega_is_little_o_log_n
    let f (k : ℕ) := (Real.log 2)^s + (ω (2^k + 1) : ℝ)^(1-s) * (Real.log (2^k + 1))^s
    
    have hf : f =o[atTop] linear := by
      /- unfold omega_real log_of_nat at h_omega_growth   -/
      /- clear h_denom_def h_denom_pos h_2inprimes h_2 hpown1 -/
      /- have h : atTop.Tendsto pow2triple atTop := sorry  -/
      
      sorry  -- from h_omega_growth, compose with pow2triple
    
    /-
    -- Now we only need to show that denom grows not faster than f
    -/
    suffices denom =O[atTop] f by -- will need to change
      exact Asymptotics.IsBigO.trans_isLittleO this hf
    
    rw [Asymptotics.isBigO_iff]

    
    let c := 1 
    have hcpos : 0 < c := Nat.one_pos
    use c 
    rw [eventually_atTop]
    let k_min := 1000 
    have hkmin : 1 < k_min := by exact one_lt_succ_succ 998
    use k_min

    intro k hk
    let denom_k := denom k
    let ome := ω (2^k + 1)
    have home : 0 < ome := by
      unfold ome 
      rw [ArithmeticFunction.cardDistinctFactors_apply]
      suffices (2 ^ k + 1).primeFactors.Nonempty by 
        exact List.length_pos_iff_exists_mem.mpr this
      rw [Nat.nonempty_primeFactors]
      simp only [lt_add_iff_pos_left, ofNat_pos, pow_pos]
    
    let coeff (k : ℕ) : ℝ := 1 / ↑ ome

    have herase2 : WAM.Helpers.getPrimes (2^k+1) = (WAM.Helpers.getPrimes (pow2triple k)).erase 2 := by 
      sorry

    set expr1 := ∑ p ∈ WAM.Helpers.getPrimes (2^k+1), (coeff p) * (Real.log p)^s with hexpr1 
    have h_denom_k : denom_k = (Real.log 2)^s + ome * expr1 := by 
      /- unfold denom_k denom ome expr1 coeff ome -/
      sorry
    set expr2 := (∑ p ∈ WAM.Helpers.getPrimes (2^k+1), (coeff p) * Real.log p)^s with hexpr2
    
    set expr3 := ome^(-s) * (∑ p ∈ WAM.Helpers.getPrimes (2^k+1), Real.log p)^s with hexpr3 
    set expr4 := ome^(-s) * (Real.log (2^k+1))^s with hexpr4

    /-
    -- Jensens inequality
    -/
    have hrel1 : expr1 ≤ expr2 := by
      
      unfold expr1 expr2 
      refine ConcaveOn.le_map_sum (exp_s_concave hs0 hs1) ?_ ?_ ?_
      . -- coeffs positive
        intro p _ 
        unfold coeff 
        simp only [one_div, inv_nonneg, cast_nonneg]
        
      . -- sum of coeffs is 1 
        unfold coeff 
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
        unfold WAM.Helpers.getPrimes ome 
        suffices (2^k+1).primeFactors.card = ω (2^k+1) by 
          generalize (2^k+1).primeFactors.card = n at this ⊢
          unfold ome at home
          generalize ω (2^k + 1) = m at this home ⊢ 
          rw [this] 
          field_simp 

        simp [ArithmeticFunction.cardDistinctFactors]
        exact rfl

      . -- log p in valid range 
        intro p hp 
        suffices 1 < p by
          simp only [mem_setOf_eq]
          exact Real.log_pos (one_lt_cast.mpr this)
        suffices p.Prime by 
          exact Prime.one_lt this
        unfold WAM.Helpers.getPrimes at hp
        exact prime_of_mem_primeFactors hp


    have hrel2 : expr2 = expr3 := by
      unfold expr2 expr3 coeff 
      rw [← Finset.mul_sum (WAM.Helpers.getPrimes (2 ^ k + 1)) (fun x ↦ Real.log (x:ℝ)) (1 / (ome:ℝ))]
      rw [Real.mul_rpow] 
      . simp only [mul_eq_mul_right_iff]
        left 
        calc ((1:ℝ) / ome)^s = ((ome:ℝ)⁻¹) ^ s := by 
              refine (Real.rpow_left_inj ?_ ?_ ?_).mpr ?_
              . exact one_div_cast_nonneg ome 
              . exact inv_nonneg.mpr (cast_nonneg' ome)
              . exact Ne.symm (_root_.ne_of_lt hs0) 
              . exact one_div (ome:ℝ)
          _ = ((ome:ℝ) ^ s)⁻¹ := Real.inv_rpow (cast_nonneg ome) s 
          _ = ome ^ (-s) := Eq.symm (Real.rpow_neg (cast_nonneg ome) s)
      . exact one_div_cast_nonneg ome 
      . suffices ∀ p ∈ WAM.Helpers.getPrimes (2 ^ k + 1), 0 ≤ Real.log (p : ℝ) by 
          exact Finset.sum_nonneg this
        intro p _ 
        exact Real.log_natCast_nonneg p

    have hrel3 : expr3 ≤ expr4 := by
      unfold expr3 expr4 
      suffices (∑ p ∈ WAM.Helpers.getPrimes (2 ^ k + 1), Real.log ↑p) ^ s ≤ Real.log (2 ^ k + 1) ^ s by 
        refine (mul_le_mul_iff_of_pos_left ?_).mpr this
        exact Real.rpow_pos_of_pos (cast_pos.mpr home) (-s)
      suffices (∑ p ∈ WAM.Helpers.getPrimes (2 ^ k + 1), Real.log ↑p) ≤ Real.log (2 ^ k + 1) by 
        refine Real.rpow_le_rpow ?_ this ?_
        . suffices ∀ p ∈ WAM.Helpers.getPrimes (2 ^ k + 1), 0 ≤ Real.log (p : ℝ) by 
            exact Finset.sum_nonneg this
          intro p _ 
          exact Real.log_natCast_nonneg p
        . exact le_of_lt hs0
      
      rw [← Real.log_prod (WAM.Helpers.getPrimes (2 ^ k + 1)) (fun x ↦ (x:ℝ)) ?_] 
      . unfold WAM.Helpers.getPrimes 
        rw [Real.log_le_log_iff ?_ ?_] 
        . sorry -- by Nat.prod_primeFactorsList
        . sorry  
        . sorry
      intro p hp 
      unfold WAM.Helpers.getPrimes at hp
      simp only [mem_primeFactors, ne_eq, Nat.add_eq_zero, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
        false_and, one_ne_zero, and_self, not_false_eq_true, and_true, linear] at hp 
      rw [cast_ne_zero]
      exact Nat.ne_zero_of_lt ( Nat.Prime.pos hp.1)

    -- end with tendsto... 

    simp only [Real.norm_eq_abs, ge_iff_le]

    suffices denom k ≤ c * f k by 
      calc |denom k| = denom k := (abs_of_pos (h_denom_pos k)) 
        _ ≤ c * f k := this 
        _ ≤ c * |f k| := by 
          refine (mul_le_mul_iff_of_pos_left ?_).mpr ?_
          . exact cast_pos'.mpr hcpos
          . exact le_abs_self (f k)

    unfold denom
    
    -- Apply relations to finish computation
    calc WAM.Helpers.denominator (pow2triple k) s  = (Real.log 2)^s + ome * expr1  := h_denom_k
      _ ≤ (Real.log 2)^s + ome * expr2 := by
        refine (add_le_add_iff_left (Real.log 2 ^ s)).mpr ?_
        refine (mul_le_mul_iff_of_pos_left ?_).mpr hrel1
        exact cast_pos'.mpr home
      _ = (Real.log 2)^s + ome * expr3 := by
        exact congrArg (HAdd.hAdd (Real.log 2 ^ s)) (congrArg (HMul.hMul ↑ome) hrel2)
      _ ≤ (Real.log 2)^s + ome * expr4 := by 
        refine (add_le_add_iff_left (Real.log 2 ^ s)).mpr ?_
        refine (mul_le_mul_iff_of_pos_left ?_).mpr hrel3
        exact cast_pos'.mpr home
      _ = Real.log 2 ^ s + ome^(1-s) *  Real.log (2 ^ k + 1) ^ s  := by
        suffices ome * expr4 = ome ^ (1 - s) * Real.log (2 ^ k + 1) ^ s by
          exact congrArg (HAdd.hAdd (Real.log 2 ^ s)) this
        unfold expr4
        rw [← mul_assoc]
        suffices (ome:ℝ) * (ome:ℝ)^(-s) = (ome:ℝ)^(1-s) by 
          rw [this]
        rw [show 1 - s = 1 + (-s) by rfl]
        rw [Real.rpow_add (show 0 < (ome:ℝ) by exact cast_pos'.mpr home) 1 (-s)]
        simp only [pow_one, Real.rpow_one]
      _ = c * f k := by
        unfold c f ome
        simp only [cast_one, one_mul]

  exact Asymptotics.IsLittleO.trans_isBigO h_denom h_num

