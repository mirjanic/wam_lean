import Mathlib.Data.Nat.Basic
import Batteries.Data.Nat.Gcd
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow 

import ABC.WAM.Defs
import ABC.Asymptotics.OmegaGrowth

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

  
lemma pow_s_concave {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : ConcaveOn ℝ {x : ℝ | 0 ≤ x} (λ x ↦ x^s) := by 
  rw [show {x : ℝ | 0 ≤ x} = Set.Ici 0 by rfl]
  exact Real.concaveOn_rpow (le_of_lt h0) (le_of_lt h1)
  

lemma prime_factor_erase_num {p n k : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hk : k ≠ 0) : 
    (p^k * n).primeFactors.erase p = n.primeFactors.erase p := by 
  rw [Nat.primeFactors_mul (pow_ne_zero k (Nat.Prime.ne_zero hp)) hn]
  rw [Nat.primeFactors_prime_pow hk hp] 
  refine (Finset.erase_eq_iff_eq_insert ?_ ?_).mpr ?_
  . refine Finset.mem_union_left n.primeFactors ?_
    exact Finset.mem_singleton.mpr rfl
  . exact Finset.notMem_erase p n.primeFactors
  rw [Finset.insert_eq,
      ← Finset.sdiff_singleton_eq_erase p n.primeFactors]
  exact Eq.symm Finset.union_sdiff_self_eq_union

lemma prime_factors_erase_eq {n k : ℕ} (h : ¬ k ∣ n) : n.primeFactors.erase k = n.primeFactors := by 
  apply Finset.erase_eq_self.mpr
  apply Nat.dvd_of_mem_primeFactors.mt
  exact h

lemma rad_le {n : ℕ} (h : 0 < n) : ∏ i ∈ n.primeFactors, i ≤ n := by 
  apply le_of_dvd
  . exact h 
  . exact Nat.prod_primeFactors_dvd n

lemma log_rad_le {n : ℕ} (h : 0 < n) : ∑ p ∈ n.primeFactors, Real.log (p:ℝ) ≤ Real.log n := by
  set lhs := ∑ p ∈ n.primeFactors, Real.log (p:ℝ) with h_lhs 
  set rhs := Real.log n with h_rhs 
  rw [← StrictMono.le_iff_le Real.exp_strictMono]
  unfold rhs 
  rw [Real.exp_log (cast_pos'.mpr h)] 
  unfold lhs 
  rw [Real.exp_sum]
  suffices ∏ x ∈ n.primeFactors, Real.exp (Real.log ↑x) = ∏ x ∈ n.primeFactors, x by 
    rw [this] 
    exact cast_le.mpr (rad_le h) 
  rw [cast_prod]
  apply Finset.prod_congr rfl
  intro x hx 
  apply Real.exp_log
  simp_all only [cast_pos, mem_primeFactors, ne_eq, lhs, rhs]
  exact Prime.pos hx.1


/-
-- pow2triples 
-/ 

abbrev pow2triple (k : ℕ) := 2^k * (2^k+1)

lemma one_lt_pow2triple (k : ℕ) : 1 < pow2triple k := by 
  unfold pow2triple 
  apply Nat.one_lt_mul_iff.mpr
  constructor 
  . exact Nat.two_pow_pos k
  constructor 
  . exact zero_lt_succ (2 ^ k)
  right 
  apply Nat.lt_add_of_pos_left
  exact Nat.two_pow_pos k


lemma pow2triple_factorization_two {k : ℕ} (hk : k ≠ 0) : (pow2triple k).factorization 2 = k := by 
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
  
lemma two_in_pow2triple_primes (k : ℕ) : 2 ∈ WAM.Helpers.getPrimes (pow2triple k) := by 
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

lemma herase2 {k : ℕ} (hk : 0 < k) : 
    WAM.Helpers.getPrimes (2^k+1) = (WAM.Helpers.getPrimes (pow2triple k)).erase 2 := by 
  unfold WAM.Helpers.getPrimes pow2triple
  apply Eq.symm
  calc (2^k * (2^k+1)).primeFactors.erase 2 = (2^k+1).primeFactors.erase 2 := by 
        refine prime_factor_erase_num ?_ ?_ ?_ 
        . exact prime_two 
        . exact Ne.symm (zero_ne_add_one (2 ^ k))
        . exact Nat.ne_zero_of_lt hk
    _ =  (2 ^ k + 1).primeFactors := by 
        refine prime_factors_erase_eq ?_
        have h : 2^k = 2 * 2^(k-1 : ℕ) := by 
          refine Eq.symm (mul_pow_sub_one ?_ 2)   
          exact Nat.ne_zero_of_lt hk
        rw [h]
        exact Nat.two_not_dvd_two_mul_add_one (2^(k-1))

/-
-- Main theorem 
-/


def h_omega_growth := omega_is_little_o_log_n
noncomputable def f_base (s : ℝ) (k : ℕ) := (Real.log 2)^s + (ω k : ℝ)^(1-s) * (Real.log k)^s
def pow2 (k : ℕ) := 2^k + 1 
noncomputable def f (s : ℝ) := (f_base s) ∘ pow2
def linear : ℕ → ℝ := Nat.cast

lemma fbase_littleo_log {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 
    f_base s =o[atTop] log_of_nat := by 
  let f_base := f_base s
  calc f_base = (λ k ↦ (λ _ ↦ Real.log 2 ^ s) k + (λ x ↦ omega_real x ^ (1 - s) * log_of_nat x ^ s) k) := by 
        rw [funext_iff] 
        intro k 
        unfold f_base omega_real log_of_nat
        rfl
    _ =O[atTop] (λ k ↦ omega_real k ^ (1 - s) * log_of_nat k ^ s) := by
        apply Asymptotics.IsBigO.add 
        . rw [Asymptotics.isBigO_const_left_iff_pos_le_norm ?_]
          . use 1 
            constructor 
            . exact zero_lt_one 
            . rw [Filter.eventually_atTop] 
              use 3
              intro k hk 
              unfold omega_real log_of_nat 
              simp only [norm_mul, Real.norm_eq_abs]
              apply one_le_mul_of_one_le_of_one_le
              . suffices 1 ≤ ((ω k) : NNReal) ^ (1 - s) by 
                  rw [abs_of_pos]
                  . exact this 
                  . exact lt_of_lt_of_le zero_lt_one this 
                apply NNReal.one_le_rpow
                . rw [cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors k]
                  norm_cast 
                  rw [Finset.one_le_card, Nat.nonempty_primeFactors]
                  linarith
                . linarith
              . suffices 1 ≤ (Real.log (k : ℝ)) ^ s by 
                  rw [abs_of_pos]
                  . exact this 
                  . exact lt_of_lt_of_le zero_lt_one this

                rw [← Real.exp_zero, ← Real.le_log_iff_exp_le]
                . rw [Real.log_rpow]
                  . apply mul_nonneg 
                    . exact le_of_lt hs0 
                    . apply Real.log_nonneg 
                      rw [Real.le_log_iff_exp_le]
                      . rw [ge_iff_le] at hk
                        apply le_of_lt
                        apply lt_trans Real.exp_one_lt_d9
                        suffices 3 ≤ (k:ℝ) by 
                          linarith
                        exact ofNat_le_cast.mpr hk 
                      . norm_cast
                        linarith
                  . apply Real.log_pos
                    norm_cast
                    linarith
                . rw [Real.rpow_def_of_pos] 
                  . exact Real.exp_pos (Real.log (Real.log ↑k) * s)
                  . apply Real.log_pos
                    norm_cast
                    linarith
          . rw [ne_eq] 
            rw [Real.rpow_eq_zero_iff_of_nonneg] 
            . rw [not_and_or] 
              left 
              simp only [Real.log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or]
              linarith
            . exact Real.log_nonneg one_le_two 
        . exact Asymptotics.isBigO_refl (fun x ↦ omega_real x ^ (1 - s) * log_of_nat x ^ s) atTop
    _ =o[atTop] (λ k ↦ log_of_nat k ^ (1 - s) * log_of_nat k ^ s) := by 
        apply Asymptotics.IsLittleO.mul_isBigO ?_ ?_
        . exact omega_s_is_little_o_log_n_s hs1
        . exact Asymptotics.isBigO_refl (fun x ↦ log_of_nat x ^ s) atTop 
    _ = log_of_nat := by 
        rw [funext_iff]
        intro k 
        calc log_of_nat k ^ (1 - s) * log_of_nat k ^ s = (log_of_nat k)^((1 - s) + s) := by 
              if h : 0 < log_of_nat k then
                apply Eq.symm 
                apply Real.rpow_add
                exact h 
              else 
                have h : log_of_nat k = 0 := by 
                  suffices 0 ≤ log_of_nat k by 
                    apply Eq.symm
                    rw [← LE.le.not_lt_iff_eq this] 
                    exact h
                  exact Real.log_natCast_nonneg k 
                rw [h]
                simp only [sub_add_cancel, Real.rpow_one, _root_.mul_eq_zero]
                right 
                apply Real.zero_rpow
                exact Ne.symm (_root_.ne_of_lt hs0)
        _ = log_of_nat k := by 
            simp only [sub_add_cancel, Real.rpow_one]


lemma f_littleo_log_pow2 {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 
    (f s) =o[atTop] (log_of_nat ∘ pow2) := by
  let f := f s
  apply Asymptotics.IsLittleO.comp_tendsto 
  . exact fbase_littleo_log hs0 hs1
  . apply StrictMono.tendsto_atTop
    apply strictMono_nat_of_lt_succ 
    intro n 
    unfold pow2 
    refine Nat.add_lt_add_right ?_ 1
    refine Nat.pow_lt_pow_of_lt ?_ ?_
    . exact Nat.one_lt_two
    . exact lt_add_one n

lemma f_littleo_linear {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 
    (f s) =o[atTop] linear := by
  let f := f s
  
  apply Asymptotics.IsLittleO.trans_isBigO (f_littleo_log_pow2 hs0 hs1)
  rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
  rw [Filter.eventually_atTop]
  use 1
  intro b hb
  let c := Real.log 4 
  use c 
  intro n hn 
  unfold log_of_nat pow2 linear 
  simp only [Function.comp_apply, cast_add, cast_pow, cast_ofNat, cast_one, Real.norm_eq_abs]
  have hn : 1 ≤ n := Nat.le_trans hb hn
  simp only [abs_cast]
  suffices Real.log (2^n + 1) ≤ c * n by 
    rw [abs_eq_self.mpr ?_]
    . exact this
    apply Real.log_nonneg 
    norm_cast 
    exact Nat.le_add_left 1 (2 ^ n)
  unfold c 
  rw [Real.log_le_iff_le_exp ?_]
  swap 
  . norm_cast 
    exact zero_lt_succ (2 ^ n)
  rw [mul_comm]
  rw [Real.exp_nat_mul]
  rw [Real.exp_log four_pos]
  norm_cast
  have h_2_le_2n : 2 ≤ 2^n := Bound.le_self_pow_of_pos one_le_two hn
  calc 2^n + 1 ≤ 2^n + 2 := le_succ (2 ^ n + 1) 
    _ ≤ 2^n + 2^n := Nat.add_le_add_iff_left.mpr h_2_le_2n 
    _ = 2 * 2^n := Eq.symm (Nat.two_mul (2 ^ n)) 
    _ ≤ 2^n * 2^n := Nat.mul_le_mul_right (2 ^ n) h_2_le_2n
    _ = (2 * 2)^n := Eq.symm (Nat.mul_pow 2 2 n) 
    _ = 4^n := by exact rfl

lemma sum_erase {α β : Type} [DecidableEq α] [AddCommMonoid β] 
  {s : Finset α} {x₀ : α} (f : α → β) (h : x₀ ∈ s): 
    ∑ x ∈ s, f x = f x₀ + ∑ x ∈ s.erase x₀, f x := by 
  set t := s.erase x₀ with ht 
  have hs : s = insert x₀ t := by exact Eq.symm (Finset.insert_erase h) 
  rw [hs, Finset.sum_insert]
  exact Finset.notMem_erase x₀ s

theorem wam_of_pow2_triples_diverges (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : 
atTop.Tendsto (λ k ↦ WAM (2^k * (2^k + 1)) s) atTop := by 

  unfold WAM

  /-
  -- Define numerator and denominator 
  -/
  let num (k : ℕ) := WAM.Helpers.numerator (pow2triple k) s 
  have h_num_def (k : ℕ) : num k = WAM.Helpers.numerator (pow2triple k) s := rfl

  let denom (k : ℕ) := WAM.Helpers.denominator (pow2triple k) s 
  have h_denom_def (k : ℕ) : denom k = WAM.Helpers.denominator (pow2triple k) s := rfl

  have h_denom_pos (k : ℕ) : 0 < denom k := by 
    refine WAM.Helpers.denominator_pos (pow2triple k) s ?_
    exact one_lt_pow2triple k

  have h_num_pos (k : ℕ) : num k > 0 := by 
    have h := WAM_ge_1 (pow2triple k) s (one_lt_pow2triple k) 
    unfold WAM at h 
    rw [← h_num_def, ← h_denom_def] at h 
    suffices num k ≥ denom k by 
      exact lt_of_lt_of_le (h_denom_pos k) this
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
        simp only [inv_inv]
        . rw [mul_comm]
          exact this 
        . simp only [inv_pos]
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
      rw [← Finset.add_sum_erase (WAM.Helpers.getPrimes (pow2triple k)) f (two_in_pow2triple_primes k)]
      simp only [ge_iff_le, le_add_iff_nonneg_right]
      refine Finset.sum_nonneg fun i a ↦ hf0 i ?_
      simp only [Finset.mem_erase, ne_eq] at a
      obtain ⟨_, a⟩ := a 
      unfold WAM.Helpers.getPrimes at a 
      exact prime_of_mem_primeFactors a
    
    unfold WAM.Helpers.termVal c 
    simp only [cast_ofNat, mul_eq_mul_right_iff, Nat.cast_inj]
    left 
    exact pow2triple_factorization_two hk 

  /-
  -- denom k is o(k)
  -/
  have h_denom : denom =o[atTop] linear := by 
     
    clear h_num h_num_pos h_num_def 
    clear_value num 

    let f := f s
    have hf := f_littleo_linear hs0 hs1
        
    /-
    -- Now we only need to show that denom grows not faster than f
    -/
    suffices denom =O[atTop] f by
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
    have hk1 : 1 < k := lt_of_le_of_lt' hk hkmin
    let denom_k := denom k
    let ome := ω (2^k + 1)
    have home : 0 < ome := by
      unfold ome 
      rw [ArithmeticFunction.cardDistinctFactors_apply]
      suffices (2 ^ k + 1).primeFactors.Nonempty by 
        exact List.length_pos_iff_exists_mem.mpr this
      rw [Nat.nonempty_primeFactors]
      simp only [lt_add_iff_pos_left, ofNat_pos, pow_pos]
    
    let coeff (_ : ℕ) : ℝ := 1 / ↑ ome
        
    set expr1 := ∑ p ∈ WAM.Helpers.getPrimes (2^k+1), (coeff p) * (Real.log p)^s with hexpr1 
    have h_denom_k : denom_k = (Real.log 2)^s + ome * expr1 := by 
      calc denom_k = WAM.Helpers.denominator (pow2triple k) s := by rfl 
        _ = ∑ p ∈ (pow2triple k).primeFactors, (Real.log p)^s := by rfl
        _ = Real.log 2^s + ∑ p ∈ (pow2triple k).primeFactors.erase 2, (Real.log p)^s := by 
            apply sum_erase
            exact two_in_pow2triple_primes k
        _ = Real.log 2^s + ∑ p ∈ (WAM.Helpers.getPrimes (pow2triple k)).erase 2, (Real.log p)^s := by rfl 
        _ = Real.log 2^s + ∑ p ∈ WAM.Helpers.getPrimes (2^k+1), (Real.log (Nat.cast p))^s := by 
          rw [← herase2]
          exact zero_lt_of_lt hk
        _ = Real.log 2^s + ∑ p ∈ WAM.Helpers.getPrimes (2^k+1), (Real.log p)^s := by rfl
        _ = Real.log 2^s + ∑ p ∈ WAM.Helpers.getPrimes (2^k+1), ↑ome * (1 / ↑ome) * (Real.log p)^s := by 
          ring_nf
          rw [mul_inv_cancel₀]
          . simp only [one_mul]
          . simp only [ne_eq, cast_eq_zero] 
            exact Nat.ne_zero_of_lt home
        _ = Real.log 2^s + ↑ome * ∑ p ∈ WAM.Helpers.getPrimes (2^k+1), (1 / ↑ome) * (Real.log p)^s := by
          rw [Finset.mul_sum]
          ring_nf
        _ = Real.log 2^s + ↑ome * expr1 := by rfl
    set expr2 := (∑ p ∈ WAM.Helpers.getPrimes (2^k+1), (coeff p) * Real.log p)^s with hexpr2
    
    set expr3 := ome^(-s) * (∑ p ∈ (WAM.Helpers.getPrimes (2^k+1) : Finset ℕ), Real.log (p:ℝ))^s with hexpr3 
    set expr4 := ome^(-s) * (Real.log (2^k+1))^s with hexpr4

    /-
    -- Jensens inequality
    -/
    have hrel1 : expr1 ≤ expr2 := by
      
      unfold expr1 expr2 
      refine ConcaveOn.le_map_sum (pow_s_concave hs0 hs1) ?_ ?_ ?_
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
          exact Real.log_natCast_nonneg p
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
      suffices (∑ p ∈ (WAM.Helpers.getPrimes (2 ^ k + 1):Finset ℕ), Real.log ↑p) ^ s ≤ Real.log (2 ^ k + 1) ^ s by 
        refine (mul_le_mul_iff_of_pos_left ?_).mpr this
        exact Real.rpow_pos_of_pos (cast_pos.mpr home) (-s)
      suffices (∑ p ∈ (WAM.Helpers.getPrimes (2 ^ k + 1):Finset ℕ), Real.log ↑p) ≤ Real.log (2 ^ k + 1) by 
        refine Real.rpow_le_rpow ?_ this ?_
        . suffices ∀ p ∈ WAM.Helpers.getPrimes (2 ^ k + 1), 0 ≤ Real.log (p : ℝ) by 
            exact Finset.sum_nonneg this
          intro p _ 
          exact Real.log_natCast_nonneg p
        . exact le_of_lt hs0
      
      rw [← Real.log_prod (WAM.Helpers.getPrimes (2 ^ k + 1)) (fun x ↦ x) ?_] 
      . unfold WAM.Helpers.getPrimes 
        rw [Real.log_le_log_iff ?_ ?_] 
        . -- ∏ i ∈ (2 ^ k + 1).primeFactors, ↑i ≤ 2 ^ k + 1
          suffices ∏ i ∈ (2 ^ k + 1).primeFactors, i ≤ 2 ^ k + 1 by
            rify at this 
            exact this
          apply rad_le 
          exact Nat.add_pos_right (2 ^ k) hcpos
        . -- 0 < ∏ i ∈ (2 ^ k + 1).primeFactors, ↑i
          apply Finset.prod_pos
          intro p hp 
          rw [mem_primeFactors] at hp  
          exact_mod_cast Prime.pos hp.1 
        . -- 0 < 2 ^ k + 1
          exact_mod_cast zero_lt_succ (2^k)
      intro p hp 
      unfold WAM.Helpers.getPrimes at hp
      simp only [mem_primeFactors, ne_eq, Nat.add_eq_zero, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
        false_and, one_ne_zero, and_self, not_false_eq_true, and_true] at hp 
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
    calc WAM.Helpers.denominator (pow2triple k) s = Real.log 2^s + ome * expr1  := h_denom_k
      _ ≤ (Real.log 2)^s + ome * expr2 := by
        refine (add_le_add_iff_left (Real.log 2 ^ s)).mpr ?_
        refine (mul_le_mul_iff_of_pos_left ?_).mpr hrel1
        exact cast_pos'.mpr home
      _ = (Real.log 2)^s + ome * expr3 := by
        simp only [add_right_inj, mul_eq_mul_left_iff, cast_eq_zero]
        left 
        exact hrel2
      _ ≤ (Real.log 2)^s + ome * expr4 := by 
        refine (add_le_add_iff_left (Real.log 2 ^ s)).mpr ?_
        refine (mul_le_mul_iff_of_pos_left ?_).mpr hrel3
        exact cast_pos'.mpr home
      _ = (Real.log 2) ^ s + ome^(1-s) *  Real.log (2 ^ k + 1) ^ s  := by
        suffices ome * expr4 = ome ^ (1 - s) * Real.log (2 ^ k + 1) ^ s by
          exact congrArg (HAdd.hAdd (Real.log 2 ^ s)) this
        unfold expr4
        rw [← mul_assoc]
        suffices (ome:ℝ) * (ome:ℝ)^(-s) = (ome:ℝ)^(1-s) by 
          rw [this]
        rw [show 1 - s = 1 + (-s) by rfl]
        rw [Real.rpow_add (show 0 < (ome:ℝ) by exact cast_pos'.mpr home) 1 (-s)]
        simp only [Real.rpow_one]
      _ = c * f k := by
        unfold c f  _root_.f pow2 f_base ome
        simp only [cast_one, Function.comp_apply, cast_add, cast_pow, cast_ofNat, one_mul]

  exact Asymptotics.IsLittleO.trans_isBigO h_denom h_num

