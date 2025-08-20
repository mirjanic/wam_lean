import Mathlib.Data.Nat.Factorial.Basic -- For Nat.factorial
import Mathlib.Tactic.Linarith -- For solving inequalities
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.ArithmeticFunction

import Canonical

open Nat ArithmeticFunction


noncomputable abbrev nthPrime (n : ℕ) := Nat.nth Nat.Prime n

lemma nth_prime_is_prime (n : ℕ) : Nat.Prime (nthPrime n) := Nat.nth_mem_of_infinite infinite_setOf_prime n 
lemma nth_prime_strict_mono : StrictMono nthPrime := Nat.nth_strictMono infinite_setOf_prime  
lemma nth_prime_injective : Function.Injective nthPrime := StrictMono.injective nth_prime_strict_mono 

lemma nth_prime_bound (n : ℕ) : n + 1 ≤ nthPrime n := by
  induction n with 
  | zero => 
    rw [nthPrime, nth_prime_zero_eq_two]
    exact le_of_ble_eq_true rfl
  | succ m ih => 
    suffices nthPrime m < nthPrime (m + 1) by 
      exact Lean.Grind.Nat.le_lo (m + 1) (nth Nat.Prime m) (nth Nat.Prime (m + 1)) 1 ih this
    rw [Nat.nth_lt_nth]
    . exact lt_add_one m
    exact infinite_setOf_prime

/- 
  Primorial 
-/

noncomputable def primorial : ℕ → ℕ
  | 0 => 1
  | succ n => (nthPrime n) * primorial n


@[simp] lemma primorial_zero : primorial 0 = 1 := by rfl
@[simp] lemma primorial_one : primorial 1 = 2 := by simp only [primorial, mul_one, nth_prime_zero_eq_two]
lemma primorial_succ (n : ℕ) : primorial (n + 1) = (nthPrime n) * primorial n := by
  rw [primorial]


theorem primorial_pos (n : ℕ) : primorial n > 0 := by
  induction n with
  | zero => simp [primorial_zero]
  | succ k ih =>
    rw [primorial_succ]
    apply mul_pos
    · exact Nat.Prime.pos (nth_prime_is_prime k)
    · exact ih

/-
  First n primes list
-/

noncomputable def first_n_primes_list : ℕ → List ℕ
  | 0 => []
  | Nat.succ n => first_n_primes_list n ++ [nthPrime n]


lemma in_first_n_primes_list {p n : ℕ} : p ∈ first_n_primes_list n → ∃ i < n, p = nthPrime i := by 
  intro hp 
  induction n with 
  | zero => 
    simp only [not_lt_zero', false_and, exists_const]
    simp only [first_n_primes_list, List.not_mem_nil] at hp
  | succ k ih => 
    rw [first_n_primes_list] at hp 
    apply exists_lt_succ_right.mpr
    apply List.mem_append.mp at hp
    cases hp with
    | inl h =>
      left
      simp_all only [forall_const]
    | inr h => 
      right 
      simp_all only [List.mem_cons, List.not_mem_nil, or_false]

lemma first_n_primes_max (n : ℕ) : (first_n_primes_list (n+1)).maximum = nthPrime n := by 
  induction n with 
  | zero => 
    rw [first_n_primes_list]
    simp only [nth_prime_zero_eq_two, cast_ofNat]
    rw [List.maximum_concat] 
    rfl
  | succ k ih => 
    rw [first_n_primes_list, List.maximum_concat, ih]
    apply max_eq_right_of_lt 
    apply WithBot.coe_lt_coe.mpr
    exact nth_prime_strict_mono (lt_add_one k)

/- lemma first_n_primes_map (n : ℕ) : first_n_primes_list n = (List.range n).map nthPrime := by  -/
/-   induction n with  -/
/-   | zero => rfl -/
/-   | succ k ih =>  -/
/-     rw [first_n_primes_list, ih] -/
/-     rw [show List.range (k+1) = List.range k ++ [k+1] by sorry] -/
/-     sorry -/

lemma first_n_primes_prod (n : ℕ) : (first_n_primes_list n).prod = primorial n := by 
  induction n with 
  | zero => 
    simp only [primorial_zero, first_n_primes_list]
    rfl
  | succ k ih => 
    rw [first_n_primes_list, primorial] 
    simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [ih]
    exact Nat.mul_comm (primorial k) (nthPrime k)

lemma first_n_primes_len (n : ℕ) : (first_n_primes_list n).length = n := by 
  induction n with 
  | zero => rfl
  | succ k ih =>
    unfold first_n_primes_list 
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
      Nat.add_right_cancel_iff]
    exact ih 

theorem nodup_first_n_primes (n : ℕ) : (first_n_primes_list n).Nodup := by 
  induction n with 
  | zero => exact List.dedup_eq_self.mp rfl 
  | succ k ih => 
    rw [first_n_primes_list]
    rw [← List.concat_eq_append]
    refine List.Nodup.concat ?_ ?_
    . apply in_first_n_primes_list.mt 
      apply not_exists.mpr
      intro i 
      by_contra h 
      obtain ⟨h1,h2⟩ := h
      apply (nth_prime_strict_mono h1).not_le 
      exact Nat.le_of_eq h2
    exact ih

theorem dedup_first_n_primes (n : ℕ) : (first_n_primes_list n) = (first_n_primes_list n).dedup := by 
  exact Eq.symm (List.Nodup.dedup (nodup_first_n_primes n))


abbrev le_sorted {α : Type} [LinearOrder α] (l : List α) := List.Sorted (fun x1 x2 => x1 ≤ x2) l

lemma first_n_primes_sorted (n : ℕ) : le_sorted (first_n_primes_list n) := by 
  induction n with 
  | zero => 
    rw [first_n_primes_list]
    exact List.sorted_nil
  | succ k ih =>
    rw [first_n_primes_list]
    rw [le_sorted, List.Sorted] at ⊢ ih
    rw [← List.reverse_reverse (first_n_primes_list k ++ [nthPrime k])]
    rw [← List.reverse_reverse (first_n_primes_list k)] at ih
    rw [List.pairwise_reverse] at ⊢ ih
    rw [List.reverse_concat', List.pairwise_cons]
    constructor 
    . intro a ha 
      rw [List.mem_reverse] at ha
      apply in_first_n_primes_list at ha 
      obtain ⟨i, h1, h2⟩ := ha 
      rw [h2]
      apply le_of_lt 
      exact nth_prime_strict_mono h1
    . exact ih

/- lemma first_n_primes_below_primeFactors {n : ℕ} (h : 1 < n) :  -/
/-     nthPrime (n.primeFactors.card - 1) ≤ n.primeFactors.max := by  -/
/-   sorry -/

/- 
  Main statements 
-/

lemma primorial_prime_factors_perm (n : ℕ) : (first_n_primes_list n).Perm (primorial n).primeFactorsList := by 
  apply Nat.primeFactorsList_unique 
  . rw [first_n_primes_prod n] 
  . intro p hp 
    apply in_first_n_primes_list at hp 
    obtain ⟨i, _, hi⟩ := hp 
    rw [hi]
    exact nth_prime_is_prime i

lemma sorted_list_perm_eq' {α : Type} [LinearOrder α] {n : ℕ} : ∀ l1 l2 : List α, 
  (le_sorted l1) → (le_sorted l2) → (l1.length = n) → (l2.length = n) → (l1.Perm l2) → l1 = l2 := by 
  induction n with 
  | zero => 
    intro l1 l2 _ _ h1 h2 hp 
    simp_all only [List.length_eq_zero_iff]
  | succ k ih =>
    intro l1 l2 h1 h2 hl1 hl2 hp
    cases l1 with 
    | nil => 
      simp_all only [List.sorted_nil, List.nil_perm, Nat.add_eq_left, one_ne_zero, imp_self,
        implies_true, List.length_nil, Nat.right_eq_add, Nat.add_eq_zero, and_false]
    | cons a as => 
      cases l2 with 
      | nil => 
        simp_all only [List.sorted_cons, List.length_cons, Nat.add_right_cancel_iff,
          List.sorted_nil, List.length_nil, Nat.right_eq_add, Nat.add_eq_zero, one_ne_zero,
          and_false]
      | cons b bs =>
        simp only [List.cons.injEq]
        suffices a = b by 
          constructor 
          . -- a = b 
            exact this
          . -- as = bs 
            apply ih as bs (List.Sorted.of_cons h1) (List.Sorted.of_cons h2) (succ_inj.mp hl1) (succ_inj.mp hl2) 
            simp_all only [List.sorted_cons, implies_true, and_self, List.length_cons,
              Nat.add_right_cancel_iff, List.perm_cons] 
        simp_all only [List.sorted_cons, implies_true, and_self, List.length_cons,
          Nat.add_right_cancel_iff] 
        have h1 := h1.1 
        have h2 := h2.1 
        clear ih hl1 hl2 
        have h_cons_self (x : α) (l : List α) (h : ∀ y ∈ l, x ≤ y) :  ∀ y ∈ (x :: l), x ≤ y := by 
          simp only [List.mem_cons, forall_eq_or_imp, le_refl, true_and]
          exact h
        rw [le_antisymm_iff]
        constructor 
        . -- a ≤ b 
          apply h_cons_self a as h1
          apply (List.Perm.mem_iff hp.symm).mp  
          exact List.mem_cons_self
        . -- b ≤ a 
          apply h_cons_self b bs h2 
          apply (List.Perm.mem_iff hp).mp  
          exact List.mem_cons_self


lemma sorted_list_perm_eq {α : Type} {l1 l2 : List α} [LinearOrder α]
    (h1 : le_sorted l1) (h2 : le_sorted l2) (hp : l1.Perm l2) : 
    l1 = l2 := by 
  let n := l1.length 
  have h : l2.length = n := by exact List.Perm.length_eq (_root_.id (List.Perm.symm hp))
  exact sorted_list_perm_eq' l1 l2 h1 h2 (_root_.id (Eq.symm h)) rfl hp
  
theorem primorial_prime_factors (n : ℕ) : (primorial n).primeFactorsList = first_n_primes_list n := by 
  apply sorted_list_perm_eq  
  . exact primeFactorsList_sorted (primorial n)
  . exact first_n_primes_sorted n 
  . exact List.Perm.symm (primorial_prime_factors_perm n)

theorem omega_primorial_eq_self (n : ℕ) : ω (primorial n) = n := by 
  rw [ArithmeticFunction.cardDistinctFactors_apply]
  rw [primorial_prime_factors n]
  rw [← dedup_first_n_primes n]
  exact first_n_primes_len n

lemma omega_impl_exists' {n k : ℕ} (hn : ω n = k) (hk : 0 < k) :
    ∃ x : ℕ, k-1 ≤ x ∧ nthPrime x ∣ n := by 

  sorry

lemma omega_impl_exists {n k : ℕ} (hn : ω n = k) (hk : 0 < k) : 
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ nthPrime (k-1) ≤ p := by 
  rw [cardDistinctFactors_apply] at hn
  have hnobot : n.primeFactors.max ≠ ⊥ := by sorry 
  set pmax := n.primeFactors.max.unbot hnobot with hpmax
  have hpmaxin : pmax ∈ n.primeFactors := by sorry
  use pmax
  constructor
  . -- prime 
    exact prime_of_mem_primeFactors hpmaxin 
  . constructor 
    . -- dvd 
      exact dvd_of_mem_primeFactors hpmaxin
    . -- le 
      if hk1 : 0 < k-1 then 


        let m := n / (pmax ^ (n.factorization pmax)) 
        have hm : ω n = k - 1 := by sorry
        obtain ⟨p, hp, hpdiv, hple⟩ := omega_impl_exists hm hk1
        
        sorry
      else 
        have heq : k = 1 := by 
          simp only [tsub_pos_iff_lt, not_lt] at hk1
          exact Eq.symm (Nat.le_antisymm hk hk1)
        rw [heq] 
        simp only [tsub_self, nth_prime_zero_eq_two, ge_iff_le]
        apply Prime.two_le 
        exact prime_of_mem_primeFactors hpmaxin

lemma pf_dedup_len {n : ℕ} : n.primeFactorsList.dedup.length = n.primeFactors.card := rfl

lemma primorial_le {k : ℕ} (h : 0 < k) : ∀ n : ℕ, ω n = k → primorial k ≤ n := by 
  induction k, h using Nat.le_induction with
  | base => 
    intro n hn 
    simp only [succ_eq_add_one, zero_add, primorial_one]
    simp only [succ_eq_add_one, zero_add] at hn
    contrapose! hn 
    interval_cases n 
    . simp only [cardDistinctFactors_zero, ne_eq, zero_ne_one, not_false_eq_true]
    . simp only [cardDistinctFactors_one, ne_eq, zero_ne_one, not_false_eq_true] 
  | succ k hk ih =>
    intro n hn 
    rw [primorial] 
    obtain ⟨p, hpprime, hpdvdn, hpbound⟩ := omega_impl_exists hn (Nat.add_pos_left hk 1) 
    have hn0 : n ≠ 0 := by 
      simp_all only [succ_eq_add_one, zero_add, add_tsub_cancel_right, ne_eq]
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [ArithmeticFunction.map_zero, reduceCtorEq]
    obtain ⟨e, m, hpm, hfactor⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p (Nat.Prime.ne_one hpprime) 
    have hm0 : m ≠ 0 := by 
      subst hfactor
      simp_all only [succ_eq_add_one, zero_add, add_tsub_cancel_right, mem_primeFactors, ne_eq, not_false_eq_true,
        and_true, true_and, _root_.mul_eq_zero, Nat.pow_eq_zero, not_or, not_and, Decidable.not_not]
    have hmdvdn : m ∣ n := Dvd.intro_left (p ^ e) (_root_.id (Eq.symm hfactor)) 
    have hm : m.primeFactors = n.primeFactors.erase p := by 
      apply Finset.Subset.antisymm 
      . rw [Finset.subset_iff]
        intro x hx 
        refine Finset.mem_erase_of_ne_of_mem ?_ ?_
        . -- x ≠ p
          suffices p ∉ m.primeFactors by 
            exact ne_of_mem_of_not_mem hx this
          simp only [mem_primeFactors, ne_eq, not_and, Decidable.not_not]
          exact fun _ a ↦ False.elim (hpm a)
        . -- x ∈ ... 
          rw [Nat.mem_primeFactors_of_ne_zero hn0] 
          rw [Nat.mem_primeFactors_of_ne_zero hm0] at hx 
          exact ⟨hx.1, dvd_trans hx.2 hmdvdn⟩
      . rw [Finset.subset_iff]
        intro x hx
        rw [mem_primeFactors]
        rw [Finset.mem_erase] at hx 
        obtain ⟨hxnep, hx⟩ := hx 
        rw [mem_primeFactors] at hx 
        refine ⟨hx.1, ?_, hm0⟩
        have h := hx.2.1 
        rw [hfactor, Nat.Prime.dvd_mul hx.1] at h
        rcases h with h1 | h2 
        . exfalso 
          apply Nat.Prime.dvd_of_dvd_pow hx.1 at h1
          rw [Nat.dvd_prime hpprime] at h1
          rcases h1 with hx1 | hxp 
          . apply Nat.not_prime_one 
            rw [← hx1] 
            exact hx.1
          . exact hxnep hxp
        . exact h2
    have he : 0 < e := by 
      by_contra h 
      simp only [not_lt, nonpos_iff_eq_zero] at h
      rw [h] at hfactor 
      simp only [pow_zero, one_mul] at hfactor
      have hp : p ∈ n.primeFactors := by 
        refine mem_primeFactors.mpr ?_
        exact ⟨hpprime, hpdvdn, hn0⟩
      have hnotp : p ∉ m.primeFactors := by 
        rw [hm] 
        exact Finset.notMem_erase p n.primeFactors
      rw [hfactor] at hp 
      exact hnotp hp
    rw [hfactor]
    apply mul_le_mul' 
    . -- nthPrime k ≤ p^e 
      calc nthPrime k = nthPrime (k + 1 - 1) := rfl
        _ ≤ p := hpbound
        _ ≤ p^e := le_pow he
    . -- primorial k ≤ m
      apply ih m 
      rw [cardDistinctFactors_apply, pf_dedup_len] at ⊢ hn 
      have h : k = n.primeFactors.card - 1 := by exact Nat.eq_sub_of_add_eq (_root_.id (Eq.symm hn))
      rw [h, hm]
      apply Finset.card_erase_of_mem 
      apply (mem_primeFactors_of_ne_zero hn0).mpr
      exact And.symm ⟨hpdvdn, hpprime⟩

theorem primorial_omega_le_self {n : ℕ} (h : 0 < ω n) : primorial (ω n) ≤ n := primorial_le h n rfl

-- Auxiliary theorem: primorial (m+1) > factorial (m+1) for m : ℕ
-- This covers all cases n ≥ 1 by letting n = m+1.
theorem primorial_gt_factorial_aux (m : ℕ) :
    primorial (m + 1) > factorial (m + 1) := by
  induction m with
  -- Base case: m = 0. We prove for m+1 = 1.
  | zero =>
    show primorial (0 + 1) > factorial (0 + 1) -- i.e., primorial 1 > factorial 1
    rw [primorial_succ 0, factorial_succ 0]     -- Expand primorial (0+1) and factorial (0+1)
    rw [primorial_zero, factorial_zero]         -- Expand primorial 0 and factorial 0
    rw [nthPrime, nth_prime_zero_eq_two]                          -- nthPrime 0 is 2
    -- Goal becomes: 2 * 1 > 1 * 1
    norm_num -- Proves 2 > 1

  -- Inductive step: m = j.
  -- ih : primorial (j + 1) > factorial (j + 1) (Inductive hypothesis for P(j+1))
  -- We want to show: primorial ((j + 1) + 1) > factorial ((j + 1) + 1) (Goal is P(j+2))
  | succ j ih =>
    show primorial (j + 1 + 1) > factorial (j + 1 + 1)
    rw [primorial_succ (j + 1), factorial_succ (j + 1)]
    -- Goal: nthPrime (j + 1) * primorial (j + 1) > ((j + 1) + 1) * factorial (j + 1)

    have h_mul_prim_gt_mul_fac : 
    (nthPrime (j + 1)) * primorial (j + 1) > (nthPrime (j + 1)) * factorial (j + 1) := by
      apply Nat.mul_lt_mul_of_pos_left
      · exact ih -- primorial (j + 1) > factorial (j + 1)
      · exact Prime.pos (nth_prime_is_prime (j + 1))
    
    simp_all only [gt_iff_lt]
    
    refine Nat.mul_lt_mul_of_le_of_lt' ?_ ?_ ?_
    . exact nth_prime_bound (j + 1) 
    . exact ih
    . exact zero_lt_succ (j + 1)

-- Main theorem: primorial n > n! for n ≥ 1
theorem primorial_gt_factorial_for_n_ge_1 (n : ℕ) (hn : n ≥ 1) :
    primorial n > factorial n := by
  cases n with
  | zero =>
    exfalso
    exact Nat.not_le_of_lt zero_lt_one hn 
  | succ m =>
    exact primorial_gt_factorial_aux m
