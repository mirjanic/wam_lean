import Mathlib.Data.Nat.Factorial.Basic -- For Nat.factorial
import Mathlib.Tactic.Linarith -- For solving inequalities
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.ArithmeticFunction

import ABC.Primorials.Defs

open Nat ArithmeticFunction

lemma primorial_prime_factors_perm (n : ℕ) : (first_n_primes_list n).Perm (primorial n).primeFactorsList := by 
  apply Nat.primeFactorsList_unique 
  . rw [first_n_primes_prod n] 
  . intro p hp 
    obtain ⟨i, _, hi⟩ := in_first_n_primes_list hp 
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
      simp_all only [List.sorted_nil,one_ne_zero, List.length_nil, Nat.right_eq_add, Nat.add_eq_zero, and_false]
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
  have h : l2.length = n := List.Perm.length_eq (_root_.id (List.Perm.symm hp))
  exact sorted_list_perm_eq' l1 l2 h1 h2 (_root_.id (Eq.symm h)) rfl hp
  
theorem primorial_prime_factors (n : ℕ) : (primorial n).primeFactorsList = first_n_primes_list n := by 
  apply sorted_list_perm_eq  
  . exact primeFactorsList_sorted (primorial n)
  . exact first_n_primes_sorted n 
  . exact List.Perm.symm (primorial_prime_factors_perm n)

theorem omega_primorial_eq_self (n : ℕ) : ω (primorial n) = n := by 
  rw [ArithmeticFunction.cardDistinctFactors_apply, primorial_prime_factors n, ← dedup_first_n_primes n]
  exact first_n_primes_len n

lemma omega_impl_exists' {n k : ℕ} (hn : ω n = k) (hk : 0 < k) :
    ∃ x : ℕ, k-1 ≤ x ∧ nthPrime x ∣ n := by 
  rw [cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors n] at hn
  have hnpfnonempty : n.primeFactors.Nonempty := by 
    subst hn 
    exact Finset.card_pos.mp hk
  have hn1 : 1 < n := by 
    rw [← Nat.nonempty_primeFactors]
    exact hnpfnonempty
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn1
  set pmax := n.primeFactors.max' hnpfnonempty with hpmax
  have hpmaxin : pmax ∈ n.primeFactors := Finset.max'_mem n.primeFactors hnpfnonempty
  have hpmaxprime : Nat.Prime pmax := prime_of_mem_primeFactors hpmaxin

  obtain ⟨x, hx⟩ := prime_to_nth_prime hpmaxprime 
  have hx := Eq.symm hx
  use x 
  constructor 
  . if hk1 : 0 < k-1 then 
    obtain ⟨e, m, hpmaxm, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 pmax (Nat.Prime.ne_one hpmaxprime)
    have hm0 : m ≠ 0 := by 
      rw [hmn] at hn0 
      exact right_ne_zero_of_mul hn0
    have hpe0 : pmax^e ≠ 0 := by 
        rw [hmn] at hn0
        exact left_ne_zero_of_mul hn0 
    have hmerase : m.primeFactors = n.primeFactors.erase pmax := by 
      rw [hmn, Finset.ext_iff] 
      intro p
      rw [iff_iff_implies_and_implies]
      constructor 
      . intro h
        apply Finset.mem_erase_of_ne_of_mem
        . by_contra heq 
          subst heq 
          refine hpmaxm ?_ 
          exact dvd_of_mem_primeFactors h
        . rw [Nat.primeFactors_mul hpe0 hm0] 
          apply Finset.mem_union_right (pmax ^ e).primeFactors
          exact h
      . intro h
        simp only [Finset.mem_erase, ne_eq, mem_primeFactors, _root_.mul_eq_zero, Nat.pow_eq_zero, not_or, not_and, Decidable.not_not] at h
        obtain ⟨hpnotpmax, hpprime, hpdiv, hpe, _⟩ := h 
        rw [mem_primeFactors_of_ne_zero hm0] 
        refine ⟨hpprime, ?_⟩ 
        rw [Nat.Prime.dvd_mul hpprime] at hpdiv 
        rcases hpdiv with h1 | h2 
        . exfalso 
          refine hpnotpmax ?_
          rw [← Nat.prime_dvd_prime_iff_eq hpprime hpmaxprime]
          exact Nat.Prime.dvd_of_dvd_pow hpprime h1
        . exact h2
    have hm : ω m = k-1 := by 
      rw [cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors m, hmerase, ← hn] 
      exact Finset.card_erase_of_mem hpmaxin
    obtain ⟨y, hy, hydvd⟩ := omega_impl_exists' hm hk1
    have hyx : y ≠ x := by 
      by_contra hyx 
      subst hyx
      rw [← hx] at hydvd 
      exact hpmaxm hydvd
    have hyx : y < x := by 
      refine Nat.lt_of_le_of_ne ?_ hyx
      rw [← StrictMono.le_iff_le nth_prime_strict_mono, ← hx, hpmax]
      apply Finset.le_max'
      rw [hmn]
      rw [Nat.primeFactors_mul hpe0 hm0] 
      apply Finset.mem_union_right (pmax ^ e).primeFactors
      rw [mem_primeFactors] 
      exact ⟨nth_prime_is_prime y, hydvd, hm0⟩
    grind only [cases Or]
    else 
    have hk1 : k = 1 := by 
      simp only [tsub_pos_iff_lt, not_lt] at hk1
      exact Eq.symm (Nat.le_antisymm hk hk1)
    rw [hk1] 
    simp only [tsub_self, zero_le]
  . rw [← hx]
    exact dvd_of_mem_primeFactors hpmaxin

lemma omega_impl_exists {n k : ℕ} (hn : ω n = k) (hk : 0 < k) : 
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ nthPrime (k-1) ≤ p := by 
  obtain ⟨x, hx, hdiv⟩ := omega_impl_exists' hn hk 
  refine ⟨nthPrime x, nth_prime_is_prime x, hdiv, ?_⟩
  rw [StrictMono.le_iff_le nth_prime_strict_mono]
  exact hx

lemma pf_dedup_len {n : ℕ} : n.primeFactorsList.dedup.length = n.primeFactors.card := rfl

lemma primorial_le {k : ℕ} (h : 0 < k) : ∀ n : ℕ, ω n = k → primorial k ≤ n := by 
  induction k, h using Nat.le_induction with
  | base => 
    intro n hn 
    simp only [cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors n,succ_eq_add_one, zero_add, ← isPrimePow_iff_card_primeFactors_eq_one] at hn
    simp only [succ_eq_add_one, zero_add, primorial_one]
    exact IsPrimePow.two_le hn
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
      simp_all only [succ_eq_add_one, zero_add, add_tsub_cancel_right, ne_eq, not_false_eq_true,
        _root_.mul_eq_zero, Nat.pow_eq_zero, not_or, not_and, Decidable.not_not]
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

theorem primorial_gt_factorial_aux (m : ℕ) :
    primorial (m + 1) > factorial (m + 1) := by
  induction m with
  | zero => simp only [zero_add, primorial_one, factorial_one, gt_iff_lt, one_lt_ofNat]
  | succ j ih =>
    rw [primorial_succ (j + 1), factorial_succ (j + 1)]
    simp_all only [gt_iff_lt]
    refine Nat.mul_lt_mul_of_le_of_lt' ?_ ?_ ?_
    . exact nth_prime_bound (j + 1) 
    . exact ih
    . exact zero_lt_succ (j + 1)

-- Main theorem: primorial n > n! for n ≥ 1
theorem primorial_gt_factorial_for_n_ge_1 (n : ℕ) (hn : 0 < n) :
    primorial n > factorial n := by
  rw [←succ_pred_eq_of_pos hn]
  exact primorial_gt_factorial_aux n.pred
