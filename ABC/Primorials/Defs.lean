import Mathlib.Data.Nat.Factorial.Basic -- For Nat.factorial
import Mathlib.Tactic.Linarith -- For solving inequalities
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.ArithmeticFunction

open Nat ArithmeticFunction


/-
Definition of nth prime 
-/ 

noncomputable abbrev nthPrime (n : ℕ) := Nat.nth Nat.Prime n

@[simp] lemma nth_prime_is_prime (n : ℕ) : Nat.Prime (nthPrime n) := 
  Nat.nth_mem_of_infinite infinite_setOf_prime n 

@[simp, mono] lemma nth_prime_strict_mono : StrictMono nthPrime := 
  Nat.nth_strictMono infinite_setOf_prime  

@[simp] lemma nth_prime_injective : Function.Injective nthPrime :=
  StrictMono.injective nth_prime_strict_mono 

@[simp] lemma prime_to_nth_prime {p : ℕ} (hp : Nat.Prime p) : ∃ n : ℕ, nthPrime n = p := 
  ⟨Nat.count Nat.Prime p, Nat.nth_count hp⟩

lemma nth_prime_bound' (n : ℕ) : n < nthPrime n := by
  induction n with 
  | zero => simp only [nth_prime_zero_eq_two, ofNat_pos] 
  | succ m ih => 
    calc m + 1 ≤ (nthPrime m) := by grind only
      _ < nthPrime (m + 1) := nth_prime_strict_mono (lt_add_one m)
    
lemma nth_prime_bound (n : ℕ) : n + 1 ≤ nthPrime n := nth_prime_bound' n
  

/- 
Primorial 
-/

noncomputable def primorial : ℕ → ℕ
  | 0 => 1
  | succ n => (nthPrime n) * primorial n

@[simp] lemma primorial_zero : primorial 0 = 1 := rfl

@[simp] lemma primorial_one : primorial 1 = 2 := by 
  simp only [primorial, mul_one, nth_prime_zero_eq_two]

lemma primorial_succ (n : ℕ) : primorial (n + 1) = (nthPrime n) * primorial n := by
  rw [primorial]

lemma primorial_pos (n : ℕ) : 0 < primorial n := by
  induction n with
  | zero => simp only [primorial_zero, zero_lt_one]
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
  | zero => simp only [first_n_primes_list, List.not_mem_nil] at hp
  | succ k ih => 
    simp only [first_n_primes_list, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    grind only [=_ List.contains_iff_mem, List.contains_eq_mem]

lemma first_n_primes_max (n : ℕ) : (first_n_primes_list (n+1)).maximum = nthPrime n := by 
  induction n with 
  | zero => simp only [first_n_primes_list, nth_prime_zero_eq_two, List.nil_append, List.maximum_singleton, WithBot.coe_ofNat,
      cast_ofNat]
  | succ k ih => 
    rw [first_n_primes_list, List.maximum_concat, ih]
    apply max_eq_right_of_lt 
    apply WithBot.coe_lt_coe.mpr
    exact nth_prime_strict_mono (lt_add_one k)

lemma first_n_primes_prod (n : ℕ) : (first_n_primes_list n).prod = primorial n := by 
  induction n with 
  | zero => simp only [primorial_zero, first_n_primes_list, List.prod_nil]
  | succ k ih => grind only [first_n_primes_list, primorial, List.prod_append, List.prod_cons, List.prod_nil]

lemma first_n_primes_len (n : ℕ) : (first_n_primes_list n).length = n := by 
  induction n with 
  | zero => rfl
  | succ k ih => grind only [first_n_primes_list, List.length_cons, List.length_nil, List.length_append,→ List.eq_nil_of_append_eq_nil]

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
      apply (nth_prime_strict_mono h1).not_ge 
      exact Nat.le_of_eq h2
    exact ih

theorem dedup_first_n_primes (n : ℕ) : (first_n_primes_list n) = (first_n_primes_list n).dedup := Eq.symm (List.Nodup.dedup (nodup_first_n_primes n))

/- 
list n primes sorted 
-/ 

abbrev le_sorted {α : Type} [LinearOrder α] (l : List α) := List.Sorted (fun x1 x2 => x1 ≤ x2) l

lemma first_n_primes_sorted (n : ℕ) : le_sorted (first_n_primes_list n) := by 
  induction n with 
  | zero => simp only [first_n_primes_list, List.sorted_nil]
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

