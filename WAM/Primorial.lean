import Mathlib.Data.Nat.Factorial.Basic -- For Nat.factorial
import Mathlib.Tactic.Linarith -- For solving inequalities
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.ArithmeticFunction

import Canonical

open Nat ArithmeticFunction


lemma nth_prime_is_prime (n : ℕ) : Nat.Prime (Nat.nth Nat.Prime n) := Nat.nth_mem_of_infinite infinite_setOf_prime n 
lemma nth_prime_strict_mono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono infinite_setOf_prime  
lemma nth_prime_injective : Function.Injective (Nat.nth Nat.Prime) := StrictMono.injective nth_prime_strict_mono 

lemma nth_prime_bound (n : ℕ) : n + 1 ≤ Nat.nth Nat.Prime n := by
  induction n with 
  | zero => 
    rw [nth_prime_zero_eq_two]
    exact le_of_ble_eq_true rfl
  | succ m ih => 
    suffices Nat.nth Nat.Prime m < Nat.nth Nat.Prime (m + 1) by 
      exact Lean.Grind.Nat.le_lo (m + 1) (nth Nat.Prime m) (nth Nat.Prime (m + 1)) 1 ih this
    rw [Nat.nth_lt_nth]
    . exact lt_add_one m
    exact infinite_setOf_prime

/- 
  Primorial 
-/

noncomputable def primorial : ℕ → ℕ
  | 0 => 1
  | succ n => (Nat.nth Nat.Prime n) * primorial n


@[simp] lemma primorial_zero : primorial 0 = 1 := by rfl
@[simp] lemma primorial_one : primorial 1 = 2 := by simp only [primorial, mul_one, nth_prime_zero_eq_two]
lemma primorial_succ (n : ℕ) : primorial (n + 1) = (Nat.nth Nat.Prime n) * primorial n := by
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
  | Nat.succ n => first_n_primes_list n ++ [Nat.nth Nat.Prime n]


lemma first_n_primes_len (n : ℕ) : (first_n_primes_list n).length = n := by 
  induction n with 
  | zero => rfl
  | succ k ih =>
    unfold first_n_primes_list 
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
      Nat.add_right_cancel_iff]
    exact ih 
    

lemma first_n_primes_as_map (n : ℕ) : (first_n_primes_list n) = (List.finRange n).map (Nat.nth Nat.Prime) := by
  induction n with 
  | zero => rfl
  | succ k ih =>
    rw [first_n_primes_list]
     
    sorry 

theorem nodup_first_n_primes (n : ℕ) : (first_n_primes_list n).Nodup := by 
  rw [first_n_primes_as_map n]
  rw [List.nodup_map_iff nth_prime_injective]
  suffices (List.finRange n).Nodup by 
    . simp [List.flatMap_singleton]
       
      sorry
  exact List.nodup_finRange n

theorem dedup_first_n_primes (n : ℕ) : (first_n_primes_list n) = (first_n_primes_list n).dedup := by 
  exact Eq.symm (List.Nodup.dedup (nodup_first_n_primes n))


/- 
  Main statements 
-/

theorem primorial_prime_factors (n : ℕ) : (primorial n).primeFactorsList = first_n_primes_list n := by 
  induction n with 
  | zero => 
    unfold first_n_primes_list 
    simp only [primorial_zero, primeFactorsList_one]
  | succ k ih => 
    rw [primorial_succ k]
    let p := Nat.nth Nat.Prime k
    have hp : Nat.Prime p := nth_prime_is_prime k 
    rw [first_n_primes_list, ← ih]
    rw [← Nat.primeFactorsList_prime hp]
    
    sorry


theorem omega_primorial_eq_self (n : ℕ) : ω (primorial n) = n := by 
  rw [ArithmeticFunction.cardDistinctFactors_apply]
  rw [primorial_prime_factors n]
  rw [← dedup_first_n_primes n]
  exact first_n_primes_len n

theorem primorial_omega_le_self (n : ℕ) : primorial (ω n) ≤ n := by 
   
  sorry

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
    rw [nth_prime_zero_eq_two]                          -- nthPrime 0 is 2
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
    (Nat.nth Nat.Prime (j + 1)) * primorial (j + 1) > (Nat.nth Nat.Prime (j + 1)) * factorial (j + 1) := by
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
  -- We know n ≥ 1. So, n can be written as m + 1 for some m : ℕ.
  cases n with
  | zero =>
    -- If n = 0, then hn : 0 ≥ 1. This is a contradiction.
    -- linarith can solve this, or more explicitly:
    exfalso
    exact Nat.not_le_of_lt zero_lt_one hn -- (0 < 1) and (1 ≤ 0) is impossible
  | succ m =>
    -- If n = m + 1, the goal is primorial (m + 1) > factorial (m + 1).
    -- This is exactly what primorial_gt_factorial_aux m proves.
    exact primorial_gt_factorial_aux m
