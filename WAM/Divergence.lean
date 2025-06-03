import Mathlib.Data.Nat.Basic
import Batteries.Data.Nat.Gcd
import Mathlib.Data.Set.Basic -- For Set.Infinite
import Mathlib.Order.Monotone.Basic -- For StrictMono
import Mathlib.Algebra.Group.Defs -- For one_mul
import Mathlib.Data.Finite.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Monotone.Basic

import WAM.Defs

open Nat Set Filter ArithmeticFunction 


def ABCTriple (a b c : ℕ) : Prop := a > 0 ∧ b > 0 ∧ a.Coprime b ∧ a + b = c 

lemma abc_c_pos (a b c : ℕ) (habc : ABCTriple a b c) : c > 0 := by 
  obtain ⟨ha, hb, hcoab, hsum⟩ := habc 
  rw [← hsum]
  exact Nat.add_pos_left ha b

lemma abc_ab_comm (a b c : ℕ) (habc : ABCTriple a b c) : ABCTriple b a c := by 
  obtain ⟨ha, hb, hcoab, hsum⟩ := habc 
  constructor
  . exact hb 
  constructor 
  . exact ha 
  constructor 
  . exact coprime_comm.mp hcoab
  rw [← hsum]
  exact Nat.add_comm b a

lemma abc_ac_copr (a b c : ℕ) (habc : ABCTriple a b c) : a.Coprime c := by
  obtain ⟨ha, hb, hcoab, hsum⟩ := habc 
  rw [← hsum]
  rw [Nat.coprime_iff_gcd_eq_one]
  simp only [gcd_self_add_right]
  rw [Nat.coprime_iff_gcd_eq_one] at hcoab 
  exact hcoab
 
lemma abc_bc_copr (a b c : ℕ) (habc : ABCTriple a b c) : b.Coprime c := by
  obtain ⟨ha, hb, hcoab, hsum⟩ := habc 
  rw [← hsum]
  rw [Nat.coprime_iff_gcd_eq_one]
  simp only [gcd_add_self_right]
  rw [Nat.coprime_iff_gcd_eq_one] at hcoab 
  rw [Nat.gcd_comm]
  exact hcoab 

lemma pow2_is_abc (k : ℕ) : ABCTriple 1 (2^k) (2^k + 1) := by 
  constructor 
  . exact Nat.one_pos
  constructor 
  . exact Nat.two_pow_pos k
  constructor 
  . exact gcd_pow_right_of_gcd_eq_one rfl
  exact Nat.add_comm 1 (2 ^ k)


def NisABC (n : ℕ) : Prop := ∃ a b c : ℕ, ABCTriple a b c ∧ n = a * b * c

def ABCTripleSet : Set ℕ := {n | NisABC n} 

