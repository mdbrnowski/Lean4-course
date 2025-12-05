import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.Use

-- Zadanie 1
example {x y : Nat} (h₁ : x = y + 2) (h₂ : y = 3) : x < 6 := by
  rw [h₂] at h₁
  rw [h₁]
  decide

-- Zadanie 2
example {k : Nat} (h : 15 = k * 3) : 10 ≤ 3 * k := by
  rw [Nat.mul_comm]
  rw [←h]
  decide

-- Zadanie 3
example {x y : Nat} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  apply Nat.zero_lt_of_ne_zero
  have x_ne_zero := Nat.ne_zero_iff_zero_lt.mpr hx
  have y_ne_zero := Nat.ne_zero_iff_zero_lt.mpr hy
  rw [ne_eq, Nat.mul_eq_zero, not_or]
  trivial

example {x y : Nat} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  exact Nat.mul_pos hx hy

-- Zadanie 4
example : ∃! n : Nat, n ^ 2 = 9 := by
  use 3
  constructor
  · decide
  · intro a ha
    have h9 : 9 = 3 ^ 2 := by decide
    rw [h9] at ha
    have two_neq_zero : 2 ≠ 0 := by decide
    exact (Nat.pow_left_inj two_neq_zero).mp ha

-- Zadanie 5
example {x y : Nat} (h_eq : 3 * x = 9) (h_lt : 2 * y < 8) : y * 2 * x * 3 ≤ 100 := by
  rw [Nat.mul_comm] at h_eq
  rw [Nat.mul_assoc]
  rw [h_eq]
  rw [Nat.mul_comm y]
  have h_le : 2 * y ≤ 8 := Nat.le_of_lt h_lt
  have := Nat.mul_le_mul_right 9 h_le
  apply Nat.le_trans this (show 8 * 9 ≤ 100 by decide)

example {x y : Nat} (h_eq : 3 * x = 9) (h_lt : 2 * y < 8) : y * 2 * x * 3 ≤ 100 := by
  rw [Nat.mul_comm] at h_eq
  rw [Nat.mul_assoc, h_eq, Nat.mul_comm y]
  have := Nat.mul_le_mul_right 9 (show 2 * y ≤ 8 by omega)
  apply Nat.le_trans this (by decide)

-- Zadanie 6
example (m n : Nat) (h₁ : m ≥ n) (h₂ : n ≥ m) : n = m := by
  have := Nat.not_lt.mpr h₁
  have := Nat.not_lt.mpr h₂
  rcases Nat.lt_trichotomy n m with t₁ | t₂ | t₃ <;> trivial

example (m n : Nat) (h₁ : m ≥ n) (h₂ : n ≥ m) : n = m := by
  rcases Nat.lt_trichotomy n m <;> omega

example (m n : Nat) (h₁ : m ≥ n) (h₂ : n ≥ m) : n = m := by
  omega

-- Zadanie 7
axiom one_eq_two : 1 = 2

example : 2 = 3 := by
  have h₁ : 3 = 2 + 1 := by decide
  rw [h₁]
  rw [←one_eq_two]
  have h₂ : 1 + 1 = 2 := by decide
  rw [h₂]
  exact one_eq_two
