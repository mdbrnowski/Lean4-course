import Mathlib.Logic.ExistsUnique

-- Zadanie 1
example {x y : Nat} (h₁ : x = y + 2) (h₂ : y = 3) : x < 6 := sorry

-- Zadanie 2
example {k : Nat} (h : 15 = k * 3) : 10 ≤ 3 * k := sorry

-- Zadanie 3
example {x y : Nat} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := sorry

-- Zadanie 4
example : ∃! n : Nat, n ^ 2 = 9 := sorry

-- Zadanie 5
example {x y : Nat} (h_eq : 3 * x = 9) (h_lt : 2 * y < 8) : (y * 2) * x * 3 ≤ 100 := sorry

-- Zadanie 6
example (m n : Nat) (h₁ : ¬(m < n)) (h₂ : ¬(n < m)) : n = m := sorry

-- Zadanie 7
axiom one_eq_two : 1 = 2

example : 2 = 3 := sorry
