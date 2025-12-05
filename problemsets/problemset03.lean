import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic

-- Zadanie 1
example {x : ℝ} (hx : 0 < x) : 2 ≤ x + 1 / x := sorry

-- Zadanie 2
-- Udowodnić, że (A, op) jest grupą przemienną.
def A := {x : ℚ // -1 < x ∧ x < 1}
def op (a b : ℚ) := (a + b) / (1 + a * b)

instance : CommGroup A := sorry
