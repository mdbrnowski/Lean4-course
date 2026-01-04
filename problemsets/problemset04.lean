import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Data.Finite.Defs

-- Zadanie 1
-- Udowodnić, że każdy skończony pierścień całkowity jest ciałem.
theorem finite_integral_domain_is_field (R : Type*) [CommRing R] [IsDomain R] [Finite R] :
    IsField R := sorry

-- Zadanie 2
-- Podpowiedź: użyj Nat.le_induction
example {n : ℕ} (hn : 2 ≤ n) : 3^n > n * 2^n := sorry
