import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Data.Finite.Defs

-- Zadanie 1
-- Udowodnić, że każdy skończony pierścień całkowity jest ciałem.
theorem finite_integral_domain_is_field (R : Type*) [CommRing R] [IsDomain R] [Finite R] :
    IsField R := sorry
