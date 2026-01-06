import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Data.Finite.Card

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring


-- Zadanie 1
-- Udowodnić, że każdy skończony pierścień całkowity jest ciałem.
section
open Function

theorem finite_integral_domain_is_field (R : Type*) [CommRing R] [IsDomain R] [Finite R] :
    IsField R := by
  constructor
  · exact IsDomain.mk.exists_pair_ne
  · exact CommRing.mul_comm
  · intro a ha
    let f : R → R := fun x => a * x
    have h_inj : Injective f := fun x y h => mul_left_cancel₀ ha (h : f x = f y)
    have h_surj : Surjective f := Finite.injective_iff_surjective.mp h_inj
    exact h_surj 1

theorem finite_integral_domain_is_field' (R : Type*) [CommRing R] [IsDomain R] [Finite R] :
    IsField R := {
      exists_pair_ne := IsDomain.mk.exists_pair_ne
      mul_comm := CommRing.mul_comm
      mul_inv_cancel := by
        intro a ha
        let f : R → R := fun x => a * x
        have h_inj : Injective f := fun x y h => mul_left_cancel₀ ha (h : f x = f y)
        have h_surj : Surjective f := Finite.injective_iff_surjective.mp h_inj
        exact h_surj 1
    }

end

-- Zadanie 2
example {n : ℕ} (hn : 2 ≤ n) : 3^n > n * 2^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    calc
      _ = 3 * 3^k := by ring
      _ > 3 * (k * 2^k) := by simp [ih]
      _ = k * 2^k + k * 2^(k + 1) := by ring
      _ ≥ 2 * 2^k + k * 2^(k + 1) := by simp; exact hk
      _ = (k + 1) * 2^(k + 1) := by ring
