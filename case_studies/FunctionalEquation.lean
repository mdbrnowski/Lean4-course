import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Linarith

example {f : ℕ+ → ℕ+} : (∀ m n : ℕ+, m * m + f n ∣ m * f m + n) ↔ f = id := by
  constructor
  · intro h
    have f2_eq_2 : f 2 = 2 := by
      specialize h 2 2
      obtain ⟨k, hk⟩ := exists_eq_mul_left_of_dvd (PNat.dvd_iff.mp h)
      have k_eq_1 : k = 1 := by
        nlinarith
      apply PNat.eq
      nlinarith
    funext x
    rw [id_eq]
    refine le_antisymm ?_ ?_
    · specialize h 2 x
      rw [f2_eq_2] at h
      have := PNat.le_of_dvd h
      simpa
    · specialize h x x
      have := PNat.le_of_dvd h
      change (x * x + f x : ℕ) ≤ x * f x + x at this
      change (x : ℕ) ≤ f x
      nlinarith [PNat.pos x, PNat.pos (f x)]
  · intro h
    simp [h]
