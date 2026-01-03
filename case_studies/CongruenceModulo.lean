import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

example {n : ℕ} : 4^n ≡ 1 + 3*n [MOD 9] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      _ = 4 * 4^n := by ring
      _ ≡ 4 * (1 + 3*n) [MOD 9] := by gcongr
      _ = 4 + 12*n := by ring
      _ ≡ 4 + 3*n [MOD 9] := by gcongr; rfl
      _ = _ := by ring
