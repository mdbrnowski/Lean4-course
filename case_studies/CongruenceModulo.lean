import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

open Nat

theorem power_mod_nine (n : ℕ) : 4^n ≡ 1 + 3*n [MOD 9] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      _ = 4 * 4^n := by ring
      _ ≡ 4 * (1 + 3*n) [MOD 9] := by
          apply ModEq.mul_left
          exact ih
      _ = 4 + 12*n := by ring
      _ = 4 + 3*n + 9*n := by ring
      _ ≡ 4 + 3*n + 0*n [MOD 9] := by
          apply ModEq.add_left
          apply ModEq.mul_right
          rfl
      _ = 1 + 3*(n + 1) := by ring

theorem power_mod_nine' (n : ℕ) : 4^n ≡ 1 + 3*n [MOD 9] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      _ = 4 * 4^n := by ring
      _ ≡ 4 * (1 + 3*n) [MOD 9] := by gcongr
      _ = 4 + 12*n := by ring
      _ ≡ 4 + 3*n [MOD 9] := by gcongr; rfl
      _ = 1 + 3*(n + 1) := by ring
