import Mathlib.Data.Rat.Init
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

def A : Type := {x : ℚ // x ≠ 1}
def op (a b : ℚ) : ℚ := a * b - a - b + 2

lemma op_ne_one {a b : ℚ} (ha : a ≠ 1) (hb : b ≠ 1) : op a b ≠ 1 := by
  intro h
  unfold op at h
  have : (a - 1) * (b - 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with ha' | hb'
  · have : a = 1 := by linarith
    contradiction
  · have : b = 1 := by linarith
    contradiction

instance : Mul A where
  mul a b := ⟨op a.val b.val, op_ne_one a.prop b.prop⟩

instance : Semigroup A where
  mul_assoc a b c := by
    apply Subtype.ext
    change op (op a.val b.val) c.val = op a.val (op b.val c.val)
    unfold op
    ring

instance : One A where
  one := ⟨2, by decide⟩

instance : Monoid A where
  one_mul a := by
    apply Subtype.ext
    change op 2 a.val = a.val
    unfold op
    ring
  mul_one a := by
    apply Subtype.ext
    change op a.val 2 = a.val
    unfold op
    ring

lemma op_inv_ne_one {a : ℚ} (ha : a ≠ 1) : a / (a - 1) ≠ 1 := by
  intro h
  have a_sub_one_ne_zero : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have := (div_eq_one_iff_eq a_sub_one_ne_zero).mp h
  linarith

instance : Inv A where
  inv a := ⟨a.val / (a.val - 1), op_inv_ne_one a.prop⟩

instance : Group A where
  inv_mul_cancel a := by
    apply Subtype.ext
    change op (a.val / (a.val - 1)) a.val = 2
    unfold op
    field_simp
    have : (a.val - 1) / (a.val - 1) = 1 := by
      have a_sub_one_ne_zero : a.val - 1 ≠ 0 := sub_ne_zero.mpr a.prop
      exact div_self a_sub_one_ne_zero
    rw [this]
    ring

instance : CommGroup A where
  mul_comm a b := by
    apply Subtype.ext
    change op a.val b.val = op b.val a.val
    unfold op
    ring

instance : CancelCommMonoid A := by
  infer_instance
