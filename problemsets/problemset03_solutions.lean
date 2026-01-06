import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- Zadanie 1
section
open Real

example {x : ℝ} (hx : 0 < x) : 2 ≤ x + 1 / x := by
  have h_eq : x + 1 / x = 2 + (sqrt x - 1 / sqrt x) ^ 2 := by
    field_simp
    rw [sq_sqrt (le_of_lt hx)]
    ring
  rw [h_eq]
  simp [sq_nonneg]

end

-- Zadanie 2
-- Udowodnić, że (A, op) jest grupą przemienną.
def A := {x : ℚ // -1 < x ∧ x < 1}
def op (a b : ℚ) := (a + b) / (1 + a * b)

lemma op_in_A {a b : ℚ} (ha : -1 < a ∧ a < 1) (hb : -1 < b ∧ b < 1) : -1 < op a b ∧ op a b < 1 := by
  unfold op
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  have : 0 < 1 + a * b := by nlinarith
  constructor <;> (field_simp; nlinarith)

instance : Mul A where
  mul a b := ⟨op a.val b.val, op_in_A a.prop b.prop⟩

instance : Semigroup A where
  mul_assoc a b c := by
    apply Subtype.ext
    change op (op a.val b.val) c.val = op a.val (op b.val c.val)
    unfold op
    field_simp
    obtain ⟨ha₁, ha₂⟩ := a.prop
    obtain ⟨hb₁, hb₂⟩ := b.prop
    obtain ⟨hc₁, hc₂⟩ := c.prop
    have ab : (1 : ℚ) + a.val * b.val ≠ 0 := by nlinarith
    have bc : (1 : ℚ) + b.val * c.val ≠ 0 := by nlinarith
    rw [add_div_eq_mul_add_div]
    · field_simp
      ring
    · assumption

instance : One A where
  one := ⟨0, by decide⟩

instance : Monoid A where
  one_mul a := by
    apply Subtype.ext
    change op 0 a.val = a.val
    unfold op
    ring
  mul_one a := by
    apply Subtype.ext
    change op a.val 0 = a.val
    unfold op
    ring

instance : Inv A where
  inv a := ⟨-a.val, by
    obtain ⟨ha₁, ha₂⟩ := a.prop
    constructor <;> linarith⟩

instance : Group A where
  inv_mul_cancel a := by
    apply Subtype.ext
    change op (-a.val) a.val = 0
    unfold op
    ring

instance : CommGroup A where
  mul_comm a b := by
    apply Subtype.ext
    change op a.val b.val = op b.val a.val
    unfold op
    ring
