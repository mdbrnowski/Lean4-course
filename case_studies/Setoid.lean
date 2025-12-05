structure Point where
  x : Int
  y : Int

instance : Setoid Point where
  r a b := a.x + a.y = b.x + b.y
  iseqv := {
    refl := by intro p; rfl
    symm := by intro p q h; rw [h]
    trans := by intro p q r h₁ h₂; rw [h₁, h₂]
  }
