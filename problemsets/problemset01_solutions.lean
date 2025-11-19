-- Zadanie 1
example {A B C D : Prop} (h₁ : A → B) (h₂ : B → C) (h₃ : C → D) : A → D := by
  intro h₀
  exact h₃ (h₂ (h₁ h₀))

example {A B C D : Prop} (h₁ : A → B) (h₂ : B → C) (h₃ : C → D) : A → D := by
  intro h₀
  exact h₃ <| h₂ <| h₁ <| h₀

example {A B C D : Prop} (h₁ : A → B) (h₂ : B → C) (h₃ : C → D) : A → D := by
  intro h₀
  exact h₀ |> h₁ |> h₂ |> h₃

-- Zadanie 2
example (P Q R : Prop) (h₁ : P ∧ Q) (h₂ : P → R) : R := by
  exact h₂ h₁.left

-- Zadanie 3
theorem modus_tollens {P Q : Prop} (h₁ : P → Q) (h₂ : ¬Q) : ¬P := by
  intro hp
  apply h₂
  apply h₁
  exact hp

-- Zadanie 4
example {P Q : Prop} (h : ¬(P ∨ Q)) : ¬P ∧ ¬Q := by
  constructor
  · intro hp
    apply h
    left
    exact hp
  · intro hq
    apply h
    right
    exact hq

-- Zadanie 5
example {P Q : Prop} (h : ¬P ∧ ¬Q) : ¬(P ∨ Q) := by
  intro hpq
  rcases hpq with hp | hq
  · exact False.elim (h.left hp)
  · exact False.elim (h.right hq)

example {P Q : Prop} (h : ¬P ∧ ¬Q) : ¬(P ∨ Q) := by
  intro hpq
  rcases hpq with hp | hq
  · exact absurd hp h.left
  · exact absurd hq h.right

-- Zadanie 6
example (A B C D E : Prop) (h₁ : A ∧ B) (h₂ : B → ¬C ∧ D) (h₃ : E → C) : ¬E := by
  exact modus_tollens h₃ (h₂ h₁.right).left

example (A B C D E : Prop) (h₁ : A ∧ B) (h₂ : B → ¬C ∧ D) (h₃ : E → C) : ¬E := by
  intro e
  have not_c := (h₂ h₁.right).left
  have c := h₃ e
  contradiction

-- Zadanie 7
example {P : Prop} : ((P → P) → P) → P := by
  intro h₁
  apply h₁
  intro h₂
  exact h₂

-- Zadanie 8
-- Pokaż, że system logiczny oparty na logice klasycznej z aksjomatem A jest trywialny.
axiom A {P : Prop} : (((P → P) → P) → P) → P

example {Q : Prop} : Q := by
  apply False.elim
  apply A
  intro h₁
  apply h₁
  intro h₂
  exact h₂
