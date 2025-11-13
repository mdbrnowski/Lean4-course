-- Zadanie 1
example {A B C D : Prop} (h₁ : A → B) (h₂ : B → C) (h₃ : C → D) : A → D := sorry

-- Zadanie 2
example (P Q R : Prop) (h₁ : P ∧ Q) (h₂ : P → R) : R := sorry

-- Zadanie 3
theorem modus_tollens {P Q : Prop} (h₁ : P → Q) (h₂ : ¬Q) : ¬P := sorry

-- Zadanie 4
example {P Q : Prop} (h : ¬(P ∨ Q)) : ¬P ∧ ¬Q := sorry

-- Zadanie 5
example {P Q : Prop} (h : ¬P ∧ ¬Q) : ¬(P ∨ Q) := sorry

-- Zadanie 6
example (A B C D E : Prop) (h₁ : A ∧ B) (h₂ : B → ¬C ∧ D) (h₃ : E → C) : ¬E := sorry

-- Zadanie 7
example {P : Prop} : ((P → P) → P) → P := sorry

-- Zadanie 8
-- Pokaż, że system logiczny oparty na logice klasycznej z aksjomatem A jest trywialny.
axiom A {P : Prop} : (((P → P) → P) → P) → P

example {Q : Prop} : Q := sorry
