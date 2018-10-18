open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r :=
sorry
example : r → (∃ x : α, r) :=
sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
sorry
example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
sorry
