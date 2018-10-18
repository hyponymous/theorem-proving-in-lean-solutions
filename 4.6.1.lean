variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
    (assume h : (∀ x, p x ∧ q x),
        show (∀ x, p x) ∧ (∀ x, q x), from
        and.intro
            (assume z : α,
                (h z).left)
            (assume z : α,
                (h z).right))
    (assume h : (∀ x, p x) ∧ (∀ x, q x),
        show (∀ x, p x ∧ q x), from
        assume z : α,
            and.intro (h.left z) (h.right z))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
assume h1 : (∀ x, p x → q x),
show (∀ x, p x) → (∀ x, q x), from
    assume h2 : (∀ x, p x),
    show (∀ x, q x), from
        assume z : α,
        (h1 z) (h2 z)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
assume h : (∀ x, p x) ∨ (∀ x, q x),
show ∀ x, p x ∨ q x, from
    assume z : α,
    or.elim h
        (assume hl : ∀ x, p x,
            or.inl (hl z))
        (assume hr : ∀ x, q x,
            or.inr (hr z))

