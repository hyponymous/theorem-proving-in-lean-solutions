open classical

variables (α : Type) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) :=
assume a : α,
show (∀ x : α, r) ↔ r, from
iff.intro
    (assume : (∀ x : α, r),
        show r, from
        this a)
    (assume : r,
        show (∀ x : α, r), from
        assume b : α, this)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
iff.intro
    (assume h : (∀ x, p x ∨ r),
        show (∀ x, p x) ∨ r, from
        or.elim (em r)
            or.inr
            (assume hnr : ¬r,
                or.inl (assume z : α, (
                    or.elim (h z)
                        id
                        (assume hr : r, absurd hr hnr)))))
    (assume h : (∀ x, p x) ∨ r,
        show (∀ x, p x ∨ r), from
        assume z : α,
        or.elim h
            (assume hl : (∀ x, p x),
                or.inl (hl z))
            (assume hr : r,
                or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
iff.intro
    (assume h : (∀ x, r → p x),
        show (r → ∀ x, p x), from
        assume hr : r,
        show (∀ x, p x), from
        assume z : α,
        (h z) hr)
    (assume h : r → ∀ x, p x,
        show ∀ x, r → p x, from
        assume z : α,
        assume hr : r,
        h hr z)

