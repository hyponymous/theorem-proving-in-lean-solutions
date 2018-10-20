open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

--

-- using exists.elim
example : (∃ x : α, r) → r :=
assume h : ∃ x : α, r,
show r, from
exists.elim h
    (assume w,
    assume hw : r,
    hw)

-- using match
example : (∃ x : α, r) → r :=
assume h : ∃ x : α, r,
match h with ⟨w, (hw : r)⟩ :=
    hw
end

example : r → (∃ x : α, r) :=
assume hr : r,
⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro
    (assume h : ∃ x, p x ∧ r,
        show (∃ x, p x) ∧ r, from
        match h with ⟨w, (hw : p w ∧ r)⟩ :=
            ⟨⟨w, hw.left⟩, hw.right⟩
        end)
    (assume h : (∃ x, p x) ∧ r,
        show ∃ x, p x ∧ r, from
        match h.left with ⟨w, (hw : p w)⟩ :=
            ⟨w, ⟨hw, h.right⟩⟩
        end)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
    (assume h : (∃ x, p x ∨ q x),
        show (∃ x, p x) ∨ (∃ x, q x), from
        match h with ⟨w, (hw : p w ∨ q w)⟩ :=
            or.elim hw
                (assume hpw : p w,
                    or.inl ⟨w, hpw⟩)
                (assume hqw : q w,
                    or.inr ⟨w, hqw⟩)
        end)
    (assume h : (∃ x, p x) ∨ (∃ x, q x),
        show (∃ x, p x ∨ q x), from
        or.elim h
            (assume hleft : ∃ x, p x,
                match hleft with ⟨w, hw⟩ :=
                    ⟨w, or.inl hw⟩
                end)
            (assume hright : ∃ x, q x,
                match hright with ⟨w, hw⟩ :=
                    ⟨w, or.inr hw⟩
                end))

--

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
iff.intro
    (assume h : (∀ x, p x),
        show ¬ (∃ x, ¬ p x), from
        assume hneg : ∃ x, ¬ p x,
        show false, from
        match hneg with ⟨w, (hw : ¬ p w)⟩ :=
            absurd (h w) hw
        end)
    (assume h : ¬ (∃ x, ¬ p x),
        show (∀ x, p x), from
        assume z : α,
        show p z, from
        by_contradiction
            (assume hnpz : ¬ p z,
                show false, from
                h ⟨z, hnpz⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
sorry

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
sorry

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
sorry

--

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
sorry

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
sorry

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
sorry

--

