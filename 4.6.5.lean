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

-- refactor some lemmas for reuse {

lemma not_exists_then_forall_not
    {α : Type} {p : α → Prop} : (¬ ∃ x, p x) → (∀ x, ¬ p x) :=
assume h : ¬ ∃ x, p x,
    show ∀ x, ¬ p x, from
    assume z : α,
    show ¬ p z, from
    (assume hpz : p z,
        show false, from
        h ⟨z, hpz⟩)

lemma not_not_exists_then_forall
    {α : Type} {p : α → Prop} : ¬ (∃ x, ¬ p x) → (∀ x, p x) :=
assume h : ¬ (∃ x, ¬ p x),
    show (∀ x, p x), from
    assume z : α,
    show p z, from
    by_contradiction
        (assume hnpz : ¬ p z,
            show false, from
            h ⟨z, hnpz⟩)

-- }

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
        not_not_exists_then_forall h)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
iff.intro
    (assume h : ∃ x, p x,
        show ¬ (∀ x, ¬ p x), from
        match h with ⟨w, hw⟩ :=
            assume hneg : ∀ x, ¬ p x,
            show false, from
            absurd hw (hneg w)
        end)
    (assume h : ¬ (∀ x, ¬ p x), -- ∀ x, ¬ p x → false
        show ∃ x, p x, from
        by_contradiction
            (assume h_tofalsify : ¬ (∃ x, p x),
                have h2 : ∀ x, ¬ p x, from not_exists_then_forall_not h_tofalsify,
                absurd h2 h))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
iff.intro
    (assume h : ¬ ∃ x, p x,
        show ∀ x, ¬ p x, from
        not_exists_then_forall_not h)
    (assume h : ∀ x, ¬ p x,
        show ¬ ∃ x, p x, from
        (assume h2 : ∃ x, p x,
            show false, from
            match h2 with ⟨w, hw⟩ :=
                absurd hw (h w)
            end))

theorem not_forall_iff_not_exists
    {α : Type} {p : α → Prop} : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
iff.intro
    (assume h : ¬ ∀ x, p x,
        show ∃ x, ¬ p x, from
        by_contradiction
            (assume h_tofalsify : ¬ (∃ x, ¬ p x),
                have h2 : ∀ x, p x, from not_not_exists_then_forall h_tofalsify,
                absurd h2 h))
    (assume h : ∃ x, ¬ p x,
        show ¬ ∀ x, p x, from
        match h with ⟨w, hw⟩ :=
            assume hallp : ∀ x, p x,
            show false, from
            absurd (hallp w) hw
        end)

--

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
iff.intro
    (assume h : (∀ x, p x → r),
        show (∃ x, p x) → r, from
        (assume h2 : ∃ x, p x,
            show r, from
            match h2 with ⟨w, (hw : p w)⟩ :=
                (h w) hw
            end))
    (assume h : (∃ x, p x) → r,
        show ∀ x, p x → r, from
        assume z : α,
        show p z → r, from
            (assume hpz : p z,
                show r, from
                h ⟨z, hpz⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
iff.intro
    (assume h : ∃ x, p x → r,
        show (∀ x, p x) → r, from
        match h with ⟨w, (hw : p w → r)⟩ :=
            assume h2 : ∀ x, p x,
            show r, from
            hw (h2 w)
        end)
    (assume h : (∀ x, p x) → r,
        show ∃ x, p x → r, from
        by_cases
            (assume h_all : ∀ x, p x,
                ⟨a, (λ hpa, h h_all)⟩)
            (assume h_nall : ¬ ∀ x, p x,
                have h2 : ∃ x, ¬ p x, from not_forall_iff_not_exists.mp h_nall,
                match h2 with ⟨w, hw⟩ :=
                    ⟨w, (
                        show p w → r, from
                        (assume hpw : p w, absurd hpw hw)
                    )⟩
                end))

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
iff.intro
    (assume h : (∃ x, r → p x),
        show (r → ∃ x, p x), from
        match h with ⟨w, (hw : r → p w)⟩ :=
            assume hr : r,
            show ∃ x, p x, from
            ⟨w, hw hr⟩
        end)
    (assume h : (r → ∃ x, p x),
        show (∃ x, r → p x), from
        by_cases
            (assume hr : r,
                have h2 : ∃ x, p x, from h hr,
                match h2 with ⟨w, (hw : p w)⟩ :=
                    ⟨w, (λ _, hw)⟩
                end)
            (assume hnr : ¬r,
                ⟨a, (λ hr, absurd hr hnr)⟩))

--

