variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume h : p ∧ q,
    show q ∧ p, from ⟨(and.right h), (and.left h)⟩)
  (assume h : q ∧ p,
    show p ∧ q, from ⟨(and.right h), (and.left h)⟩)

example : p ∨ q ↔ q ∨ p :=
iff.intro
  (assume h : p ∨ q,
    or.elim h
      (assume hp : p,
        show q ∨ p, from or.inr hp)
      (assume hq : q,
        show q ∨ p, from or.inl hq))
  (assume h : q ∨ p,
    or.elim h
      (assume hq : q,
        show p ∨ q, from or.inr hq)
      (assume hp : p,
        show p ∨ q, from or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro
    (assume h : (p ∧ q) ∧ r,
        have hpq : p ∧ q, from and.left h,
        show p ∧ (q ∧ r), from
            ⟨and.left hpq, ⟨and.right hpq, and.right h⟩⟩)
    (assume h : p ∧ (q ∧ r),
        have hqr : q ∧ r, from and.right h,
        show (p ∧ q) ∧ r, from
            ⟨⟨and.left h, and.left hqr⟩, and.right hqr⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
iff.intro
    (assume h : (p ∨ q) ∨ r,
        show p ∨ (q ∨ r), from
        or.elim h
            (assume hpq : p ∨ q,
                or.elim hpq
                    (assume hp : p, or.inl hp)
                    (assume hq : q, or.inr (or.inl hq)))
            (assume hr : r,
                or.inr (or.inr hr)))
    (assume h : p ∨ (q ∨ r),
        show (p ∨ q) ∨ r, from
        or.elim h
            (assume hp : p, or.inl (or.inl hp))
            (assume hqr : q ∨ r,
                or.elim hqr
                    (assume hq : q, or.inl (or.inr hq))
                    (assume hr : r, or.inr hr)))

-- distributivity

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
    (assume h : p ∧ (q ∨ r),
        show (p ∧ q) ∨ (p ∧ r), from
        have hp : p, from and.left h,
        or.elim (and.right h)
            (assume hq : q, or.inl ⟨hp, hq⟩)
            (assume hr : r, or.inr ⟨hp, hr⟩))
    (assume h: (p ∧ q) ∨ (p ∧ r),
        show p ∧ (q ∨ r), from
        or.elim h
            (assume hpq : p ∧ q, ⟨and.left hpq, or.inl (and.right hpq)⟩)
            (assume hpr : p ∧ r, ⟨and.left hpr, or.inr (and.right hpr)⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
iff.intro
    (assume h : p ∨ (q ∧ r),
        show (p ∨ q) ∧ (p ∨ r), from
        or.elim h
            (assume hp : p, ⟨or.inl hp, or.inl hp⟩)
            (assume hqr : q ∧ r,
                have hq : q, from hqr.left,
                have hr : r, from hqr.right,
                ⟨or.inr hq, or.inr hr⟩))
    (assume h : (p ∨ q) ∧ (p ∨ r),
        show p ∨ (q ∧ r), from
        have hpq : p ∨ q, from h.left,
        have hpr : p ∨ r, from h.right,
        or.elim hpq
            (assume hp : p, or.inl hp)
            (assume hq : q,
                or.elim hpr
                    (assume hp : p, or.inl hp)
                    (assume hr : r, or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
iff.intro
    (assume h : (p → (q → r)),
        show (p ∧ q → r), from
        assume hpq : p ∧ q,
            h hpq.left hpq.right)
    (assume h : (p ∧ q → r),
        show (p → (q → r)), from
        assume hp : p,
            assume hq : q,
                h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
iff.intro
    (assume h : ((p ∨ q) → r),
        show (p → r) ∧ (q → r), from
        and.intro
            (assume hp : p, h (or.inl hp))
            (assume hq : q, h (or.inr hq)))
    (assume h : (p → r) ∧ (q → r),
        show ((p ∨ q) → r), from
        assume hpq : p ∨ q,
            or.elim hpq
                (assume hp : p, h.left hp)
                (assume hq : q, h.right hq))

theorem dem1 : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro
    (assume h : ¬(p ∨ q),
        show ¬p ∧ ¬q, from
        and.intro
            (show ¬p, from
                (assume hp : p, h (or.inl hp)))
            (show ¬q, from
                (assume hq : q, h (or.inr hq))))
    (assume h : ¬p ∧ ¬q,
        show ¬(p ∨ q), from
        (assume hpq : p ∨ q,
            or.elim hpq
                (assume hp : p, absurd hp h.left)
                (assume hq : q, absurd hq h.right)))

theorem dem2 : ¬p ∨ ¬q → ¬(p ∧ q) :=
assume h : ¬p ∨ ¬q,
    show ¬(p ∧ q), from
    (assume hpq : p ∧ q,
        or.elim h
            (assume hnp : ¬p, absurd hpq.left hnp)
            (assume hnq : ¬q, absurd hpq.right hnq))

example : ¬(p ∧ ¬p) :=
show ¬(p ∧ ¬p), from
assume hpnp : p ∧ ¬p,
    absurd hpnp.left hpnp.right

example : p ∧ ¬q → ¬(p → q) :=
assume h : p ∧ ¬q,
    show ¬(p → q), from
    assume hnpiq : p → q,
        absurd (hnpiq h.left) h.right 

example : ¬p → (p → q) :=
assume hnp : ¬p,
    show p → q, from
    assume hp : p,
        absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
assume h : (¬p ∨ q),
    show (p → q), from
    (assume hp : p,
        or.elim h
            (assume hnp : ¬p, absurd hp hnp)
            (assume hq : q, hq))

example : p ∨ false ↔ p :=
iff.intro
    (assume h : p ∨ false,
        show p, from
        or.elim h
            (assume hp : p, hp)
            false.elim)
    (assume hp : p,
        show p ∨ false, from
        or.inl hp)

example : p ∧ false ↔ false :=
iff.intro
    (assume h : p ∧ false,
        show false, from
        h.right)
    false.elim

-- with classical (because couldn't figure out how to do it without, for a while)
-- p ¬(p ↔ ¬p)
-- 1         1
-- 0         1
example : ¬(p ↔ ¬p) :=
assume hneg : p ↔ ¬p,
or.elim (classical.em p)
    (assume hp : p,
        absurd hp (hneg.mp hp))
    (assume hnp : ¬p,
        absurd (hneg.mpr hnp) hnp)

-- without classical
example : ¬(p ↔ ¬p) :=
assume h : p ↔ ¬p,
have hnp : ¬p, from
    (show p → false, from
        assume hp : p,
        absurd hp (h.mp hp)),
absurd (h.mpr hnp) hnp

example : (p → q) → (¬q → ¬p) :=
assume h : p → q,
show ¬q → ¬p, from -- (q → false) → (p → false)
    assume hnq : ¬q,
    show ¬p, from
    assume hp : p,
        absurd (h hp) hnq

-- these require classical reasoning
open classical

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
assume h : p → r ∨ s,
show (p → r) ∨ (p → s), from
or.elim (em p)
    (assume hp : p,
        have hrs : r ∨ s, from h hp,
        or.elim hrs
            (assume hr : r,
                show (p → r) ∨ (p → s), from
                suffices hpr : p → r, from or.inl hpr,
                show (p → r), from
                assume hp : p, hr)
            (assume hs : s,
                show (p → r) ∨ (p → s), from
                suffices hps : p → s, from or.inr hps,
                show (p → s), from
                assume hp : p, hs))
    (assume hnp : ¬p,
        show (p → r) ∨ (p → s), from
        suffices hpr : p → r, from or.inl hpr,
        show (p → r), from
        assume hp : p, absurd hp hnp)

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
assume h : ¬(p ∧ q),
show ¬p ∨ ¬q, from
or.elim (em p)
    (assume hp : p,
        or.elim (em q)
            (assume hq : q,
                show ¬p ∨ ¬q, from
                false.elim (h ⟨hp, hq⟩))
            or.inr)
    or.inl

example : ¬(p → q) → p ∧ ¬q :=
assume h : ¬(p → q),
show p ∧ ¬q, from
or.elim (em q)
    (assume hq : q,
        suffices hneg : p → q, from false.elim (h hneg),
        assume hp : p, hq)
    (assume hnq : ¬q,
        or.elim (em p)
            (assume hp : p, ⟨hp, hnq⟩)
            (assume hnp : ¬p,
                suffices hneg : p → q, from false.elim (h hneg),
                assume hp : p, absurd hp hnp))

-- p q ¬p ∨ q
-- 1 1      1
-- 1 0      0
-- 0 1      1
-- 0 0      1
example : (p → q) → (¬p ∨ q) :=
assume h : p → q,
show ¬p ∨ q, from
or.elim (em q)
    (assume hq : q,
        or.inr hq)
    (assume hnq : ¬q,
        show ¬p ∨ q, from
        or.elim (em p)
            (assume hp : p,
                absurd (h hp) hnq)
            (assume hnp : ¬p,
                or.inl hnp))

-- p q ¬q → ¬p p → q
-- 1 1       1     1
-- 1 0       0     0
-- 0 1       1     1
-- 0 0       1     1
example : (¬q → ¬p) → (p → q) :=
assume h : ¬q → ¬p,
show p → q, from
or.elim (em p)
    (assume hp : p,
        or.elim (em q)
            (assume hq : q,
                show p → q, from
                assume hp : p, hq)
            (assume hnq : ¬q,
                suffices hneg : ¬(¬q → ¬p), from absurd h hneg,
                absurd hp (h hnq)))
    (assume hnp : ¬p,
        assume hp : p, absurd hp hnp)

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
assume h1 : (p → q) → p,
show p, from
or.elim (em p)
    id
    (assume hnp : ¬p,
        have hpq : p → q, from (assume hp : p, absurd hp hnp),
        absurd (h1 hpq) hnp)

