open classical

variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

theorem not_p_iff_not_p {p : Prop} : ¬(p ↔ ¬p) :=
assume h : p ↔ ¬p,
have hnp : ¬p, from (assume hp : p, (h.mp hp) hp),
hnp (h.mpr hnp)

-- via not_p_iff_not_p
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
not_p_iff_not_p (h barber)

-- standalone
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
have hparadox : shaves barber barber ↔ ¬shaves barber barber, from
    (h barber),
have hn_self_shave : ¬shaves barber barber, from
    (show shaves barber barber → false, from
        assume h_self_shave : shaves barber barber,
        absurd h_self_shave (hparadox.mp h_self_shave)),
absurd (hparadox.mpr hn_self_shave) hn_self_shave

