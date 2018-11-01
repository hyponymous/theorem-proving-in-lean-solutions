-- there are several ways of doing this, and probably more compact and/or
-- idiomatic ways than what I have here

example (p q r : Prop) (hp : p) :
    (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by simp *

example (p q r : Prop) (hp : p) :
    (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by { constructor, left, assumption, constructor, right, left, assumption, right, right, assumption }

example (p q r : Prop) (hp : p) :
    (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by { repeat { split; repeat { { left, assumption } <|> right <|> assumption } } }

