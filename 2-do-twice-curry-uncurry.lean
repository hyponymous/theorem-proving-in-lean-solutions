def double : ℕ → ℕ := λ x, x + x
def square : ℕ → ℕ := λ x, x * x
def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)

def octuple : ℕ → ℕ := λ x, double (do_twice double x)
#reduce octuple 10

def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := λ g f x, g (g f) x
#reduce do_twice double 2
#reduce Do_Twice do_twice double 2

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ x y, f (x, y)

def foo : ((ℕ × ℕ) → ℕ) := λ pair, pair.1 + pair.2 + pair.2
#reduce (curry ℕ ℕ ℕ foo) 10 1

def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ pair, f pair.1 pair.2

def bar : (ℕ → ℕ → ℕ) := λ x y, x + y + y
#reduce (uncurry ℕ ℕ ℕ bar) (10, 1)
#reduce (uncurry ℕ ℕ ℕ (curry ℕ ℕ ℕ foo)) (10, 1)
#reduce (curry ℕ ℕ ℕ (uncurry ℕ ℕ ℕ bar)) 10 1
