namespace hidden

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n : ℕ) : Prop := 2 ∣ n

-- BEGIN
def prime (n : ℕ) : Prop :=
¬∃ m, m > 1 ∧ m < n ∧ (m ∣ n)

def infinitely_many_primes : Prop :=
∀ n, ∃ p, p > n ∧ prime p

def Fermat_number (n : ℕ) : Prop :=
∃ k : ℕ, 2^(2^k) + 1 = n

def Fermat_prime (n : ℕ) : Prop :=
prime n ∧ Fermat_number n

def infinitely_many_Fermat_primes : Prop :=
∀ n, ∃ fp, fp > n ∧ Fermat_prime fp

-- Every even integer greater than 2 can be expressed as the sum of two primes
def goldbach_conjecture : Prop :=
∀ n, n > 2 → ∃ p q, p + q = n ∧ prime p ∧ prime q

-- Every odd number greater than 5 can be expressed as the sum of three primes
def Goldbach's_weak_conjecture : Prop :=
∀ n, even n ∧ n > 5 → ∃ p p' p'', p + p' + p'' = n ∧ prime p ∧ prime p' ∧ prime p''

-- no three positive integers a, b, and c satisfy the equation an + bn = cn for
-- any integer value of n greater than 2
def Fermat's_last_theorem : Prop :=
∀ n, n > 2 → ¬∃ a b c, a^n + b^n = c^n ∧ a > 0 ∧ b > 0 ∧ c > 0

-- END

end hidden
