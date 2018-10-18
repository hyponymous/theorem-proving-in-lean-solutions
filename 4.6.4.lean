namespace hidden

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n : ℕ) : Prop := 2 ∣ n

-- BEGIN
def prime (n : ℕ) : Prop :=
sorry

def infinitely_many_primes : Prop :=
sorry

def Fermat_prime (n : ℕ) : Prop :=
sorry

def infinitely_many_Fermat_primes : Prop :=
sorry

def goldbach_conjecture : Prop :=
sorry

def Goldbach's_weak_conjecture : Prop :=
sorry

def Fermat's_last_theorem : Prop :=
sorry
-- END

end hidden
