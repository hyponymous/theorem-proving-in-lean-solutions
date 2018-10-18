universe u
constant vec : Type u → ℕ → Type u

namespace vec
  constant empty : Π α : Type u, vec α 0
  constant cons :
    Π {α : Type u} {n : ℕ}, α → vec α n → vec α (n + 1)
  constant append :
    Π {α : Type u} {n m : ℕ},  vec α m → vec α n → vec α (n + m)
end vec

#check vec

-- Above, we used the example vec α n for vectors of elements of type α of
-- length n. Declare a constant vec_add that could represent a function
-- that adds two vectors of natural numbers of the same length, and a constant
-- vec_reverse that can represent a function that reverses its argument.
-- Use implicit arguments for parameters that can be inferred. Declare some
-- variables and check some expressions involving the constants that you have
-- declared.
constant vec_add : Π {α : Type u} {n : ℕ}, vec α n → vec α n → vec α n
#reduce vec.cons 456 (vec.cons 123 (vec.empty _))
#check vec_add (vec.cons 456 (vec.cons 123 (vec.empty _))) (vec.cons 456 (vec.cons 123 (vec.empty _)))

constant vec_reverse : Π {α : Type u} {n : ℕ}, vec α n → vec α n
#check vec_reverse (vec.cons 456 (vec.cons 123 (vec.empty _)))

-- Similarly, declare a constant matrix so that matrix α m n could represent the
-- type of m by n matrices. Declare some constants to represent functions on
-- this type, such as matrix addition and multiplication, and (using vec)
-- multiplication of a matrix by a vector. Once again, declare some variables
-- and check some expressions involving the constants that you have declared.

constant matrix : Type u → ℕ → ℕ → Type u
constant matrix_add : Π {α : Type u} {n m : ℕ}, matrix α n m → matrix α n m
constant matrix_mul : Π {α : Type u} {n m k : ℕ}, matrix α n m → matrix α m k → matrix α n k
constant matrix_vec_mul : Π {α : Type u} {n m : ℕ}, matrix α n m → vec α m → vec α n
