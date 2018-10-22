#check sub_self

example (x : ℤ) : x * 0 = 0 :=
calc
    x * 0 = x * (x - x)   : by rw sub_self
      ... = x * x - x * x : by rw mul_sub
      ... = 0             : by rw sub_self

