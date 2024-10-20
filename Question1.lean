-- This module serves as the root of the `Question1` library.
-- Import modules here that should be built as part of the library.
import Question1.Basic

namespace QA
-- Define factorial
def fact (x : Nat): Nat:=
  match x with
  | 0   => 1
  | n + 1 => (n + 1) * fact n

#eval fact 100

-- Define binomial coefficient using factorial
def binom (n k : Nat) : Nat :=
  fact n / ( fact k * fact (n-k) )


#eval binom 1 1
#eval binom 9 7
#eval binom 2 2
#eval binom 2 0
#eval binom 3 2
#eval binom 2 2
#eval binom 5 4

def choose (a b : Nat): Nat:=
  match a, b with
  | _      ,       0 => 1
  | 0       , _      => 0
  | (n + 1) ,(k + 1) => choose n k + choose n (Nat.succ k)

#eval choose 10 0

theorem binom_zero2 (n: Nat) : choose n 0 = 1 := by simp[choose]

--theorem bion1_equal_bion2_0 (n: Nat) :choose a 0 = binom a 0 := 
--  Nat.recOn ( motive := fun x => choose a 0 = binom a 0)
--    n
--    (show choose n 0 = binom n 0 from rfl)
--    (fun (n: Nat) (ih : choose n 0 = binom a 0) => 
--      show choose (succ n) 0 = binom (succ n) 0 from
--      calc choose (succ n) 0 
--      _ =>)
--theorem binom_zero2 (n: Nat) : choose n 0 = 1 := 
--  Nat.recOn ( motive := fun x => choose x 0 = 1 )
--    n
--    (show choose n 0 = 1 from rfl)
--    (fun (n: Nat) (ih: choose n 0 = 1) =>
--      show choose (succ n) 0 = 1 from
--      calc choose (succ n) 0
--        _ = )

-- Import the necessary library for natural numbers (ℕ)

-- Prove that f a * f b = f b * f a using the built-in `mul_comm`
theorem mul_comm_for_functions {f : Nat → Nat} (a b : Nat) : f a * f b = f b * f a :=
   Nat.mul_comm (f a) (f b)

theorem functions_one {f : Nat → Nat} (a) : f a * 1  = f a :=
   Nat.mul_one (f a)


theorem binom_symmetry (n k : Nat) (h : k ≤ n) : binom n k = binom n (n - k) := 
  by
    -- Unfold the definition of binom
    unfold binom
    -- Simplify using commutativity of multiplication (fact k * fact (n - k) = fact (n - k) * fact k)
    rw [Nat.mul_comm (fact k) (fact (n - k))]
    have : n - (n - k) = k := by
      -- Use `Nat.sub_add_eq_add_sub` to show that n - (n - k) = k
      exact Nat.sub_sub_self h
    rw [this]

theorem fact_pos (n : Nat) : fact n > 0 := by
  induction n with
  | zero =>
    simp [fact]
  | succ n ih =>
    simp_all [fact]

theorem binom_zero_n_zero (n : Nat) : binom n 0 = 1 :=
  by
    -- Unfold the definition of binom
    unfold binom
    -- Simplify the expression
    rw [Nat.sub_zero]  -- n - 0 = n
    -- Rewrite fact 0 = 1
    have fact_0 : fact 0 = 1 := rfl
    rw [fact_0]  -- Replace fact 0 in the expression
    rw [Nat.mul_comm]

    rw [functions_one]-- Now it simplifies to fact n / fact n
    -- The expression is now fact n / (1 * fact n)
    rw [Nat.div_self]   -- Show that fact n / fact n = 1
    exact fact_pos n


theorem binom_zero_n_n (n : Nat) : binom n n = 1 :=
  by
    have h_symmetry: binom n n  = binom n (n-n) := binom_symmetry n n (Nat.le_refl n)
    rw [Nat.sub_self] at h_symmetry  -- n - n = 0
    rw [binom_zero_n_zero n] at h_symmetry
    -- Now we have binom n n = 1
    exact h_symmetry
