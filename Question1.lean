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


theorem binom_zero (n : Nat) (h :  n > 0) : binom n 0 = 1 :=
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
    have fact_pos : fact n > 0 := sorry
    rw [Nat.div_self]   -- Show that fact n / fact n = 1


theorem fact_pos (n : Nat) (h : n > 0) : fact n > 0 := sorry
--  by
--    -- Use cases on n
--    cases n with
--    | zero =>
--      -- This case won't occur since h: n > 0
--      -- No need to prove fact 0 > 0, as we know n is greater than 0
--      contradiction
--    | succ n' =>
--      -- Now we have n = n' + 1
--      -- Show that fact (n' + 1) > 0
--      unfold fact
--      -- We have fact (n' + 1) = (n' + 1) * fact n'
--      apply Nat.mul_pos
--      -- Prove that n' + 1 > 0
--      exact Nat.succ_pos n'
--      -- Prove that fact n' > 0 using the induction hypothesis
--      apply fact_pos
--      -- Show that n' is still > 0
--      exact Nat.succ_pos n'  -- n' = n - 1, thus n' >= 0
-- Theorem: binom n 0 = 1

open Nat
theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
    n
    (show 0 + 0 = 0 from rfl)
    (fun (n : Nat) (ih : 0 + n = n) =>
      show 0 + succ n = succ n from
      calc 0 + succ n
        _ = succ (0 + n) := rfl
        _ = succ n       := by rw [ih])

namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
    n
    rfl
    (fun n ih => by simp [add_succ, ih])
end Hidden

