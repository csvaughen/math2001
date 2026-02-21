/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- From Section 1.3 Tips and Tricks in Mechanics of Proof by Heather Macbeth
-- see textbook Mechanics of Proof for hints

/- For full credit use only "calc" blocks for a proof and use only "ring", or "rw".
   You may also use the "have" tactic, for an intermediate result, but this is not
   really necessary given that "have" is introduced in chapter 2.
-/


-- Example 1.3.6
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
    x
    = (2 * x - y) + (y - x + 1) - 1 := by ring
  _ = 4 + 2 - 1 := by rw [h1, h2]
  _ = 5 := by ring

-- Example 1.3.7
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u
    = ((u + 2 * v) + (u - 2 * v)) / 2 := by ring
  _ = (4 + 6) / 2 := by rw [h1, h2]
  _ = 5:= by ring


-- Example 1.3.8
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    x
    = (3 * (x + y) + (5 * x - 3 * y)) / 8 := by ring
  _ = (3 * 4 + 4) / 8 := by rw [h1, h2]
  _ = 2 := by ring

-- Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3
    = ((a - 3) ^ 2 + 6 * a - 9) - a + 3 := by ring
  _ = (a - 3) ^ 2 + 5 * a - 6 := by ring
  _ = (a - 3) ^ 2 + 5 * ((a - 3) + 3) - 6 := by ring
  _ = (a - 3) ^ 2 + 5 * (a - 3) + 9 := by ring
  _ = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw [h1]
  _ = 4 * b ^ 2 + 10 * b + 9 := by ring



-- Example 1.3.10
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
    z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1
    = (z ^ 2 - 2) * (z ^ 2 - z + 1) + 3 := by ring
  _ = 0 * (z ^ 2 - z + 1) + 3 := by rw [h1]
  _ = 3 := by ring



-- a few additional examples:

example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
    y
    = 4 * x - 3 := by rw [h2]
  _ = 4 * 3 - 3 := by rw [h1]
  _= 9 := by ring



example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
    a
    = a - b + b := by ring
  _ = 0 + b := by rw [h]
  _ = b := by ring


example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  calc
    a
    = (a + 2 * b + 3 * c) - ((b + 2 * c) + (b + 2 * c) + c - 2 * c) := by ring
  _ = 7 - (3 + 3 + 1 - 2 * 1)  := by rw [h1, h2, h3]
  _ = 2 := by ring
