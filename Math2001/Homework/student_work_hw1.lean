/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- # Section 1.2: Proving equalities in Lean (continued) -/


-- Example 1.2.3
-- Exercise: replace the words "sorry" with the correct Lean justification.

example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw [h1, h2]
    _ = 2 := by ring


-- Example 1.2.4.
-- Exercise: type out the whole proof printed in the text as a Lean proof.

example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e)
    = (a * d) * f - (d * e) * b := by ring
  _ = (b * c) * f - (d * e) * b := by rw [h1]
  _ = (b * c) * f - (c * f) * b := by rw [h2]
  _= 0 := by ring

/-! # Section 1.3: Tips and tricks

Exercise: choose some of these examples and type out the whole proofs printed in the text as Lean
proofs. -/


-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a
    = 2 * 3 + 5 := by rw [h1, h2]
  _ = 11 := by ring

-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x
    = x + 4 - 4 := by ring
  _ = 2 - 4 := by rw [h1]
  _ = -2 := by ring

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a
    = a - 5 * b + 5 * b := by ring
  _ = 4 + 5 * b := by rw [h1]
  _ = -6 + 5 * (b + 2) := by ring
  _ = -6 + 5 * 3 := by rw [h2]
  _ = 9 := by ring

-- Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w
    = (3 * w + 1) / 3 - 1 / 3 := by ring
  _ = 4 / 3 - 1 /  3 := by rw [h1]
  _ = 1 := by ring


-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
    x
    = 2 * x + 3 - x - 3 := by ring
  _ = x - x - 3 := by rw [h1]
  _ = -3 := by ring

example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  by
  have h2 : x + 3 = 0 := by
    calc
      x + 3 = (2 * x + 3) - x := by ring
      _     = x - x           := by rw [h1]
      _     = 0               := by ring
  have h3 : x = -3 := by
    calc
      x = x + 3 - 3 := by ring
      _ = 0 - 3     := by rw [h2]
      _ = -3        := by ring
  exact h3
