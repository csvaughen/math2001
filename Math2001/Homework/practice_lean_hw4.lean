
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring

/-
 **Problem 1.**
 Let `x` and `y` be real numbers with `x + y = 10` and `x - y = 4`. Show that `x = 7`.
-/


/- this doesn't work
example {x y : ℝ} (h1 : x + y = 10) (h2: x - y = 4): x = 7 := by
  have h3 : 2*x=14 := by addarith [h1,h2]
  addarith [h3]
-/

/- this also doesn't work
example {x y : ℝ} (h1 : x + y = 10) (h2 : x - y = 4) : x = 7 := by
  have h3 : 2 * x = 14 := by addarith [h1, h2]
  calc
    x = 2 * x / 2 := by ring
    _ = 14 / 2 := by rw [h3]
    _ = 7 := by numbers
-/

/-got it!!! the lesson is "have" doesn't really work well here
  because addarith is a custom tactic from Macbeth that doesn't handle the neccessary
  division
-/

example {x y : ℝ} (h1 : x + y = 10) (h2 : x - y = 4) : x = 7 := by
  calc
    x = ((x + y) + (x - y)) / 2 := by ring
    _ = (10 + 4) / 2 := by rw [h1, h2]
    _ = 7 := by numbers
