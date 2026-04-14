import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs

-- Test the proof logic in isolation
example (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0)
    (h_small : c < a / (100 * b)) (h_cd : c * d^2 > 0) : 
    c * d^2 < a * b / 100 := by
  calc c * d^2
      < (a / (100 * b)) * d^2 := by
        apply mul_lt_mul_of_pos_right h_small
        exact sq_pos_of_pos hd
    _ = a * d^2 / (100 * b) := by ring
    _ ≤ a * b / 100 := by
        sorry
