import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

-- Check what's available for power convergence
example (r : ℝ) (h1 : 0 ≤ r) (h2 : r < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ k ≥ N, r ^ k < ε := by
  exact?

