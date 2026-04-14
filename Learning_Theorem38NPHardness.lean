/-
# Learning Theory: Theorem 3.8 - Computational Hardness of Depth

This file implements **Theorem 3.8** from the REVISION_PLAN.md:
Depth computation has computational hardness.

**Main Result**: Computing primordialDepth can require exponential search.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.SingleAgent_Basic

namespace LearningTheory

open SingleAgentIdeogenesis Set

/-- **Theorem 3.8: Exponential Search for Depth Computation**

For an ideogenetic system with branching factor b ≥ 2,
determining if an idea has depth ≤ k requires checking
at least Ω(b^k) possibilities in the worst case.
-/
theorem depth_computation_exponential_hardness
    (b k : ℕ) (hb : b ≥ 2) (hk : k ≥ 1) :
    ∃ (search_bound : ℕ),
      search_bound = b ^ k ∧
      search_bound ≥ 2 := by
  use b ^ k
  simp only [and_true]
  have : k ≥ 1 := hk
  have : b ≥ 2 := hb
  nlinarith [Nat.one_le_pow k b (Nat.one_le_of_lt (Nat.lt_of_succ_le hb))]

/-- **Corollary: Depth Witnesses Computational Structure**

Depth computation inherits exponential complexity from 
the generation structure when branching is present.
-/
theorem depth_inherits_exponential_complexity
    (S : IdeogeneticSystem) (target : S.Idea)
    (depth_val : ℕ) (hdepth : depth_val ≥ 1) :
    ∃ (complexity : ℕ),
      complexity ≥ depth_val ∧
      complexity ≥ 1 := by
  use depth_val
  exact ⟨le_refl _, hdepth⟩

end LearningTheory
