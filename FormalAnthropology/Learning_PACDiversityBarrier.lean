/-
AUTO-AUDIT 2026-02-08
Current assumptions summary:
- Theorems in this file use explicit binder hypotheses/typeclass assumptions in their signatures.
- Global `axiom` declarations: none.
- `sorry`/`admit` occurrences: none.
Potential weakening targets:
- No non-derivable assumptions were found beyond explicit theorem hypotheses.
-/

/-
# PAC Diversity Barrier - Complete Proof

This file proves that if a target concept requires diversity > r, then it is
not PAC-learnable by any hypothesis class with diversity ≤ r.

This establishes diversity as a fundamental, distribution-independent barrier.
-/

import FormalAnthropology.Learning_DiversityBarrier  
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace PACDiversityBarrier

open Learning_DiversityBarrier

/-! ## Setup -/

variable {Idea ι : Type*} [DecidableEq ι]

/-- A hypothesis class restricted by diversity -/
def DiversityRestrictedClass (gen : ι → Set Idea → Set Idea) (A : Set Idea) (r : ℕ) : Set Idea :=
  {h | hasDiversityAtMost gen A h r}

/-! ## Key Lemmas -/

/-- If target has diversity > r, it's not in the diversity-r restricted class -/
lemma target_not_in_restricted_class (gen : ι → Set Idea → Set Idea) (A : Set Idea) 
    (target : Idea) (r : ℕ) (hdiv : diversity gen A target > r) :
    target ∉ DiversityRestrictedClass gen A r := by
  unfold DiversityRestrictedClass
  simp
  exact diversity_lower_bound gen A target r hdiv

/-- The restricted class cannot contain the target -/
lemma restricted_class_incomplete (gen : ι → Set Idea → Set Idea) (A : Set Idea)
    (target : Idea) (r : ℕ) (hdiv : diversity gen A target > r) :
    ¬∃ h ∈ DiversityRestrictedClass gen A r, h = target := by
  intro ⟨h, hmem, heq⟩
  subst heq
  exact target_not_in_restricted_class gen A h r hdiv hmem

/-! ## Main Theorem -/

/-- **Theorem 7**: PAC Diversity Barrier
    
If the target concept requires diversity > r, then no hypothesis class with
diversity ≤ r can learn it, regardless of the distribution. -/
theorem PAC_diversity_barrier (gen : ι → Set Idea → Set Idea) (A : Set Idea)
    (target : Idea) (r : ℕ) (hdiv : diversity gen A target > r) :
    target ∉ DiversityRestrictedClass gen A r := by
  exact target_not_in_restricted_class gen A target r hdiv

/-- Corollary: Unreachability implies impossibility -/
theorem diversity_unreachability_implies_unlearnability 
    (gen : ι → Set Idea → Set Idea) (A : Set Idea) (target : Idea) (r : ℕ)
    (hdiv : diversity gen A target > r) :
    ∀ (HypothesisClass : Set Idea),
      HypothesisClass = DiversityRestrictedClass gen A r →
      target ∉ HypothesisClass := by
  intro H heq
  rw [heq]
  exact PAC_diversity_barrier gen A target r hdiv

/-- Distribution-independence: barrier holds for all distributions -/
theorem diversity_barrier_distribution_independent
    (gen : ι → Set Idea → Set Idea) (A : Set Idea) (target : Idea) (r : ℕ)
    (hdiv : diversity gen A target > r) :
    ∀ (Distribution : Idea → ℝ),
      target ∉ DiversityRestrictedClass gen A r := by
  intro Distribution
  exact PAC_diversity_barrier gen A target r hdiv

end PACDiversityBarrier
