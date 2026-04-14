/-
# Type Separation Examples (Concrete Coordinate System)

We construct a concrete generator family acting on disjoint coordinates
(finite sets of indices). This system satisfies type separation and
the depth–diversity decomposition from Learning_DiversityBarrier.

## Current Assumptions and Axioms:

### Axioms Used:
- **propext**: Propositional extensionality (standard in Lean/Mathlib)
- **Quot.sound**: Quotient soundness (standard in Lean/Mathlib)
- **Classical.choice**: Used implicitly via `Classical.propDecidable` (line 94)

### Key Assumptions:

1. **Classical Logic** (line 94):
   - `attribute [local instance] Classical.propDecidable`
   - NECESSARY for decidability of existence predicates
   - Inherited from Learning_DiversityBarrier for noncomputable depth/diversity definitions
   - Cannot be eliminated without switching to constructive versions

2. **DecidableEq ι** (throughout):
   - FUNDAMENTAL REQUIREMENT - Cannot be weakened for this concrete example
   - Required by `Finset.insert` operation (line 99)
   - Required by `List.toFinset` operation (used throughout)
   - This is an INTRINSIC limitation of working with finite sets in Lean
   - However, this requirement is SATISFIED by most concrete types:
     * Nat, Int, Bool, Fin n all have DecidableEq
     * Any finite type can be given DecidableEq
     * String, Char have DecidableEq
   - The requirement is NOT weakenable while still using Finset-based coordinates

3. **Finite ι or Fintype assumption**:
   - NOT REQUIRED - this file works for arbitrary index types ι with DecidableEq
   - Only requires that Finset ι exists (always true in Lean)
   - Can be countably infinite, uncountable, etc. - no restriction on cardinality

4. **Alternative Weakening Strategy**:
   - To remove DecidableEq requirement entirely, would need to:
     a) Replace Finset ι with Set ι (loses computability)
     b) Replace List.toFinset with a different diversity measure
     c) Use multisets or other structures
   - This would be a DIFFERENT example, not a weakening of this one
   - The current example is the SIMPLEST concrete instantiation

### Sorries/Admits:
- **NONE** - All proofs are complete and verified

### What Was Actually Weakened:

**Previous issues that have been fixed:**
1. Changed `Finset.card_le_of_subset` to `Finset.card_le_card` (API update)
2. Fixed union commutativity proof using extensionality
3. Made all type parameters explicit to avoid ambiguity

**Key insight**: This file demonstrates type separation using the SIMPLEST possible
concrete example. The DecidableEq requirement is INHERENT to this approach, not
an artifact of the formalization. To get more general results that apply without
DecidableEq, use the abstract theorems in Learning_DiversityBarrier directly.

### Locations Where Assumptions Are Used:
- Classical.propDecidable: line 94 (for noncomputable definitions from imported module)
- DecidableEq ι: Required globally for Finset operations (insert, toFinset)
- typeSeparated: Proven as theorem coord_type_separation (line 248), not assumed
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import FormalAnthropology.Learning_DiversityBarrier

namespace LearningTheory

open Set Learning_DiversityBarrier
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [DecidableEq ι]

/-! ## Concrete coordinate generator -/

def coordGen (i : ι) (A : Set (Finset ι)) : Set (Finset ι) :=
  {s | ∃ t ∈ A, s = insert i t}

def coordSeed : Set (Finset ι) := {∅}

/-! ## Derivation witnesses -/

lemma mem_deriveWith_union_toFinset_aux (A : Set (Finset ι)) (t : Finset ι) (ht : t ∈ A) :
    ∀ d, t ∪ d.toFinset ∈ deriveWith coordGen d A := by
  intro d
  induction d generalizing A t with
  | nil =>
      simpa [deriveWith] using ht
  | cons i is ih =>
      -- Move to the updated seed A ∪ coordGen i A.
      have ht' : insert i t ∈ A ∪ coordGen i A := by
        right
        exact ⟨t, ht, rfl⟩
      have hmem := ih (A := A ∪ coordGen i A) (t := insert i t) ht'
      have hunion : t ∪ (i :: is).toFinset = insert i t ∪ is.toFinset := by
        ext x
        simp only [Finset.mem_union, List.toFinset_cons, Finset.mem_insert]
        tauto
      simpa [deriveWith, hunion] using hmem

lemma mem_deriveWith_toFinset (d : List ι) :
    d.toFinset ∈ deriveWith coordGen d (coordSeed : Set (Finset ι)) := by
  have hmem := mem_deriveWith_union_toFinset_aux (A := coordSeed) (t := (∅ : Finset ι))
    (by simp [coordSeed]) d
  simpa using hmem

lemma deriveWith_subset_of_seed_subset (A : Set (Finset ι)) (U : Finset ι)
    (hA : ∀ t ∈ A, t ⊆ U) :
    ∀ d s, s ∈ deriveWith coordGen d A → s ⊆ U ∪ d.toFinset := by
  intro d
  induction d generalizing A U with
  | nil =>
      intro s hs
      simpa [deriveWith] using hA s hs
  | cons i is ih =>
      intro s hs
      have hA' : ∀ t ∈ A ∪ coordGen i A, t ⊆ U ∪ {i} := by
        intro t ht
        cases ht with
        | inl htA =>
            intro x hx
            have hxU := hA t htA hx
            exact Finset.mem_union.mpr (Or.inl hxU)
        | inr htGen =>
            rcases htGen with ⟨t0, ht0A, rfl⟩
            intro x hx
            simp only [Finset.mem_insert] at hx
            cases hx with
            | inl hxEq =>
                subst hxEq
                exact Finset.mem_union.mpr (Or.inr (by simp))
            | inr hxT0 =>
                have hxU := hA t0 ht0A hxT0
                exact Finset.mem_union.mpr (Or.inl hxU)
      have hsubset := ih (A := A ∪ coordGen i A) (U := U ∪ {i}) hA' _ hs
      have hunion : U ∪ {i} ∪ is.toFinset = U ∪ (i :: is).toFinset := by
        ext x
        simp only [Finset.mem_union, Finset.mem_singleton, List.toFinset_cons, Finset.mem_insert]
        tauto
      simpa [deriveWith, hunion] using hsubset

/-! ## Cardinality bounds from derivations -/

lemma card_le_of_hasDepthAtMost (s : Finset ι) (k : Nat)
    (hk : hasDepthAtMost coordGen coordSeed s k) :
    s.card ≤ k := by
  rcases hk with ⟨d, hmem, hlen⟩
  have hsubset : s ⊆ d.toFinset := by
    have hA : ∀ t ∈ coordSeed, t ⊆ (∅ : Finset ι) := by
      intro t ht
      have ht' : t = (∅ : Finset ι) := by
        simpa [coordSeed] using ht
      subst ht'
      simp
    have hsubset' := deriveWith_subset_of_seed_subset (A := coordSeed) (U := (∅ : Finset ι)) hA d s hmem
    simpa using hsubset'
  have hcard_le : s.card ≤ d.toFinset.card := Finset.card_le_card hsubset
  have hcard_le' : s.card ≤ d.length := by
    exact hcard_le.trans (by simpa using (List.toFinset_card_le d))
  exact hcard_le'.trans hlen

lemma card_le_of_hasDiversityAtMost (s : Finset ι) (r : Nat)
    (hr : hasDiversityAtMost coordGen coordSeed s r) :
    s.card ≤ r := by
  rcases hr with ⟨d, hmem, hcard⟩
  have hsubset : s ⊆ d.toFinset := by
    have hA : ∀ t ∈ coordSeed, t ⊆ (∅ : Finset ι) := by
      intro t ht
      have ht' : t = (∅ : Finset ι) := by
        simpa [coordSeed] using ht
      subst ht'
      simp
    have hsubset' := deriveWith_subset_of_seed_subset (A := coordSeed) (U := (∅ : Finset ι)) hA d s hmem
    simpa using hsubset'
  have hcard_le : s.card ≤ d.toFinset.card := Finset.card_le_card hsubset
  exact hcard_le.trans hcard

lemma toList_length_eq_card (s : Finset ι) : s.toList.length = s.card := by
  have hnodup := s.nodup_toList
  have hcard := List.toFinset_card_of_nodup hnodup
  have hlen : s.toList.length = s.card := by
    have hcard' : s.toList.toFinset.card = s.toList.length := hcard
    -- Rewrite the LHS to `s.card`.
    simpa [Finset.toList_toFinset] using hcard'.symm
  exact hlen

/-! ## Depth and diversity equal cardinality -/

lemma derivationDepth_eq_card (s : Finset ι) :
    derivationDepth coordGen coordSeed s = s.card := by
  -- Upper bound via the explicit derivation.
  have hmem : s ∈ deriveWith coordGen s.toList coordSeed := by
    simpa [Finset.toList_toFinset] using (mem_deriveWith_toFinset (d := s.toList))
  have hlen : s.toList.length ≤ s.card := by
    simpa [toList_length_eq_card s] using (le_of_eq (toList_length_eq_card s))
  have hdepthAtMost : hasDepthAtMost coordGen coordSeed s s.card :=
    ⟨s.toList, hmem, hlen⟩
  have hle := derivationDepth_le_of_derivation coordGen coordSeed s s.card hdepthAtMost
  -- Lower bound via minimality.
  have hreach : ∃ k, hasDepthAtMost coordGen coordSeed s k := ⟨s.card, hdepthAtMost⟩
  have hspec : hasDepthAtMost coordGen coordSeed s (derivationDepth coordGen coordSeed s) := by
    unfold derivationDepth
    rw [dif_pos hreach]
    exact Nat.find_spec hreach
  have hge := card_le_of_hasDepthAtMost s (derivationDepth coordGen coordSeed s) hspec
  exact le_antisymm hle hge

lemma diversity_eq_card (s : Finset ι) :
    diversity coordGen coordSeed s = s.card := by
  -- Upper bound via explicit derivation.
  have hmem : s ∈ deriveWith coordGen s.toList coordSeed := by
    simpa [Finset.toList_toFinset] using (mem_deriveWith_toFinset (d := s.toList))
  have hcard : s.toList.toFinset.card ≤ s.card := by
    have hEq : s.toList.toFinset.card = s.card := by
      have hlen : s.toList.length = s.card := toList_length_eq_card s
      have hcard' : s.toList.toFinset.card = s.toList.length :=
        List.toFinset_card_of_nodup s.nodup_toList
      exact hcard'.trans hlen
    simpa [hEq]
  have hdivAtMost : hasDiversityAtMost coordGen coordSeed s s.card :=
    ⟨s.toList, hmem, hcard⟩
  have hle := diversity_le_of_derivation coordGen coordSeed s s.card hdivAtMost
  -- Lower bound via minimality.
  have hreach : ∃ r, hasDiversityAtMost coordGen coordSeed s r := ⟨s.card, hdivAtMost⟩
  have hspec : hasDiversityAtMost coordGen coordSeed s (diversity coordGen coordSeed s) := by
    unfold diversity
    rw [dif_pos hreach]
    exact Nat.find_spec hreach
  have hge := card_le_of_hasDiversityAtMost s (diversity coordGen coordSeed s) hspec
  exact le_antisymm hle hge

/-! ## Type separation and decomposition -/

/--
**Main Result**: The coordinate system satisfies type separation.

This theorem shows that for the concrete coordinate generator system,
there exists a SINGLE derivation that simultaneously achieves both
minimal depth and minimal diversity. This is a special property of
this particular example - in general, type separation does not hold.

The key insight is that for coordinate generators, the most efficient
path (using fewest steps) is also the most diverse path (using all
necessary coordinate directions). This is because:
- Each coordinate must be added exactly once
- Adding coordinates in any order gives the same result
- The shortest derivation uses each needed coordinate exactly once
-/
theorem coord_type_separation : @typeSeparated (Finset ι) ι _ coordGen coordSeed := by
  intro s _hreach
  refine ⟨s.toList, ?_, ?_, ?_⟩
  · simpa [Finset.toList_toFinset] using (mem_deriveWith_toFinset (d := s.toList))
  · have hlen : s.toList.length = s.card := toList_length_eq_card s
    simp [derivationDepth_eq_card s, hlen]
  · have hcard : s.toList.toFinset.card = s.card := by
      simpa [Finset.toList_toFinset] using (List.toFinset_card_of_nodup s.nodup_toList)
    simp [diversity_eq_card s, hcard]

/--
**Main Result**: Depth-diversity decomposition for the coordinate system.

This theorem establishes that the set of ideas reachable within k steps
using at most r generator types is exactly characterized by the ideas
with depth ≤ k and diversity ≤ r. This is a consequence of type separation.
-/
theorem coord_depth_diversity_decomposition (k r : Nat) :
    @reachWithin (Finset ι) ι _ coordGen coordSeed k r =
      {h | reachable coordGen coordSeed h ∧
        derivationDepth coordGen coordSeed h ≤ k ∧
        @diversity (Finset ι) ι _ coordGen coordSeed h ≤ r} := by
  exact @depth_diversity_decomposition (Finset ι) ι _ coordGen coordSeed k r coord_type_separation

/-!
## Summary and Generalization Strategy

This file provides a CONCRETE EXAMPLE of a generator system satisfying type separation.
The example is intentionally simple to be easily verifiable and understandable.

### What Cannot Be Weakened:
- **DecidableEq ι**: Fundamental to Finset operations, cannot be removed while using Finsets
- **Classical logic**: Needed for noncomputable definitions of depth/diversity

### Why This Example Is Important:
1. **Existence**: Proves that type separation is not vacuous - systems satisfying it exist
2. **Simplicity**: Provides the simplest concrete instantiation for understanding the concepts
3. **Verification**: All proofs are complete and mechanically verified

### For More General Results:
- Use the abstract theorems in Learning_DiversityBarrier
- Those theorems work for ANY generator system (no DecidableEq needed)
- Only the depth-diversity decomposition requires the typeSeparated assumption
- All other key results (diversity barriers, access expansion) hold generally

### Implementation Note:
The coordinate system works for ANY type ι with DecidableEq, including:
- Finite types: Fin n, Bool, small enums
- Infinite types: Nat, Int, String
- Custom types: any type you define with decidable equality

The cardinality of ι can be countable or uncountable - no restriction is imposed.
-/

end LearningTheory
