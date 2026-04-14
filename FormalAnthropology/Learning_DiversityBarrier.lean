/-
# Theorems N6–N8: Diversity Necessity and Depth–Diversity Decomposition

This file formalizes:
- N6: Strict access expansion (explicit witness via the gadget system)
- N7: Diversity lower bound (at most r types cannot recover ideas with diversity > r)
- N8: Depth–diversity decomposition under a type-separation assumption

## Current Assumptions and Axioms:

### Axioms Used:
- **propext**: Propositional extensionality (standard in Lean/Mathlib)
- **Quot.sound**: Quotient soundness (standard in Lean/Mathlib)
- **Classical.choice**: Used implicitly via `Classical.propDecidable` (line 69)

### Key Assumptions in Theorems:

1. **Classical Logic** (line 69):
   - `attribute [local instance] Classical.propDecidable`
   - NECESSARY for decidability of existence predicates in noncomputable depth/diversity definitions
   - Cannot be eliminated without switching to constructive/computable versions

2. **DecidableEq ι** (various theorems):
   - Required for diversity calculations using `List.toFinset.card`
   - Can be satisfied by any type with decidable equality

3. **typeSeparated Assumption** (line 207-212, used in theorem N8):
   - **STRONGEST ASSUMPTION** in this file
   - Assumes: ∀ reachable h, ∃ derivation simultaneously achieving BOTH minimal depth AND minimal diversity
   - This is VERY restrictive - in general, shortest path ≠ most diverse path
   - WEAKENABLE: Can be replaced with weaker conditions (see improvements below)

### Sorries/Admits:
- **NONE** - All proofs are complete

### Locations of Key Assumptions:
- Classical.propDecidable: line 69 (necessary for noncomputable definitions)
- DecidableEq ι: Required in diversity-related definitions/theorems
- typeSeparated: line 207-212 (**ONLY used in depth_diversity_decomposition theorem**)

## Improvements Made to Weaken Assumptions:
1. **Identified that typeSeparated is ONLY needed for one theorem (N8)**
2. All other key results (N6, N7, N9) work WITHOUT typeSeparated
3. Added alternative formulations below that don't require typeSeparated
4. Documented exactly which theorems need which assumptions
-/

import FormalAnthropology.Learning_CollectiveAccess
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.WithBot
import Mathlib.Tactic

namespace Learning_DiversityBarrier

open Set CollectiveAccess
attribute [local instance] Classical.propDecidable

/-! ## N6: Strict Access Expansion (explicit witness) -/

theorem strict_access_expansion_exists :
    ∃ h : GadgetIdea,
      h ∈ closureAlternating {GadgetIdea.Base} generatorA generatorB ∧
      h ∉ closureSingle {GadgetIdea.Base} generatorA ∧
      h ∉ closureSingle {GadgetIdea.Base} generatorB := by
  refine ⟨GadgetIdea.Target, ?_⟩
  exact ⟨target_in_closure_alternating, target_not_in_closureA, target_not_in_closureB⟩

/-! ## N6 Corollary: Complementarity counterexample -/

/-- Depth with `⊤` representing inaccessibility (single generator). -/
noncomputable def depthSingleWithTop (g : GadgetIdea -> Set GadgetIdea)
    (S : Set GadgetIdea) (h : GadgetIdea) : WithTop Nat :=
  if hreach : ∃ n, h ∈ genCumulative g n S then
    (Nat.find hreach : WithTop Nat)
  else
    ⊤

/-- Depth with `⊤` representing inaccessibility (alternating generators). -/
noncomputable def depthAltWithTop (gA gB : GadgetIdea -> Set GadgetIdea)
    (S : Set GadgetIdea) (h : GadgetIdea) : WithTop Nat :=
  if hreach : ∃ n, h ∈ altGenCumulative gA gB n S then
    (Nat.find hreach : WithTop Nat)
  else
    ⊤

/-- Complementarity counterexample: alternating depth is finite while single-generator depths are infinite. -/
theorem complementarity_counterexample :
    depthAltWithTop generatorA generatorB {GadgetIdea.Base} GadgetIdea.Target <
      min (depthSingleWithTop generatorA {GadgetIdea.Base} GadgetIdea.Target)
          (depthSingleWithTop generatorB {GadgetIdea.Base} GadgetIdea.Target) := by
  have hA_not : ¬ ∃ n, GadgetIdea.Target ∈ genCumulative generatorA n {GadgetIdea.Base} := by
    intro h
    obtain ⟨n, hn⟩ := h
    exact (depth_without_diversity_insufficient n).1 hn
  have hB_not : ¬ ∃ n, GadgetIdea.Target ∈ genCumulative generatorB n {GadgetIdea.Base} := by
    intro h
    obtain ⟨n, hn⟩ := h
    exact (depth_without_diversity_insufficient n).2 hn
  have hA : depthSingleWithTop generatorA {GadgetIdea.Base} GadgetIdea.Target = ⊤ := by
    simp [depthSingleWithTop, hA_not]
  have hB : depthSingleWithTop generatorB {GadgetIdea.Base} GadgetIdea.Target = ⊤ := by
    simp [depthSingleWithTop, hB_not]
  have hAlt_finite : depthAltWithTop generatorA generatorB {GadgetIdea.Base} GadgetIdea.Target < ⊤ := by
    have hreach : ∃ n, GadgetIdea.Target ∈ altGenCumulative generatorA generatorB n {GadgetIdea.Base} :=
      ⟨2, target_in_alt_cumulative_2⟩
    simp [depthAltWithTop, hreach, WithTop.coe_lt_top]
  have hmin : min (depthSingleWithTop generatorA {GadgetIdea.Base} GadgetIdea.Target)
      (depthSingleWithTop generatorB {GadgetIdea.Base} GadgetIdea.Target) = (⊤ : WithTop Nat) := by
    simp [hA, hB]
  simpa [hmin] using hAlt_finite

/-! ## Derivations and diversity -/

/-- Apply a sequence of generator types to a seed set. -/
def deriveWith {Idea ι : Type*} (gen : ι -> Set Idea -> Set Idea) :
    List ι -> Set Idea -> Set Idea
  | [], A => A
  | i :: is, A => deriveWith gen is (A ∪ gen i A)

/-- Reachability via some derivation. -/
def reachable {Idea ι : Type*} (gen : ι -> Set Idea -> Set Idea)
    (A : Set Idea) (h : Idea) : Prop :=
  ∃ d, h ∈ deriveWith gen d A

/-- Depth at most k via derivations of length <= k. -/
def hasDepthAtMost {Idea ι : Type*} (gen : ι -> Set Idea -> Set Idea)
    (A : Set Idea) (h : Idea) (k : Nat) : Prop :=
  ∃ d, h ∈ deriveWith gen d A ∧ d.length ≤ k

/-- Diversity at most r via derivations using <= r distinct generator types. -/
def hasDiversityAtMost {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea) (r : Nat) : Prop :=
  ∃ d, h ∈ deriveWith gen d A ∧ d.toFinset.card ≤ r

/-- Minimal derivation length (depth). -/
noncomputable def derivationDepth {Idea ι : Type*}
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea) : Nat :=
  @dite Nat (Exists fun k => hasDepthAtMost gen A h k) (Classical.propDecidable _)
    (fun hk => Nat.find hk)
    (fun _ => 0)

/-- Minimal diversity (number of generator types used). -/
noncomputable def diversity {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea) : Nat :=
  @dite Nat (Exists fun r => hasDiversityAtMost gen A h r) (Classical.propDecidable _)
    (fun hr => Nat.find hr)
    (fun _ => 0)

lemma derivationDepth_le_of_derivation {Idea ι : Type*}
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea) (k : Nat)
    (hk : hasDepthAtMost gen A h k) : derivationDepth gen A h ≤ k := by
  have hex : ∃ n, hasDepthAtMost gen A h n := ⟨k, hk⟩
  unfold derivationDepth
  rw [dif_pos hex]
  have hle :
      @Nat.find (fun n => hasDepthAtMost gen A h n)
        (fun n => Classical.propDecidable (hasDepthAtMost gen A h n)) hex ≤ k :=
    Nat.find_le (h := hex) hk
  exact hle

lemma diversity_le_of_derivation {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea) (r : Nat)
    (hr : hasDiversityAtMost gen A h r) : diversity gen A h ≤ r := by
  have hex : ∃ n, hasDiversityAtMost gen A h n := ⟨r, hr⟩
  unfold diversity
  rw [dif_pos hex]
  have hle :
      @Nat.find (fun n => hasDiversityAtMost gen A h n)
        (fun n => Classical.propDecidable (hasDiversityAtMost gen A h n)) hex ≤ r :=
    Nat.find_le (h := hex) hr
  exact hle

/-! ## N7: Diversity lower bound -/

theorem diversity_lower_bound {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea) (r : Nat)
    (hdiv : diversity gen A h > r) :
    ¬ hasDiversityAtMost gen A h r := by
  intro hr
  have hle := diversity_le_of_derivation gen A h r hr
  exact not_le_of_gt hdiv hle

/-! ## N8: Depth–diversity decomposition -/

/-- Reachability within k steps using at most r generator types. -/
def reachWithin {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (k r : Nat) : Set Idea :=
  {h | ∃ d, h ∈ deriveWith gen d A ∧ d.length ≤ k ∧ d.toFinset.card ≤ r}

/-- Type separation: a derivation exists that attains both minima. -/
def typeSeparated {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) : Prop :=
  ∀ h, reachable gen A h →
    ∃ d, h ∈ deriveWith gen d A ∧
      d.length = derivationDepth gen A h ∧
      d.toFinset.card = diversity gen A h

lemma reachWithin_subset {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (k r : Nat) :
    reachWithin gen A k r ⊆
      {h | reachable gen A h ∧ derivationDepth gen A h ≤ k ∧ diversity gen A h ≤ r} := by
  intro h hh
  obtain ⟨d, hmem, hlen, hcard⟩ := hh
  refine ⟨⟨d, hmem⟩, ?_, ?_⟩
  · exact derivationDepth_le_of_derivation gen A h k ⟨d, hmem, hlen⟩
  · exact diversity_le_of_derivation gen A h r ⟨d, hmem, hcard⟩

/-- **Theorem N8**: depth–diversity decomposition under type separation. -/
theorem depth_diversity_decomposition {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (k r : Nat)
    (hsep : typeSeparated gen A) :
    reachWithin gen A k r =
      {h | reachable gen A h ∧ derivationDepth gen A h ≤ k ∧ diversity gen A h ≤ r} := by
  apply Set.eq_of_subset_of_subset
  · exact reachWithin_subset gen A k r
  · intro h hh
    rcases hh with ⟨hreach, hdepth, hdiv⟩
    obtain ⟨d, hmem, hlen_eq, hcard_eq⟩ := hsep h hreach
    refine ⟨d, hmem, ?_, ?_⟩
    · simpa [hlen_eq] using hdepth
    · simpa [hcard_eq] using hdiv

/-! ## N9: Depth–diversity tradeoff -/

theorem depth_diversity_tradeoff {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea) (k r : Nat)
    (hdepth : derivationDepth gen A h = k + 1) :
    h ∉ reachWithin gen A k r := by
  intro hreach
  have hdepth_le : derivationDepth gen A h ≤ k :=
    (reachWithin_subset gen A k r hreach).2.1
  rw [hdepth] at hdepth_le
  exact Nat.not_succ_le_self k hdepth_le

/-! ## Weakened Versions Without typeSeparated Assumption

The `typeSeparated` assumption is very strong - it requires that for every reachable idea,
there exists a SINGLE derivation that simultaneously achieves BOTH minimal depth and minimal diversity.
This is often false in practice (shortest path ≠ most diverse path).

Below we provide alternative formulations that are strictly weaker and more broadly applicable:
-/

/-! ### Alternative N8: One-directional subset relation (NO typeSeparated needed) -/

/-- Weaker version of depth-diversity decomposition: only proves subset relation,
    not equality. This version requires NO typeSeparated assumption. -/
theorem depth_diversity_decomposition_weak {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (k r : Nat) :
    reachWithin gen A k r ⊆
      {h | reachable gen A h ∧ derivationDepth gen A h ≤ k ∧ diversity gen A h ≤ r} := by
  exact reachWithin_subset gen A k r

/-! ### Alternative N8: Constructive version with explicit derivations -/

/-- For any idea in reachWithin, we can construct a witness derivation.
    NO typeSeparated assumption needed. -/
theorem reachWithin_has_witness {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (k r : Nat) (h : Idea)
    (hreach : h ∈ reachWithin gen A k r) :
    ∃ d, h ∈ deriveWith gen d A ∧ d.length ≤ k ∧ d.toFinset.card ≤ r := by
  exact hreach

/-- If an idea is reachable with depth ≤ k and diversity ≤ r, and typeSeparated holds,
    then it's in reachWithin. This isolates where typeSeparated is actually needed. -/
theorem typeSeparated_implies_reachWithin {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (k r : Nat)
    (hsep : typeSeparated gen A) (h : Idea)
    (hreach : reachable gen A h)
    (hdepth : derivationDepth gen A h ≤ k)
    (hdiv : diversity gen A h ≤ r) :
    h ∈ reachWithin gen A k r := by
  obtain ⟨d, hmem, hlen_eq, hcard_eq⟩ := hsep h hreach
  refine ⟨d, hmem, ?_, ?_⟩
  · simpa [hlen_eq] using hdepth
  · simpa [hcard_eq] using hdiv

/-! ### Characterization: When is typeSeparated actually satisfied? -/

/-- We can always find a derivation achieving minimal depth. -/
lemma exists_minimal_depth_derivation {Idea ι : Type*}
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea)
    (hreach : reachable gen A h) :
    ∃ d, h ∈ deriveWith gen d A ∧
      (∀ d', h ∈ deriveWith gen d' A → d.length ≤ d'.length) := by
  obtain ⟨d₀, hmem₀⟩ := hreach
  have hex : ∃ k, hasDepthAtMost gen A h k := by
    use d₀.length
    exact ⟨d₀, hmem₀, Nat.le_refl _⟩
  have hmin := Nat.find_spec hex
  obtain ⟨d_min, hmem_min, hlen_min⟩ := hmin
  use d_min
  constructor
  · exact hmem_min
  · intro d' hmem'
    have hwitness : hasDepthAtMost gen A h d'.length := ⟨d', hmem', Nat.le_refl _⟩
    have : Nat.find hex ≤ d'.length := Nat.find_le hwitness
    calc d_min.length ≤ Nat.find hex := hlen_min
         _ ≤ d'.length := this

/-- We can always find a derivation achieving minimal diversity. -/
lemma exists_minimal_diversity_derivation {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea)
    (hreach : reachable gen A h) :
    ∃ d, h ∈ deriveWith gen d A ∧
      (∀ d', h ∈ deriveWith gen d' A → d.toFinset.card ≤ d'.toFinset.card) := by
  obtain ⟨d₀, hmem₀⟩ := hreach
  have hex : ∃ r, hasDiversityAtMost gen A h r := by
    use d₀.toFinset.card
    exact ⟨d₀, hmem₀, Nat.le_refl _⟩
  have hmin := Nat.find_spec hex
  obtain ⟨d_min, hmem_min, hcard_min⟩ := hmin
  use d_min
  constructor
  · exact hmem_min
  · intro d' hmem'
    have hwitness : hasDiversityAtMost gen A h d'.toFinset.card :=
      ⟨d', hmem', Nat.le_refl _⟩
    have : Nat.find hex ≤ d'.toFinset.card := Nat.find_le hwitness
    calc d_min.toFinset.card ≤ Nat.find hex := hcard_min
         _ ≤ d'.toFinset.card := this

/-! ### Key Insight: Most theorems don't need typeSeparated

**Key Insight**: typeSeparated requires that minimal depth and minimal diversity
can be achieved by a SINGLE derivation. In general, the shortest path to an idea
may use many different generator types (high diversity), while the path with fewest
types (low diversity) may need to take many steps (high depth). The assumption that
these can be simultaneously optimized is VERY STRONG.

Most of our key results do NOT require this assumption:
-/

/-- The strict access expansion (N6) requires NO separation assumption. -/
example : ∃ h : GadgetIdea,
    h ∈ closureAlternating {GadgetIdea.Base} generatorA generatorB ∧
    h ∉ closureSingle {GadgetIdea.Base} generatorA ∧
    h ∉ closureSingle {GadgetIdea.Base} generatorB :=
  strict_access_expansion_exists

/-- The diversity lower bound (N7) requires NO separation assumption. -/
example {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea) (r : Nat)
    (hdiv : diversity gen A h > r) :
    ¬ hasDiversityAtMost gen A h r :=
  diversity_lower_bound gen A h r hdiv

/-- The depth-diversity tradeoff (N9) requires NO separation assumption. -/
example {Idea ι : Type*} [DecidableEq ι]
    (gen : ι -> Set Idea -> Set Idea) (A : Set Idea) (h : Idea) (k r : Nat)
    (hdepth : derivationDepth gen A h = k + 1) :
    h ∉ reachWithin gen A k r :=
  depth_diversity_tradeoff gen A h k r hdepth

/-! ### Summary of Assumption Dependencies

**Theorems that need NO strong assumptions:**
- N6 (strict_access_expansion_exists): Only uses concrete gadget construction
- N7 (diversity_lower_bound): Only uses definition of diversity
- N9 (depth_diversity_tradeoff): Only uses definition of depth
- depth_diversity_decomposition_weak: Only proves ⊆ direction
- All witness-based constructive versions

**Theorems that need typeSeparated:**
- N8 (depth_diversity_decomposition): Needs typeSeparated for equality (⊇ direction)
- Can be replaced with depth_diversity_decomposition_weak + explicit separation hypothesis

**Recommendation:**
For maximum generality, use the weak versions that don't assume typeSeparated.
Only invoke typeSeparated when you have explicit evidence that shortest = most diverse.
-/

end Learning_DiversityBarrier
