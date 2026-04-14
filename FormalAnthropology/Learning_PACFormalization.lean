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
# Learning Theory: PAC Formalization with Explicit Types

This file addresses Reviewer Concern 1: the types for PAC learning must be explicit.
We provide a complete formalization connecting:
- Instance space X (where examples live)
- Label space Y (classification targets)
- Idea space I (from ideogenetic systems)
- Representation function: ideas → classifiers

## Key Results:
- Definition: PACGenerativeLearning with explicit typing
- Theorem: Accessible classifiers form a subset of the concept class
- Theorem: Generative VC dimension is well-defined on classifiers

This file makes the connection to classical PAC learning fully explicit.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.Learning_Basic
import FormalAnthropology.SingleAgent_Basic

namespace LearningTheory

open SingleAgentIdeogenesis Set

/-! ## Section 1: Classical PAC Learning Framework

We first establish the classical PAC setting with explicit types.
-/

/-- A classifier is a function from instances to labels -/
abbrev Classifier (X Y : Type*) := X → Y

/-- A concept class is a set of classifiers -/
abbrev ConceptClass (X Y : Type*) := Set (X → Y)

/-- A labeled example is an instance-label pair -/
structure LabeledExample (X Y : Type*) where
  point : X
  label : Y

/-- A sample is a finite set of labeled examples -/
abbrev Sample (X Y : Type*) := Finset (LabeledExample X Y)

/-- The error of a classifier h on target c under a distribution.
    For now we work with finite instance spaces and uniform distribution. -/
noncomputable def classifierError {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X]
    (h c : X → Y) : ℚ :=
  if Fintype.card X = 0 then 0
  else (Finset.filter (fun x => h x ≠ c x) Finset.univ).card / Fintype.card X

/-! ## Section 2: Shattering and VC Dimension for Classifiers

We provide both general (multi-class) and binary shattering definitions.
-/

/-- General shattering: A set S is shattered by C if C induces all possible
    labelings on S. This works for any label type Y.
    For finite S and finite Y, this means |{h|_S : h ∈ C}| = |Y|^|S|. -/
def shatters {X Y : Type*} (C : ConceptClass X Y) (S : Finset X) : Prop :=
  ∀ labeling : X → Y,
    ∃ h ∈ C, ∀ x ∈ S, h x = labeling x

/-- A set of instances S is shattered by a concept class C if for every
    subset T ⊆ S, there exists a classifier h ∈ C that "picks out" T.
    For binary classification with labels {0, 1}, this means:
    h(x) = 1 iff x ∈ T. -/
def shattersBinary {X : Type*} (C : ConceptClass X Bool) (S : Finset X) : Prop :=
  ∀ T : Finset X, T ⊆ S →
    ∃ h ∈ C, ∀ x ∈ S, h x = true ↔ x ∈ T

/-- General VC dimension: the sup of sizes of shattered sets.
    This works for any label type Y, not just binary classification. -/
noncomputable def vcDimension {X Y : Type*} (C : ConceptClass X Y) : ℕ :=
  sSup { n : ℕ | ∃ S : Finset X, S.card = n ∧ shatters C S }

/-- The VC dimension of a binary concept class is the sup of sizes of shattered sets -/
noncomputable def vcDimensionBinary {X : Type*} (C : ConceptClass X Bool) : ℕ :=
  sSup { n : ℕ | ∃ S : Finset X, S.card = n ∧ shattersBinary C S }

/-- General version: VC dimension is at least d -/
def vcDimensionAtLeast {X Y : Type*} (C : ConceptClass X Y) (d : ℕ) : Prop :=
  ∃ S : Finset X, S.card = d ∧ shatters C S

/-- VC dimension is at least d if there exists a shattered set of size d -/
def vcDimensionAtLeastBinary {X : Type*} (C : ConceptClass X Bool) (d : ℕ) : Prop :=
  ∃ S : Finset X, S.card = d ∧ shattersBinary C S

/-- Binary shattering implies general shattering for Bool labels -/
theorem shattersBinary_implies_shatters {X : Type*} (C : ConceptClass X Bool) (S : Finset X) :
    shattersBinary C S → shatters C S := by
  intro hbin labeling
  -- For binary case, we pick T = {x ∈ S | labeling x = true}
  let T := S.filter (fun x => labeling x = true)
  have hT : T ⊆ S := Finset.filter_subset _ S
  obtain ⟨h, hh, heq⟩ := hbin T hT
  use h, hh
  intro x hx
  specialize heq x hx
  by_cases hlabel : labeling x = true
  · -- Case: labeling x = true, so x ∈ T
    have hxT : x ∈ T := by
      simp only [T, Finset.mem_filter]
      exact ⟨hx, hlabel⟩
    rw [heq.mpr hxT, hlabel]
  · -- Case: labeling x = false
    push_neg at hlabel
    have hxnT : x ∉ T := by
      simp only [T, Finset.mem_filter, not_and]
      intro _
      exact hlabel
    have hnot_true : h x ≠ true := by
      intro contra
      have := heq.mp contra
      exact hxnT this
    have hlabel' : labeling x = false := by
      cases hxl : labeling x with
      | true => cases (hlabel hxl)
      | false => rfl
    have hfalse : h x = false := by
      cases hx : h x with
      | true => exact absurd hx hnot_true
      | false => rfl
    -- Both h x and labeling x are false
    simpa [hlabel', hfalse]

/-- Connection theorem: if a concept class shatters in binary sense, 
    it shatters in general sense -/
theorem vcDimensionBinary_le_vcDimension {X : Type*} (C : ConceptClass X Bool) (d : ℕ) :
    vcDimensionAtLeastBinary C d → vcDimensionAtLeast C d := by
  intro ⟨S, hcard, hshatter⟩
  exact ⟨S, hcard, shattersBinary_implies_shatters C S hshatter⟩

/-! ## Section 3: Generative PAC Learning - The Core Definition

This is the key definition addressing Concern 1.
A GenerativePACInstance connects:
- The ideogenetic system (ideas + generation)
- The instance space (where examples live)
- The representation function (how ideas become classifiers)

We provide both a general version (arbitrary label types) and 
a specialized binary version.
-/

/-- A Generative PAC Learning Instance - GENERAL VERSION.

    This makes explicit:
    - X: instance space (domain of classifiers)
    - Y: label space (codomain of classifiers)
    - I: idea space (what gets generated)
    - represent: how ideas become classifiers
    - The concept class: classifiers representable by some idea
    - The accessible concept class: classifiers representable by reachable ideas -/
structure GenerativePACInstance (X Y : Type*) where
  /-- The ideogenetic system providing the generative structure -/
  system : IdeogeneticSystem
  /-- Representation function: each idea encodes a classifier -/
  represent : system.Idea → (X → Y)

/-- A Generative PAC Learning Instance - BINARY CLASSIFICATION VERSION.
    
    Specialized to binary classification for compatibility with existing theorems. -/
abbrev BinaryGenerativePACInstance (X : Type*) := GenerativePACInstance X Bool

variable {X Y : Type*}

/-- The full concept class: all classifiers representable by any idea (GENERAL) -/
def GenerativePACInstance.conceptClass (G : GenerativePACInstance X Y) : ConceptClass X Y :=
  { c | ∃ a : G.system.Idea, G.represent a = c }

/-- The accessible concept class: classifiers representable by reachable ideas (GENERAL).
    This is H_acc in the paper - what we can actually learn. -/
def GenerativePACInstance.accessibleConceptClass (G : GenerativePACInstance X Y) : ConceptClass X Y :=
  { c | ∃ a ∈ primordialClosure G.system, G.represent a = c }

/-- An idea is accessible if it's in the primordial closure -/
def GenerativePACInstance.isAccessibleIdea (G : GenerativePACInstance X Y) (a : G.system.Idea) : Prop :=
  a ∈ primordialClosure G.system

/-- A classifier is accessible if it's representable by an accessible idea (GENERAL) -/
def GenerativePACInstance.isAccessibleClassifier (G : GenerativePACInstance X Y) (c : X → Y) : Prop :=
  c ∈ G.accessibleConceptClass

/-! ## Section 4: Key Structural Theorems

Theorems about the relationship between accessible and full concept classes.
These work for ANY label type Y.
-/

/-- Accessible concept class is a subset of the full concept class (GENERAL) -/
theorem accessible_subset_concept (G : GenerativePACInstance X Y) :
    G.accessibleConceptClass ⊆ G.conceptClass := by
  intro c hc
  simp only [GenerativePACInstance.accessibleConceptClass, mem_setOf_eq] at hc
  obtain ⟨a, _, ha_rep⟩ := hc
  simp only [GenerativePACInstance.conceptClass, mem_setOf_eq]
  exact ⟨a, ha_rep⟩

/-- represent maps onto the accessible concept class (GENERAL) -/
theorem represent_surjective_onto_accessible (G : GenerativePACInstance X Y) :
    ∀ c ∈ G.accessibleConceptClass,
      ∃ a : G.system.Idea, a ∈ primordialClosure G.system ∧ G.represent a = c := by
  intro c hc
  simp only [GenerativePACInstance.accessibleConceptClass, mem_setOf_eq] at hc
  exact hc

/-! ## Section 5: Generative VC Dimension for Classifiers

Now we define the generative VC dimension in terms of classifier shattering.
We provide both general (multi-class) and binary versions.
-/

/-- The generative VC dimension (GENERAL): VC dimension of the accessible concept class.
    Works for arbitrary label types. -/
noncomputable def generativeVCDim (G : GenerativePACInstance X Y) : ℕ :=
  vcDimension G.accessibleConceptClass

/-- The classical VC dimension (GENERAL) of the full concept class -/
noncomputable def classicalVCDim (G : GenerativePACInstance X Y) : ℕ :=
  vcDimension G.conceptClass

/-- The generative VC dimension (BINARY): specialized to binary classification -/
noncomputable def generativeVCDimBinary (G : BinaryGenerativePACInstance X) : ℕ :=
  vcDimensionBinary G.accessibleConceptClass

/-- The classical VC dimension (BINARY) of the full concept class -/
noncomputable def classicalVCDimBinary (G : BinaryGenerativePACInstance X) : ℕ :=
  vcDimensionBinary G.conceptClass

/-- If a set is shattered by the accessible class, it's shattered by the full class (BINARY).
    This is the witness version of GVC ≤ VC. -/
theorem shattered_accessible_implies_shattered_concept (G : BinaryGenerativePACInstance X)
    (S : Finset X) (hshatter : shattersBinary G.accessibleConceptClass S) :
    shattersBinary G.conceptClass S := by
  intro T hT
  obtain ⟨h, hh, heq⟩ := hshatter T hT
  exact ⟨h, accessible_subset_concept G hh, heq⟩

/-- VC dimension at least d for accessible implies at least d for concept (BINARY) -/
theorem vcAtLeast_accessible_implies_concept (G : BinaryGenerativePACInstance X) (d : ℕ) :
    vcDimensionAtLeastBinary G.accessibleConceptClass d →
    vcDimensionAtLeastBinary G.conceptClass d := by
  intro ⟨S, hcard, hshatter⟩
  exact ⟨S, hcard, shattered_accessible_implies_shattered_concept G S hshatter⟩

/-! ## Section 6: Depth-Stratified Accessible Classes

Ideas at different depths give different accessible classes.
These definitions work for ANY label type Y.
-/

/-- Ideas accessible at depth at most k -/
def ideasAtDepthAtMostPAC (G : GenerativePACInstance X Y) (k : ℕ) : Set G.system.Idea :=
  { a | a ∈ primordialClosure G.system ∧ primordialDepth G.system a ≤ k }

/-- Classifiers accessible at depth at most k (GENERAL) -/
def accessibleAtDepthK (G : GenerativePACInstance X Y) (k : ℕ) : ConceptClass X Y :=
  { c | ∃ a ∈ ideasAtDepthAtMostPAC G k, G.represent a = c }

/-- Depth-k accessible classes are monotone in k (GENERAL) -/
theorem accessibleAtDepthK_mono (G : GenerativePACInstance X Y) (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    accessibleAtDepthK G k₁ ⊆ accessibleAtDepthK G k₂ := by
  intro c hc
  simp only [accessibleAtDepthK, ideasAtDepthAtMostPAC, mem_setOf_eq] at hc ⊢
  obtain ⟨a, ⟨ha_cl, ha_depth⟩, ha_rep⟩ := hc
  exact ⟨a, ⟨ha_cl, Nat.le_trans ha_depth h⟩, ha_rep⟩

/-- The depth-k generative VC dimension (GENERAL) -/
noncomputable def depthKGenerativeVCDim (G : GenerativePACInstance X Y) (k : ℕ) : ℕ :=
  vcDimension (accessibleAtDepthK G k)

/-- The depth-k generative VC dimension (BINARY) -/
noncomputable def depthKGenerativeVCDimBinary (G : BinaryGenerativePACInstance X) (k : ℕ) : ℕ :=
  vcDimensionBinary (accessibleAtDepthK G k)

/-- The primordial is at depth 0 -/
theorem primordial_depth_zero (G : GenerativePACInstance X Y) :
    primordialDepth G.system G.system.primordial = 0 := by
  unfold primordialDepth
  have h0 : G.system.primordial ∈ genCumulative G.system 0 {G.system.primordial} := by
    simp only [genCumulative, mem_singleton_iff]
  have hle := depth_le_of_mem G.system {G.system.primordial} G.system.primordial 0 h0
  omega

/-- The primordial is always accessible at depth 0 -/
theorem primordial_accessible_at_depth_zero (G : GenerativePACInstance X Y) :
    G.system.primordial ∈ ideasAtDepthAtMostPAC G 0 := by
  simp only [ideasAtDepthAtMostPAC, mem_setOf_eq]
  constructor
  · exact primordial_in_closure G.system
  · rw [primordial_depth_zero G]

/-- If a set is shattered at depth k₁, it's shattered at depth k₂ ≥ k₁ (BINARY) -/
theorem shattered_depthK_mono (G : BinaryGenerativePACInstance X) (k₁ k₂ : ℕ) (h : k₁ ≤ k₂)
    (S : Finset X) (hshatter : shattersBinary (accessibleAtDepthK G k₁) S) :
    shattersBinary (accessibleAtDepthK G k₂) S := by
  intro T hT
  obtain ⟨c, hc, heq⟩ := hshatter T hT
  exact ⟨c, accessibleAtDepthK_mono G k₁ k₂ h hc, heq⟩

/-- VC dimension at least d is monotone in depth (BINARY) -/
theorem vcAtLeast_depthK_mono (G : BinaryGenerativePACInstance X) (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) (d : ℕ) :
    vcDimensionAtLeastBinary (accessibleAtDepthK G k₁) d →
    vcDimensionAtLeastBinary (accessibleAtDepthK G k₂) d := by
  intro ⟨S, hcard, hshatter⟩
  exact ⟨S, hcard, shattered_depthK_mono G k₁ k₂ h S hshatter⟩

/-! ## Section 7: The Union of Depth Classes Equals the Accessible Class

These results hold for ANY label type Y.
-/

/-- The accessible concept class is the union of all depth-k classes (GENERAL) -/
theorem accessibleConceptClass_eq_iUnion (G : GenerativePACInstance X Y) :
    G.accessibleConceptClass = ⋃ k, accessibleAtDepthK G k := by
  apply Set.eq_of_subset_of_subset
  · -- accessibleConceptClass ⊆ ⋃ k, accessibleAtDepthK G k
    intro c hc
    simp only [GenerativePACInstance.accessibleConceptClass, mem_setOf_eq] at hc
    obtain ⟨a, ha, ha_rep⟩ := hc
    simp only [mem_iUnion, accessibleAtDepthK, ideasAtDepthAtMostPAC, mem_setOf_eq]
    refine ⟨primordialDepth G.system a, a, ⟨ha, le_refl _⟩, ha_rep⟩
  · -- ⋃ k, accessibleAtDepthK G k ⊆ accessibleConceptClass
    intro c hc
    simp only [mem_iUnion, accessibleAtDepthK, ideasAtDepthAtMostPAC, mem_setOf_eq] at hc
    obtain ⟨k, a, ⟨ha_cl, _⟩, ha_rep⟩ := hc
    simp only [GenerativePACInstance.accessibleConceptClass, mem_setOf_eq]
    exact ⟨a, ha_cl, ha_rep⟩

/-- Depth-k accessible is contained in the full accessible class (GENERAL) -/
theorem depthK_subset_accessible (G : GenerativePACInstance X Y) (k : ℕ) :
    accessibleAtDepthK G k ⊆ G.accessibleConceptClass := by
  intro c hc
  simp only [accessibleAtDepthK, ideasAtDepthAtMostPAC, mem_setOf_eq] at hc
  obtain ⟨a, ⟨ha_cl, _⟩, ha_rep⟩ := hc
  simp only [GenerativePACInstance.accessibleConceptClass, mem_setOf_eq]
  exact ⟨a, ha_cl, ha_rep⟩

/-- If a set is shattered at depth k, it's shattered by the accessible class (BINARY) -/
theorem shattered_depthK_implies_accessible (G : BinaryGenerativePACInstance X) (k : ℕ)
    (S : Finset X) (hshatter : shattersBinary (accessibleAtDepthK G k) S) :
    shattersBinary G.accessibleConceptClass S := by
  intro T hT
  obtain ⟨c, hc, heq⟩ := hshatter T hT
  exact ⟨c, depthK_subset_accessible G k hc, heq⟩

/-! ## Section 8: Connecting to Ideas-as-Hypotheses View

The paper's original formulation treats ideas as hypotheses (sets).
We show this is a special case of our representation framework.
These constructions work for arbitrary label types.
-/

/-- Construct a BinaryGenerativePACInstance from an ideogenetic system and
    a function mapping ideas to sets of instances.
    WEAKENED: Uses classical decidability when membership is not decidable. -/
noncomputable def fromIdeaToSet {X : Type*}
    (S : IdeogeneticSystem) (ideaToSet : S.Idea → Set X) : BinaryGenerativePACInstance X where
  system := S
  represent := fun a x => @decide (x ∈ ideaToSet a) (Classical.propDecidable _)

/-- Constructive version when membership is decidable -/
def fromIdeaToSetDecidable {X : Type*}
    (S : IdeogeneticSystem) (ideaToSet : S.Idea → Set X)
    [∀ a, DecidablePred (· ∈ ideaToSet a)] : BinaryGenerativePACInstance X where
  system := S
  represent := fun a x => decide (x ∈ ideaToSet a)

/-- General version: construct a GenerativePACInstance from ideas to any property.
    Maps ideas to predicates (X → Prop), which become classifiers via a conversion function. -/
noncomputable def fromIdeaToProp {X Y : Type*} [Inhabited Y]
    (S : IdeogeneticSystem) (ideaToProp : S.Idea → (X → Prop)) 
    (toLabel : Prop → Y) : GenerativePACInstance X Y where
  system := S
  represent := fun a x => toLabel (ideaToProp a x)

/-! ## Section 9: Examples

Concrete examples showing the framework in action.
-/

/-- A simple propositional ideogenetic system over n variables.
    Ideas are CNF formulas: lists of clauses, each clause is a list of literals. -/
def propositionalSystem (n : ℕ) : IdeogeneticSystem where
  Idea := List (List (Bool × Fin n))  -- CNF: list of clauses, each clause is list of literals
  generate := fun φ =>
    -- Generate new formulas by adding a single-literal clause
    { φ ++ [[⟨true, i⟩]] | i : Fin n } ∪ { φ ++ [[⟨false, i⟩]] | i : Fin n }
  primordial := []  -- Empty formula (always true)

/-- Evaluation of a CNF formula on an assignment -/
def evalCNF (n : ℕ) (φ : List (List (Bool × Fin n))) (assignment : Fin n → Bool) : Bool :=
  φ.all fun clause =>
    clause.any fun (polarity, var) =>
      assignment var == polarity

/-- The propositional generative PAC instance (BINARY) -/
def propositionalPAC (n : ℕ) : BinaryGenerativePACInstance (Fin n → Bool) where
  system := propositionalSystem n
  represent := evalCNF n

/-- The empty formula (primordial) evaluates to true on all assignments -/
theorem evalCNF_empty (n : ℕ) (assignment : Fin n → Bool) :
    evalCNF n [] assignment = true := by
  simp only [evalCNF, List.all_nil]

/-- The empty formula represents the "always true" classifier -/
theorem propositionalPAC_primordial_always_true (n : ℕ) :
    (propositionalPAC n).represent (propositionalPAC n).system.primordial = fun _ => true := by
  funext assignment
  simp only [propositionalPAC, propositionalSystem, evalCNF_empty]

/-! ## Section 10: Connection to IdeogeneticLearner

Show how GenerativePACInstance relates to the existing IdeogeneticLearner.
This works for any label type Y.
-/

/-- Convert a GenerativePACInstance to an IdeogeneticLearner (GENERAL).
    Each classifier c becomes a hypothesis: the set of ideas representing c. -/
noncomputable def toIdeogeneticLearner (G : GenerativePACInstance X Y) : IdeogeneticLearner where
  system := G.system
  hypotheses := { H : Set G.system.Idea | ∃ c : X → Y, H = { a | G.represent a = c } }
  prior := ⟨fun _ => 0⟩  -- Simplified: no constraints needed
  lossFunc := ⟨fun _ _ => 0⟩  -- Simplified: no constraints needed

/-- For nonempty H in accessible hypotheses, there's a corresponding accessible classifier (GENERAL) -/
theorem accessible_correspondence_nonempty (G : GenerativePACInstance X Y) :
    ∀ H ∈ (toIdeogeneticLearner G).accessibleHypotheses, H.Nonempty →
      ∃ c ∈ G.accessibleConceptClass, H = { a | G.represent a = c } := by
  intro H hH hne
  simp only [IdeogeneticLearner.accessibleHypotheses, mem_sep_iff, toIdeogeneticLearner] at hH
  obtain ⟨⟨c, hH_eq⟩, hH_sub⟩ := hH
  use c
  constructor
  · simp only [GenerativePACInstance.accessibleConceptClass, mem_setOf_eq]
    obtain ⟨a, ha⟩ := hne
    use a
    constructor
    · exact hH_sub ha
    · rw [hH_eq] at ha
      exact ha
  · exact hH_eq

end LearningTheory
