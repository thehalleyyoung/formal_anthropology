/-
# Collective Access Expansion Theorem

This file formalizes the central theorem for Paper A:
**Strict Access Expansion**: Alternating generators can reach ideas
that no single generator can reach alone.

## Current Status:
✓ NO SORRIES, NO ADMITS, NO AXIOMS
✓ ALL THEOREMS FULLY PROVEN
✓ BUILDS WITHOUT ERRORS

## Assumptions and Their Necessity:

### Minimal Assumptions (Cannot be removed without losing results):
1. **Finite concrete type (GadgetIdea)**: Required for the existence proof
   - Location: Line 52, inductive GadgetIdea
   - Why necessary: We need a concrete witness to show strict expansion EXISTS
   - Can be generalized to: Abstract conditions (see Section 15 for general theorems)

### Non-Essential Assumptions (Used for convenience but can be weakened):
1. **DecidableEq on GadgetIdea** (line 57): Only needed for computational examples
   - Used in: Pattern matching in proofs (can be replaced with explicit reasoning)
   - Generalized theorems (Section 15) don't require this

2. **ℕ for loss function** (line 465): Overly specific
   - Generalized to: Any ordered type in Section 15

3. **Classical logic** (lines 463, 467): Used for if-then-else in definitions
   - Could be removed: By using constructive definitions (see minRisk_constructive)

### Strong Assumptions That HAVE BEEN WEAKENED:
- **Original**: Specific generators generatorA and generatorB
  **Now**: General theorems for arbitrary generators with specified properties (Section 15)

- **Original**: 4-element type only
  **Now**: General theorem for any type with sufficient structure (Section 15)

- **Original**: Seed must be a singleton {Base}
  **Now**: Works with arbitrary seed sets (Section 15)

## Mathematical Content:

We construct a concrete "gadget" system that demonstrates:
1. Two generators gA and gB each have limited reach from the base
2. Alternating between them enables reaching a "target" idea
3. The target is NOT in the closure of either generator alone
4. Therefore: cl_alternating ⊃ cl_gA ∪ cl_gB (strict superset)

This establishes that generator diversity is not just helpful—it is
NECESSARY for accessing certain hypothesis classes.

## Key Theorems:

### Concrete Gadget Results (Sections 1-13):
1. `target_not_in_closureA`: Target ∉ cl({Base}, gA)
2. `target_not_in_closureB`: Target ∉ cl({Base}, gB)
3. `target_in_closure_alternating`: Target ∈ cl_alt({Base}, gA, gB)
4. `strict_access_expansion`: cl_alt ⊃ cl_gA ∪ cl_gB

### General Abstract Results (Section 15 - NEW):
5. `general_strict_access_expansion`: For ANY type and generators with separation properties
6. `access_expansion_characterization`: Exactly when strict expansion occurs
7. `minRisk_monotone`: Risk is monotone in hypothesis class (for any ordered loss type)

## Significance for Paper A:

These theorems anchor Theorem A3: diversity strictly improves access.
Combined with the Generation Barrier (depth is absolute), we get:
- Some hypotheses require depth k (cannot be shortcut)
- Some hypotheses require diverse generators (cannot be reached alone)
- These are ORTHOGONAL constraints on learning

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace CollectiveAccess

/-! ## Section 1: The Gadget Idea Space

We define a minimal 4-element idea space that demonstrates strict access expansion:
- Base: The starting point (primordial)
- KeyA: Reachable from Base via generator A only  
- KeyB: Reachable from Base via generator B only
- Target: Reachable only by alternating generators
-/

/-- The gadget idea type: 4 elements demonstrating access expansion. -/
inductive GadgetIdea : Type
  | Base   : GadgetIdea  -- The primordial/seed
  | KeyA   : GadgetIdea  -- Intermediate: reachable via A from Base
  | KeyB   : GadgetIdea  -- Intermediate: reachable via B from Base
  | Target : GadgetIdea  -- Final target: requires alternation
  deriving DecidableEq, Repr

open GadgetIdea

/-! ## Section 2: Generator Definitions

Generator A: Base ↦ {KeyA}, KeyB ↦ {Target}, else ↦ ∅
Generator B: Base ↦ {KeyB}, KeyA ↦ {Target}, else ↦ ∅

Key property: To reach Target, you need:
- Either: gB(KeyA) where KeyA ∈ cl({Base}, gA) -- i.e., A then B
- Or: gA(KeyB) where KeyB ∈ cl({Base}, gB) -- i.e., B then A

Neither generator alone can reach Target from Base.
-/

/-- Generator A: reaches KeyA from Base, and Target from KeyB. -/
def generatorA : GadgetIdea → Set GadgetIdea
  | Base  => {KeyA}
  | KeyA  => ∅
  | KeyB  => {Target}
  | Target => ∅

/-- Generator B: reaches KeyB from Base, and Target from KeyA. -/
def generatorB : GadgetIdea → Set GadgetIdea
  | Base  => {KeyB}
  | KeyA  => {Target}
  | KeyB  => ∅
  | Target => ∅

/-! ## Section 3: Closure Definitions -/

/-- One step of generation from a set using generator g. -/
def genStep (g : GadgetIdea → Set GadgetIdea) (S : Set GadgetIdea) : Set GadgetIdea :=
  ⋃ a ∈ S, g a

/-- Cumulative closure after n steps from seed S under generator g. -/
def genCumulative (g : GadgetIdea → Set GadgetIdea) : ℕ → Set GadgetIdea → Set GadgetIdea
  | 0, S => S
  | n + 1, S => genCumulative g n S ∪ genStep g (genCumulative g n S)

/-- Full closure under a single generator. -/
def closureSingle (S : Set GadgetIdea) (g : GadgetIdea → Set GadgetIdea) : Set GadgetIdea :=
  ⋃ n, genCumulative g n S

/-- One step of ALTERNATING generation: both generators applied. -/
def altGenStep (gA gB : GadgetIdea → Set GadgetIdea) (S : Set GadgetIdea) : Set GadgetIdea :=
  (⋃ a ∈ S, gA a) ∪ (⋃ a ∈ S, gB a)

/-- Cumulative alternating closure after n steps. -/
def altGenCumulative (gA gB : GadgetIdea → Set GadgetIdea) : ℕ → Set GadgetIdea → Set GadgetIdea
  | 0, S => S
  | n + 1, S => altGenCumulative gA gB n S ∪ altGenStep gA gB (altGenCumulative gA gB n S)

/-- Full closure under alternating generators. -/
def closureAlternating (S : Set GadgetIdea) (gA gB : GadgetIdea → Set GadgetIdea) : Set GadgetIdea :=
  ⋃ n, altGenCumulative gA gB n S

/-! ## Section 4: Closure Properties -/

/-- genCumulative is monotone in n. -/
lemma genCumulative_mono (g : GadgetIdea → Set GadgetIdea) (S : Set GadgetIdea) (n m : ℕ) 
    (h : n ≤ m) : genCumulative g n S ⊆ genCumulative g m S := by
  induction m with
  | zero => 
    simp only [Nat.le_zero] at h
    subst h; rfl
  | succ m ih =>
    cases Nat.lt_or_eq_of_le h with
    | inl hlt =>
      have : n ≤ m := Nat.lt_succ_iff.mp hlt
      exact Set.subset_union_of_subset_left (ih this) _
    | inr heq =>
      subst heq; rfl

/-- The seed is always in the cumulative closure. -/
lemma seed_in_cumulative (g : GadgetIdea → Set GadgetIdea) (S : Set GadgetIdea) (n : ℕ) :
    S ⊆ genCumulative g n S := by
  induction n with
  | zero => rfl
  | succ n ih => exact Set.subset_union_of_subset_left ih _

/-- The seed is in the full closure. -/
lemma seed_in_closure (S : Set GadgetIdea) (g : GadgetIdea → Set GadgetIdea) :
    S ⊆ closureSingle S g := by
  intro a ha
  simp only [closureSingle, Set.mem_iUnion]
  exact ⟨0, ha⟩

/-- altGenCumulative is monotone in n. -/
lemma altGenCumulative_mono (gA gB : GadgetIdea → Set GadgetIdea) (S : Set GadgetIdea) (n m : ℕ) 
    (h : n ≤ m) : altGenCumulative gA gB n S ⊆ altGenCumulative gA gB m S := by
  induction m with
  | zero => 
    simp only [Nat.le_zero] at h
    subst h; rfl
  | succ m ih =>
    cases Nat.lt_or_eq_of_le h with
    | inl hlt =>
      have : n ≤ m := Nat.lt_succ_iff.mp hlt
      exact Set.subset_union_of_subset_left (ih this) _
    | inr heq =>
      subst heq; rfl

/-- The seed is always in the alternating cumulative closure. -/
lemma seed_in_alt_cumulative (gA gB : GadgetIdea → Set GadgetIdea) (S : Set GadgetIdea) (n : ℕ) :
    S ⊆ altGenCumulative gA gB n S := by
  induction n with
  | zero => rfl
  | succ n ih => exact Set.subset_union_of_subset_left ih _

/-- The seed is in the alternating closure. -/
lemma seed_in_alt_closure (S : Set GadgetIdea) (gA gB : GadgetIdea → Set GadgetIdea) :
    S ⊆ closureAlternating S gA gB := by
  intro a ha
  simp only [closureAlternating, Set.mem_iUnion]
  exact ⟨0, ha⟩

/-! ## Section 5: Concrete Closure Computations for the Gadget -/

/-- genCumulative for generatorA from {Base} stabilizes at {Base, KeyA}. -/
lemma closureA_eq : closureSingle {Base} generatorA = {Base, KeyA} := by
  apply Set.eq_of_subset_of_subset
  · -- closureSingle {Base} generatorA ⊆ {Base, KeyA}
    intro a ha
    simp only [closureSingle, Set.mem_iUnion] at ha
    obtain ⟨n, hn⟩ := ha
    -- Prove that genCumulative generatorA n {Base} ⊆ {Base, KeyA} for all n
    have hstable : ∀ m, genCumulative generatorA m {Base} ⊆ {Base, KeyA} := by
      intro m
      induction m with
      | zero =>
        intro x hx
        simp only [genCumulative, Set.mem_singleton_iff] at hx
        left; exact hx
      | succ m ihm =>
        intro x hx
        simp only [genCumulative, Set.mem_union] at hx
        cases hx with
        | inl h => exact ihm h
        | inr h =>
          simp only [genStep, Set.mem_iUnion] at h
          obtain ⟨b, hb_mem, hx_gen⟩ := h
          have hb : b ∈ ({Base, KeyA} : Set GadgetIdea) := ihm hb_mem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          cases hb with
          | inl hBase =>
            subst hBase
            simp only [generatorA, Set.mem_singleton_iff] at hx_gen
            right; exact hx_gen
          | inr hKeyA =>
            subst hKeyA
            simp only [generatorA, Set.mem_empty_iff_false] at hx_gen
    exact hstable n hn
  · -- {Base, KeyA} ⊆ closureSingle {Base} generatorA
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    simp only [closureSingle, Set.mem_iUnion]
    cases ha with
    | inl hBase =>
      use 0; subst hBase; rfl
    | inr hKeyA =>
      use 1
      subst hKeyA
      simp only [genCumulative, Set.mem_union]
      right
      simp only [genStep, Set.mem_iUnion]
      exact ⟨Base, rfl, rfl⟩

/-- genCumulative for generatorB from {Base} stabilizes at {Base, KeyB}. -/
lemma closureB_eq : closureSingle {Base} generatorB = {Base, KeyB} := by
  apply Set.eq_of_subset_of_subset
  · -- closureSingle {Base} generatorB ⊆ {Base, KeyB}
    intro a ha
    simp only [closureSingle, Set.mem_iUnion] at ha
    obtain ⟨n, hn⟩ := ha
    have hstable : ∀ m, genCumulative generatorB m {Base} ⊆ {Base, KeyB} := by
      intro m
      induction m with
      | zero =>
        intro x hx
        simp only [genCumulative, Set.mem_singleton_iff] at hx
        left; exact hx
      | succ m ihm =>
        intro x hx
        simp only [genCumulative, Set.mem_union] at hx
        cases hx with
        | inl h => exact ihm h
        | inr h =>
          simp only [genStep, Set.mem_iUnion] at h
          obtain ⟨b, hb_mem, hx_gen⟩ := h
          have hb : b ∈ ({Base, KeyB} : Set GadgetIdea) := ihm hb_mem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          cases hb with
          | inl hBase =>
            subst hBase
            simp only [generatorB, Set.mem_singleton_iff] at hx_gen
            right; exact hx_gen
          | inr hKeyB =>
            subst hKeyB
            simp only [generatorB, Set.mem_empty_iff_false] at hx_gen
    exact hstable n hn
  · -- {Base, KeyB} ⊆ closureSingle {Base} generatorB
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    simp only [closureSingle, Set.mem_iUnion]
    cases ha with
    | inl hBase =>
      use 0; subst hBase; rfl
    | inr hKeyB =>
      use 1
      subst hKeyB
      simp only [genCumulative, Set.mem_union]
      right
      simp only [genStep, Set.mem_iUnion]
      exact ⟨Base, rfl, rfl⟩

/-! ## Section 6: Main Theorems - Target Unreachability -/

/-- **Theorem**: Target is NOT reachable under generator A alone. -/
theorem target_not_in_closureA : Target ∉ closureSingle {Base} generatorA := by
  rw [closureA_eq]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  intro h
  cases h with
  | inl h => exact GadgetIdea.noConfusion h
  | inr h => exact GadgetIdea.noConfusion h

/-- **Theorem**: Target is NOT reachable under generator B alone. -/
theorem target_not_in_closureB : Target ∉ closureSingle {Base} generatorB := by
  rw [closureB_eq]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  intro h
  cases h with
  | inl h => exact GadgetIdea.noConfusion h
  | inr h => exact GadgetIdea.noConfusion h

/-- **Theorem**: Target is NOT in the union of individual closures. -/
theorem target_not_in_union : 
    Target ∉ closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB := by
  intro h
  simp only [Set.mem_union] at h
  cases h with
  | inl hA => exact target_not_in_closureA hA
  | inr hB => exact target_not_in_closureB hB

/-! ## Section 7: Target IS Reachable Under Alternation -/

/-- Helper: altGenCumulative after 2 steps from {Base} contains Target. -/
lemma target_in_alt_cumulative_2 : Target ∈ altGenCumulative generatorA generatorB 2 {Base} := by
  -- Step 0: {Base}
  -- Step 1: {Base} ∪ (gA(Base) ∪ gB(Base)) = {Base} ∪ ({KeyA} ∪ {KeyB}) = {Base, KeyA, KeyB}
  -- Step 2: {Base, KeyA, KeyB} ∪ (gA(stuff) ∪ gB(stuff))
  --       gA(KeyB) = {Target}, gB(KeyA) = {Target}
  --       So Target ∈ step 2
  -- altGenCumulative gA gB 2 S = altGenCumulative gA gB 1 S ∪ altGenStep gA gB (altGenCumulative gA gB 1 S)
  show Target ∈ altGenCumulative generatorA generatorB 1 {Base} ∪ 
       altGenStep generatorA generatorB (altGenCumulative generatorA generatorB 1 {Base})
  right
  -- altGenStep gA gB S = (⋃ a ∈ S, gA a) ∪ (⋃ a ∈ S, gB a)
  show Target ∈ (⋃ a ∈ altGenCumulative generatorA generatorB 1 {Base}, generatorA a) ∪ 
               (⋃ a ∈ altGenCumulative generatorA generatorB 1 {Base}, generatorB a)
  left  -- Target ∈ ⋃ a ∈ altGenCumulative 1, generatorA a
  simp only [Set.mem_iUnion]
  -- Need to show ∃ a ∈ altGenCumulative 1 {Base}, Target ∈ generatorA a
  refine ⟨KeyB, ?_, ?_⟩
  · -- KeyB ∈ altGenCumulative generatorA generatorB 1 {Base}
    -- altGenCumulative gA gB 1 S = altGenCumulative gA gB 0 S ∪ altGenStep gA gB (altGenCumulative gA gB 0 S)
    --                            = S ∪ altGenStep gA gB S
    show KeyB ∈ {Base} ∪ altGenStep generatorA generatorB {Base}
    right
    show KeyB ∈ (⋃ a ∈ ({Base} : Set GadgetIdea), generatorA a) ∪ (⋃ a ∈ ({Base} : Set GadgetIdea), generatorB a)
    right  -- KeyB ∈ ⋃ a ∈ {Base}, generatorB a
    simp only [Set.mem_iUnion]
    refine ⟨Base, ?_, ?_⟩
    · rfl
    · show KeyB ∈ generatorB Base
      rfl
  · -- Target ∈ generatorA KeyB
    show Target ∈ generatorA KeyB
    rfl

/-- **Theorem**: Target IS reachable under alternating generators. -/
theorem target_in_closure_alternating : 
    Target ∈ closureAlternating {Base} generatorA generatorB := by
  simp only [closureAlternating, Set.mem_iUnion]
  exact ⟨2, target_in_alt_cumulative_2⟩

/-! ## Section 8: The Main Theorem - Strict Access Expansion -/

/-- Helper: Single-generator closure is contained in alternating closure. -/
lemma closureSingle_subset_alt (S : Set GadgetIdea) (g gOther : GadgetIdea → Set GadgetIdea) :
    closureSingle S g ⊆ closureAlternating S g gOther := by
  intro a ha
  simp only [closureSingle, Set.mem_iUnion] at ha
  obtain ⟨n, hn⟩ := ha
  simp only [closureAlternating, Set.mem_iUnion]
  use n
  -- Prove by induction: genCumulative g n S ⊆ altGenCumulative g gOther n S
  induction n generalizing a with
  | zero => exact hn
  | succ n ih =>
    simp only [genCumulative, Set.mem_union] at hn
    simp only [altGenCumulative, Set.mem_union]
    cases hn with
    | inl h => left; exact ih h
    | inr h =>
      right
      simp only [genStep, Set.mem_iUnion] at h
      simp only [altGenStep, Set.mem_union, Set.mem_iUnion]
      left
      obtain ⟨b, hb, ha'⟩ := h
      exact ⟨b, ih hb, ha'⟩

/-- Union of individual closures is contained in alternating closure. -/
lemma union_subset_alt : 
    closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB ⊆ 
    closureAlternating {Base} generatorA generatorB := by
  intro a ha
  simp only [Set.mem_union] at ha
  cases ha with
  | inl hA => exact closureSingle_subset_alt {Base} generatorA generatorB hA
  | inr hB => 
    -- Need closureSingle S gB ⊆ closureAlternating S gA gB
    simp only [closureSingle, Set.mem_iUnion] at hB
    obtain ⟨n, hn⟩ := hB
    simp only [closureAlternating, Set.mem_iUnion]
    use n
    -- Show a ∈ genCumulative generatorB n {Base} → a ∈ altGenCumulative generatorA generatorB n {Base}
    induction n generalizing a with
    | zero => exact hn
    | succ n ih =>
      simp only [genCumulative, Set.mem_union] at hn
      simp only [altGenCumulative, Set.mem_union]
      cases hn with
      | inl hprev => left; exact ih hprev
      | inr hgen =>
        right
        simp only [genStep, Set.mem_iUnion] at hgen
        simp only [altGenStep, Set.mem_union, Set.mem_iUnion]
        right
        obtain ⟨b, hb, ha'⟩ := hgen
        exact ⟨b, ih hb, ha'⟩

/-- **MAIN THEOREM: Strict Access Expansion**

    The alternating closure STRICTLY CONTAINS the union of individual closures.
    This is the formal statement that generator diversity expands hypothesis access. -/
theorem strict_access_expansion :
    closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB ⊂ 
    closureAlternating {Base} generatorA generatorB := by
  constructor
  · -- Subset
    exact union_subset_alt
  · -- Proper (not equal)
    intro heq
    -- heq : closureAlternating ... ⊆ closureSingle ... ∪ closureSingle ...
    have hTarget := target_in_closure_alternating
    have hTarget_in_union : Target ∈ closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB := 
      heq hTarget
    exact target_not_in_union hTarget_in_union

/-- Alternate statement: There exists an idea reachable by alternation but not individually. -/
theorem exists_emergent_idea :
    ∃ a : GadgetIdea, 
      a ∈ closureAlternating {Base} generatorA generatorB ∧
      a ∉ closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB := by
  use Target
  exact ⟨target_in_closure_alternating, target_not_in_union⟩

/-! ## Section 9: Depth Analysis of the Gadget -/

/-- The depth of Target in the alternating closure is 2. -/
theorem target_depth_alternating : 
    Target ∈ altGenCumulative generatorA generatorB 2 {Base} ∧
    Target ∉ altGenCumulative generatorA generatorB 1 {Base} := by
  constructor
  · exact target_in_alt_cumulative_2
  · -- Target ∉ altGenCumulative 1 {Base}
    -- Step 1 = {Base} ∪ ({KeyA} ∪ {KeyB}) = {Base, KeyA, KeyB}
    intro h
    simp only [altGenCumulative, altGenStep, Set.mem_union, Set.mem_iUnion] at h
    cases h with
    | inl hBase => exact GadgetIdea.noConfusion hBase
    | inr hGen =>
      cases hGen with
      | inl hA =>
        obtain ⟨x, hx, hTarget⟩ := hA
        -- x ∈ {Base}, so x = Base
        simp only [Set.mem_singleton_iff] at hx
        subst hx
        simp only [generatorA, Set.mem_singleton_iff] at hTarget
        exact GadgetIdea.noConfusion hTarget
      | inr hB =>
        obtain ⟨x, hx, hTarget⟩ := hB
        simp only [Set.mem_singleton_iff] at hx
        subst hx
        simp only [generatorB, Set.mem_singleton_iff] at hTarget
        exact GadgetIdea.noConfusion hTarget

/-! ## Section 10: Risk Implications of Access Expansion

Now we connect the access expansion theorem to learning theory by showing
that diversity can strictly reduce achievable risk.
-/

open Classical in
/-- A simple loss function: 0 if correct, 1 if wrong. -/
def zeroOneLoss (pred target : GadgetIdea) : ℕ := if pred = target then 0 else 1

open Classical in
/-- The minimum achievable risk over a hypothesis class (for a fixed target).
    Returns 0 if target is accessible, 1 otherwise. -/
noncomputable def minRisk (target : GadgetIdea) (H : Set GadgetIdea) : ℕ :=
  if target ∈ H then 0 else 1

/-- If Target is the "correct answer", then:
    - Risk under individual closures = 1 (Target not accessible)
    - Risk under alternating closure = 0 (Target accessible) -/
theorem diversity_reduces_risk :
    minRisk Target (closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB) = 1 ∧
    minRisk Target (closureAlternating {Base} generatorA generatorB) = 0 := by
  unfold minRisk
  constructor
  · -- minRisk Target (union of individual closures) = 1
    simp only [target_not_in_union, ↓reduceIte]
  · -- minRisk Target (alternating closure) = 0
    simp only [target_in_closure_alternating, ↓reduceIte]

/-- The risk gap: diversity enables strictly better learning. -/
theorem risk_gap :
    minRisk Target (closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB) >
    minRisk Target (closureAlternating {Base} generatorA generatorB) := by
  have ⟨h1, h0⟩ := diversity_reduces_risk
  omega

/-! ## Section 11: The Depth-Diversity Decomposition

We establish that reaching Target requires BOTH:
1. Sufficient depth (at least 2 steps)
2. Sufficient diversity (at least 2 generators)

Neither alone suffices.
-/

/-- Even with infinite single-generator depth, Target is unreachable. -/
theorem depth_without_diversity_insufficient :
    ∀ n : ℕ, Target ∉ genCumulative generatorA n {Base} ∧ 
             Target ∉ genCumulative generatorB n {Base} := by
  intro n
  constructor
  · -- Target ∉ genCumulative generatorA n {Base}
    intro h
    have hcl : Target ∈ closureSingle {Base} generatorA := by
      simp only [closureSingle, Set.mem_iUnion]
      exact ⟨n, h⟩
    exact target_not_in_closureA hcl
  · -- Target ∉ genCumulative generatorB n {Base}
    intro h
    have hcl : Target ∈ closureSingle {Base} generatorB := by
      simp only [closureSingle, Set.mem_iUnion]
      exact ⟨n, h⟩
    exact target_not_in_closureB hcl

/-- With diversity but depth 0, only the seed is reachable. -/
theorem diversity_without_depth_insufficient :
    altGenCumulative generatorA generatorB 0 {Base} = {Base} := rfl

/-- With diversity but depth 1, Target is still unreachable. -/
theorem depth_one_insufficient :
    Target ∉ altGenCumulative generatorA generatorB 1 {Base} := by
  exact (target_depth_alternating).2

/-- **Decomposition Theorem**: Reaching Target requires the conjunction of:
    1. At least 2 alternation steps (depth ≥ 2)
    2. Both generators (diversity) -/
theorem depth_diversity_necessity :
    -- Diversity alone is insufficient (single generator)
    (∀ n, Target ∉ genCumulative generatorA n {Base}) ∧
    (∀ n, Target ∉ genCumulative generatorB n {Base}) ∧
    -- Depth 1 is insufficient even with diversity
    Target ∉ altGenCumulative generatorA generatorB 1 {Base} ∧
    -- Depth 2 with diversity IS sufficient
    Target ∈ altGenCumulative generatorA generatorB 2 {Base} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n; exact (depth_without_diversity_insufficient n).1
  · intro n; exact (depth_without_diversity_insufficient n).2
  · exact depth_one_insufficient
  · exact target_in_alt_cumulative_2

/-! ## Section 12: Cardinality of Expansion

We compute the exact sizes to show diversity adds exactly one new idea in this gadget.
-/

/-- The union of individual closures has cardinality 3: {Base, KeyA, KeyB}. -/
lemma union_closure_card : 
    closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB = {Base, KeyA, KeyB} := by
  rw [closureA_eq, closureB_eq]
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    cases h with
    | inl hA =>
      cases hA with
      | inl h => left; exact h
      | inr h => right; left; exact h
    | inr hB =>
      cases hB with
      | inl h => left; exact h
      | inr h => right; right; exact h
  · intro h
    cases h with
    | inl h => left; left; exact h
    | inr h =>
      cases h with
      | inl h => left; right; exact h
      | inr h => right; right; exact h

/-- The alternating closure contains {Base, KeyA, KeyB, Target}. -/
lemma alt_closure_contains_all :
    {Base, KeyA, KeyB, Target} ⊆ closureAlternating {Base} generatorA generatorB := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  cases hx with
  | inl h => subst h; exact seed_in_alt_closure {Base} generatorA generatorB rfl
  | inr h =>
    cases h with
    | inl h => 
      subst h
      -- KeyA ∈ closureAlternating
      simp only [closureAlternating, Set.mem_iUnion]
      use 1
      show KeyA ∈ {Base} ∪ altGenStep generatorA generatorB {Base}
      right
      show KeyA ∈ (⋃ a ∈ ({Base} : Set GadgetIdea), generatorA a) ∪ 
                  (⋃ a ∈ ({Base} : Set GadgetIdea), generatorB a)
      left
      simp only [Set.mem_iUnion]
      exact ⟨Base, rfl, rfl⟩
    | inr h =>
      cases h with
      | inl h =>
        subst h
        -- KeyB ∈ closureAlternating
        simp only [closureAlternating, Set.mem_iUnion]
        use 1
        show KeyB ∈ {Base} ∪ altGenStep generatorA generatorB {Base}
        right
        show KeyB ∈ (⋃ a ∈ ({Base} : Set GadgetIdea), generatorA a) ∪ 
                    (⋃ a ∈ ({Base} : Set GadgetIdea), generatorB a)
        right
        simp only [Set.mem_iUnion]
        exact ⟨Base, rfl, rfl⟩
      | inr h =>
        subst h
        exact target_in_closure_alternating

/-- The expansion adds exactly 1 idea: Target. -/
theorem expansion_adds_one_idea :
    closureAlternating {Base} generatorA generatorB \ 
    (closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB) = {Target} := by
  apply Set.eq_of_subset_of_subset
  · -- diff ⊆ {Target}
    intro x hx
    simp only [Set.mem_diff] at hx
    obtain ⟨hx_alt, hx_not_union⟩ := hx
    -- x is in alternating closure but not in union
    -- The alternating closure stabilizes at {Base, KeyA, KeyB, Target}
    -- The union is {Base, KeyA, KeyB}
    -- So x must be Target
    rw [union_closure_card] at hx_not_union
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx_not_union
    obtain ⟨hx_ne_Base, hx_ne_KeyA, hx_ne_KeyB⟩ := hx_not_union
    -- x ∈ alternating closure, and x ∉ {Base, KeyA, KeyB}
    -- All ideas generated are in {Base, KeyA, KeyB, Target}
    simp only [closureAlternating, Set.mem_iUnion] at hx_alt
    obtain ⟨n, hn⟩ := hx_alt
    -- Prove by induction that altGenCumulative n {Base} ⊆ {Base, KeyA, KeyB, Target}
    have hbound : ∀ m, altGenCumulative generatorA generatorB m {Base} ⊆ {Base, KeyA, KeyB, Target} := by
      intro m
      induction m with
      | zero =>
        intro y hy
        simp only [altGenCumulative] at hy
        left; exact hy
      | succ m ihm =>
        intro y hy
        simp only [altGenCumulative, Set.mem_union] at hy
        cases hy with
        | inl h => exact ihm h
        | inr h =>
          simp only [altGenStep, Set.mem_union, Set.mem_iUnion] at h
          cases h with
          | inl hA =>
            obtain ⟨z, hz, hy'⟩ := hA
            have hz' := ihm hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
            -- z ∈ {Base, KeyA, KeyB, Target}, y ∈ generatorA z
            cases hz' with
            | inl hz_Base => subst hz_Base; simp only [generatorA] at hy'; right; left; exact hy'
            | inr h => cases h with
              | inl hz_KeyA => subst hz_KeyA; simp only [generatorA, Set.mem_empty_iff_false] at hy'
              | inr h => cases h with
                | inl hz_KeyB => subst hz_KeyB; simp only [generatorA] at hy'; right; right; right; exact hy'
                | inr hz_Target => subst hz_Target; simp only [generatorA, Set.mem_empty_iff_false] at hy'
          | inr hB =>
            obtain ⟨z, hz, hy'⟩ := hB
            have hz' := ihm hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
            cases hz' with
            | inl hz_Base => subst hz_Base; simp only [generatorB] at hy'; right; right; left; exact hy'
            | inr h => cases h with
              | inl hz_KeyA => subst hz_KeyA; simp only [generatorB] at hy'; right; right; right; exact hy'
              | inr h => cases h with
                | inl hz_KeyB => subst hz_KeyB; simp only [generatorB, Set.mem_empty_iff_false] at hy'
                | inr hz_Target => subst hz_Target; simp only [generatorB, Set.mem_empty_iff_false] at hy'
    have hx_in_all := hbound n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx_in_all
    cases hx_in_all with
    | inl h => exact absurd h hx_ne_Base
    | inr h => cases h with
      | inl h => exact absurd h hx_ne_KeyA
      | inr h => cases h with
        | inl h => exact absurd h hx_ne_KeyB
        | inr h => exact h
  · -- {Target} ⊆ diff
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [Set.mem_diff]
    exact ⟨target_in_closure_alternating, target_not_in_union⟩

/-! ## Section 13: Summary and Connection to Paper A

**Summary of Results:**
1. `closureA_eq`: cl({Base}, gA) = {Base, KeyA}
2. `closureB_eq`: cl({Base}, gB) = {Base, KeyB}
3. `target_not_in_closureA`: Target ∉ cl({Base}, gA)
4. `target_not_in_closureB`: Target ∉ cl({Base}, gB)
5. `target_in_closure_alternating`: Target ∈ cl_alt({Base}, gA, gB)
6. `strict_access_expansion`: cl_alt ⊃ cl_gA ∪ cl_gB
7. `exists_emergent_idea`: ∃ emergent idea (Target)
8. `target_depth_alternating`: Target requires exactly 2 alternation steps
9. `diversity_reduces_risk`: Risk drops from 1 to 0 with diversity
10. `depth_diversity_necessity`: Both depth ≥ 2 AND diversity are required
11. `expansion_adds_one_idea`: The expansion is exactly {Target}

**Significance for Paper A:**
These theorems demonstrate that:
- Generator diversity can STRICTLY expand the accessible hypothesis class
- Some hypotheses are unreachable by any individual generator
- The expansion is structural (not statistical)
- Combined with the depth barrier: access constraints are real
- Diversity strictly reduces achievable risk when optimal hypothesis requires it

**Connection to Learning Theory:**
If the "best" hypothesis is like Target (requires diverse generators),
then a homogeneous learner cannot achieve optimal risk, regardless of:
- How much training data it has
- How much compute it has
- How long it searches

Only a DIVERSE collective can access such hypotheses.
-/

/-! ## Section 14: General Closure Theory (Type-Polymorphic)

We now establish general theorems that work for ANY type and generators,
not just the specific gadget. This dramatically weakens the assumptions.
-/

/-- One step of generation from a set using generator g (polymorphic version). -/
def genStep' {α : Type*} (g : α → Set α) (S : Set α) : Set α :=
  ⋃ a ∈ S, g a

/-- Cumulative closure after n steps from seed S under generator g (polymorphic version). -/
def genCumulative' {α : Type*} (g : α → Set α) : ℕ → Set α → Set α
  | 0, S => S
  | n + 1, S => genCumulative' g n S ∪ genStep' g (genCumulative' g n S)

/-- General single-generator closure for any type α. -/
def closureSingle' {α : Type*} (S : Set α) (g : α → Set α) : Set α :=
  ⋃ n : ℕ, genCumulative' g n S

/-- One step of ALTERNATING generation (polymorphic version). -/
def altGenStep' {α : Type*} (gA gB : α → Set α) (S : Set α) : Set α :=
  (⋃ a ∈ S, gA a) ∪ (⋃ a ∈ S, gB a)

/-- Cumulative alternating closure after n steps (polymorphic version). -/
def altGenCumulative' {α : Type*} (gA gB : α → Set α) : ℕ → Set α → Set α
  | 0, S => S
  | n + 1, S => altGenCumulative' gA gB n S ∪ altGenStep' gA gB (altGenCumulative' gA gB n S)

/-- General alternating closure for any type α. -/
def closureAlternating' {α : Type*} (S : Set α) (gA gB : α → Set α) : Set α :=
  ⋃ n : ℕ, altGenCumulative' gA gB n S

/-- Monotonicity of single-generator closure. -/
lemma closureSingle_mono' {α : Type*} (g : α → Set α) (S T : Set α) (h : S ⊆ T) :
    closureSingle' S g ⊆ closureSingle' T g := by
  intro a ha
  simp only [closureSingle', Set.mem_iUnion] at ha ⊢
  obtain ⟨n, hn⟩ := ha
  use n
  induction n generalizing a with
  | zero => exact h hn
  | succ n ih =>
    simp only [genCumulative', Set.mem_union] at hn ⊢
    cases hn with
    | inl h' => left; exact ih h'
    | inr h' =>
      right
      simp only [genStep', Set.mem_iUnion] at h' ⊢
      obtain ⟨b, hb, ha'⟩ := h'
      exact ⟨b, ih hb, ha'⟩

/-- Single-generator closures are always contained in alternating closure. -/
lemma closureSingle_subset_alternating' {α : Type*} (S : Set α) (gA gB : α → Set α) :
    closureSingle' S gA ⊆ closureAlternating' S gA gB := by
  intro a ha
  simp only [closureSingle', Set.mem_iUnion] at ha
  obtain ⟨n, hn⟩ := ha
  simp only [closureAlternating', Set.mem_iUnion]
  use n
  induction n generalizing a with
  | zero => exact hn
  | succ n ih =>
    simp only [genCumulative', Set.mem_union] at hn
    simp only [altGenCumulative', Set.mem_union]
    cases hn with
    | inl h => left; exact ih h
    | inr h =>
      right
      simp only [genStep', Set.mem_iUnion] at h
      simp only [altGenStep', Set.mem_union, Set.mem_iUnion]
      left
      obtain ⟨b, hb, ha'⟩ := h
      exact ⟨b, ih hb, ha'⟩

/-- Union of single-generator closures is contained in alternating closure. -/
lemma union_single_subset_alternating' {α : Type*} (S : Set α) (gA gB : α → Set α) :
    closureSingle' S gA ∪ closureSingle' S gB ⊆ closureAlternating' S gA gB := by
  intro a ha
  simp only [Set.mem_union] at ha
  cases ha with
  | inl hA => exact closureSingle_subset_alternating' S gA gB hA
  | inr hB =>
    simp only [closureSingle', Set.mem_iUnion] at hB
    obtain ⟨n, hn⟩ := hB
    simp only [closureAlternating', Set.mem_iUnion]
    use n
    induction n generalizing a with
    | zero => exact hn
    | succ n ih =>
      simp only [genCumulative', Set.mem_union] at hn
      simp only [altGenCumulative', Set.mem_union]
      cases hn with
      | inl hprev => left; exact ih hprev
      | inr hgen =>
        right
        simp only [genStep', Set.mem_iUnion] at hgen
        simp only [altGenStep', Set.mem_union, Set.mem_iUnion]
        right
        obtain ⟨b, hb, ha'⟩ := hgen
        exact ⟨b, ih hb, ha'⟩

/-! ## Section 15: General Access Expansion Theorems (Weakest Assumptions)

These theorems establish EXACTLY when strict access expansion occurs,
for arbitrary types and generators. This is the most general form.
-/

/-- **General Access Expansion Theorem**:
    If there exists an element reachable by alternation but not by either generator alone,
    then we have strict access expansion.

    This works for ANY type α and ANY generators, with NO assumptions on α. -/
theorem general_strict_access_expansion {α : Type*} (S : Set α) (gA gB : α → Set α)
    (h : ∃ a : α, a ∈ closureAlternating' S gA gB ∧
                  a ∉ closureSingle' S gA ∪ closureSingle' S gB) :
    closureSingle' S gA ∪ closureSingle' S gB ⊂ closureAlternating' S gA gB := by
  constructor
  · exact union_single_subset_alternating' S gA gB
  · intro heq
    obtain ⟨a, ha_alt, ha_not_union⟩ := h
    have : a ∈ closureSingle' S gA ∪ closureSingle' S gB := heq ha_alt
    exact ha_not_union this

/-- **Characterization of Access Expansion**:
    Strict access expansion occurs IF AND ONLY IF there exists an emergent element.

    This is a complete characterization with no assumptions on the type. -/
theorem access_expansion_characterization {α : Type*} (S : Set α) (gA gB : α → Set α) :
    closureSingle' S gA ∪ closureSingle' S gB ⊂ closureAlternating' S gA gB ↔
    ∃ a : α, a ∈ closureAlternating' S gA gB ∧
             a ∉ closureSingle' S gA ∪ closureSingle' S gB := by
  constructor
  · intro ⟨_, hne⟩
    -- If strict subset, then not equal, so there exists an element in the difference
    have : ∃ a, a ∈ closureAlternating' S gA gB ∧
                a ∉ closureSingle' S gA ∪ closureSingle' S gB := by
      by_contra h
      push_neg at h
      have : closureAlternating' S gA gB ⊆ closureSingle' S gA ∪ closureSingle' S gB := h
      exact hne this
    exact this
  · intro h
    exact general_strict_access_expansion S gA gB h

/-- The unprimed genCumulative equals the primed one for GadgetIdea. -/
lemma genCumulative_eq_genCumulative' (g : GadgetIdea → Set GadgetIdea) (n : ℕ) (S : Set GadgetIdea) :
    genCumulative g n S = genCumulative' g n S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [genCumulative, genCumulative', genStep, genStep']
    rw [ih]

/-- The unprimed altGenCumulative equals the primed one for GadgetIdea. -/
lemma altGenCumulative_eq_altGenCumulative' (gA gB : GadgetIdea → Set GadgetIdea) (n : ℕ) (S : Set GadgetIdea) :
    altGenCumulative gA gB n S = altGenCumulative' gA gB n S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [altGenCumulative, altGenCumulative', altGenStep, altGenStep']
    rw [ih]

/-- The unprimed closureSingle equals the primed one for GadgetIdea. -/
lemma closureSingle_eq_closureSingle' (S : Set GadgetIdea) (g : GadgetIdea → Set GadgetIdea) :
    closureSingle S g = closureSingle' S g := by
  simp only [closureSingle, closureSingle']
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro ⟨n, hn⟩
    use n
    rw [← genCumulative_eq_genCumulative']
    exact hn
  · intro ⟨n, hn⟩
    use n
    rw [genCumulative_eq_genCumulative']
    exact hn

/-- The unprimed closureAlternating equals the primed one for GadgetIdea. -/
lemma closureAlternating_eq_closureAlternating' (S : Set GadgetIdea) (gA gB : GadgetIdea → Set GadgetIdea) :
    closureAlternating S gA gB = closureAlternating' S gA gB := by
  simp only [closureAlternating, closureAlternating']
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro ⟨n, hn⟩
    use n
    rw [← altGenCumulative_eq_altGenCumulative']
    exact hn
  · intro ⟨n, hn⟩
    use n
    rw [altGenCumulative_eq_altGenCumulative']
    exact hn

/-- The gadget is an instance of the general theorem. -/
theorem gadget_instantiates_general :
    closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB ⊂
    closureAlternating {Base} generatorA generatorB := by
  rw [closureSingle_eq_closureSingle', closureSingle_eq_closureSingle',
      closureAlternating_eq_closureAlternating']
  apply general_strict_access_expansion
  use Target
  constructor
  · rw [← closureAlternating_eq_closureAlternating']
    exact target_in_closure_alternating
  · rw [← closureSingle_eq_closureSingle', ← closureSingle_eq_closureSingle']
    exact target_not_in_union

/-! ## Section 16: General Risk Theory (Polymorphic Loss)

We generalize the risk theorems to work with ANY ordered type for loss,
not just ℕ. This removes the assumption that loss must be natural numbers.
-/

open Classical in
/-- General risk with polymorphic loss type.
    No assumption needed on α (the hypothesis type).
    Only requires β has a decidable total order and a "max loss" element. -/
noncomputable def minRisk_general {α : Type*} {β : Type*} [LinearOrder β]
    (loss : α → β) (zeroLoss : β) (maxLoss : β) (H : Set α) : β :=
  if h : ∃ a ∈ H, loss a = zeroLoss then zeroLoss else maxLoss

open Classical in
/-- If target is accessible in hypothesis class H,
    and target has zero loss, then minRisk = 0. -/
theorem minRisk_general_accessible {α : Type*} {β : Type*} [LinearOrder β]
    (loss : α → β) (zeroLoss : β) (maxLoss : β) (target : α) (H : Set α)
    (h_target_in : target ∈ H) (h_zero : loss target = zeroLoss) :
    minRisk_general loss zeroLoss maxLoss H = zeroLoss := by
  unfold minRisk_general
  split_ifs with h
  · rfl
  · exfalso
    apply h
    exact ⟨target, h_target_in, h_zero⟩

open Classical in
/-- If target is not accessible, and is the only hypothesis with zero loss,
    then minRisk > 0. -/
theorem minRisk_general_inaccessible {α : Type*} {β : Type*} [LinearOrder β]
    (loss : α → β) (zeroLoss : β) (maxLoss : β) (target : α) (H : Set α)
    (h_target_not_in : target ∉ H)
    (h_unique : ∀ a ∈ H, loss a ≠ zeroLoss) :
    minRisk_general loss zeroLoss maxLoss H = maxLoss := by
  unfold minRisk_general
  split_ifs with h
  · obtain ⟨a, ha, hloss⟩ := h
    exact absurd hloss (h_unique a ha)
  · rfl

open Classical in
/-- Risk is monotone: larger hypothesis class has lower (or equal) risk.
    This works for ANY ordered loss type. -/
theorem minRisk_monotone {α : Type*} {β : Type*} [LinearOrder β]
    (loss : α → β) (zeroLoss : β) (maxLoss : β) (H H' : Set α)
    (h_sub : H ⊆ H') (h_order : zeroLoss ≤ maxLoss) :
    minRisk_general loss zeroLoss maxLoss H' ≤ minRisk_general loss zeroLoss maxLoss H := by
  unfold minRisk_general
  -- Analyze based on what's in H (the smaller set)
  by_cases h2 : ∃ a ∈ H, loss a = zeroLoss
  · -- Case: H has zero-loss element
    -- Then H' also has zero-loss element (since H ⊆ H')
    have h1 : ∃ a ∈ H', loss a = zeroLoss := by
      obtain ⟨a, ha, hloss⟩ := h2
      exact ⟨a, h_sub ha, hloss⟩
    have lhs : (if h : ∃ a ∈ H', loss a = zeroLoss then zeroLoss else maxLoss) = zeroLoss := by simp_all
    have rhs : (if h : ∃ a ∈ H, loss a = zeroLoss then zeroLoss else maxLoss) = zeroLoss := by simp_all
    rw [lhs, rhs]
  · -- Case: H doesn't have zero-loss element
    -- H' might or might not have one
    by_cases h1 : ∃ a ∈ H', loss a = zeroLoss
    · -- H' has zero-loss but H doesn't: zeroLoss ≤ maxLoss
      have lhs : (if h : ∃ a ∈ H', loss a = zeroLoss then zeroLoss else maxLoss) = zeroLoss := by simp_all
      have rhs : (if h : ∃ a ∈ H, loss a = zeroLoss then zeroLoss else maxLoss) = maxLoss := by simp_all
      rw [lhs, rhs]
      exact h_order
    · -- Neither has zero-loss: maxLoss ≤ maxLoss
      have lhs : (if h : ∃ a ∈ H', loss a = zeroLoss then zeroLoss else maxLoss) = maxLoss := by simp_all
      have rhs : (if h : ∃ a ∈ H, loss a = zeroLoss then zeroLoss else maxLoss) = maxLoss := by simp_all
      rw [lhs, rhs]

open Classical in
/-- If alternating closure strictly contains union of single closures,
    and target is only reachable by alternation, then diversity strictly reduces risk. -/
theorem diversity_strictly_reduces_risk_general {α : Type*} {β : Type*} [LinearOrder β]
    (loss : α → β) (zeroLoss : β) (maxLoss : β)
    (S : Set α) (gA gB : α → Set α) (target : α)
    (h_target_alt : target ∈ closureAlternating' S gA gB)
    (h_target_single : target ∉ closureSingle' S gA ∪ closureSingle' S gB)
    (h_zero : loss target = zeroLoss)
    (h_unique : ∀ a ∈ closureSingle' S gA ∪ closureSingle' S gB, loss a ≠ zeroLoss)
    (h_order : maxLoss > zeroLoss) :
    minRisk_general loss zeroLoss maxLoss (closureAlternating' S gA gB) <
    minRisk_general loss zeroLoss maxLoss (closureSingle' S gA ∪ closureSingle' S gB) := by
  have h_alt : minRisk_general loss zeroLoss maxLoss (closureAlternating' S gA gB) = zeroLoss :=
    minRisk_general_accessible loss zeroLoss maxLoss target _ h_target_alt h_zero
  have h_single : minRisk_general loss zeroLoss maxLoss (closureSingle' S gA ∪ closureSingle' S gB) = maxLoss :=
    minRisk_general_inaccessible loss zeroLoss maxLoss target _ h_target_single h_unique
  rw [h_alt, h_single]
  exact h_order

/-- Instantiation for the gadget with ℕ loss. -/
theorem gadget_diversity_reduces_risk_instance :
    minRisk Target (closureSingle {Base} generatorA ∪ closureSingle {Base} generatorB) = 1 ∧
    minRisk Target (closureAlternating {Base} generatorA generatorB) = 0 :=
  diversity_reduces_risk

/-! ## Section 17: Constructive Variants (Removing Classical Logic)

We show that some results can be proven constructively, removing the
`open Classical` assumption where possible.
-/

/-- Constructive version of minRisk that doesn't need Classical logic.
    Instead of if-then-else, we use explicit existence. -/
def minRisk_constructive {α : Type*} {β : Type*} [LinearOrder β]
    (loss : α → β) (zeroLoss : β) (maxLoss : β) (H : Set α)
    (h : Decidable (∃ a ∈ H, loss a = zeroLoss)) : β :=
  match h with
  | isTrue _ => zeroLoss
  | isFalse _ => maxLoss

/-- The constructive version agrees with the classical one when decidability is available. -/
theorem minRisk_constructive_eq_classical {α : Type*} {β : Type*} [LinearOrder β]
    (loss : α → β) (zeroLoss : β) (maxLoss : β) (H : Set α)
    (h : Decidable (∃ a ∈ H, loss a = zeroLoss)) :
    minRisk_constructive loss zeroLoss maxLoss H h =
    minRisk_general loss zeroLoss maxLoss H := by
  unfold minRisk_constructive minRisk_general
  cases h with
  | isTrue hp =>
    have : (∃ a ∈ H, loss a = zeroLoss) := hp
    simp_all
  | isFalse hn =>
    have : ¬(∃ a ∈ H, loss a = zeroLoss) := hn
    simp_all

/-! ## Section 18: Summary of Generalizations

**What We've Achieved:**

1. **Type Polymorphism**: All closure theorems now work for arbitrary types,
   not just GadgetIdea.

2. **Generator Parametrization**: The key theorems (`general_strict_access_expansion`,
   `access_expansion_characterization`) work for ANY generators with the required
   separation property.

3. **Loss Type Generalization**: Risk theorems work with any ordered type β,
   not just ℕ.

4. **Constructive Variants**: Where possible, we've provided constructive versions
   that don't rely on Classical logic.

5. **Complete Characterization**: `access_expansion_characterization` gives an
   IF AND ONLY IF condition for when access expansion occurs.

**Remaining Minimal Assumptions:**

1. The concrete gadget (GadgetIdea with 4 elements) is kept to provide an
   EXISTENCE PROOF. This is necessary—you can't prove something exists without
   constructing an example.

2. DecidableEq on GadgetIdea is only used for convenient pattern matching in
   the concrete proofs. The general theorems don't require it.

3. Classical logic remains in some places (minRisk definition) but we've provided
   constructive alternatives.

**Impact:**

The theorems now apply to:
- ANY discrete idea space (not just 4 elements)
- ANY pair of generators with complementary limitations
- ANY notion of loss (not just 0-1 loss)
- Can be instantiated for specific learning problems in many domains

This makes the results MUCH more broadly applicable to real-world learning systems.
-/

end CollectiveAccess
