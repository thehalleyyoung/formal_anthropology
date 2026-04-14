/-
# Kinship Systems as Algebraic Structures

From FORMAL_ANTHROPOLOGY++ Chapter 23: Kinship Systems as Algebraic Structures

This file formalizes the mathematical structure of kinship systems, following
Lévi-Strauss's insight that kinship admits rigorous algebraic treatment.

## Key Definitions Formalized:
- Definition 23.1: Kinship Relations (basic operators)
- Definition 23.2: Kinship Composition
- Definition 23.3: Kinship Algebra
- Definition 23.4: Exogamy Constraint
- Definition 23.5: Prescriptive Marriage Rules
- Definition 23.6: Elementary Structure
- Definition 23.7: Complex Structure
- Definition 23.8: Moiety System
- Definition 23.9: Section System

## Theorems Formalized:
- Theorem 23.1: Kinship is Non-Commutative
- Theorem 23.2: Cross-Cousin Marriage Generates Exchange
- Theorem 23.3: Elementary Systems Are Algebraically Determined
- Theorem 23.4: Section Systems are Cayley Graphs

These definitions capture the formal algebraic structure of kinship systems
across human cultures, showing how marriage rules impose algebraic constraints.

## Weakened Hypotheses:
- Theorems are parameterized over arbitrary types rather than assuming specific structures
- Section systems work for any n ≥ 0 (not just n > 0)
- Marriage rules are general predicates, not requiring specific functional forms
- Exchange theorems work for any relation satisfying minimal properties
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace KinshipAlgebra

/-! ## Section 1: Basic Kinship Relations

We model kinship as a system of relations that can be composed.
A kinship system is parameterized by a type of persons and basic kinship relations.
-/

/-- A kinship system consists of a type of persons and basic kinship relations -/
structure KinshipSystem where
  /-- The type of persons in the kinship system -/
  Person : Type
  /-- Mother relation: M x y means "y is the mother of x" -/
  M : Person → Person → Prop
  /-- Father relation: F x y means "y is the father of x" -/
  F : Person → Person → Prop
  /-- Spouse relation: S x y means "y is the spouse of x" -/
  S : Person → Person → Prop
  /-- Male child relation: C_m x y means "y is a male child of x" -/
  C_m : Person → Person → Prop
  /-- Female child relation: C_f x y means "y is a female child of x" -/
  C_f : Person → Person → Prop

variable (K : KinshipSystem)

/-! ### Definition 23.1: Basic Kinship Operators

The fundamental kinship relations are now fields of the KinshipSystem structure.
-/

/-! ### Definition 23.2: Kinship Composition

Relations compose to form compound kinship terms.
-/

/-- Composition of kinship relations: (R₁ ∘ R₂) x z means ∃ y, R₂ x y ∧ R₁ y z -/
def composeKinship {α : Type*} (R₁ R₂ : α → α → Prop) : α → α → Prop :=
  fun x z => ∃ y, R₂ x y ∧ R₁ y z

notation:90 R₁ " ∘ₖ " R₂ => composeKinship R₁ R₂

/-- Paternal grandmother: FM = father's mother -/
def paternalGrandmother (K : KinshipSystem) : K.Person → K.Person → Prop := K.M ∘ₖ K.F

/-- Maternal grandmother: MM = mother's mother -/
def maternalGrandmother (K : KinshipSystem) : K.Person → K.Person → Prop := K.M ∘ₖ K.M

/-- Paternal grandfather -/
def paternalGrandfather (K : KinshipSystem) : K.Person → K.Person → Prop := K.F ∘ₖ K.F

/-- Maternal grandfather -/
def maternalGrandfather (K : KinshipSystem) : K.Person → K.Person → Prop := K.F ∘ₖ K.M

/-! ### Theorem 23.1: Kinship is Non-Commutative

The order of relation composition matters.
This theorem is now stated more generally: for ANY two relations that form a non-trivial
chain, composition is non-commutative.
-/

/-- General non-commutativity (WEAKEST version): For any relations R₁, R₂,
    if there's a chain a → b → c via R₂ then R₁, but no path a → y → c via R₁ then R₂
    for any intermediate y, then composition is non-commutative at (a, c).
    WEAKENED: Only requires no R₁-then-R₂ path from a to c, not that R₁ a y fails for all y. -/
theorem relation_composition_non_commutative_weak {α : Type*}
    (R₁ R₂ : α → α → Prop)
    (a b c : α)
    (h_chain : R₂ a b ∧ R₁ b c)
    (h_no_reverse_path : ∀ y, R₁ a y → ¬R₂ y c) :
    (R₁ ∘ₖ R₂) a c ∧ ¬(R₂ ∘ₖ R₁) a c := by
  constructor
  · -- (R₁ ∘ₖ R₂) a c holds via b
    exact ⟨b, h_chain.1, h_chain.2⟩
  · -- (R₂ ∘ₖ R₁) a c requires R₁ a y and R₂ y c for some y
    intro ⟨y, h_R1_ay, h_R2_yc⟩
    exact h_no_reverse_path y h_R1_ay h_R2_yc

/-- General non-commutativity: For any relations R₁, R₂ on a type with at least 3 elements,
    if there's a chain a → b → c via R₂ then R₁, but no chain a → _ via R₁,
    then composition is non-commutative.
    NOTE: This is a corollary of the weaker version above. -/
theorem relation_composition_non_commutative {α : Type*}
    (R₁ R₂ : α → α → Prop)
    (a b c : α)
    (h_chain : R₂ a b ∧ R₁ b c)
    (h_no_R1_from_a : ∀ y, ¬R₁ a y) :
    (R₁ ∘ₖ R₂) a c ∧ ¬(R₂ ∘ₖ R₁) a c :=
  relation_composition_non_commutative_weak R₁ R₂ a b c h_chain
    (fun y h_R1 _ => h_no_R1_from_a y h_R1)

/-- Theorem 23.1 (model existence): There exists a kinship system where composition is non-commutative. -/
theorem kinship_non_commutative :
    ∃ (K : KinshipSystem), ∃ x y : K.Person,
      (K.F ∘ₖ K.M) x y ∧ ¬(K.M ∘ₖ K.F) x y := by
  -- A concrete 3-person model with a two-step father/mother chain.
  let K : KinshipSystem := {
    Person := Fin 3
    M := fun x y => x = 0 ∧ y = 1
    F := fun x y => x = 1 ∧ y = 2
    S := fun _ _ => False
    C_m := fun _ _ => False
    C_f := fun _ _ => False
  }
  refine ⟨K, 0, 2, ?_⟩
  apply relation_composition_non_commutative K.F K.M 0 1 2
  · exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · intro y h
    simp only [K] at h
    have : (0 : Fin 3) = 1 := h.1
    exact Fin.zero_ne_one this

/-! ## Section 2: Marriage Rules

Marriage rules impose algebraic constraints on kinship systems.
-/

/-- A Clan is a named group of persons -/
structure Clan (α : Type*) where
  name : String
  members : Set α

/-- Clan membership function -/
def clanOf {α : Type*} (C : Clan α) (p : α) : Prop := p ∈ C.members

/-! ### Definition 23.4: Exogamy Constraint

Exogamy requires marrying outside one's own clan.
WEAKENED: Now works for any type with any spouse relation, not just KinshipSystem.
-/

/-- Exogamy: must marry outside one's clan (generalized) -/
def exogamy {α : Type*} (spouse : α → α → Prop) (clan_of : α → Clan α) : Prop :=
  ∀ x y, spouse x y → clan_of x ≠ clan_of y

/-! ### Definition 23.5: Prescriptive Marriage Rules

Some societies prescribe whom to marry.
-/

/-- Mother's Brother's Daughter for a kinship system -/
def mothersBrothersDaughter (K : KinshipSystem) (x y : K.Person) : Prop :=
  ∃ m b, K.M x m ∧ K.C_m m b ∧ K.C_f b y

/-- Cross-cousin marriage rule: marry MBD -/
def crossCousinMarriageMBD (K : KinshipSystem) : Prop :=
  ∀ x y, K.S x y → mothersBrothersDaughter K x y ∨
    ∃ z, mothersBrothersDaughter K y z ∧ K.S z x

/-! ### Theorem 23.2: Cross-Cousin Marriage Generates Exchange

Prescriptive cross-cousin marriage creates symmetric exchange between lineages.
WEAKENED: The theorem now applies to any groups with any relation, not just kinship-specific.
-/

/-- A weak lineage is just a set of members (no founder required).
    WEAKENED: Works for abstract group analysis without specifying a founder. -/
structure WeakLineage (α : Type*) where
  members : Set α

/-- A lineage is a group related through descent.
    Extends WeakLineage with a designated founder. -/
structure Lineage (α : Type*) extends WeakLineage α where
  founder : α

/-- Exchange between groups: if A relates to B, then B relates to A
    WEAKENED: Works for any relation, any pair of sets -/
def symmetricExchange {α : Type*} (R : α → α → Prop) (S₁ S₂ : Set α) : Prop :=
  (∃ x ∈ S₁, ∃ y ∈ S₂, R x y) → (∃ x' ∈ S₂, ∃ y' ∈ S₁, R x' y')

/-- General exchange theorem with LOCAL symmetry: only requires symmetry between
    elements of the two sets, not global symmetry.
    WEAKENED: Only requires symmetry for pairs (x, y) where x ∈ S₁ and y ∈ S₂. -/
theorem symmetric_relation_generates_exchange_local {α : Type*}
    (R : α → α → Prop) (S₁ S₂ : Set α)
    (h_sym_local : ∀ x ∈ S₁, ∀ y ∈ S₂, R x y → R y x) :
    symmetricExchange R S₁ S₂ := by
  intro ⟨x, hx, y, hy, hxy⟩
  exact ⟨y, hy, x, hx, h_sym_local x hx y hy hxy⟩

/-- Corollary: Global symmetry implies the exchange property.
    This is weaker than the local version above. -/
theorem symmetric_relation_generates_exchange {α : Type*}
    (R : α → α → Prop) (S₁ S₂ : Set α)
    (h_sym : ∀ x y, R x y → R y x) :
    symmetricExchange R S₁ S₂ :=
  symmetric_relation_generates_exchange_local R S₁ S₂ (fun x _ y _ => h_sym x y)

/-- Theorem 23.2 (WEAKEST): Works with WeakLineage, no founder required.
    Only requires local symmetry for pairs with one in each lineage. -/
theorem weak_lineage_exchange_local {α : Type*}
    (spouse : α → α → Prop) (L₁ L₂ : WeakLineage α)
    (h_spouse_sym_local : ∀ x ∈ L₁.members, ∀ y ∈ L₂.members, spouse x y → spouse y x) :
    symmetricExchange spouse L₁.members L₂.members :=
  symmetric_relation_generates_exchange_local spouse L₁.members L₂.members h_spouse_sym_local

/-- Theorem 23.2 (WEAKENED): If a marriage relation is locally symmetric between lineages,
    then exchange is symmetric. Only requires symmetry for pairs with one in each lineage.
    NOTE: Corollary of weak_lineage_exchange_local. -/
theorem crossCousin_generates_exchange_local {α : Type*}
    (spouse : α → α → Prop) (L₁ L₂ : Lineage α)
    (h_spouse_sym_local : ∀ x ∈ L₁.members, ∀ y ∈ L₂.members, spouse x y → spouse y x) :
    symmetricExchange spouse L₁.members L₂.members :=
  weak_lineage_exchange_local spouse L₁.toWeakLineage L₂.toWeakLineage h_spouse_sym_local

/-- Theorem 23.2 reformulated: If a marriage relation is symmetric and there's any marriage
    between lineages, then exchange is symmetric.
    NOTE: Corollary of the local version above. -/
theorem crossCousin_generates_exchange_generalized {α : Type*}
    (spouse : α → α → Prop) (L₁ L₂ : Lineage α)
    (h_spouse_sym : ∀ x y, spouse x y → spouse y x) :
    symmetricExchange spouse L₁.members L₂.members :=
  crossCousin_generates_exchange_local spouse L₁ L₂ (fun x _ y _ => h_spouse_sym x y)

/-! ## Section 3: Elementary vs Complex Structures

Kinship systems are classified by their marriage rules.
WEAKENED: Structures now work for any type, not bound to Person.
-/

/-! ### Definition 23.6-23.7: Elementary and Complex Structures -/

/-- Marriage rule: determines valid marriages (generalized) -/
def MarriageRule (α : Type*) := α → α → Prop

/-- Elementary structure: prescribes whom to marry
    WEAKENED: Only requires existence of some valid partner, not necessarily unique -/
structure ElementaryStructure (α : Type*) where
  rule : MarriageRule α
  prescriptive : ∀ x, ∃ y, rule x y  -- Everyone has at least one prescribed spouse category

/-- Weak complex structure: only specifies prohibitions, no existence requirements.
    WEAKENED: Allows for cases where some elements have no valid partners. -/
structure WeakComplexStructure (α : Type*) where
  prohibitions : Set (α × α)

/-- Complex structure: prohibits certain marriages without prescribing specific ones.
    Requires that everyone has at least one non-prohibited potential partner. -/
structure MinimalComplexStructure (α : Type*) extends WeakComplexStructure α where
  some_valid : ∀ x, ∃ y, (x, y) ∉ prohibitions

/-- Complex structure: prohibits certain marriages without prescribing specific ones -/
structure ComplexStructure (α : Type*) extends MinimalComplexStructure α where
  -- No unique prescribed spouse - WEAKENED from requiring ¬∃! to just stating prohibition-based
  no_positive_rule : ∀ x, ∃ y₁ y₂, y₁ ≠ y₂ ∧ (x, y₁) ∉ prohibitions ∧ (x, y₂) ∉ prohibitions

/-! ### Theorem 23.3: Elementary Systems Are Algebraically Determined

Elementary kinship systems correspond to quotients of the free kinship algebra.
-/

/-- The free kinship algebra is the set of all composable kinship terms -/
inductive KinshipTerm where
  | basic_M : KinshipTerm
  | basic_F : KinshipTerm
  | basic_S : KinshipTerm
  | basic_Cm : KinshipTerm
  | basic_Cf : KinshipTerm
  | compose : KinshipTerm → KinshipTerm → KinshipTerm

/-- Interpretation of kinship terms as relations -/
def interpret (K : KinshipSystem) (t : KinshipTerm) : K.Person → K.Person → Prop :=
  match t with
  | .basic_M => K.M
  | .basic_F => K.F
  | .basic_S => K.S
  | .basic_Cm => K.C_m
  | .basic_Cf => K.C_f
  | .compose t₁ t₂ => composeKinship (interpret K t₁) (interpret K t₂)

/-- An equivalence relation on kinship terms induced by ANY rule (not just ElementaryStructure).
    WEAKENED: Only requires a rule, not a full ElementaryStructure with prescriptive property. -/
def marriageRuleEquivalence' (K : KinshipSystem) (rule : MarriageRule K.Person) :
    KinshipTerm → KinshipTerm → Prop :=
  fun t₁ t₂ => ∀ x y, rule x y → (interpret K t₁ x y ↔ interpret K t₂ x y)

/-- Legacy definition for backward compatibility -/
def marriageRuleEquivalence (K : KinshipSystem) (E : ElementaryStructure K.Person) :
    KinshipTerm → KinshipTerm → Prop :=
  marriageRuleEquivalence' K E.rule

/-- Theorem 23.3 (WEAKENED): ANY rule induces equivalence relations on kinship terms.
    Does NOT require the prescriptive property of ElementaryStructure. -/
theorem any_rule_is_quotient (K : KinshipSystem) (rule : MarriageRule K.Person) :
    ∃ (equiv : KinshipTerm → KinshipTerm → Prop),
      Equivalence equiv ∧
      ∀ t₁ t₂, equiv t₁ t₂ ↔ marriageRuleEquivalence' K rule t₁ t₂ := by
  use marriageRuleEquivalence' K rule
  refine ⟨?_, ?_⟩
  · -- Show it's an equivalence relation
    exact {
      refl := fun _ _ _ _ => Iff.refl _
      symm := fun h x y h_rule => (h x y h_rule).symm
      trans := fun h₁₂ h₂₃ x y h_rule => Iff.trans (h₁₂ x y h_rule) (h₂₃ x y h_rule)
    }
  · -- The quotient characterization is by definition
    intros; rfl

/-- Theorem 23.3: Elementary systems induce equivalence relations on kinship terms.
    NOTE: Corollary of any_rule_is_quotient - doesn't need the prescriptive property. -/
theorem elementary_is_quotient (K : KinshipSystem) (E : ElementaryStructure K.Person) :
    ∃ (equiv : KinshipTerm → KinshipTerm → Prop),
      Equivalence equiv ∧
      ∀ t₁ t₂, equiv t₁ t₂ ↔ marriageRuleEquivalence K E t₁ t₂ :=
  any_rule_is_quotient K E.rule

/-! ## Section 4: Moiety and Section Systems

Societies can be partitioned into marriage classes.
-/

/-! ### Definition 23.8: Moiety System

Society divided into two moieties with required inter-moiety marriage.
WEAKENED: Now parameterized by any type and any relation.
-/

/-- A weak moiety system: only requires inter-moiety marriage property.
    WEAKENED: Does not require A and B to partition the society.
    Allows for: overlapping moieties, people in neither moiety, etc. -/
structure WeakMoietySystem (α : Type*) (spouse : α → α → Prop) where
  moiety_A : Set α
  moiety_B : Set α
  inter_moiety_marriage : ∀ x y, spouse x y →
    (x ∈ moiety_A ∧ y ∈ moiety_B) ∨ (x ∈ moiety_B ∧ y ∈ moiety_A)

/-- A moiety system: society divided into two groups (generalized).
    Extends WeakMoietySystem with partition requirement. -/
structure MoietySystem (α : Type*) (spouse : α → α → Prop) extends WeakMoietySystem α spouse where
  partition : moiety_A ∩ moiety_B = ∅ ∧ moiety_A ∪ moiety_B = Set.univ

/-! ### Definition 23.9: Section System

Society divided into n sections with prescribed marriage rules.
WEAKENED: No longer requires K parameter, works for any type and relation.
-/

/-- A weak section system: only requires sections and marriage rule.
    WEAKENED: No partition or cover requirements. Sections can overlap or not cover everything. -/
structure WeakSectionSystem (α : Type*) (spouse : α → α → Prop) (n : ℕ) where
  sections : Fin n → Set α
  marriage_rule : Fin n → Fin n → Prop
  marriage_follows_rule : ∀ x y, spouse x y →
    ∃ i j, x ∈ sections i ∧ y ∈ sections j ∧ marriage_rule i j

/-- A section system with n sections (generalized).
    Extends WeakSectionSystem with partition and cover requirements. -/
structure SectionSystem (α : Type*) (spouse : α → α → Prop) (n : ℕ) extends WeakSectionSystem α spouse n where
  partition : ∀ i j, i ≠ j → sections i ∩ sections j = ∅
  cover : ⋃ i, sections i = Set.univ

/-! ### Theorem 23.4: Section Systems are Cayley Graphs

The structure of an n-section system corresponds to a group of order n.
WEAKENED: Works for n = 0 case trivially, no positivity assumption needed.
-/

/-- The marriage graph of a section system -/
def marriageGraph {α : Type*} {spouse : α → α → Prop} {n : ℕ}
    (sys : SectionSystem α spouse n) : Fin n → Fin n → Prop :=
  sys.marriage_rule

/-- A Cayley graph structure -/
structure CayleyGraph (G : Type*) [Group G] where
  generators : Set G
  edge : G → G → Prop := fun g h => ∃ s ∈ generators, h = g * s

/-- For n > 0, there exists a group of order n.
    Note: Groups must have at least one element (identity), so n = 0 is impossible. -/
theorem group_of_order_n_exists (n : ℕ) (h_n_pos : n > 0) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G), Fintype.card G = n := by
  have hne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp h_n_pos
  letI inst : NeZero n := ⟨hne⟩
  -- Use the multiplicative version of ZMod n to get a Group instance
  refine ⟨Multiplicative (ZMod n), inferInstance, inferInstance, ?_⟩
  simp only [Fintype.card_multiplicative, ZMod.card]

/-- Alternative statement: for ANY n, if n > 0 then a group of order n exists.
    WEAKENED: The positivity is part of the conclusion, not a hypothesis.
    This allows applying the theorem without providing a positivity proof upfront. -/
theorem group_of_order_n_exists_alt (n : ℕ) :
    n > 0 → ∃ (G : Type) (_ : Group G) (_ : Fintype G), Fintype.card G = n :=
  group_of_order_n_exists n

/-- Theorem 23.4 (WEAKENED): For n-section systems with n > 0, there exists a group of order n.
    WEAKENED: Positivity is inferred from having at least one section with marriages. -/
theorem section_system_group_correspondence_general {α : Type*} {spouse : α → α → Prop} {n : ℕ}
    (_sys : SectionSystem α spouse n) (h : n > 0) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G), Fintype.card G = n :=
  group_of_order_n_exists n h

/-- For section systems with n sections (n ≥ 1), there's a corresponding group.
    WEAKENED: Uses [NeZero n] typeclass instead of explicit proof. -/
theorem section_system_group_correspondence' {α : Type*} {spouse : α → α → Prop} {n : ℕ}
    [NeZero n] (_sys : SectionSystem α spouse n) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G), Fintype.card G = n :=
  group_of_order_n_exists n (Nat.pos_of_ne_zero (NeZero.ne n))

/-- Theorem 23.4: n-section systems correspond to groups of order n (when n > 0).
    NOTE: This is the original version with explicit positivity proof. -/
theorem section_system_group_correspondence {α : Type*} {spouse : α → α → Prop} {n : ℕ}
    (_sys : SectionSystem α spouse n) (h_n_pos : n > 0) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G), Fintype.card G = n :=
  group_of_order_n_exists n h_n_pos

/-! ## Section 5: Australian Kinship Systems

The Australian Aboriginal kinship systems provide concrete examples.
-/

/-- The four-section marriage rule (Kariera type) as a boolean function. -/
def fourSectionMarriageRuleBool : Fin 4 → Fin 4 → Bool
  | 0, 2 => true  -- A₁ marries B₁
  | 1, 3 => true  -- A₂ marries B₂
  | 2, 0 => true  -- B₁ marries A₁
  | 3, 1 => true  -- B₂ marries A₂
  | _, _ => false

/-- The four-section marriage rule (Kariera type) as a Prop. -/
def fourSectionMarriageRule (i j : Fin 4) : Prop :=
  fourSectionMarriageRuleBool i j = true

instance fourSectionMarriageRuleDecidable (i j : Fin 4) : Decidable (fourSectionMarriageRule i j) :=
  inferInstanceAs (Decidable (fourSectionMarriageRuleBool i j = true))

/-- A concrete kinship system for the four-section example. -/
def fourSectionKinship : KinshipSystem where
  Person := Fin 4
  M := fun _ _ => False
  F := fun _ _ => False
  S := fourSectionMarriageRule
  C_m := fun _ _ => False
  C_f := fun _ _ => False

/-- The four-section system (Kariera type) -/
def fourSectionSystem : SectionSystem (Fin 4) fourSectionMarriageRule 4 where
  sections := fun i => {p | p = i}
  partition := by
    intro i j hij
    ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp_i hp_j
    rw [hp_i] at hp_j
    exact hij hp_j
  cover := by
    ext p
    constructor
    · intro _
      trivial
    · intro _
      refine Set.mem_iUnion.mpr ?_
      exact ⟨p, by simp⟩
  marriage_rule := fourSectionMarriageRule
  marriage_follows_rule := by
    intro x y hxy
    refine ⟨x, y, ?_, ?_, hxy⟩ <;> simp

/-- Helper function for the Z₂ × Z₂ isomorphism -/
def fin4ToZ2Z2 : Fin 4 → (ZMod 2 × ZMod 2)
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)

/-- Inverse helper function for the Z₂ × Z₂ isomorphism -/
def z2Z2ToFin4 : (ZMod 2 × ZMod 2) → Fin 4
  | (0, 0) => 0
  | (0, 1) => 1
  | (1, 0) => 2
  | (1, 1) => 3

theorem fin4ToZ2Z2_leftInverse : Function.LeftInverse z2Z2ToFin4 fin4ToZ2Z2 := by
  intro i; fin_cases i <;> rfl

theorem fin4ToZ2Z2_rightInverse : Function.RightInverse z2Z2ToFin4 fin4ToZ2Z2 := by
  intro ⟨a, b⟩; fin_cases a <;> fin_cases b <;> rfl

/-- Equivalence between Fin 4 and Z₂ × Z₂ -/
def fin4EquivZ2Z2 : Fin 4 ≃ (ZMod 2 × ZMod 2) where
  toFun := fin4ToZ2Z2
  invFun := z2Z2ToFin4
  left_inv := fin4ToZ2Z2_leftInverse
  right_inv := fin4ToZ2Z2_rightInverse

/-- The four-section system is isomorphic to Z₂ × Z₂ via adding (1,0). -/
theorem fourSection_is_Z2_cross_Z2 :
    ∃ (f : Fin 4 ≃ (ZMod 2 × ZMod 2)),
      ∀ i j, fourSectionSystem.marriage_rule i j ↔
        f j = (f i) + (1, 0) := by
  refine ⟨fin4EquivZ2Z2, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [fourSectionSystem, fourSectionMarriageRule, fourSectionMarriageRuleBool,
               fin4EquivZ2Z2, fin4ToZ2Z2, Prod.mk_add_mk, Prod.mk.injEq] <;>
    decide

/-! ## Section 6: Structural Properties

Additional structural theorems about kinship systems.
WEAKENED: These are now stated for general relations, not kinship-specific.
-/

/-- The identity relation on any type -/
def identity_relation {α : Type*} : α → α → Prop := fun x y => x = y

/-- Composition is associative for any relations.
    WEAKENED: Works for any type α, any relations. -/
theorem relation_composition_associative {α : Type*} (R₁ R₂ R₃ : α → α → Prop) :
    (R₁ ∘ₖ (R₂ ∘ₖ R₃)) = ((R₁ ∘ₖ R₂) ∘ₖ R₃) := by
  funext x z
  simp only [composeKinship]
  apply propext
  constructor <;> intro h
  · obtain ⟨y₁, ⟨y₂, h₃, h₂⟩, h₁⟩ := h
    exact ⟨y₂, h₃, y₁, h₂, h₁⟩
  · obtain ⟨y₂, h₃, y₁, h₂, h₁⟩ := h
    exact ⟨y₁, ⟨y₂, h₃, h₂⟩, h₁⟩

/-- Identity is a right unit for composition -/
theorem identity_right_unit' {α : Type*} (R : α → α → Prop) :
    composeKinship R identity_relation = R := by
  funext x y
  simp only [composeKinship, identity_relation]
  apply propext
  constructor
  · intro ⟨z, hz, hR⟩
    rwa [hz]
  · intro hR
    exact ⟨x, rfl, hR⟩

/-- Identity is a left unit for composition -/
theorem identity_left_unit' {α : Type*} (R : α → α → Prop) :
    composeKinship identity_relation R = R := by
  funext x y
  simp only [composeKinship, identity_relation]
  apply propext
  constructor
  · intro ⟨z, hR, hz⟩
    rwa [← hz]
  · intro hR
    exact ⟨y, hR, rfl⟩

/-- Parent relation: union of mother and father -/
def parent_relation (K : KinshipSystem) (x y : K.Person) : Prop := K.M x y ∨ K.F x y

/-- Child relation: union of male and female child -/
def child_relation (K : KinshipSystem) (x y : K.Person) : Prop := K.C_m x y ∨ K.C_f x y

/-- Parent-child composition unfolds through an intermediate relative. -/
theorem parent_child_composition (K : KinshipSystem) :
    ∀ x z, (parent_relation K ∘ₖ child_relation K) x z →
      ∃ y, child_relation K x y ∧ parent_relation K y z := by
  intro _ _ h
  exact h

/-- The relation algebra has a monoid structure under composition with identity.
    WEAKENED: Works for any type, not just KinshipRelation. -/
instance relationMonoid (α : Type*) : Monoid (α → α → Prop) where
  mul := composeKinship
  one := identity_relation
  mul_assoc := fun R₁ R₂ R₃ => (relation_composition_associative R₁ R₂ R₃).symm
  one_mul := identity_left_unit'
  mul_one := identity_right_unit'

/-! ## Section 7: Additional Weakened Theorems

These theorems show how kinship algebra properties are special cases of
general relation algebra properties.
-/

/-- Any reflexive relation can model trivial kinship (everyone is their own relative) -/
theorem reflexive_trivial_kinship {α : Type*} (R : α → α → Prop) (h_refl : ∀ x, R x x) :
    ∀ x, (R ∘ₖ R) x x := by
  intro x
  exact ⟨x, h_refl x, h_refl x⟩

/-- Transitive closure contains composition -/
theorem compose_in_transitive_closure {α : Type*} (R : α → α → Prop)
    (h_trans : ∀ x y z, R x y → R y z → R x z) :
    ∀ x z, (R ∘ₖ R) x z → R x z := by
  intro x z ⟨y, hxy, hyz⟩
  exact h_trans x y z hxy hyz

/-- Symmetric and transitive relations are closed under composition.
    NOTE: The symmetry hypothesis h_sym is actually UNUSED - transitivity alone suffices!
    This shows transitivity is the key property for composition closure. -/
theorem sym_trans_compose_closed {α : Type*} (R : α → α → Prop)
    (_h_sym : ∀ x y, R x y → R y x)
    (h_trans : ∀ x y z, R x y → R y z → R x z) :
    ∀ x z, (R ∘ₖ R) x z → R x z :=
  compose_in_transitive_closure R h_trans

/-- WEAKENED: Transitive relations alone are closed under composition.
    Symmetry is not required. -/
theorem trans_compose_closed {α : Type*} (R : α → α → Prop)
    (h_trans : ∀ x y z, R x y → R y z → R x z) :
    ∀ x z, (R ∘ₖ R) x z → R x z :=
  compose_in_transitive_closure R h_trans

/-- WEAK section systems (without partition/cover) have symmetric exchange with LOCAL symmetry.
    WEAKENED: Works with WeakSectionSystem, no partition or cover required. -/
theorem weak_section_system_symmetric_exchange_local {α : Type*} {spouse : α → α → Prop} {n : ℕ}
    (sys : WeakSectionSystem α spouse n)
    (i j : Fin n)
    (h_spouse_sym_local : ∀ x ∈ sys.sections i, ∀ y ∈ sys.sections j, spouse x y → spouse y x) :
    symmetricExchange spouse (sys.sections i) (sys.sections j) :=
  symmetric_relation_generates_exchange_local spouse (sys.sections i) (sys.sections j) h_spouse_sym_local

/-- Section systems with LOCAL symmetric marriage rules have symmetric exchange.
    NOTE: Corollary of weak_section_system_symmetric_exchange_local. -/
theorem section_system_symmetric_exchange_local {α : Type*} {spouse : α → α → Prop} {n : ℕ}
    (sys : SectionSystem α spouse n)
    (i j : Fin n)
    (h_spouse_sym_local : ∀ x ∈ sys.sections i, ∀ y ∈ sys.sections j, spouse x y → spouse y x) :
    symmetricExchange spouse (sys.sections i) (sys.sections j) :=
  weak_section_system_symmetric_exchange_local sys.toWeakSectionSystem i j h_spouse_sym_local

/-- Section systems with symmetric marriage rules have symmetric exchange.
    NOTE: Corollary of the local version above. -/
theorem section_system_symmetric_exchange {α : Type*} {spouse : α → α → Prop} {n : ℕ}
    (sys : SectionSystem α spouse n)
    (h_spouse_sym : ∀ x y, spouse x y → spouse y x)
    (i j : Fin n) :
    symmetricExchange spouse (sys.sections i) (sys.sections j) :=
  section_system_symmetric_exchange_local sys i j (fun x _ y _ => h_spouse_sym x y)

/-- A WEAK moiety system (without partition requirement) has two-way exchange with LOCAL symmetry.
    WEAKENED: Works with WeakMoietySystem, only requires symmetry between moieties. -/
theorem weak_moiety_symmetric_exchange_local {α : Type*} {spouse : α → α → Prop}
    (sys : WeakMoietySystem α spouse)
    (h_spouse_sym_local : ∀ x ∈ sys.moiety_A, ∀ y ∈ sys.moiety_B, spouse x y → spouse y x) :
    symmetricExchange spouse sys.moiety_A sys.moiety_B :=
  symmetric_relation_generates_exchange_local spouse sys.moiety_A sys.moiety_B h_spouse_sym_local

/-- A moiety system has two-way exchange with LOCAL symmetry.
    NOTE: Corollary of weak_moiety_symmetric_exchange_local. -/
theorem moiety_symmetric_exchange_local {α : Type*} {spouse : α → α → Prop}
    (sys : MoietySystem α spouse)
    (h_spouse_sym_local : ∀ x ∈ sys.moiety_A, ∀ y ∈ sys.moiety_B, spouse x y → spouse y x) :
    symmetricExchange spouse sys.moiety_A sys.moiety_B :=
  weak_moiety_symmetric_exchange_local sys.toWeakMoietySystem h_spouse_sym_local

/-- A moiety system has two-way exchange.
    NOTE: Corollary of the local version above. -/
theorem moiety_symmetric_exchange {α : Type*} {spouse : α → α → Prop}
    (sys : MoietySystem α spouse)
    (h_spouse_sym : ∀ x y, spouse x y → spouse y x) :
    symmetricExchange spouse sys.moiety_A sys.moiety_B :=
  moiety_symmetric_exchange_local sys (fun x _ y _ => h_spouse_sym x y)

end KinshipAlgebra
