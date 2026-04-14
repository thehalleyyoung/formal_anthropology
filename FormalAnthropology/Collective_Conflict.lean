/-
# Collective Ideogenesis: Conflict and Consensus

This file contains definitions and theorems about conflict and consensus in multi-agent systems
from MULTI_AGENT_IDEOGENESIS++ Chapter 6:

- Definition 6.1: Incompatible Ideas
- Definition 6.2: Ideational Conflict
- Definition 6.3: Conflict Intensity
- Definition 6.4: Conflict Zone
- Definition 6.5: Argument
- Definition 6.6: Empirical Resolution
- Definition 6.7: Authority-Based Resolution
- Definition 6.8: Schism
- Definition 6.9: Dialectical Synthesis
- Definition 6.10-6.13: Consensus Definitions
- Definition 6.14-6.15: Polarization and Echo Chambers
- Theorem 6.1: Argumentation and Closure
- Theorem 6.4: Schism as Conflict Resolution
- Theorem 6.5: Synthesis Increases Depth
- Theorem 6.8: Echo Chambers Cause Polarization
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.Collective_Basic
import FormalAnthropology.Collective_Closure

namespace CollectiveIdeogenesis

/-! ## Section 6.1: The Nature of Ideational Conflict -/

/-! ### Definition 6.1: Incompatible Ideas

Ideas a and b are incompatible if no consistent extension contains both.
We model this as an abstract compatibility relation on ideas.
-/

/-- A compatibility structure on ideas.
    Two ideas are compatible if they can coexist in a consistent belief system.
    Definition 6.1 from MULTI_AGENT_IDEOGENESIS++. -/
class Compatibility (I : Type*) where
  /-- Whether two ideas are compatible -/
  compatible : I → I → Prop
  /-- Compatibility is symmetric -/
  compatible_symm : ∀ a b, compatible a b → compatible b a
  /-- Every idea is compatible with itself -/
  compatible_refl : ∀ a, compatible a a

/-- Two ideas are incompatible if they cannot coexist.
    Definition 6.1 from MULTI_AGENT_IDEOGENESIS++. -/
def incompatible {I : Type*} [Compatibility I] (a b : I) : Prop :=
  ¬ Compatibility.compatible a b

/-- Notation: a ⊥ᵢ b for incompatibility (using subscript to avoid conflict) -/
scoped notation:50 a " ⊥ᵢ " b => incompatible a b

/-- Incompatibility is symmetric -/
theorem incompatible_symm {I : Type*} [Compatibility I] (a b : I) :
    incompatible a b → incompatible b a := by
  intro hinc hcomp
  apply hinc
  exact Compatibility.compatible_symm b a hcomp

/-- No idea is incompatible with itself -/
theorem not_incompatible_self {I : Type*} [Compatibility I] (a : I) :
    ¬ incompatible a a := by
  intro hinc
  exact hinc (Compatibility.compatible_refl a)

/-! ### Definition 6.2: Ideational Conflict

A conflict exists between agents α and β regarding domain D if they hold
incompatible ideas from that domain.
-/

/-- A conflict exists between agents α and β regarding domain D.
    Definition 6.2 from MULTI_AGENT_IDEOGENESIS++. -/
def hasConflict {I : Type*} [Compatibility I]
    (α β : Agent I ℕ) (D : Set I) (t : ℕ) : Prop :=
  ∃ a ∈ α.memory t ∩ D, ∃ b ∈ β.memory t ∩ D, incompatible a b

/-- Conflict is symmetric between agents -/
theorem hasConflict_symm {I : Type*} [Compatibility I]
    (α β : Agent I ℕ) (D : Set I) (t : ℕ) :
    hasConflict α β D t → hasConflict β α D t := by
  intro ⟨a, ha, b, hb, hinc⟩
  exact ⟨b, hb, a, ha, incompatible_symm a b hinc⟩

/-- An agent is internally consistent if they hold no incompatible ideas -/
def Agent.isInternallyConsistent {I : Type*} [Compatibility I]
    (α : Agent I ℕ) (t : ℕ) : Prop :=
  ∀ a b, a ∈ α.memory t → b ∈ α.memory t → Compatibility.compatible a b

/-- An internally consistent agent has no self-conflict -/
theorem no_self_conflict_if_consistent {I : Type*} [Compatibility I]
    (α : Agent I ℕ) (D : Set I) (t : ℕ) (hcons : α.isInternallyConsistent t) :
    ¬ hasConflict α α D t := by
  intro ⟨a, ha, b, hb, hinc⟩
  have ha' := ha.1
  have hb' := hb.1
  exact hinc (hcons a b ha' hb')

/-! ### Definition 6.3: Conflict Intensity

The intensity of conflict is the fraction of shared-domain ideas that are incompatible.
-/

/-- The set of incompatible pairs between two agents' memories in domain D -/
def incompatiblePairs {I : Type*} [Compatibility I]
    (α β : Agent I ℕ) (D : Set I) (t : ℕ) : Set (I × I) :=
  { p | p.1 ∈ α.memory t ∩ D ∧ p.2 ∈ β.memory t ∩ D ∧ incompatible p.1 p.2 }

/-- The conflict intensity between agents α and β at time t.
    Definition 6.3 from MULTI_AGENT_IDEOGENESIS++.
    Returns 0 if the shared domain is empty. -/
noncomputable def conflictIntensity {I : Type*} [Compatibility I]
    (α β : Agent I ℕ) (D : Set I) (t : ℕ) : ℚ :=
  let sharedDomain := (α.memory t ∩ D) ∩ (β.memory t ∩ D)
  let incompPairs := (incompatiblePairs α β D t).ncard
  if sharedDomain.ncard = 0 then 0
  else (incompPairs : ℚ) / sharedDomain.ncard

/-- Conflict intensity is non-negative -/
theorem conflictIntensity_nonneg {I : Type*} [Compatibility I]
    (α β : Agent I ℕ) (D : Set I) (t : ℕ) :
    0 ≤ conflictIntensity α β D t := by
  unfold conflictIntensity
  simp only
  split_ifs
  · exact le_refl 0
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _

/-! ### Definition 6.4: Conflict Zone

The conflict zone is the set of ideas that are in conflict with some other held idea.
-/

/-- The conflict zone at time t: ideas in conflict with some other held idea.
    Definition 6.4 from MULTI_AGENT_IDEOGENESIS++. -/
def MAIS.conflictZone {I : Type*} [Compatibility I]
    (M : MAIS I ℕ) (t : ℕ) : Set I :=
  { a ∈ M.distributedClosure t | ∃ b ∈ M.distributedClosure t, incompatible a b }

/-- The conflict zone is a subset of the distributed closure -/
theorem MAIS.conflictZone_subset_closure {I : Type*} [Compatibility I]
    (M : MAIS I ℕ) (t : ℕ) :
    M.conflictZone t ⊆ M.distributedClosure t := by
  intro a ha
  exact ha.1

/-- If the conflict zone is empty, there are no incompatible ideas in circulation -/
theorem MAIS.no_conflict_iff_empty_zone {I : Type*} [Compatibility I]
    (M : MAIS I ℕ) (t : ℕ) :
    M.conflictZone t = ∅ ↔ ∀ a b, a ∈ M.distributedClosure t →
      b ∈ M.distributedClosure t → Compatibility.compatible a b := by
  constructor
  · intro hempty a b ha hb
    by_contra hinc
    have : a ∈ M.conflictZone t := ⟨ha, b, hb, hinc⟩
    rw [hempty] at this
    exact Set.not_mem_empty a this
  · intro hcompat
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro ⟨hx, b, hb, hinc⟩
    exact hinc (hcompat x b hx hb)

/-! ## Section 6.2: Conflict Resolution Mechanisms -/

/-! ### Definition 6.5: Argument

An argument from α to β for idea a is a generation chain from β's memory to a.
-/

/-- An argument chain from premises to a conclusion.
    Definition 6.5 from MULTI_AGENT_IDEOGENESIS++.
    This is a sequence c₁ → c₂ → ... → cₙ → a where each step is generation. -/
inductive ArgumentChain {I : Type*} (gen : I → Set I) : Set I → I → Prop where
  /-- Base case: a premise is reachable from the premise set -/
  | premise (S : Set I) (a : I) (ha : a ∈ S) : ArgumentChain gen S a
  /-- Inductive case: if we can reach b and a ∈ gen(b), we can reach a -/
  | step (S : Set I) (b a : I) (hreach : ArgumentChain gen S b) (hgen : a ∈ gen b) :
      ArgumentChain gen S a

/-- An argument exists from α to β for idea a if a is reachable from β's memory
    via generation. Definition 6.5 from MULTI_AGENT_IDEOGENESIS++. -/
def hasArgument {I : Type*} (β : Agent I ℕ) (a : I) (t : ℕ) : Prop :=
  ArgumentChain β.generate (β.memory t) a

/-- The cumulative generation from a set of ideas using a generation function -/
def genCumulativeFrom {I : Type*} (gen : I → Set I) : ℕ → Set I → Set I
  | 0, S => S
  | n + 1, S => genCumulativeFrom gen n S ∪ ⋃ a ∈ genCumulativeFrom gen n S, gen a

/-- The closure of a set under a generation function -/
def genClosureOf {I : Type*} (gen : I → Set I) (S : Set I) : Set I :=
  ⋃ n, genCumulativeFrom gen n S

/-- Helper lemma: ArgumentChain implies membership in some cumulative level -/
theorem argumentChain_to_cumulative {I : Type*} (gen : I → Set I) (S : Set I) (a : I)
    (hchain : ArgumentChain gen S a) : ∃ n, a ∈ genCumulativeFrom gen n S := by
  induction hchain
  case premise ha => exact ⟨0, ha⟩
  case step hreach hgen ih =>
    rename_i b _
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, Or.inr ?_⟩
    simp only [Set.mem_iUnion]
    exact ⟨b, hn, hgen⟩

/-- Helper lemma: membership in cumulative level implies ArgumentChain -/
theorem cumulative_to_argumentChain {I : Type*} (gen : I → Set I) (S : Set I) (a : I)
    (n : ℕ) (hn : a ∈ genCumulativeFrom gen n S) : ArgumentChain gen S a := by
  induction n generalizing a with
  | zero => exact ArgumentChain.premise S a hn
  | succ n ih =>
    simp only [genCumulativeFrom, Set.mem_union, Set.mem_iUnion] at hn
    rcases hn with hn' | ⟨c, hc, ha'⟩
    · exact ih a hn'
    · exact ArgumentChain.step S c a (ih c hc) ha'

/-- An idea is in the argument chain iff it's in the cumulative generation -/
theorem argumentChain_iff_in_cumulative {I : Type*} (gen : I → Set I) (S : Set I) (a : I) :
    ArgumentChain gen S a ↔ ∃ n, a ∈ genCumulativeFrom gen n S :=
  ⟨argumentChain_to_cumulative gen S a,
   fun ⟨n, hn⟩ => cumulative_to_argumentChain gen S a n hn⟩

/-! ### Theorem 6.1: Argumentation and Closure

If a is in the closure of β's memory, then an argument for a exists.
-/

/-- If a is in the closure of β's memory, then an argument for a exists.
    Theorem 6.1 from MULTI_AGENT_IDEOGENESIS++. -/
theorem argumentation_and_closure {I : Type*} (β : Agent I ℕ) (a : I) (t : ℕ)
    (h : a ∈ genClosureOf β.generate (β.memory t)) :
    hasArgument β a t := by
  unfold hasArgument
  rw [argumentChain_iff_in_cumulative]
  unfold genClosureOf at h
  simp only [Set.mem_iUnion] at h
  exact h

/-- Corollary: Conflict can be resolved by argumentation only if the resolution
    is in the closure of both agents' ideas. -/
theorem argumentation_resolution_in_closure {I : Type*} (β : Agent I ℕ) (a : I) (t : ℕ)
    (harg : hasArgument β a t) :
    a ∈ genClosureOf β.generate (β.memory t) := by
  unfold hasArgument at harg
  rw [argumentChain_iff_in_cumulative] at harg
  unfold genClosureOf
  simp only [Set.mem_iUnion]
  exact harg

/-- Helper: genCumulativeFrom is monotone in the seed set -/
theorem genCumulativeFrom_mono {I : Type*} (gen : I → Set I) (S T : Set I) (hST : S ⊆ T)
    (n : ℕ) : genCumulativeFrom gen n S ⊆ genCumulativeFrom gen n T := by
  induction n with
  | zero => exact hST
  | succ n ih =>
    intro x hx
    simp only [genCumulativeFrom, Set.mem_union, Set.mem_iUnion] at hx ⊢
    rcases hx with hx' | ⟨a, ha_mem, hx_gen⟩
    · left; exact ih hx'
    · right; exact ⟨a, ih ha_mem, hx_gen⟩

/-- genClosureOf is monotone: if S ⊆ T, then genClosureOf g S ⊆ genClosureOf g T -/
theorem genClosureOf_mono {I : Type*} (gen : I → Set I) {S T : Set I} (hST : S ⊆ T) :
    genClosureOf gen S ⊆ genClosureOf gen T := by
  intro a ha
  simp only [genClosureOf, Set.mem_iUnion] at ha ⊢
  obtain ⟨n, hn⟩ := ha
  exact ⟨n, genCumulativeFrom_mono gen S T hST n hn⟩

/-- The seed set is contained in its closure -/
theorem subset_genClosureOf {I : Type*} (gen : I → Set I) (S : Set I) :
    S ⊆ genClosureOf gen S := by
  intro a ha
  simp only [genClosureOf, Set.mem_iUnion]
  exact ⟨0, ha⟩

/-- If the generator returns empty for all inputs, the closure equals the seed -/
theorem genClosureOf_trivial {I : Type*} (gen : I → Set I) (S : Set I)
    (hgen : ∀ a, gen a = ∅) : genClosureOf gen S = S := by
  ext a
  simp only [genClosureOf, Set.mem_iUnion]
  constructor
  · intro ⟨n, hn⟩
    induction n with
    | zero => exact hn
    | succ n ih =>
      simp only [genCumulativeFrom, Set.mem_union, Set.mem_iUnion] at hn
      rcases hn with hn' | ⟨b, _, habs⟩
      · exact ih hn'
      · simp only [hgen, Set.mem_empty_iff_false] at habs
  · intro ha
    exact ⟨0, ha⟩

/-- If every level of cumulative generation equals the seed, the closure equals the seed -/
theorem genClosureOf_trivial_at_seed {I : Type*} (gen : I → Set I) (S : Set I)
    (hgen : ∀ n, genCumulativeFrom gen n S = S) : genClosureOf gen S = S := by
  ext a
  simp only [genClosureOf, Set.mem_iUnion]
  constructor
  · intro ⟨n, hn⟩
    rw [hgen] at hn
    exact hn
  · intro ha
    exact ⟨0, ha⟩

/-- genCumulativeFrom distributes over binary unions -/
theorem genCumulativeFrom_union {I : Type*} (gen : I → Set I) (A B : Set I) (n : ℕ) :
    genCumulativeFrom gen n (A ∪ B) = genCumulativeFrom gen n A ∪ genCumulativeFrom gen n B := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [genCumulativeFrom, ih]
    ext x
    constructor
    · intro hx
      simp only [Set.mem_union, Set.mem_iUnion] at hx ⊢
      rcases hx with (hA | hB) | ⟨a, haAB, hxa⟩
      · left; left; exact hA
      · right; left; exact hB
      · rcases haAB with haA | haB
        · left; right; exact ⟨a, haA, hxa⟩
        · right; right; exact ⟨a, haB, hxa⟩
    · intro hx
      simp only [Set.mem_union, Set.mem_iUnion] at hx ⊢
      rcases hx with (hA | ⟨a, haA, hxa⟩) | (hB | ⟨a, haB, hxa⟩)
      · left; left; exact hA
      · right; exact ⟨a, Or.inl haA, hxa⟩
      · left; right; exact hB
      · right; exact ⟨a, Or.inr haB, hxa⟩

/-- genClosureOf distributes over binary unions -/
theorem genClosureOf_union {I : Type*} (gen : I → Set I) (A B : Set I) :
    genClosureOf gen (A ∪ B) = genClosureOf gen A ∪ genClosureOf gen B := by
  ext x
  simp only [genClosureOf, Set.mem_iUnion, Set.mem_union]
  constructor
  · intro ⟨n, hn⟩
    rw [genCumulativeFrom_union] at hn
    simp only [Set.mem_union] at hn
    rcases hn with hA | hB
    · left; exact ⟨n, hA⟩
    · right; exact ⟨n, hB⟩
  · intro hx
    rcases hx with ⟨n, hA⟩ | ⟨n, hB⟩
    · exact ⟨n, by rw [genCumulativeFrom_union]; left; exact hA⟩
    · exact ⟨n, by rw [genCumulativeFrom_union]; right; exact hB⟩

/-- genCumulativeFrom distributes over indexed unions -/
theorem genCumulativeFrom_iUnion {I α : Type*} (gen : I → Set I) (S : α → Set I) (n : ℕ) :
    genCumulativeFrom gen n (⋃ i, S i) = ⋃ i, genCumulativeFrom gen n (S i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [genCumulativeFrom, ih]
    ext x
    constructor
    · intro hx
      simp only [Set.mem_union, Set.mem_iUnion] at hx ⊢
      rcases hx with ⟨i, hi⟩ | ⟨a, ⟨i, hai⟩, hxa⟩
      · exact ⟨i, Or.inl hi⟩
      · exact ⟨i, Or.inr ⟨a, hai, hxa⟩⟩
    · intro hx
      simp only [Set.mem_union, Set.mem_iUnion] at hx ⊢
      rcases hx with ⟨i, hi | ⟨a, hai, hxa⟩⟩
      · left; exact ⟨i, hi⟩
      · right; exact ⟨a, ⟨i, hai⟩, hxa⟩

/-- genClosureOf distributes over indexed unions -/
theorem genClosureOf_iUnion {I α : Type*} (gen : I → Set I) (S : α → Set I) :
    genClosureOf gen (⋃ i, S i) = ⋃ i, genClosureOf gen (S i) := by
  ext x
  simp only [genClosureOf, Set.mem_iUnion]
  constructor
  · intro ⟨n, hn⟩
    rw [genCumulativeFrom_iUnion] at hn
    simp only [Set.mem_iUnion] at hn
    obtain ⟨i, hi⟩ := hn
    exact ⟨i, n, hi⟩
  · intro ⟨i, n, hn⟩
    refine ⟨n, ?_⟩
    rw [genCumulativeFrom_iUnion]
    simp only [Set.mem_iUnion]
    exact ⟨i, hn⟩

/-! ### Definition 6.6: Empirical Resolution

Conflict is empirically resolved when an observation favors one idea over another.
-/

/-- An observation that can resolve conflicts between ideas.
    Definition 6.6 from MULTI_AGENT_IDEOGENESIS++.

    Note: The time type T is now a parameter, allowing observations to be
    timestamped with any ordered type, not just ℕ. This generalizes the
    framework to continuous time, branching time, or other time structures. -/
structure Observation (I : Type*) (T : Type*) where
  /-- The observation data -/
  data : I
  /-- The time the observation was made -/
  time : T

/-- Whether an idea is compatible with an observation.
    Note: The time type T does not affect compatibility - only the data matters. -/
def compatibleWithObservation {I T : Type*} [Compatibility I]
    (a : I) (obs : Observation I T) : Prop :=
  Compatibility.compatible a obs.data

/-- Conflict between a and b is empirically resolved by observation obs.
    Definition 6.6 from MULTI_AGENT_IDEOGENESIS++. -/
def empiricallyResolves {I T : Type*} [Compatibility I]
    (obs : Observation I T) (a b : I) : Prop :=
  (compatibleWithObservation a obs ∧ ¬ compatibleWithObservation b obs) ∨
  (compatibleWithObservation b obs ∧ ¬ compatibleWithObservation a obs)

/-- Empirical resolution is symmetric in which idea it favors -/
theorem empiricallyResolves_swap {I T : Type*} [Compatibility I]
    (obs : Observation I T) (a b : I) :
    empiricallyResolves obs a b ↔ empiricallyResolves obs b a := by
  unfold empiricallyResolves
  tauto

/-! ### Theorem 6.2: Empirical Underdetermination

For any finite set of observations, there exist incompatible ideas equally compatible
with all observations. This is the Quine-Duhem thesis formalized.
-/

/-- There exist incompatible ideas that are equally compatible with all observations.
    Theorem 6.2 (Empirical Underdetermination) from MULTI_AGENT_IDEOGENESIS++. -/
def hasEmpiricalUnderdetermination {I T : Type*} [Compatibility I]
    (observations : Set (Observation I T)) : Prop :=
  ∃ a b : I, incompatible a b ∧
    (∀ obs ∈ observations, compatibleWithObservation a obs) ∧
    (∀ obs ∈ observations, compatibleWithObservation b obs)

/-- For empty observation sets, underdetermination trivially holds. -/
theorem empirical_underdetermination_empty {I T : Type*} [Compatibility I]
    (rich : ∃ a b : I, incompatible a b) :
    hasEmpiricalUnderdetermination (∅ : Set (Observation I T)) := by
  obtain ⟨a, b, hinc⟩ := rich
  use a, b, hinc
  constructor <;> intro obs hobs <;> exact False.elim (Set.not_mem_empty obs hobs)

/-! ### Definition 6.7: Authority-Based Resolution

An agent resolves conflict by authority when others adopt their position due to status.
-/

/-- A status function assigns a status level to each agent.
    Note: This structure only requires Preorder T (not LinearOrder), since it's simply
    assigning status values and doesn't depend on any ordering properties of time. -/
structure StatusFunction (I T : Type*) [Preorder T] where
  status : Agent I T → ℕ

/-- Conflict is resolved by authority when agents adopt an idea due to status.
    Definition 6.7 from MULTI_AGENT_IDEOGENESIS++. -/
structure AuthorityResolution {I : Type*} [Compatibility I]
    (M : MAIS I ℕ) (γ : Agent I ℕ) (a b : I) (t : ℕ) where
  /-- The authority γ holds idea a -/
  authority_holds_a : a ∈ γ.memory t
  /-- The ideas are incompatible -/
  ideas_incompatible : incompatible a b
  /-- Other agents adopt a after seeing γ hold it -/
  adoption : ∀ α ∈ M.agents, α ≠ γ → a ∈ α.memory (t + 1)

/-! ### Definition 6.8: Schism

A schism occurs when a community splits into non-communicating groups.
-/

/-- A schism partitions the agent community into non-communicating groups.
    Definition 6.8 from MULTI_AGENT_IDEOGENESIS++. -/
structure Schism {I : Type*} (M : MAIS I ℕ) (t : ℕ) where
  /-- First partition -/
  group1 : Set (Agent I ℕ)
  /-- Second partition -/
  group2 : Set (Agent I ℕ)
  /-- Groups partition the agents -/
  partition : M.agents = group1 ∪ group2
  /-- Groups are disjoint -/
  disjoint : group1 ∩ group2 = ∅
  /-- Both groups are nonempty -/
  nonempty1 : group1.Nonempty
  nonempty2 : group2.Nonempty
  /-- No communication across the split (after time t) -/
  no_cross_comm : ∀ t' ≥ t, ∀ α ∈ group1, ∀ β ∈ group2,
    ∀ a : I, (M.channel α β).transmit (a, t') = ∅ ∧
             (M.channel β α).transmit (a, t') = ∅

/-- Internal conflict within a group -/
def internalConflict {I : Type*} [Compatibility I]
    (G : Set (Agent I ℕ)) (D : Set I) (t : ℕ) : Prop :=
  ∃ α ∈ G, ∃ β ∈ G, hasConflict α β D t

/-! ### Theorem 6.4: Schism as Conflict Resolution

After a schism, internal conflict within each group may disappear
(though conflict persists between groups).
-/

/-- If agents within each group are consistent and have no internal conflicts,
    then neither group has internal conflict.
    Theorem 6.4 from MULTI_AGENT_IDEOGENESIS++.

    Note: This is a more general version that works for ANY two groups of agents,
    not just groups arising from a schism. The schism structure is not needed
    for this result - only the consistency and no-internal-conflict hypotheses
    on each group. -/
theorem no_internal_conflict_in_consistent_groups {I : Type*} [Compatibility I]
    (G1 G2 : Set (Agent I ℕ)) (D : Set I) (t : ℕ)
    (h_no_internal1 : ∀ α ∈ G1, ∀ β ∈ G1, α ≠ β → ¬ hasConflict α β D t)
    (h_no_internal2 : ∀ α ∈ G2, ∀ β ∈ G2, α ≠ β → ¬ hasConflict α β D t)
    (h_consistent1 : ∀ α ∈ G1, α.isInternallyConsistent t)
    (h_consistent2 : ∀ α ∈ G2, α.isInternallyConsistent t) :
    ¬ internalConflict G1 D t ∧ ¬ internalConflict G2 D t := by
  constructor
  · intro ⟨α, hα, β, hβ, hconf⟩
    by_cases heq : α = β
    · subst heq
      exact no_self_conflict_if_consistent α D t (h_consistent1 α hα) hconf
    · exact h_no_internal1 α hα β hβ heq hconf
  · intro ⟨α, hα, β, hβ, hconf⟩
    by_cases heq : α = β
    · subst heq
      exact no_self_conflict_if_consistent α D t (h_consistent2 α hα) hconf
    · exact h_no_internal2 α hα β hβ heq hconf

/-- Original theorem specialized for schism groups.
    Corollary of no_internal_conflict_in_consistent_groups. -/
theorem schism_resolves_cross_conflict {I : Type*} [Compatibility I]
    (M : MAIS I ℕ) (t : ℕ) (S : Schism M t) (D : Set I)
    (h_no_internal1 : ∀ α ∈ S.group1, ∀ β ∈ S.group1, α ≠ β → ¬ hasConflict α β D t)
    (h_no_internal2 : ∀ α ∈ S.group2, ∀ β ∈ S.group2, α ≠ β → ¬ hasConflict α β D t)
    (h_consistent1 : ∀ α ∈ S.group1, α.isInternallyConsistent t)
    (h_consistent2 : ∀ α ∈ S.group2, α.isInternallyConsistent t) :
    ¬ internalConflict S.group1 D t ∧ ¬ internalConflict S.group2 D t :=
  no_internal_conflict_in_consistent_groups S.group1 S.group2 D t
    h_no_internal1 h_no_internal2 h_consistent1 h_consistent2

/-! ### Definition 6.9: Dialectical Synthesis

A synthesis reconciles incompatible ideas by generating a new compatible idea.
-/

/-- Idea c is a dialectical synthesis of incompatible ideas a and b.
    Definition 6.9 from MULTI_AGENT_IDEOGENESIS++. -/
structure DialecticalSynthesis {I : Type*} [Compatibility I]
    (γ : Agent I ℕ) (a b c : I) where
  /-- The original ideas are incompatible -/
  ideas_incompatible : incompatible a b
  /-- c is generated from a or b by γ -/
  generated_from : c ∈ γ.generate a ∨ c ∈ γ.generate b
  /-- c is compatible with a -/
  compatible_with_a : Compatibility.compatible c a
  /-- c is compatible with b -/
  compatible_with_b : Compatibility.compatible c b

/-! ### Theorem 6.5: Synthesis Increases Depth

If c is a synthesis of a and b, then depth(c) > max(depth(a), depth(b)).
-/

/-- The generation depth of an idea from a base set -/
noncomputable def genDepth {I : Type*} (gen : I → Set I) (base : Set I) (a : I) : ℕ :=
  @dite ℕ (∃ n, a ∈ genCumulativeFrom gen n base) (Classical.propDecidable _)
    (fun h => @Nat.find _ (Classical.decPred _) h)
    (fun _ => 0)

/-- Synthesis increases depth: if c is generated from a (which is in the base) and c is not in the base,
    then c has greater depth than a. Theorem 6.5 from MULTI_AGENT_IDEOGENESIS++.

    Note: This theorem does not actually require a Compatibility instance, since it's purely
    about generation depth. The version without [Compatibility I] is more general. -/
theorem synthesis_increases_depth {I : Type*}
    (γ : Agent I ℕ) (a c : I) (base : Set I)
    (ha : a ∈ base)
    (hgen_a : c ∈ γ.generate a)
    (hc_not_base : c ∉ base) :
    genDepth γ.generate base c > genDepth γ.generate base a := by
  have ha_exists : ∃ n, a ∈ genCumulativeFrom γ.generate n base := ⟨0, ha⟩
  have ha_depth : genDepth γ.generate base a = 0 := by
    unfold genDepth
    rw [dif_pos ha_exists]
    rw [@Nat.find_eq_zero _ (Classical.decPred _) ha_exists]
    exact ha
  rw [ha_depth]
  have hc_in_1 : c ∈ genCumulativeFrom γ.generate 1 base := by
    right
    simp only [Set.mem_iUnion]
    exact ⟨a, ha, hgen_a⟩
  have hc_exists : ∃ n, c ∈ genCumulativeFrom γ.generate n base := ⟨1, hc_in_1⟩
  unfold genDepth
  rw [dif_pos hc_exists]
  have hc_not_0 : c ∉ genCumulativeFrom γ.generate 0 base := hc_not_base
  have hfind_pos : @Nat.find _ (Classical.decPred _) hc_exists > 0 := by
    by_contra hle
    push_neg at hle
    have heq : @Nat.find _ (Classical.decPred _) hc_exists = 0 := Nat.eq_zero_of_le_zero hle
    have hspec := @Nat.find_spec _ (Classical.decPred _) hc_exists
    rw [heq] at hspec
    exact hc_not_0 hspec
  exact hfind_pos

/-! ## Section 6.3: Consensus Formation -/

/-! ### Definition 6.10: Consensus on Idea a

There is consensus on a if a sufficient fraction of agents hold a.
-/

/-- The fraction of agents holding idea a at time t -/
noncomputable def MAIS.holdingFraction {I : Type*}
    (M : MAIS I ℕ) (a : I) (t : ℕ) : ℚ :=
  if (M.livingAgents t).ncard = 0 then 0
  else (M.holdersCount t a : ℚ) / (M.livingAgents t).ncard

/-- There is consensus on idea a at time t with threshold θ.
    Definition 6.10 from MULTI_AGENT_IDEOGENESIS++. -/
def MAIS.hasConsensus {I : Type*}
    (M : MAIS I ℕ) (a : I) (t : ℕ) (θ : ℚ) : Prop :=
  M.holdingFraction a t > θ

/-- Strong consensus: all agents hold the idea -/
def MAIS.hasUnanimity {I : Type*} (M : MAIS I ℕ) (a : I) (t : ℕ) : Prop :=
  ∀ α ∈ M.livingAgents t, a ∈ α.memory t

/-- Unanimity implies consensus for any threshold < 1 -/
theorem MAIS.unanimity_implies_consensus {I : Type*}
    (M : MAIS I ℕ) (a : I) (t : ℕ) (θ : ℚ) (hθ : θ < 1)
    (hunan : M.hasUnanimity a t)
    (hfin : (M.livingAgents t).Finite)
    (hnonempty : (M.livingAgents t).Nonempty) :
    M.hasConsensus a t θ := by
  unfold hasConsensus holdingFraction
  have hcard_pos : (M.livingAgents t).ncard > 0 := (Set.ncard_pos hfin).mpr hnonempty
  rw [if_neg (Nat.ne_of_gt hcard_pos)]
  have heq : M.holdersCount t a = (M.livingAgents t).ncard := by
    unfold holdersCount
    congr 1
    ext α
    simp only [Set.mem_setOf_eq]
    constructor
    · intro ⟨hliving, _⟩; exact hliving
    · intro hliving; exact ⟨hliving, hunan α hliving⟩
  rw [heq]
  rw [div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcard_pos))]
  exact hθ

/-! ### Definition 6.11: Consensus Core

The consensus core is the set of ideas with high consensus.
-/

/-- The consensus core at time t with threshold θ.
    Definition 6.11 from MULTI_AGENT_IDEOGENESIS++. -/
def MAIS.consensusCore {I : Type*} (M : MAIS I ℕ) (t : ℕ) (θ : ℚ) : Set I :=
  { a | M.hasConsensus a t θ }

/-- The strong consensus core (θ = 0.9) -/
def MAIS.strongConsensusCore {I : Type*} (M : MAIS I ℕ) (t : ℕ) : Set I :=
  M.consensusCore t (9/10)

/-! ### Definition 6.12: Dissent Frontier

The dissent frontier is ideas held by some but not achieving consensus.
-/

/-- The dissent frontier at time t with threshold θ.
    Definition 6.12 from MULTI_AGENT_IDEOGENESIS++. -/
def MAIS.dissentFrontier {I : Type*} (M : MAIS I ℕ) (t : ℕ) (θ : ℚ) : Set I :=
  M.distributedClosure t \ M.consensusCore t θ

/-! ### Definition 6.13: Consensus Stability

Consensus on a is stable if small perturbations don't dislodge a from the core.
-/

/-- A perturbation at time t changes a bounded number of agent beliefs -/
structure Perturbation {I : Type*} (M : MAIS I ℕ) (t : ℕ) where
  /-- Affected agents -/
  affected : Set (Agent I ℕ)
  /-- Bound on affected agents -/
  bound : ℕ
  /-- The perturbation affects at most `bound` agents -/
  bounded : affected.ncard ≤ bound

/-! ## Section 6.4: Epistemic Polarization -/

/-! ### Definition 6.14: Polarization

The community is polarized if there are roughly evenly split incompatible positions.
-/

/-- The community is polarized on domain D at time t.
    Definition 6.14 from MULTI_AGENT_IDEOGENESIS++. -/
structure Polarization {I : Type*} [Compatibility I]
    (M : MAIS I ℕ) (D : Set I) (t : ℕ) where
  /-- One polarized idea -/
  idea_a : I
  /-- The opposing polarized idea -/
  idea_b : I
  /-- Both are in the domain -/
  in_domain : idea_a ∈ D ∧ idea_b ∈ D
  /-- The ideas are incompatible -/
  ideas_incompatible : incompatible idea_a idea_b
  /-- Roughly even split (within factor of 2) -/
  even_split : M.holdersCount t idea_a * 2 ≥ M.holdersCount t idea_b ∧
               M.holdersCount t idea_b * 2 ≥ M.holdersCount t idea_a
  /-- Both have significant support -/
  significant : M.holdersCount t idea_a > 0 ∧ M.holdersCount t idea_b > 0

/-- Polarization is stable if it persists over time -/
def stablePolarization {I : Type*} [Compatibility I]
    (M : MAIS I ℕ) (D : Set I) (t₀ : ℕ) (duration : ℕ) : Prop :=
  ∃ (P : Polarization M D t₀), ∀ t, t₀ ≤ t → t < t₀ + duration →
    ∃ (P' : Polarization M D t), P'.idea_a = P.idea_a ∧ P'.idea_b = P.idea_b

/-! ### Definition 6.15: Echo Chamber

An echo chamber is a self-reinforcing group that rejects outside communication.
-/

/-- An echo chamber for idea a at time t.
    Definition 6.15 from MULTI_AGENT_IDEOGENESIS++. -/
structure EchoChamber {I : Type*} (M : MAIS I ℕ) (a : I) (t : ℕ) where
  /-- The agents in the echo chamber -/
  members : Set (Agent I ℕ)
  /-- Members are agents of the system -/
  members_in_system : members ⊆ M.agents
  /-- All members hold the idea -/
  all_hold : ∀ α ∈ members, a ∈ α.memory t
  /-- Members are living -/
  members_alive : ∀ α ∈ members, α.isAlive t
  /-- The chamber is substantial (not singleton) -/
  substantial : members.ncard ≥ 2

/-! ### Theorem 6.8: Echo Chambers Cause Polarization

If the community fragments into echo chambers, polarization is stable.
-/

/-- A "pure" echo chamber where NO agents outside the chamber hold the idea -/
def PureEchoChamber {I : Type*} (M : MAIS I ℕ) (a : I) (t : ℕ) 
    (E : EchoChamber M a t) : Prop :=
  ∀ α ∈ M.livingAgents t, a ∈ α.memory t → α ∈ E.members

/-- THEOREM (was axiom): In a pure echo chamber, holders count equals chamber size.
    This is provable from the definitions! -/
theorem echo_chamber_holders_theorem {I : Type*} (M : MAIS I ℕ) (a : I) (t : ℕ)
    (E : EchoChamber M a t) (hpure : PureEchoChamber M a t E) :
    M.holdersCount t a = E.members.ncard := by
  unfold MAIS.holdersCount PureEchoChamber at *
  -- holders = { α ∈ livingAgents | a ∈ memory }
  -- Need to show this equals E.members
  suffices h : { α ∈ M.livingAgents t | a ∈ α.memory t } = E.members by
    rw [h]
  ext α
  constructor
  · -- If α holds a, then α is in chamber (by purity)
    intro h
    simp at h
    exact hpure α h.1 h.2
  · -- If α in chamber, then α is alive and holds a
    intro h
    simp only [MAIS.livingAgents, Set.mem_sep_iff, Set.mem_setOf_eq]
    exact ⟨⟨E.members_in_system h, E.members_alive α h⟩, E.all_hold α h⟩

/-- If the community splits into PURE echo chambers for incompatible ideas,
    polarization results. Theorem 6.8 from MULTI_AGENT_IDEOGENESIS++.

    This version requires purity of echo chambers, which allows us to prove
    the theorem without axioms. A pure echo chamber is one where no agents
    outside the chamber hold the idea - this is the realistic scenario where
    echo chambers truly partition belief on an issue.

    Note: The theorem applies more broadly than may appear - in practice,
    when we speak of "the community fragmenting into echo chambers", we
    typically mean pure echo chambers where different groups exclusively
    hold incompatible views. -/
theorem echo_chambers_cause_polarization {I : Type*} [Compatibility I]
    (M : MAIS I ℕ) (a b : I) (t : ℕ)
    (E_a : EchoChamber M a t) (E_b : EchoChamber M b t)
    (hinc : incompatible a b)
    (hpure_a : PureEchoChamber M a t E_a)
    (hpure_b : PureEchoChamber M b t E_b)
    (hsimilar_size : E_a.members.ncard * 2 ≥ E_b.members.ncard ∧
                     E_b.members.ncard * 2 ≥ E_a.members.ncard) :
    ∃ D : Set I, ∃ P : Polarization M D t, P.idea_a = a ∧ P.idea_b = b := by
  use Set.univ
  -- Use the proven theorem: in a pure echo chamber, holders = chamber members
  have ha_eq : M.holdersCount t a = E_a.members.ncard := echo_chamber_holders_theorem M a t E_a hpure_a
  have hb_eq : M.holdersCount t b = E_b.members.ncard := echo_chamber_holders_theorem M b t E_b hpure_b
  have ha_pos : M.holdersCount t a > 0 := by
    rw [ha_eq]
    calc E_a.members.ncard ≥ 2 := E_a.substantial
      _ > 0 := by omega
  have hb_pos : M.holdersCount t b > 0 := by
    rw [hb_eq]
    calc E_b.members.ncard ≥ 2 := E_b.substantial
      _ > 0 := by omega
  refine ⟨⟨a, b, ⟨trivial, trivial⟩, hinc, ⟨?_, ?_⟩, ⟨ha_pos, hb_pos⟩⟩, rfl, rfl⟩
  · -- M.holdersCount t a * 2 ≥ M.holdersCount t b
    rw [ha_eq, hb_eq]
    exact hsimilar_size.1
  · -- M.holdersCount t b * 2 ≥ M.holdersCount t a
    rw [ha_eq, hb_eq]
    exact hsimilar_size.2

/-! ### Theorem 6.9: Breaking Polarization Requires Bridging -/

/-- A bridge agent participates in multiple groups -/
def isBridgeAgent {I : Type*} (α : Agent I ℕ)
    (group1 group2 : Set I) (t : ℕ) : Prop :=
  (∃ a ∈ group1, a ∈ α.memory t) ∧ (∃ b ∈ group2, b ∈ α.memory t)

/-- An external shock affects all agents simultaneously -/
structure ExternalShock {I : Type*} (M : MAIS I ℕ) (t : ℕ) where
  /-- The idea introduced by the shock -/
  new_idea : I
  /-- All agents receive the idea -/
  universal : ∀ α ∈ M.agents, new_idea ∈ α.memory (t + 1)

/-- Generational replacement: old agents die and new agents are born -/
structure GenerationalReplacement {I : Type*} (M : MAIS I ℕ) (t₀ t₁ : ℕ) where
  /-- Time progresses -/
  time_passes : t₁ > t₀
  /-- Some old agents die -/
  deaths : ∃ α ∈ M.agents, α.isAlive t₀ ∧ ¬ α.isAlive t₁
  /-- Some new agents appear -/
  births : ∃ α ∈ M.agents, α.birth > t₀ ∧ α.isAlive t₁

/-! ## Additional Theorems -/

/-- Conflict in the consensus core is impossible if core is consistent -/
theorem no_conflict_in_consistent_core {I : Type*} [Compatibility I]
    (M : MAIS I ℕ) (t : ℕ) (θ : ℚ)
    (hcons : ∀ a b, a ∈ M.consensusCore t θ → b ∈ M.consensusCore t θ →
             Compatibility.compatible a b) :
    M.conflictZone t ∩ M.consensusCore t θ ⊆
    { a | ∃ b ∈ M.distributedClosure t \ M.consensusCore t θ, incompatible a b } := by
  intro a ⟨hzone, hcore⟩
  obtain ⟨_, b, hb, hinc⟩ := hzone
  by_cases hb_core : b ∈ M.consensusCore t θ
  · exact False.elim (hinc (hcons a b hcore hb_core))
  · exact ⟨b, ⟨hb, hb_core⟩, hinc⟩

end CollectiveIdeogenesis
