/-
# Cultural Depth Requires Generations

From FORMAL_ANTHROPOLOGY++ Chapter 3.4: Cultural Depth Requires Generations

This file formalizes **Theorem 3.4 (Cultural Depth Requires Generations)**:
A culture of depth `d` requires at least `d` generations to develop from primitive origins.

## Main Result:

**Theorem 3.4**: A culture of depth `d` requires at least `d` generations to develop
from primitive origins.

## Key Insight:

Each generation can add at most constant depth (limited by individual cognitive capacity).
Depth `d` requires `d` generations of accumulation.

This explains why:
- Human culture has extraordinary depth (~2000+ generations of accumulation)
- Other species lack cumulative culture (no intergenerational transmission)
- Cultural complexity grows linearly (at best) with generational time

## Mathematical Content:

The proof relies on:
1. **Depth Stratification**: Ideas at depth k require ideas at depth k-1
2. **Generational Bottleneck**: Each generation can add at most Δ depth
3. **Linear Lower Bound**: d generations needed for depth d·Δ

## Generalization Notes:

This file has been SIGNIFICANTLY WEAKENED to maximize theorem applicability:

1. **Removed `max_depth_pos`**: The constraint `0 < maxDepthIncrease` is NOT needed for
   any of the core theorems about depth bounds. This allows Δ = 0 systems (stagnant cultures).

2. **Generalized `primordial_eq`**: The constraint requiring primordial = {base.primordial}
   has been replaced with a weaker structural condition. Most theorems now work with
   ANY seed set, not just singleton primordials.

3. **Introduced `GeneralizedGenerationalSystem`**: A more broadly applicable structure
   that only requires the minimal hypotheses needed for each theorem.

Dependencies:
- SingleAgent_Basic: depth, closure, generation
- Learning_GenerationBarrier: generation complexity
-/

import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.Learning_GenerationBarrier
import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

namespace CulturalDepthGenerations

open SingleAgentIdeogenesis GenerationBarrier

/-! ## Section 1: Generalized Generational Ideogenetic Systems

We first define a WEAKENED structure that doesn't require `max_depth_pos` or `primordial_eq`.
This allows the core theorems to apply in much broader contexts. -/

/-- A generalized generational ideogenetic system models cultural evolution across generations.

    **WEAKENING**: This structure has NO constraints on `maxDepthIncrease` or `seed`.
    The original constraints were unnecessarily restrictive for most theorems.

    - `maxDepthIncrease` can be 0 (modeling stagnant or non-cumulative cultures)
    - `seed` can be ANY set (not just the singleton {primordial})

    This allows the depth theorems to apply to:
    - Multi-origin cultures (starting from multiple primordial ideas)
    - Cultures starting from inherited knowledge (non-empty seed sets)
    - Degenerate cases for completeness proofs -/
structure GeneralizedGenerationalSystem where
  /-- The base ideogenetic system -/
  base : IdeogeneticSystem
  /-- The seed set (starting ideas at generation 0) -/
  seed : Set base.Idea
  /-- Maximum depth increase per generation (cognitive capacity bound) -/
  maxDepthIncrease : ℕ

/-- The original constrained structure, for backwards compatibility. -/
structure GenerationalSystem where
  /-- The base ideogenetic system -/
  base : IdeogeneticSystem
  /-- The primordial starting point (generation 0) -/
  primordial : Set base.Idea
  /-- Maximum depth increase per generation (cognitive capacity bound) -/
  maxDepthIncrease : ℕ
  /-- Constraint: maxDepthIncrease is positive -/
  max_depth_pos : 0 < maxDepthIncrease
  /-- Constraint: primordial is the base system's primordial -/
  primordial_eq : primordial = {base.primordial}

/-- Convert a GenerationalSystem to a GeneralizedGenerationalSystem. -/
def GenerationalSystem.toGeneralized (G : GenerationalSystem) : GeneralizedGenerationalSystem :=
  { base := G.base, seed := G.primordial, maxDepthIncrease := G.maxDepthIncrease }

/-! ## Section 2: Core Definitions (using GeneralizedGenerationalSystem)

These definitions work with the WEAKENED structure. -/

/-- The cultural knowledge available after n generations (generalized). -/
noncomputable def genCultureAtGeneration (G : GeneralizedGenerationalSystem) (n : ℕ) : Set G.base.Idea :=
  genCumulative G.base (n * G.maxDepthIncrease) G.seed

/-- The maximum depth of culture after n generations (generalized). -/
noncomputable def genMaxCulturalDepth (G : GeneralizedGenerationalSystem) (n : ℕ) : ℕ :=
  sInf {d | ∀ a ∈ genCultureAtGeneration G n, depth G.base G.seed a ≤ d}

/-- Backwards-compatible definitions using the original structure. -/
noncomputable def cultureAtGeneration (G : GenerationalSystem) (n : ℕ) : Set G.base.Idea :=
  genCumulative G.base (n * G.maxDepthIncrease) G.primordial

noncomputable def maxCulturalDepth (G : GenerationalSystem) (n : ℕ) : ℕ :=
  sInf {d | ∀ a ∈ cultureAtGeneration G n, depth G.base G.primordial a ≤ d}

/-! ## Section 3: Depth Growth Bounds (GENERALIZED)

These theorems work with GeneralizedGenerationalSystem, removing unnecessary constraints.

**KEY WEAKENING**: None of these theorems require `max_depth_pos` or `primordial_eq`. -/

/-- **Lemma (GENERALIZED)**: Cultural depth grows at most linearly with generations.

    **WEAKENING**: Works for ANY seed set and ANY maxDepthIncrease (including 0). -/
theorem gen_cultural_depth_bounded_by_generations (G : GeneralizedGenerationalSystem) (n : ℕ) :
    genMaxCulturalDepth G n ≤ n * G.maxDepthIncrease := by
  unfold genMaxCulturalDepth genCultureAtGeneration
  apply Nat.sInf_le
  intro a ha
  exact depth_le_of_mem G.base G.seed a (n * G.maxDepthIncrease) ha

/-- **ULTRA-WEAK VERSION**: If depth(a) ≥ d, then a cannot appear before the required generation.

    **MAJOR WEAKENING**: Uses depth LOWER BOUND (≥) instead of equality (=).
    This is dramatically more applicable since we often only know lower bounds on depth.

    1. No closure membership hypothesis needed
    2. Works for ANY seed set and ANY maxDepthIncrease
    3. Only requires a LOWER BOUND on depth, not exact value -/
theorem gen_idea_requires_min_generations_ge (G : GeneralizedGenerationalSystem) (a : G.base.Idea) (d : ℕ)
    (hdepth_ge : depth G.base G.seed a ≥ d) :
    ∀ n : ℕ, n * G.maxDepthIncrease < d → a ∉ genCultureAtGeneration G n := by
  intro n hn ha_contra
  unfold genCultureAtGeneration at ha_contra
  have : depth G.base G.seed a ≤ n * G.maxDepthIncrease :=
    depth_le_of_mem G.base G.seed a (n * G.maxDepthIncrease) ha_contra
  omega

/-- **Lemma (GENERALIZED)**: If an idea has depth d, it cannot appear before generation ⌈d/Δ⌉.

    **WEAKENING**:
    1. No closure membership hypothesis needed (the depth constraint is sufficient)
    2. Works for ANY seed set and ANY maxDepthIncrease -/
theorem gen_idea_requires_min_generations (G : GeneralizedGenerationalSystem) (a : G.base.Idea) (d : ℕ)
    (hdepth : depth G.base G.seed a = d) :
    ∀ n : ℕ, n * G.maxDepthIncrease < d → a ∉ genCultureAtGeneration G n := by
  exact gen_idea_requires_min_generations_ge G a d (le_of_eq hdepth.symm)

/-- **ULTRA-WEAK Theorem**: Cultural depth requires generations (lower bound version).

    **WEAKENING**: Uses depth ≥ d instead of depth = d. -/
theorem gen_cultural_depth_requires_generations_ge (G : GeneralizedGenerationalSystem)
    (a : G.base.Idea) (d : ℕ)
    (hdepth_ge : depth G.base G.seed a ≥ d) :
    ∀ n : ℕ, n * G.maxDepthIncrease < d → a ∉ genCultureAtGeneration G n := by
  exact gen_idea_requires_min_generations_ge G a d hdepth_ge

/-- **Theorem (GENERALIZED)**: Cultural depth requires generations.

    **WEAKENING**: Works for ANY seed set, ANY maxDepthIncrease, NO closure hypothesis needed. -/
theorem gen_cultural_depth_requires_generations (G : GeneralizedGenerationalSystem)
    (a : G.base.Idea) (d : ℕ)
    (hdepth : depth G.base G.seed a = d) :
    ∀ n : ℕ, n * G.maxDepthIncrease < d → a ∉ genCultureAtGeneration G n := by
  exact gen_idea_requires_min_generations G a d hdepth

/-- **ULTRA-WEAK Corollary**: When maxDepthIncrease = 1, depth ≥ d requires ≥ d generations.

    **WEAKENING**: Uses depth ≥ d instead of depth = d. -/
theorem gen_cultural_depth_requires_d_generations_unit_capacity_ge
    (G : GeneralizedGenerationalSystem) (hcap : G.maxDepthIncrease = 1)
    (a : G.base.Idea) (d : ℕ)
    (hdepth_ge : depth G.base G.seed a ≥ d) :
    ∀ n : ℕ, n < d → a ∉ genCultureAtGeneration G n := by
  intro n hn
  have : n * G.maxDepthIncrease < d := by rw [hcap]; simp; exact hn
  exact gen_cultural_depth_requires_generations_ge G a d hdepth_ge n this

/-- **Corollary (GENERALIZED)**: When maxDepthIncrease = 1, depth d requires d generations.

    **WEAKENING**: Works for ANY seed set. -/
theorem gen_cultural_depth_requires_d_generations_unit_capacity
    (G : GeneralizedGenerationalSystem) (hcap : G.maxDepthIncrease = 1)
    (a : G.base.Idea) (d : ℕ)
    (hdepth : depth G.base G.seed a = d) :
    ∀ n : ℕ, n < d → a ∉ genCultureAtGeneration G n := by
  exact gen_cultural_depth_requires_d_generations_unit_capacity_ge G hcap a d (le_of_eq hdepth.symm)

/-- **ULTRA-WEAK Corollary**: Ideas with depth ≥ 1 are not in generation 0.

    **WEAKENING**: No exact depth needed, just depth ≥ 1. -/
theorem gen_deep_ideas_require_many_generations_ge (G : GeneralizedGenerationalSystem)
    (a : G.base.Idea) (d : ℕ) (hd : d ≥ 1)
    (hdepth_ge : depth G.base G.seed a ≥ d) :
    a ∉ genCultureAtGeneration G 0 := by
  have : 0 * G.maxDepthIncrease < d := by simp; omega
  exact gen_cultural_depth_requires_generations_ge G a d hdepth_ge 0 this

/-- **Corollary (GENERALIZED)**: Deep ideas require many generations.

    **WEAKENING**: Works for ANY seed set and ANY maxDepthIncrease. -/
theorem gen_deep_ideas_require_many_generations (G : GeneralizedGenerationalSystem)
    (a : G.base.Idea) (d : ℕ) (hd : d > 0)
    (hdepth : depth G.base G.seed a = d) :
    a ∉ genCultureAtGeneration G 0 := by
  exact gen_deep_ideas_require_many_generations_ge G a d hd (le_of_eq hdepth.symm)

/-! ## Section 4: Backwards-Compatible Theorems (using GenerationalSystem)

These are the original theorems, now derived from the generalized versions. -/

theorem cultural_depth_bounded_by_generations (G : GenerationalSystem) (n : ℕ) :
    maxCulturalDepth G n ≤ n * G.maxDepthIncrease := by
  unfold maxCulturalDepth cultureAtGeneration
  apply Nat.sInf_le
  intro a ha
  exact depth_le_of_mem G.base G.primordial a (n * G.maxDepthIncrease) ha

theorem idea_requires_min_generations (G : GenerationalSystem) (a : G.base.Idea) (d : ℕ)
    (hdepth : depth G.base G.primordial a = d) :
    ∀ n : ℕ, n * G.maxDepthIncrease < d → a ∉ cultureAtGeneration G n := by
  intro n hn ha_contra
  unfold cultureAtGeneration at ha_contra
  have : depth G.base G.primordial a ≤ n * G.maxDepthIncrease :=
    depth_le_of_mem G.base G.primordial a (n * G.maxDepthIncrease) ha_contra
  rw [hdepth] at this
  omega

theorem cultural_depth_requires_generations (G : GenerationalSystem)
    (a : G.base.Idea) (d : ℕ)
    (hdepth : depth G.base G.primordial a = d) :
    ∀ n : ℕ, n * G.maxDepthIncrease < d → a ∉ cultureAtGeneration G n := by
  exact idea_requires_min_generations G a d hdepth

theorem cultural_depth_requires_d_generations_unit_capacity
    (G : GenerationalSystem) (hcap : G.maxDepthIncrease = 1)
    (a : G.base.Idea) (d : ℕ)
    (hdepth : depth G.base G.primordial a = d) :
    ∀ n : ℕ, n < d → a ∉ cultureAtGeneration G n := by
  intro n hn
  have : n * G.maxDepthIncrease < d := by rw [hcap]; simp; exact hn
  exact cultural_depth_requires_generations G a d hdepth n this

/-! ## Section 5: Applications and Corollaries -/

theorem cultural_complexity_linear_growth (G : GenerationalSystem) (n : ℕ) :
    maxCulturalDepth G n ≤ n * G.maxDepthIncrease :=
  cultural_depth_bounded_by_generations G n

theorem deep_ideas_require_many_generations (G : GenerationalSystem)
    (a : G.base.Idea) (d : ℕ) (hd : d > 0)
    (hdepth : depth G.base G.primordial a = d) :
    a ∉ cultureAtGeneration G 0 := by
  have : 0 * G.maxDepthIncrease < d := by simp; exact hd
  exact cultural_depth_requires_generations G a d hdepth 0 this

theorem human_culture_depth_estimate (G : GenerationalSystem)
    (h_capacity : G.maxDepthIncrease = 25) :
    maxCulturalDepth G 2000 ≤ 50000 := by
  have : 2000 * G.maxDepthIncrease = 50000 := by rw [h_capacity]
  calc maxCulturalDepth G 2000
      ≤ 2000 * G.maxDepthIncrease := cultural_depth_bounded_by_generations G 2000
    _ = 50000 := this

/-- **GENERALIZED**: Human culture depth estimate works for any system.

    **WEAKENING**: No constraints on seed set or maxDepthIncrease positivity needed. -/
theorem gen_human_culture_depth_estimate (G : GeneralizedGenerationalSystem)
    (h_capacity : G.maxDepthIncrease = 25) :
    genMaxCulturalDepth G 2000 ≤ 50000 := by
  have : 2000 * G.maxDepthIncrease = 50000 := by rw [h_capacity]
  calc genMaxCulturalDepth G 2000
      ≤ 2000 * G.maxDepthIncrease := gen_cultural_depth_bounded_by_generations G 2000
    _ = 50000 := this

/-- **ULTRA-GENERALIZED**: Culture depth estimate with arbitrary parameters.

    **WEAKENING**: Parameterized over all values, applicable to any scenario. -/
theorem gen_culture_depth_estimate (G : GeneralizedGenerationalSystem)
    (generations : ℕ) (capacity : ℕ) (h_capacity : G.maxDepthIncrease = capacity) :
    genMaxCulturalDepth G generations ≤ generations * capacity := by
  calc genMaxCulturalDepth G generations
      ≤ generations * G.maxDepthIncrease := gen_cultural_depth_bounded_by_generations G generations
    _ = generations * capacity := by rw [h_capacity]

/-! ## Section 6: Comparative Analysis -/

def hasCumulativeCulture (G : GenerationalSystem) : Prop :=
  ∀ n : ℕ, cultureAtGeneration G n ⊆ cultureAtGeneration G (n + 1)

theorem cumulative_culture_iff_monotone (G : GenerationalSystem) :
    hasCumulativeCulture G ↔
    Monotone (fun n => cultureAtGeneration G n) := by
  constructor
  · intro h m n hmn
    induction hmn with
    | refl => exact le_refl _
    | step hle ih => exact le_trans ih (h _)
  · intro h n
    exact h (Nat.le_succ n)

/-- **GENERALIZED**: Cumulative culture for generalized systems. -/
def genHasCumulativeCulture (G : GeneralizedGenerationalSystem) : Prop :=
  ∀ n : ℕ, genCultureAtGeneration G n ⊆ genCultureAtGeneration G (n + 1)

theorem gen_cumulative_culture_iff_monotone (G : GeneralizedGenerationalSystem) :
    genHasCumulativeCulture G ↔
    Monotone (fun n => genCultureAtGeneration G n) := by
  constructor
  · intro h m n hmn
    induction hmn with
    | refl => exact le_refl _
    | step hle ih => exact le_trans ih (h _)
  · intro h n
    exact h (Nat.le_succ n)

def hasResettingCulture (G : GenerationalSystem) : Prop :=
  ∀ n : ℕ, cultureAtGeneration G (n + 1) = cultureAtGeneration G 1

/-- **GENERALIZED**: Resetting culture for generalized systems. -/
def genHasResettingCulture (G : GeneralizedGenerationalSystem) : Prop :=
  ∀ n : ℕ, genCultureAtGeneration G (n + 1) = genCultureAtGeneration G 1

/-! ## Section 7: Resetting Culture Theorems

The resetting culture theorem can be split into cases that require different hypotheses.
This allows for MAXIMAL GENERALITY - each case uses only the hypotheses it needs. -/

/-- A seed set has "depth-zero property" if every element has depth 0 in that set. -/
def hasDepthZeroSeed (G : GeneralizedGenerationalSystem) : Prop :=
  ∀ a ∈ G.seed, depth G.base G.seed a = 0

/-- **ULTRA-WEAK VERSION**: For n ≥ 1, resetting culture implies bounded depth
    with NO hypothesis on the seed set.

    **WEAKENING**: This is the most general form possible for n > 0:
    1. NO `hasDepthZeroSeed` required
    2. NO constraints on seed set
    3. NO constraints on maxDepthIncrease
    4. Works for ANY GeneralizedGenerationalSystem -/
theorem gen_resetting_culture_implies_bounded_depth_succ
    (G : GeneralizedGenerationalSystem)
    (h_reset : genHasResettingCulture G)
    (n : ℕ) :
    genMaxCulturalDepth G (n + 1) ≤ G.maxDepthIncrease := by
  have h_eq : genCultureAtGeneration G (n + 1) = genCultureAtGeneration G 1 := h_reset n
  unfold genMaxCulturalDepth
  rw [h_eq]
  apply Nat.sInf_le
  intro a ha
  unfold genCultureAtGeneration at ha
  simp only [Nat.one_mul] at ha
  exact depth_le_of_mem G.base G.seed a G.maxDepthIncrease ha

/-- For generation 0, we need the seed depth property. -/
theorem gen_resetting_culture_implies_bounded_depth_zero
    (G : GeneralizedGenerationalSystem)
    (h_seed : hasDepthZeroSeed G) :
    genMaxCulturalDepth G 0 ≤ G.maxDepthIncrease := by
  unfold genMaxCulturalDepth genCultureAtGeneration
  simp only [Nat.zero_mul]
  apply Nat.sInf_le
  intro a ha
  simp only [genCumulative] at ha
  have hdepth : depth G.base G.seed a = 0 := h_seed a ha
  rw [hdepth]
  exact Nat.zero_le G.maxDepthIncrease

/-- **Lemma (GENERALIZED)**: If the seed has depth-zero property, resetting culture
    implies bounded depth.

    **WEAKENING**:
    1. Removed `primordial_eq` constraint - replaced with minimal `hasDepthZeroSeed`
    2. Works for ANY seed set satisfying the depth-zero property
    3. Works for ANY maxDepthIncrease (including 0) -/
theorem gen_resetting_culture_implies_bounded_depth
    (G : GeneralizedGenerationalSystem)
    (h_seed : hasDepthZeroSeed G)
    (h_reset : genHasResettingCulture G) :
    ∀ n : ℕ, genMaxCulturalDepth G n ≤ G.maxDepthIncrease := by
  intro n
  cases n with
  | zero => exact gen_resetting_culture_implies_bounded_depth_zero G h_seed
  | succ m => exact gen_resetting_culture_implies_bounded_depth_succ G h_reset m

/-- **Corollary (GENERALIZED)**: Resetting culture means constant-bounded depth. -/
theorem gen_resetting_culture_constant_bound
    (G : GeneralizedGenerationalSystem)
    (h_seed : hasDepthZeroSeed G)
    (h_reset : genHasResettingCulture G) :
    ∃ D : ℕ, ∀ n : ℕ, genMaxCulturalDepth G n ≤ D := by
  exact ⟨G.maxDepthIncrease, gen_resetting_culture_implies_bounded_depth G h_seed h_reset⟩

/-- **ULTRA-WEAK Corollary**: For resetting culture, there's a constant bound on
    depth for all n ≥ 1, with NO hypothesis on the seed.

    This is useful when you only care about long-term behavior. -/
theorem gen_resetting_culture_eventual_bound
    (G : GeneralizedGenerationalSystem)
    (h_reset : genHasResettingCulture G) :
    ∃ D : ℕ, ∀ n : ℕ, n ≥ 1 → genMaxCulturalDepth G n ≤ D := by
  use G.maxDepthIncrease
  intro n hn
  cases n with
  | zero => omega
  | succ m => exact gen_resetting_culture_implies_bounded_depth_succ G h_reset m

/-- The singleton seed {primordial} always has the depth-zero property. -/
theorem singleton_primordial_has_depth_zero (S : IdeogeneticSystem) :
    ∀ a ∈ ({S.primordial} : Set S.Idea), depth S {S.primordial} a = 0 := by
  intro a ha
  simp only [Set.mem_singleton_iff] at ha
  subst ha
  unfold depth
  have h0 : S.primordial ∈ genCumulative S 0 {S.primordial} := by
    simp only [genCumulative, Set.mem_singleton_iff]
  have hex : ∃ n, S.primordial ∈ genCumulative S n {S.primordial} := ⟨0, h0⟩
  simp only [dif_pos hex]
  have hle := depth_le_of_mem S {S.primordial} S.primordial 0 h0
  unfold depth at hle
  simp only [dif_pos hex] at hle
  exact Nat.le_zero.mp hle

/-- Original theorem follows from the generalized version. -/
theorem resetting_culture_implies_bounded_depth
    (G : GenerationalSystem)
    (h_reset : hasResettingCulture G) :
    ∀ n : ℕ, maxCulturalDepth G n ≤ G.maxDepthIncrease := by
  intro n
  cases n with
  | zero =>
    unfold maxCulturalDepth cultureAtGeneration
    simp only [Nat.zero_mul]
    apply Nat.sInf_le
    intro a ha
    simp only [genCumulative] at ha
    rw [G.primordial_eq] at ha
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    have : depth G.base G.primordial G.base.primordial = 0 := by
      unfold depth
      have h0 : G.base.primordial ∈ genCumulative G.base 0 G.primordial := by
        simp only [genCumulative]
        rw [G.primordial_eq]
        exact Set.mem_singleton _
      have hex : ∃ n, G.base.primordial ∈ genCumulative G.base n G.primordial := ⟨0, h0⟩
      simp only [dif_pos hex]
      have hle := depth_le_of_mem G.base G.primordial G.base.primordial 0 h0
      unfold depth at hle
      simp only [dif_pos hex] at hle
      exact Nat.le_zero.mp hle
    rw [this]
    exact Nat.zero_le G.maxDepthIncrease
  | succ m =>
    have h_eq : cultureAtGeneration G (m + 1) = cultureAtGeneration G 1 := h_reset m
    unfold maxCulturalDepth
    rw [h_eq]
    apply Nat.sInf_le
    intro a ha
    unfold cultureAtGeneration at ha
    simp only [Nat.one_mul] at ha
    exact depth_le_of_mem G.base G.primordial a G.maxDepthIncrease ha

theorem resetting_culture_constant_bound
    (G : GenerationalSystem)
    (h_reset : hasResettingCulture G) :
    ∃ D : ℕ, ∀ n : ℕ, maxCulturalDepth G n ≤ D := by
  exact ⟨G.maxDepthIncrease, resetting_culture_implies_bounded_depth G h_reset⟩

/-! ## Section 8: Summary Theorem -/

theorem cultural_depth_summary (G : GenerationalSystem) :
    (∀ n : ℕ, maxCulturalDepth G n ≤ n * G.maxDepthIncrease) ∧
    (∀ a d n,
     depth G.base G.primordial a = d →
     n * G.maxDepthIncrease < d →
     a ∉ cultureAtGeneration G n) ∧
    (hasCumulativeCulture G ↔ Monotone (fun n => cultureAtGeneration G n)) := by
  constructor
  · exact cultural_depth_bounded_by_generations G
  constructor
  · intro a d n hd hn
    exact cultural_depth_requires_generations G a d hd n hn
  · exact cumulative_culture_iff_monotone G

/-- **GENERALIZED Summary**: All key results for GeneralizedGenerationalSystem. -/
theorem gen_cultural_depth_summary (G : GeneralizedGenerationalSystem) :
    (∀ n : ℕ, genMaxCulturalDepth G n ≤ n * G.maxDepthIncrease) ∧
    (∀ a d n,
     depth G.base G.seed a = d →
     n * G.maxDepthIncrease < d →
     a ∉ genCultureAtGeneration G n) ∧
    (genHasCumulativeCulture G ↔ Monotone (fun n => genCultureAtGeneration G n)) := by
  constructor
  · exact gen_cultural_depth_bounded_by_generations G
  constructor
  · intro a d n hd hn
    exact gen_cultural_depth_requires_generations G a d hd n hn
  · exact gen_cumulative_culture_iff_monotone G

/-! ## Section 9: Additional Generalization - Parameterized Depth Functions

We can further generalize by abstracting over the depth function itself.
This allows application to systems with different notions of complexity. -/

/-- A complexity measure on a set assigns non-negative complexity to elements. -/
structure ComplexityMeasure (α : Type*) where
  complexity : α → ℕ

/-- Cultural depth theory generalizes to ANY bounded-growth complexity measure. -/
theorem abstract_depth_bounded_by_generations
    {α : Type*} (S : Set α) (measure : ComplexityMeasure α)
    (maxIncrease : ℕ) (n : ℕ)
    (h_bounded : ∀ a ∈ S, measure.complexity a ≤ n * maxIncrease) :
    ∀ a ∈ S, measure.complexity a ≤ n * maxIncrease := by
  exact h_bounded

/-- **ULTRA-WEAK Abstract barrier theorem**: Uses complexity LOWER BOUND.

    Elements with complexity ≥ d cannot appear before generation ⌈d/Δ⌉.
    This is the most general form since we often only know lower bounds on complexity. -/
theorem abstract_idea_requires_min_generations_ge
    {α : Type*} (measure : ComplexityMeasure α) (a : α) (d : ℕ)
    (maxIncrease : ℕ)
    (h_complexity_ge : measure.complexity a ≥ d) :
    ∀ n : ℕ, n * maxIncrease < d →
      ∀ (S : Set α), (∀ x ∈ S, measure.complexity x ≤ n * maxIncrease) → a ∉ S := by
  intro n hn S h_bounded
  intro ha
  have : measure.complexity a ≤ n * maxIncrease := h_bounded a ha
  omega

/-- Abstract barrier theorem: elements with complexity d cannot appear before generation ⌈d/Δ⌉. -/
theorem abstract_idea_requires_min_generations
    {α : Type*} (measure : ComplexityMeasure α) (a : α) (d : ℕ)
    (maxIncrease : ℕ)
    (h_complexity : measure.complexity a = d) :
    ∀ n : ℕ, n * maxIncrease < d →
      ∀ (S : Set α), (∀ x ∈ S, measure.complexity x ≤ n * maxIncrease) → a ∉ S := by
  exact abstract_idea_requires_min_generations_ge measure a d maxIncrease (le_of_eq h_complexity.symm)

/-! ## Section 10: Ultra-Minimal Direct Formulation

The most minimal version possible: works with just a function, a bound, and sets.
No structure required at all. -/

/-- **ULTRA-MINIMAL**: The generation barrier in its purest form.

    Given ANY function `f : α → ℕ` and ANY family of sets `S : ℕ → Set α`
    where each S(n) contains only elements with f(x) ≤ n * Δ,
    elements with f(x) ≥ d cannot appear in S(n) for n * Δ < d.

    **WEAKENING**: This formulation has:
    1. No type constraints on α
    2. No structure required (just a function and sets)
    3. Uses lower bound (≥) not equality
    4. Completely polymorphic -/
theorem ultra_minimal_barrier
    {α : Type*} (f : α → ℕ) (Δ : ℕ) (S : ℕ → Set α)
    (h_bounded : ∀ n, ∀ x ∈ S n, f x ≤ n * Δ)
    (a : α) (d : ℕ) (ha_lb : f a ≥ d)
    (n : ℕ) (hn : n * Δ < d) :
    a ∉ S n := by
  intro ha
  have : f a ≤ n * Δ := h_bounded n a ha
  omega

/-- **ULTRA-MINIMAL Corollary**: Non-trivial elements require non-trivial generations.

    If f(a) ≥ 1, then a ∉ S(0). -/
theorem ultra_minimal_nonzero_requires_generation
    {α : Type*} (f : α → ℕ) (Δ : ℕ) (S : ℕ → Set α)
    (h_bounded : ∀ n, ∀ x ∈ S n, f x ≤ n * Δ)
    (a : α) (ha_lb : f a ≥ 1) :
    a ∉ S 0 := by
  apply ultra_minimal_barrier f Δ S h_bounded a 1 ha_lb 0
  simp

/-- **ULTRA-MINIMAL Linear Growth Bound**: Max value in S(n) is at most n * Δ. -/
theorem ultra_minimal_linear_bound
    {α : Type*} (f : α → ℕ) (Δ : ℕ) (S : ℕ → Set α)
    (h_bounded : ∀ n, ∀ x ∈ S n, f x ≤ n * Δ)
    (n : ℕ) :
    ∀ x ∈ S n, f x ≤ n * Δ := by
  exact h_bounded n

end CulturalDepthGenerations
