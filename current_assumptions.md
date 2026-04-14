# Current Assumptions in FormalAnthropology

**Generated:** February 6, 2026  
**Scope:** Every implicit and explicit assumption that the paper `formal_anthropology_academic.tex` inherits from the Lean 4 formalization in `FormalAnthropology/`.

---

## Table of Contents

1. [Foundational / Meta-logical Assumptions](#1-foundational--meta-logical-assumptions)
2. [Structural Modeling Assumptions](#2-structural-modeling-assumptions)
3. [Explicit Axioms (Unproved Postulates)](#3-explicit-axioms-unproved-postulates)
4. [Tautological "Theorems" (Conclusion = Hypothesis)](#4-tautological-theorems-conclusion--hypothesis)
5. [Sorry-Gapped Proofs](#5-sorry-gapped-proofs)
6. [Finiteness and Decidability Hypotheses](#6-finiteness-and-decidability-hypotheses)
7. [Hardcoded Numerical Constants](#7-hardcoded-numerical-constants)
8. [Single-vs-Set Primordial Mismatch](#8-single-vs-set-primordial-mismatch)
9. [Duplicate/Parallel Definitions](#9-duplicateparallel-definitions)
10. [Summary Statistics](#10-summary-statistics)

---

## 1. Foundational / Meta-logical Assumptions

These are blanket foundations the entire formalization rests on.

### 1.1 Classical Logic

The formalization uses `open Classical` or `Classical.propDecidable` in at least 15 files:

| File | Mechanism |
|---|---|
| `Collective_DynamicalSystems.lean` | `open Classical` |
| `Collective_ScientificCommunities.lean` | `open Classical` |
| `Learning_CollectiveAccess.lean` | `open Classical` |
| `Learning_DistributionalRisk.lean` | `open Classical` |
| `Learning_PaperC_Revision.lean` | `open Classical` |
| `Learning_RandomizedOracle.lean` | `open Classical` |
| `Mechanism_CompleteInformation.lean` | `open Classical` |
| `Mechanism_PatentPools.lean` | `open Classical` |
| `Mechanism_Sequential.lean` | `open Classical` |
| `PaperB_CoreTheorems.lean` | `open Classical` |
| `Welfare_TeamComposition_NoSorries.lean` | `open Classical` |
| `Welfare_TeamComposition.lean` | `open Classical` |
| `Collective_Depth.lean` | `Classical.propDecidable` via `@dite` (pervasive) |
| `Collective_CollectiveIntelligence.lean` | `Classical.propDecidable` via `@dite` (pervasive) |
| `Applications_CulturalTransmission.lean` | `Classical.propDecidable` via `@dite` |
| `Core_Agent.lean` | `Classical.propDecidable` in `GenerativeCapability.depth` |

**Consequence:** The depth function, most collective-closure computations, and all learning-theoretic results are nonconstructive. The formalization does **not** provide algorithms for computing depth, novelty, or closure — only existence proofs. Any claim about "computing" depth implicitly requires classical excluded middle.

### 1.2 Lean 4 + Mathlib Axioms

The formalization inherits Lean 4's standard axioms:
- **Quotient soundness** (`Quot.sound`)
- **Propositional extensionality** (`propext`)
- **Choice** (`Classical.choice` / `Axiom of Choice`)

These are used implicitly throughout via Mathlib lemmas about sets, cardinality, and natural numbers.

### 1.3 Noncomputable Definitions

At least **50+ definitions** are marked `noncomputable`, meaning they have no computational content. Key examples:

| Definition | File | Why noncomputable |
|---|---|---|
| `GenerativeCapability.depth` | `Core_Agent.lean` | Uses `Classical.propDecidable` + `Nat.find` |
| `cultureAtGeneration` | `Anthropology_CulturalDepthGenerations.lean` | Depends on noncomputable depth |
| `maxCulturalDepth` | `Anthropology_CulturalDepthGenerations.lean` | Takes supremum over potentially infinite set |
| `culturalDepth` | `Anthropology_CulturalDepthGenerations.lean` | Noncomputable chain |
| `transmissionOperator` | `Anthropology_CulturalDepthGenerations.lean` | Classical case split |
| `nextGenerationSize` | `Anthropology_TransmissionLoss.lean` | Real arithmetic with floor |
| `memoryAfterGenerations` | `Anthropology_TransmissionLoss.lean` | Iterated real arithmetic |
| `generationalBarrier` | `Anthropology_TransmissionLoss.lean` | Uses `Real.log` |
| `semanticDensity` | `Poetics_SemanticDensity.lean` | Depends on axiomatized `validInterpretations` |
| `branchingFactor` | `Collective_Depth.lean` | Supremum over agents |
| `MAIS.totalIdeas` | `Collective_CollectiveIntelligence.lean` | Cardinality of infinite set |
| `MAIS.holdersCount` | `Collective_Closure.lean` | Counting over potentially infinite agents |
| `closureDivergence` | `Collective_Closure.lean` | Set difference cardinality |
| `sample_complexity_no_ritual` | `Anthropology_RitualCompression.lean` | Real-valued complexity bound |
| `sample_complexity_with_ritual` | `Anthropology_RitualCompression.lean` | Real-valued complexity bound |

**Consequence:** None of the depth, novelty density, cultural depth, or transmission loss quantities are computable from the formalization. They exist only as mathematical objects.

---

## 2. Structural Modeling Assumptions

These are design choices baked into the structures that constrain what the theory can express.

### 2.1 IdeogeneticSystem: Single Primordial

```lean
structure IdeogeneticSystem where
  Idea : Type*
  generate : Idea → Set Idea
  primordial : Idea          -- ← SINGLE element, not a set
```

**Assumption:** Every ideogenetic system has exactly one primordial idea. The paper discusses "primordials $P \subseteq \mathcal{I}$" (a set), but the Lean formalization has a single `primordial : Idea`. Multi-seed systems are modeled via `{S.primordial}` (singleton set) or by passing an arbitrary `init : Set S.Idea` to `closure`, `depth`, etc.

### 2.2 Generation is Unary

```lean
generate : Idea → Set Idea
```

**Assumption:** Each idea generates successors independently. There is no built-in binary generation `(Idea × Idea) → Set Idea` in the core system. Combinative (binary) generation is only modeled in `CombinativeMAIS` as a separate extension, not in the base theory.

### 2.3 Time is ℕ (Discrete, Linear, Well-Ordered)

The `MAIS`, `Agent`, and `Channel` structures all use `T : Type* [LinearOrder T]`, but every concrete instantiation uses `T = ℕ`:

```lean
class TimeStructure (T : Type*) extends LinearOrder T where
  origin : T
  origin_le : ∀ t : T, origin ≤ t
```

**Assumption:** Time has a minimum element (origin), is totally ordered, and is discrete. There is no continuous-time model. Cultural evolution, agent lifetimes, and transmission all operate in discrete steps.

### 2.4 Agents Have Finite Lifetimes

```lean
structure Agent (I T : Type*) [LinearOrder T] where
  ...
  birth : T
  death : ExtendedTime T
  birth_before_death : ExtendedTime.finite birth < death
  memory_before_birth : ∀ t, t < birth → memory t = ∅
```

**Assumption:** Every agent has a birth time, a death time (possibly infinite), and empty memory before birth. There is no model of gradual cognitive development — agents spring into existence with their primordials already available.

### 2.5 Channel Delay is Strictly Positive

```lean
structure Channel (I₁ I₂ T : Type*) [LinearOrder T] where
  transmit : I₁ × T → Set (I₂ × T)
  delay_positive : ∀ ... (b, t₂) ∈ transmit (a, t₁) → t₁ < t₂
```

**Assumption:** All communication takes at least one time step. Instantaneous communication is impossible. This rules out synchronous multi-agent generation within a single time step.

### 2.6 MAIS: Agent Identifiers are Unique

```lean
agents_distinct : ∀ α ∈ agents, ∀ β ∈ agents, α.agentId = β.agentId → α = β
```

**Assumption:** No two distinct agents share an identifier. This is a technical requirement, but it also means the model cannot represent agent splitting, merging, or identity confusion.

### 2.7 MAIS: Primordials are Local and in Initial Memory

```lean
primordials_local : ∀ α ∈ agents, primordials α ⊆ α.localIdeas
primordials_in_memory : ∀ α ∈ agents, primordials α ⊆ α.memory α.birth
```

**Assumption:** An agent's primordials must be (a) within that agent's local idea space and (b) available at birth. There is no mechanism for an agent to acquire primordials after birth (other than through channels).

### 2.8 Ritual: Compression Ratio > 1

```lean
structure Ritual (I : Type*) where
  ...
  compression_ratio : ℝ
  is_compressed : compression_ratio > 1
```

**Assumption:** By definition, every ritual compresses. The model cannot represent rituals that expand or faithfully reproduce their content without compression.

### 2.9 Writing System: Preservation Rate > 0.9

```lean
structure WritingSystem (I : Type*) where
  written : Set I
  preservation_rate : ℝ
  h_high_fidelity : 0.9 < preservation_rate
```

**Assumption:** Every writing system has preservation rate strictly greater than 90%. This hardcodes a specific quantitative threshold rather than parameterizing it.

### 2.10 Library: Positive Size

```lean
structure Library (I : Type*) where
  collection : Set I
  size : ℕ
  h_size : 0 < size
```

**Assumption:** Every library is nonempty. Vacuous libraries are excluded by fiat.

### 2.11 GenerationalSystem: Primordial = {base.primordial}

```lean
structure GenerationalSystem where
  base : IdeogeneticSystem
  primordial : Set base.Idea
  maxDepthIncrease : ℕ
  max_depth_pos : 0 < maxDepthIncrease
  primordial_eq : primordial = {base.primordial}
```

**Assumptions:**
- Maximum depth increase per generation is a **fixed positive natural number** (no variation across generations, no real-valued cognitive capacity).
- The generational system's primordials are exactly the singleton containing the base system's primordial — no multi-seed generational systems.

### 2.12 CoalitionGame: Monotone Value Function

```lean
structure CoalitionGame (Agent : Type*) [Fintype Agent] where
  value : Finset Agent → ℚ
  value_empty : value ∅ = 0
  value_mono : ∀ S T, S ⊆ T → value S ≤ value T
```

**Assumptions:**
- Agents form a **finite type** (`Fintype Agent`).
- The coalition value function is **monotone** (larger coalitions never do worse). This rules out coordination failures, free-rider problems, and situations where adding an agent reduces group output.
- Values are rational numbers (`ℚ`), not reals.

### 2.13 Compatibility: Symmetric and Reflexive

```lean
class Compatibility (I : Type*) where
  compatible : I → I → Prop
  compatible_symm : ∀ a b, compatible a b → compatible b a
  compatible_refl : ∀ a, compatible a a
```

**Assumption:** Idea compatibility is always symmetric and reflexive. Every idea is compatible with itself, and if A is compatible with B then B is compatible with A. This excludes asymmetric compatibility (e.g., "A subsumes B but not vice versa").

### 2.14 GenerativeCapability: Finitariness is a Field, Not Enforced

```lean
structure GenerativeCapability (I : Type*) where
  generate : I → Set I
  isFinitary : Prop := ∀ a, (generate a).Finite
```

**Assumption:** `isFinitary` is a `Prop` field with a default value, but it is not enforced — a `GenerativeCapability` can be constructed with `isFinitary := False`. Theorems that need finitariness must carry it as an explicit hypothesis.

---

## 3. Explicit Axioms (Unproved Postulates)

These are `axiom` declarations — statements accepted without proof. Any theorem downstream of these inherits their unproved status.

### 3.1 `no_cumulative_culture_implies_bounded_depth`

**File:** `Anthropology_CulturalDepthGenerations.lean:194`

```
axiom no_cumulative_culture_implies_bounded_depth (G : GenerationalSystem)
    (h_no_cumulative : ¬ hasCumulativeCulture G) :
    ∃ D : ℕ, ∀ n : ℕ, maxCulturalDepth G n ≤ D
```

**Claim:** Without cumulative culture, cultural depth is bounded by a constant independent of the number of generations.

**Status:** Unproved. The docstring says it "captures the observation that non-cumulative species have limited cultural complexity."

### 3.2 `diversity_emergence_correlation`

**File:** `Collective_CollectiveIntelligence.lean:293`

```
axiom diversity_emergence_correlation {I : Type*} (M : MAIS I ℕ) (t : ℕ) ... :
    M.ideationalDiversity t > 0 → M.emergenceCount t > 0 →
    (M.emergenceCount t : ℚ) / (M.distributedClosure t).ncard ≤ M.ideationalDiversity t
```

**Claim:** The ratio of emergent ideas to total ideas is bounded by ideational diversity.

**Status:** Unproved. Described as capturing "the empirical observation that diverse collectives produce more emergent ideas."

### 3.3 `connectivity_threshold_exists`

**File:** `Collective_CollectiveIntelligence.lean:309`

```
axiom connectivity_threshold_exists {I : Type*} (M : MAIS I ℕ) :
    ∃ C_star : ℚ, C_star > 0 ∧
    (∀ t₁ t₂, t₁ < t₂ → M.effectiveConnectivity t₁ t₂ < C_star → M.emergenceCount t₂ = 0) ∧
    (∀ t₁ t₂, t₁ < t₂ → M.effectiveConnectivity t₁ t₂ > C_star → M.emergenceCount t₂ > 0)
```

**Claim:** Every MAIS has a sharp connectivity threshold: below it, no emergence; above it, guaranteed emergence.

**Status:** Unproved. This is an extremely strong claim — it asserts a sharp phase transition for *every* MAIS, not just specific families.

### 3.4 `cluster_lifetime_finite`

**File:** `Collective_CollectiveIntelligence.lean:557`

```
axiom cluster_lifetime_finite {I : Type*} (M : MAIS I ℕ) (t₁ t₂ : ℕ)
    (K : IntellectualCluster M t₁ t₂) :
    ∃ bound : ℕ, K.lifetime < bound
```

**Claim:** Every intellectual cluster has a finite lifetime.

**Status:** Unproved. The docstring says "no cluster lasts forever." Trivially true since `K.lifetime : ℕ` is already finite, making this axiom vacuous — it just says ∃ bound, K.lifetime < bound, which is true for any natural number.

### 3.5 `echo_chamber_holders_axiom`

**File:** `Collective_Conflict.lean:756`

```
axiom echo_chamber_holders_axiom {I : Type*} (M : MAIS I ℕ) (a : I) (t : ℕ)
    (E : EchoChamber M a t) : M.holdersCount t a = E.members.ncard
```

**Claim:** In an echo chamber for idea `a`, the number of holders of `a` equals the number of chamber members.

**Status:** Unproved. The file comments note this is "redundant — we can prove it for pure chambers" but it's kept "for backwards compatibility."

### 3.6 `MAIS.provenance_exists`

**File:** `Collective_Provenance.lean:103`

```
axiom MAIS.provenance_exists {I : Type*} (M : MAIS I ℕ) (α : Agent I ℕ) 
    (hα : α ∈ M.agents) (a : I) (t : ℕ) (ha : a ∈ α.memory t) :
    ∃ G : ProvenanceGraph I ℕ, M.isValidProvenanceGraph a t G
```

**Claim:** Every idea held by an agent at time `t` has a valid provenance graph.

**Status:** Unproved. This is an existential assumption about the traceability of ideas.

### 3.7 `distribError_shallow_on_conjunction`

**File:** `Learning_ApproximateLearningImpossibility.lean:108`

```
axiom distribError_shallow_on_conjunction {n k d : ℕ} 
    (hn : n ≥ 2*k) (hk : k ≥ 3) (hd : d ≤ k - 2)
    (c_star : kLiteralConjunction k n) (hsize : c_star.literals.card = k)
    (h : (Fin n → Bool) → Bool) :
  distribError h c_star.toFunc ≥ 1/4
```

**Claim:** Any hypothesis depending on ≤ k-2 variables has distributional error ≥ 1/4 on a k-literal conjunction.

**Status:** Unproved. The docstring outlines a combinatorial proof sketch (decision tree representation + counting argument over Boolean assignments) but notes it "requires formalizing decision tree representation."

### 3.8 `distribError_exponential_depth`

**File:** `Learning_ApproximateLearningImpossibility.lean:126`

```
axiom distribError_exponential_depth {n k d : ℕ}
    (hd : d < k) (hn : n ≥ k)
    (c_star : kLiteralConjunction k n) (hsize : c_star.literals.card = k)
    (h : (Fin n → Bool) → Bool) :
  distribError h c_star.toFunc ≥ (2 : ℝ)^(-(k - d : ℤ))
```

**Claim:** Error grows exponentially with depth gap k - d.

**Status:** Unproved. The docstring provides an inductive argument outline but the formal proof is missing.

### 3.9 `concept_class_growth_bound`

**File:** `Learning_ComputationalFeasibility.lean:155`

```
axiom concept_class_growth_bound {X : Type*}
    (L : PACGenerativeInstance X Bool) (b k : ℕ)
    (hb : b ≥ 1) (h_branch : ∀ a ∈ primordialClosure L.system, (L.system.generate a).ncard ≤ b) :
    (L.depthKConceptClass k).ncard ≤ (b ^ (k + 1))
```

**Claim:** With branching factor b, the depth-k concept class has at most b^(k+1) elements.

**Status:** Unproved. The bound b^(k+1) is actually weaker than the geometric sum (b^(k+1) - 1)/(b - 1) stated in the paper.

### 3.10 `exists_strictly_harder_noncumulative`

**File:** `Learning_NonCumulativeOracle.lean:134`

```
axiom exists_strictly_harder_noncumulative :
    ∃ (S : IdeogeneticSystem) (A : Set S.Idea) (target : S.Idea),
      (∃ n, target ∈ genNonCumulative S A n) ∧
      depthNonCumulative S A target > depth S A target
```

**Claim:** There exist systems where non-cumulative depth strictly exceeds cumulative depth.

**Status:** Unproved. The docstring notes "this requires careful construction" and the existence is axiomatized rather than demonstrated.

### 3.11 `hanneke_optimal_upper_bound`

**File:** `Learning_SampleComplexity.lean:99`

```
axiom hanneke_optimal_upper_bound :
  ∀ (d : ℕ) (ε δ : ℝ), d ≥ 1 → ε > 0 → δ > 0 → δ < 1 →
    ∃ (m : ℕ), m ≥ 1 ∧ m ≤ d * d + d + 1
```

**Claim:** Realizable PAC learning has sample complexity at most quadratic in VC dimension.

**Status:** Explicitly labeled as an "EXTERNAL RESULT" (Hanneke 2016). The stated bound `m ≤ d² + d + 1` is actually much weaker than Hanneke's O((d + log(1/δ))/ε) — it drops the ε and δ dependence entirely.

### 3.12 `validInterpretations`

**File:** `Poetics_SemanticDensity.lean:50`

```
axiom validInterpretations (e : Expression) : Set Interpretation
```

**Claim:** Every expression has a well-defined set of valid interpretations.

**Status:** Unproved. This is a parameter axiom — it postulates the existence of an interpretation function without specifying it.

### 3.13 `poetry_mathematics_orthogonal_goals`

**File:** `Poetics_StructureTheory.lean:217`

```
axiom poetry_mathematics_orthogonal_goals :
    goalInnerProduct mathematicsMode poetryMode < 1.0
```

**Claim:** Poetry and mathematics have orthogonal optimization goals (inner product < 1.0).

**Status:** Unproved. The threshold 1.0 is arbitrary and the "goal vectors" are not grounded in any empirical or formal framework.

### 3.14 `depth_logarithmic_in_space_size`

**File:** `Welfare_DiversityScaling.lean:165`

```
axiom depth_logarithmic_in_space_size : ∀ (n : ℕ) (h : n > 0), 
    ∃ (d : ℕ), d ≤ Nat.ceil (Real.log (n : ℝ) / Real.log 2) + 2
```

**Claim:** Depth required to cover n ideas grows at most logarithmically.

**Status:** Unproved. The "+2" is an arbitrary slack term.

### 3.15 `emergent_idea_depth_bound`

**File:** `Welfare_DiversityScaling.lean:169`

```
axiom emergent_idea_depth_bound : ∀ {Idea : Type*} (gA gB : Idea → Set Idea) 
    (S0 : Set Idea) (h : Idea) (n : ℕ),
    h ∈ closureAlternating S0 gA gB → h ∉ closureSingle S0 gA → h ∉ closureSingle S0 gB →
    ∃ (d : ℕ), d ≤ Nat.ceil (Real.log (n : ℝ) / Real.log 2) + 2
```

**Claim:** Emergent ideas have depth at most O(log n).

**Status:** Unproved. The conclusion does not even mention `h` or connect `d` to the depth of `h` — it only asserts the *existence* of a number bounded by log(n) + 2, which is trivially true.

---

## 4. Tautological "Theorems" (Conclusion = Hypothesis)

Several theorems in the phase transition section are stated so that the conclusion is literally the hypothesis restated. They type-check trivially.

### 4.1 `hyperscaling_relation`

```lean
theorem hyperscaling_relation (U : UniversalityClass) (hbelow_upper : U.dimension ≤ 4)
    (hscaling : U.satisfiesHyperscaling) :
    2 - U.exponents.α = U.dimension * U.exponents.ν := hscaling
```

The proof is `:= hscaling` — the conclusion is definitionally equal to the hypothesis `U.satisfiesHyperscaling`.

### 4.2 `rushbrooke_equality`

```lean
theorem rushbrooke_equality (U : UniversalityClass) (_hbelow_upper : U.dimension ≤ 4)
    (hscaling : U.satisfiesRushbrooke) :
    U.exponents.α + 2 * U.exponents.β + U.exponents.γ = 2 := hscaling
```

Same pattern: the conclusion **is** `satisfiesRushbrooke`.

### 4.3 `fisher_relation`

```lean
theorem fisher_relation (U : UniversalityClass) (hscaling : U.satisfiesFisher) :
    U.exponents.γ = U.exponents.ν * (2 - U.exponents.η) := hscaling
```

Same pattern.

### 4.4 `scale_free_zero_threshold`

```lean
theorem scale_free_zero_threshold {I : Type*} (M : MAIS I ℕ) (γ : ℝ) ...
    (hzero_threshold : ∃ α > 0, M.hasGiantComponent t α) :
    ∃ threshold > 0, M.hasGiantComponent t threshold := hzero_threshold
```

The conclusion is identical to the hypothesis `hzero_threshold`.

**Consequence:** The paper presents these as substantive results (e.g., "Hyperscaling Relation: $d\nu = 2 - \alpha$"), but the Lean proofs are vacuous. These theorems say: "if the scaling relation holds, then the scaling relation holds." The *real* mathematical content — deriving these relations from underlying dynamics — is not formalized.

---

## 5. Sorry-Gapped Proofs

These theorems are stated and partially proved, but contain `sorry` — meaning their proofs are incomplete. Any theorem downstream inherits the gap.

### 5.1 Theorems Cited in the Paper That Use Sorry

| Theorem | File | Reason for sorry |
|---|---|---|
| `minimal_period_divides` | `SingleAgent_FixedPointStructure.lean` | Requires Bézout's lemma / GCD properties from number theory |
| `kcyclic_of_divisor` | `SingleAgent_FixedPointStructure.lean` | Requires iteration composition lemmas |
| `orbit_card_le` | `SingleAgent_FixedPointStructure.lean` | Orbit cardinality bound |
| `generation_increases_depth` | `SingleAgent_DepthStratification.lean` | Relating closure-without-a to depth dependencies |
| `depth_partial_order` | `SingleAgent_DepthStratification.lean` | Path existence implies depth inequality |
| `memory_after_barrier` | `Anthropology_TransmissionLoss.lean` | Requires exponential/logarithm properties |
| `innovation_fidelity_tradeoff` | `Anthropology_TransmissionLoss.lean` | Requires convergence analysis |
| `institutions_vs_rediscovery` | `Anthropology_TransmissionLoss.lean` | Requires computing equilibrium values |

### 5.2 Theorems Not Directly Cited but in the Dependency Graph

| Theorem | File | Reason for sorry |
|---|---|---|
| `dialectical_is_three_cyclic` | `SingleAgent_FixedPointStructure.lean` | Depends on kcyclic_of_divisor |
| `shapleyWeight_sum_one` | `GameTheory_ShapleyAttribution.lean` | Combinatorial identity (binomial manipulation) |
| `shapley_efficiency` | `GameTheory_ShapleyAttribution.lean` | Double summation interchange |
| `memory_convergence` | `Anthropology_TransmissionLoss.lean` | Convergence analysis |
| `depth_decay_without_innovation` | `Anthropology_TransmissionLoss.lean` | Careful calculation |
| All kinship system examples | `Anthropology_KinshipSystems.lean` | Model construction / group construction (9 sorries) |
| Multi-type hierarchy lemmas | `MultiType_HierarchySimplified.lean` | 10 sorries in closureSubset, level constructions |
| Various poetics theorems | `Poetics_*.lean` | ~17 sorries total across phonetics, phonosemantics, structure theory |

### 5.3 Files with Sorry (19 files total, 75 sorry occurrences)

| File | Sorry Count |
|---|---|
| `Anthropology_KinshipSystems.lean` | 9 |
| `MultiType_HierarchySimplified.lean` | 10 |
| `Learning_ApproximateLearningImpossibility_Proven.lean` | 10 |
| `Poetics_PhoneticStructure.lean` | 7 |
| `SingleAgent_FixedPointStructure.lean` | 7 |
| `Learning_NonCumulativeOracle_Explicit.lean` | 6 |
| `Anthropology_TransmissionLoss.lean` | 5 |
| `Collective_Provenance.lean` | 4 |
| `GameTheory_ShapleyAttribution.lean` | 3 |
| `Learning_UnifiedComplexity.lean` | 2 |
| `Collective_SpecialSystems.lean` | 2 |
| `Welfare_DiversityScaling_Proven.lean` | 2 |
| `SingleAgent_DepthStratification.lean` | 2 |
| `Pragmatics_LanguageGames.lean` | 2 |
| `Poetics_PhonosemanticsStructure.lean` | 2 |
| `Poetics_StructureTheory.lean` | implicit via axioms |
| `SingleAgent_DepthMonotonicity.lean` | 1 |
| `SingleAgent_DepthAddition.lean` | 1 |
| `Learning_EmergenceCharacterization_*.lean` | scattered |

---

## 6. Finiteness and Decidability Hypotheses

Many theorems carry implicit or explicit finiteness assumptions that the paper does not always foreground.

### 6.1 `isFinitary` (Each Idea Generates Finitely Many Successors)

Required by:
- `no_universal_idea` — the main proof needs `(S.generate u).Finite` via `isFinitary`
- Various cardinality arguments throughout

**Paper presentation:** The paper states "No Universal Idea" without mentioning finitariness, but the Lean proof requires `h_finitary : isFinitary S` as an explicit hypothesis.

### 6.2 Infinite Primordial Closure

Required by:
- `no_universal_idea` — needs `(primordialClosure S).Infinite`

**Paper presentation:** The paper requires $|\mathrm{cl}(P)| \geq 2$, but the Lean proof actually requires the stronger condition that the closure is *infinite*.

### 6.3 `[Fintype I]` (Finite Idea Space)

Required by all information-theoretic results:
- `MAIS.beliefEntropy`, `entropy_dynamics_decomposition`, `critical_entropy_regime`
- All `InformationTheory_DepthComplexity.lean` theorems
- All `Probability_Framework.lean` results

### 6.4 `[DecidableEq I]` (Decidable Equality on Ideas)

Required by:
- `generational_barrier` in `Anthropology_MortalityProblem.lean`
- All sheaf-theoretic results in `Collective_SheafTheory.lean`
- All Betti number computations in `Collective_TopologicalInvariants.lean`
- All computational hardness results in `Learning_ComputationalHardness.lean`
- `empiricalError` in `Learning_Basic.lean` / `Learning_BasicV2.lean`

### 6.5 `[Fintype Agent]` (Finitely Many Agents)

Required by:
- All `CoalitionGame` theorems (Shapley value)
- All game-theoretic attributions

### 6.6 `.Finite` Set-Level Hypotheses

Many theorems carry hypotheses like:
- `(M.livingAgents t).Finite`
- `(M.distributedClosure t).Finite`
- `(M.emergentIdeas t).Finite`
- `r.encoded_ideas.Finite`
- `(cl(A)).Finite` (for novelty density theorems)

The paper typically states these results without finiteness qualifications.

### 6.7 Subadditivity Hypothesis on Generation

The diversity necessity theorem (`diversity_necessity`) requires:

```lean
(hsub : ∃ gen : I → Set I, (∀ α ∈ M.agents, α.generate = gen) ∧ Generator.isSubadditive gen)
```

**Assumption:** The shared generation rule is subadditive: gen(A ∪ B) ⊆ gen(A) ∪ gen(B). This rules out synergistic generation where combining ideas from different sources produces something neither source could produce alone. The paper mentions this but does not always emphasize that diversity necessity fails without subadditivity.

---

## 7. Hardcoded Numerical Constants

Several structures and theorems contain hardcoded numerical thresholds.

| Constant | Value | Location | Role |
|---|---|---|---|
| Writing preservation rate | > 0.9 | `WritingSystem.h_high_fidelity` | Lower bound on fidelity |
| Ritual compression ratio | > 1 | `Ritual.is_compressed` | Rituals must compress |
| Institution fidelity | 0.95 | `institutions_vs_rediscovery` | Example parameter |
| Rediscovery fidelity | 0.7 | `institutions_vs_rediscovery` | Example parameter |
| Poetry-math orthogonality | < 1.0 | `poetry_mathematics_orthogonal_goals` | Goal vector inner product threshold |
| Shallow error threshold | ≥ 1/4 | `distribError_shallow_on_conjunction` | Error lower bound |
| Library collection size | > 0 | `Library.h_size` | Nonemptiness |

---

## 8. Single-vs-Set Primordial Mismatch

The paper (`formal_anthropology_academic.tex`) defines:

> **Definition (Ideogenetic System):** A triple $(\mathcal{I}, P, \mathrm{gen})$ where $P \subseteq \mathcal{I}$ is a set (the primordials).

But the Lean formalization defines:

```lean
structure IdeogeneticSystem where
  Idea : Type*
  generate : Idea → Set Idea
  primordial : Idea    -- single element
```

The gap is bridged by defining `primordialClosure S = closure S {S.primordial}`, converting the single primordial into a singleton set. Most theorems then work with an arbitrary `init : Set S.Idea`, which can be any set, not just `{S.primordial}`.

**Consequence:** The paper's notation suggests a theory with multiple independent primordials, but the Lean structure only supports one. The generality in theorems comes from the `init` parameter, not from the structure itself.

---

## 9. Duplicate/Parallel Definitions

The codebase contains two parallel versions of several core files:

| V1 File | V2 File | Difference |
|---|---|---|
| `SingleAgent_Basic.lean` | `SingleAgent_BasicV2.lean` | V2 uses `GenerativeCapability` from `Core_Agent.lean`; V1 defines `generate` directly |
| `Collective_Basic.lean` | `Collective_BasicV2.lean` | V2 imports V2 of SingleAgent |
| `Learning_Basic.lean` | `Learning_BasicV2.lean` | V2 imports V2 chain |

Most files import V1. Files importing V2 include only `Collective_BasicV2.lean` and `Learning_BasicV2.lean`.

**Risk:** The same theorem name (e.g., `closure_idempotent`) may exist in both V1 and V2 namespaces with subtly different types or hypotheses. The paper cites theorem names without specifying which version.

---

## 10. Summary Statistics

| Category | Count |
|---|---|
| **Explicit axioms** (unproved postulates) | 15 |
| **Tautological theorems** (proof = hypothesis) | 4 |
| **Files with sorry** | 19 |
| **Total sorry occurrences** | 75 |
| **Files using `open Classical`** | 12+ |
| **Noncomputable definitions** | 50+ |
| **Hardcoded numerical constants** | 7+ |
| **Duplicate definition pairs (V1/V2)** | 3 |

### Fully Proved Core Results (No Axioms, No Sorry in Dependency Chain)

The following paper-cited theorems are **genuinely proved** with no upstream axioms or sorry:

- `closure_idempotent`, `closure_mono'`, `closure_extensive`, `closure_minimal`, `closure_closed_under_gen`
- `depth_zero_iff_in_init`, `depth_successor_bound`, `depth_prerequisite`, `depth_antimono`
- `novelty_disjoint`, `depth_stratifies`, `closure_eq_union_novelty`
- `novelty_eventually_zero_finite_closure`, `eventual_stagnation`
- `nat_depth_eq_self`, `hierarchy_strictness`
- `fixed_point_is_one_cyclic`, `one_cyclic_is_fixed_point`
- `homogeneous_collective_closure`, `diversity_necessity`, `groupthink_eliminates_emergence`
- `combinative_diversity_necessity`, `diversity_necessity_comprehensive`
- `single_agent_embedding_closure`, `MAIS.closure_chain`
- `critical_connectivity_threshold` (genuine proof, not tautological)
- `critical_slowing_down` (genuine proof using real analysis)
- `transmission_loss_exponential`, `high_fidelity_preserves_knowledge`
- `compression_fidelity_tradeoff`, `ritual_depth_preservation_bound`
- `cultural_depth_bounded_by_generations`, `cultural_depth_requires_generations`
- `writing_enables_accumulation`, `writing_causes_depth_jump`
- `queriesForFullDepthK_exponential`, `budgeted_trichotomy`

### Results That Depend on Axioms or Sorry

| Paper Theorem | Upstream Dependency |
|---|---|
| No Universal Idea | Requires `isFinitary` + infinite closure (not axioms, but unstated hypotheses in paper) |
| Minimal period divides | sorry (needs Bézout's lemma) |
| Hyperscaling, Rushbrooke, Fisher relations | Tautological (conclusion = hypothesis) |
| Scale-free zero threshold | Tautological |
| Memory convergence theorems | sorry (convergence analysis) |
| Innovation–fidelity tradeoff (convergence) | sorry |
| Concept class growth bound | axiom (3.9) |
| Distributional error bounds | axioms (3.7, 3.8) |
| Hanneke PAC bound | axiom (3.11, external result) |
| Diversity–emergence correlation | axiom (3.2) |
| Sharp connectivity threshold (∀ MAIS) | axiom (3.3) |
| Provenance existence | axiom (3.6) |
| Non-cumulative depth boundedness | axiom (3.1) |
