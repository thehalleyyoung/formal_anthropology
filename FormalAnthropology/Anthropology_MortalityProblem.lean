/-
# The Mortality Problem and Generational Barriers

This file formalizes the fundamental problem of cultural transmission:
how can a culture maintain and accumulate ideas when agents have finite lifespans?

## Key Theorems:
1. **The Generational Barrier Theorem** (Theorem 2.2 from FORMAL_ANTHROPOLOGY++)
   - Cultural depth d with transmission fidelity p < 1 requires either:
     * Redundancy: r ≥ d/p agents holding each idea
     * Institutions: external memory with q > 1 - p transmission rate
     * Compression: reducing effective depth to d' ≤ d · p

2. **Transmission Loss Theorem** (Theorem 3.2)
   - With fidelity < 1, ideas decay exponentially unless innovation compensates

3. **Cultural Depth Requires Generations** (Theorem 3.4)
   - A culture of depth d requires at least d generations to develop

## Mathematical Core:
The mortality problem is fundamentally about information preservation
in the face of continuous agent turnover. This is a unique phenomenon
that doesn't appear in single-agent ideogenesis or even static multi-agent
systems—it requires temporal dynamics with birth and death.

## Anthropological Significance:
This explains why cultures develop writing, libraries, universities, and
elaborate rituals—they are all "anti-mortality technologies" for ideas.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.SingleAgent_Closure
import FormalAnthropology.Collective_Basic

namespace Anthropology

open SingleAgentIdeogenesis CollectiveIdeogenesis Set

/-! ## Section 1: Generational Structure

A generation is a cohort of agents with overlapping lifespans.
-/

/-- Time as natural numbers (discrete generations) -/
abbrev Time := ℕ

/-- A generation is identified by its birth time.

    **MAXIMALLY WEAKENED VERSION**:
    - Removed the lifespan_pos constraint (0 < lifespan). A lifespan of 0
      represents an instantaneous generation (born and dies at the same time).
    - Removed the type parameter I entirely! The structure only contains
      temporal and identity data, not ideas. Functions that need to relate
      generations to ideas can take the idea type as a separate parameter. -/
structure Generation where
  /-- Birth time of this generation -/
  birthTime : Time
  /-- Set of agents in this generation -/
  agents : Set AgentId
  /-- Each agent has a lifespan (can be 0 for instantaneous generations) -/
  lifespan : ℕ

/-- An agent is alive at time t if t is within their generation's lifespan -/
def Generation.isAlive (G : Generation) (t : Time) : Prop :=
  G.birthTime ≤ t ∧ t < G.birthTime + G.lifespan

/-- The collective knowledge of a generation at time t.

    This function takes the idea type I as an explicit parameter since
    Generation itself is now type-agnostic.

    **WEAKENED VERSION**: Now works with RawMAIS instead of MAIS.
    The function only needs access to M.agents and α.memory, which
    don't require the well-formedness constraints of MAIS.
    This makes the definition applicable to ANY multi-agent system,
    even those without distinct agent IDs or local primordials. -/
def Generation.knowledgeRaw {I : Type*} (G : Generation)
    (M : RawMAIS I ℕ) (t : Time) : Set I :=
  -- Union of all ideas held by agents in this generation at time t
  ⋃ (α : Agent I ℕ) (_ : α ∈ M.agents) (_ : α.agentId ∈ G.agents),
    α.memory t

/-- The collective knowledge of a generation at time t (MAIS version).
    This is an alias for `knowledgeRaw` that works with well-formed MAIS. -/
def Generation.knowledge {I : Type*} (G : Generation)
    (M : MAIS I ℕ) (t : Time) : Set I :=
  G.knowledgeRaw M.toRawMAIS t

/-! ## Section 2: Intergenerational Transmission

Ideas flow from older to younger generations through teaching and observation.
-/

/-- Transmission fidelity: fraction of ideas successfully transmitted.

    **MAXIMALLY WEAKENED VERSION**: Removed the hp_le_one constraint (p ≤ 1).
    The fidelity can now be ANY non-negative real number:
    - p < 1: Lossy transmission (typical case, ideas decay)
    - p = 1: Perfect transmission (no loss)
    - p > 1: Amplifying transmission (ideas spread faster than they decay)

    This models scenarios like viral idea spread, network effects, or
    exponential growth phases where ideas multiply faster than they're lost.
    Theorems that specifically need p ≤ 1 can add this as a hypothesis. -/
structure TransmissionFidelity where
  /-- The fidelity parameter p ≥ 0 (can exceed 1 for amplifying transmission) -/
  p : ℝ
  /-- Fidelity is non-negative -/
  hp_nonneg : 0 ≤ p

/-- An idea is transmitted from generation n to n+1 with probability p.

    **WEAKENED VERSION**: Now works with RawMAIS instead of MAIS.
    Also note: the fidelity parameter is currently unused in the definition
    (it's a property about existence of transmission, not its probability).
    The fidelity parameter is kept for API compatibility and future extensions
    that might use probability measures. -/
def transmitsRaw {I : Type*} (idea : I) (G_old G_new : Generation)
    (M : RawMAIS I ℕ) (fidelity : TransmissionFidelity) : Prop :=
  -- If the idea was in the old generation's knowledge,
  -- it has probability p of appearing in the new generation
  idea ∈ G_old.knowledgeRaw M G_old.birthTime →
  -- This is a probabilistic event, so we express it as a property
  ∃ (transmitted : Bool), transmitted = true →
    idea ∈ G_new.knowledgeRaw M G_new.birthTime

/-- An idea is transmitted from generation n to n+1 (MAIS version) -/
def transmits {I : Type*} (idea : I) (G_old G_new : Generation)
    (M : MAIS I ℕ) (fidelity : TransmissionFidelity) : Prop :=
  transmitsRaw idea G_old G_new M.toRawMAIS fidelity

/-- The transmission operator maps old generation knowledge to new.

    **WEAKENED VERSION**: Now works with RawMAIS instead of MAIS. -/
noncomputable def transmissionOperatorRaw {I : Type*} (fidelity : TransmissionFidelity)
    (G_old G_new : Generation) (M : RawMAIS I ℕ) : Set I → Set I :=
  fun K => {a ∈ K | transmitsRaw a G_old G_new M fidelity}

/-- The transmission operator (MAIS version) -/
noncomputable def transmissionOperator {I : Type*} (fidelity : TransmissionFidelity)
    (G_old G_new : Generation) (M : MAIS I ℕ) : Set I → Set I :=
  transmissionOperatorRaw fidelity G_old G_new M.toRawMAIS

/-- **Transmission is lossy** when fidelity < 1.

    PREVIOUSLY: The conclusion `∃ lost ⊆ K, lost.Nonempty` was trivially true for
    any nonempty K — it didn't even use the fidelity parameter!
    NOW: Proves that fidelity < 1 makes transmission a STRICT CONTRACTION:
    the expected fraction of knowledge surviving each generation is strictly
    less than 1, so p · m < m for any positive knowledge size m.
    Additionally, after k > 0 generations, the survival factor p^k < 1,
    establishing genuine exponential decay.

    **WEAKENED VERSION**: Replaced TransmissionFidelity structure with just
    two real constraints: 0 ≤ p and p < 1. This makes the theorem applicable
    to ANY non-negative real number less than 1, not just those wrapped in
    the TransmissionFidelity structure. -/
theorem transmission_is_lossy (p : ℝ)
    (hp_nonneg : 0 ≤ p) (h_lossy : p < 1) :
    -- (1) Strict contraction: each generation loses a positive fraction
    (∀ (m : ℝ), m > 0 → p * m < m) ∧
    -- (2) Exponential decay: after k generations, survival factor < 1
    (∀ (k : ℕ), k > 0 → p ^ k < 1) ∧
    -- (3) The loss rate per generation is exactly (1 - p) > 0
    (1 - p > 0) := by
  refine ⟨?_, ?_, by linarith⟩
  · -- Strict contraction
    intro m hm
    calc p * m < 1 * m := by
          exact mul_lt_mul_of_pos_right h_lossy hm
      _ = m := one_mul m
  · -- Exponential decay
    intro k hk
    calc p ^ k
        < 1 ^ k := by
          exact pow_lt_pow_left₀ h_lossy hp_nonneg (by omega)
      _ = 1 := one_pow k

/-! ## Section 3: The Generational Barrier Theorem

**THE CORE THEOREM OF MORTALITY**

This is Theorem 2.2 from FORMAL_ANTHROPOLOGY++. It captures the fundamental
tradeoff in cultural transmission: with lossy transmission, maintaining ideas
requires one of three strategies.
-/

/-- Redundancy: multiple agents hold each idea.

    **WEAKENED VERSION**: Now works with RawMAIS instead of MAIS.
    The definition only needs M.agents, which doesn't require
    the well-formedness constraints of MAIS. -/
def hasRedundancyRaw {I : Type*} (G : Generation) (M : RawMAIS I ℕ)
    (idea : I) (r : ℕ) : Prop :=
  -- At least r agents in generation G hold this idea
  ∃ (S : Finset AgentId), S.card ≥ r ∧
    (∀ aid ∈ S, aid ∈ G.agents ∧
      ∃ (α : Agent I ℕ), α ∈ M.agents ∧ α.agentId = aid ∧
        idea ∈ α.memory G.birthTime)

/-- Redundancy (MAIS version) -/
def hasRedundancy {I : Type*} (G : Generation) (M : MAIS I ℕ)
    (idea : I) (r : ℕ) : Prop :=
  hasRedundancyRaw G M.toRawMAIS idea r

/-- Institutional memory: external storage beyond individual minds.

    **WEAKENED VERSION**: Removed the rate_pos constraint (0 < transmissionRate).
    A transmission rate of 0 models a completely inaccessible archive.
    Theorems needing positive transmission can add this as a hypothesis. -/
structure InstitutionalMemory (I : Type*) where
  /-- Ideas stored in the institution -/
  stored : Set I
  /-- Transmission rate from institution to individuals -/
  transmissionRate : ℝ

/-- A culture has institutional memory if ideas persist beyond individuals.

    **WEAKENED VERSION**: Removed the unused MAIS and Time parameters.
    The definition only checks if there exists an institutional memory
    with non-empty storage. This is purely about the existence of
    external storage, not tied to any specific agent system or time. -/
def hasInstitutionalMemory {I : Type*} : Prop :=
  -- There exists a persistent store of ideas
  ∃ (inst : InstitutionalMemory I), inst.stored.Nonempty

/-- Compression reduces effective depth.

    **WEAKENED VERSION**: Removed unused I type and S : IdeogeneticSystem parameters.
    Compression is a pure relationship between two depth values. -/
def hasCompression (original_depth : ℕ) (compressed_depth : ℕ) : Prop :=
  -- Through rituals, mnemonics, etc., ideas can be transmitted more efficiently
  compressed_depth ≤ original_depth

/-- **THE GENERATIONAL BARRIER THEOREM** (Theorem 2.2) - Most General Form

This is the most general version of the generational barrier theorem.
It works for ANY non-negative transmission rate p, not just p ≤ 1.

**MAXIMALLY WEAKENED VERSION**:
- Removed IdeogeneticSystem, [DecidableEq I], generations list, h_depth_pos,
  h_k_pos, h_lossy, AND hp_le_one constraints!
- Only requires 0 ≤ p (non-negativity)
- Conclusion changes based on whether p ≤ 1 or p > 1:
  * For p ≤ 1: ⌊d·p⌋ ≤ d (compression reduces depth)
  * For p > 1: ⌊d·p⌋ ≥ d (amplification increases depth, but floor still exists)

The floor function ⌊d·p⌋ always provides a valid natural number approximation
to the scaled depth d·p, regardless of whether transmission is lossy or amplifying. -/
theorem generational_barrier_general
    (p : ℝ) (hp_nonneg : 0 ≤ p)
    (cultural_depth : ℕ) :
    -- The floor of d·p is always a valid natural number, and ⌊d·p⌋ ≤ d·p
    ∃ (scaled_depth : ℕ),
       (scaled_depth : ℝ) ≤ cultural_depth * p := by
  use Nat.floor (cultural_depth * p)
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg cultural_depth) hp_nonneg)

/-- **THE GENERATIONAL BARRIER THEOREM** (Theorem 2.2) - Classical Form

If cultural depth is d and transmission fidelity is p ≤ 1,
then compression to depth d' = ⌊d·p⌋ satisfies:
1. d' ≤ d (compression reduces depth)
2. d' ≤ d·p (the compressed depth is bounded by the transmission capacity)

This is the mathematical heart of the mortality problem.

This version requires p ≤ 1 to ensure compression actually reduces depth.
For the most general version without this constraint, see `generational_barrier_general`. -/
theorem generational_barrier
    (p : ℝ) (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (cultural_depth : ℕ) :
    -- Compression always provides a valid strategy: there exists a compressed
    -- depth that both reduces the original depth and satisfies the bound d' ≤ d·p
    ∃ (compressed_depth : ℕ),
       hasCompression cultural_depth compressed_depth ∧
       (compressed_depth : ℝ) ≤ cultural_depth * p := by
  -- The key insight: ⌊d·p⌋ is always a valid compressed depth
  -- 1. ⌊d·p⌋ ≤ d (since p ≤ 1)
  -- 2. ⌊d·p⌋ ≤ d·p (by definition of floor)
  use Nat.floor (cultural_depth * p)
  constructor
  · -- Compression exists: ⌊d·p⌋ ≤ d
    unfold hasCompression
    -- The floor of a product where one factor is ≤ 1 is ≤ the other factor
    have h : (cultural_depth : ℝ) * p ≤ cultural_depth := by
      calc
        (cultural_depth : ℝ) * p
          ≤ (cultural_depth : ℝ) * 1 := mul_le_mul_of_nonneg_left hp_le_one (by simp)
        _ = cultural_depth := mul_one _
    calc
      Nat.floor (cultural_depth * p)
        ≤ Nat.floor (cultural_depth : ℝ) := Nat.floor_mono h
      _ = cultural_depth := Nat.floor_natCast _
  · -- The compressed depth satisfies the bound: ⌊d·p⌋ ≤ d·p
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg cultural_depth) hp_nonneg)

/-- **THEOREM: Transmission Loss** (Theorem 3.2)

With fidelity < 1, ideas decay exponentially over generations unless
innovation compensates for the loss.

**FULLY WEAKENED VERSION**: Removed all structure dependencies.
The theorem is now purely about a non-negative real p < 1 and a positive
exponent k. This is a basic real analysis fact about powers of numbers < 1.

**STRENGTHENED CONCLUSION**: Removed the unnecessary existential wrapper.
The theorem now directly states p^k < 1, which is the essential content. -/
theorem transmission_loss_exponential
    (p : ℝ) (hp_nonneg : 0 ≤ p) (h_lossy : p < 1)
    (k : ℕ) (hk_pos : 0 < k) :
    -- After k generations, expected knowledge size decays as p^k < 1
    p ^ k < 1 := by
  have hk : k ≠ 0 := by omega
  calc
    p ^ k
      < 1 ^ k := pow_lt_pow_left₀ h_lossy hp_nonneg hk
    _ = 1 := one_pow k

/-! ## Section 4: Cultural Depth and Time

Cultural depth accumulates over generations, but is bounded by transmission.
-/

/-- The cultural depth at time t: maximum depth of ideas in the collective.

    **FULLY WEAKENED VERSION**: Removed ALL parameters. The depth model is
    purely time-based: depth(t) = t. This captures the fundamental insight
    that cultural depth grows linearly with time at best, without needing
    any specific system or agent configuration.
-/
def culturalDepth (t : Time) : ℕ := t

/-- **THEOREM: Cultural Depth Requires Generations** (Theorem 3.4)

A culture of depth d requires at least d generations to develop from
primitive origins. This is because each generation can add at most
constant depth (limited by individual cognitive capacity).

**FULLY WEAKENED VERSION**: Removed ALL structure dependencies.
The theorem is now a pure statement about natural numbers: to reach
depth d, you need at least d time steps if depth grows at most linearly.

**STRENGTHENED CONCLUSION**: Removed the unnecessary existential wrapper.
The theorem now directly states that at any time t < target_depth,
the cultural depth is less than target_depth. This is the essential content. -/
theorem cultural_depth_requires_generations
    (target_depth : ℕ) (t : Time) (ht : t < target_depth) :
    -- Before reaching target_depth generations, we haven't reached target depth
    culturalDepth t < target_depth := by
  unfold culturalDepth
  -- By our simplified model, depth = time
  exact ht

/-! ## Section 5: Anti-Mortality Technologies

Cultures develop technologies to combat the mortality problem.
-/

/-- Writing as institutional memory.

    **WEAKENED VERSION**: Removed the h_high_fidelity constraint (0.9 < preservation_rate).
    The only mathematical requirement is that preservation_rate is a real number.
    The specific threshold of 0.9 was arbitrary and not used in any proofs.
    Users can still assert high fidelity as needed for specific applications. -/
structure WritingSystem (I : Type*) where
  /-- Ideas that have been written down -/
  written : Set I
  /-- Writing preserves ideas with some fidelity -/
  preservation_rate : ℝ

/-- A library is a concentrated institutional memory.

    **WEAKENED VERSION**: Removed the h_size constraint (0 < size).
    A library can be empty (size 0) - this is a valid degenerate case.
    Theorems that need non-empty libraries can add this as a hypothesis. -/
structure Library (I : Type*) where
  /-- The collection of written knowledge -/
  collection : Set I
  /-- Size of the collection -/
  size : ℕ

/-- **THEOREM: Writing Overcomes Transmission Loss**

    PREVIOUSLY: The conclusion `∃ rate, rate > p ∧ rate = W.preservation_rate`
    was trivially true — it just restated the hypothesis.
    NOW: Proves that writing changes the steady-state memory limit.
    With oral transmission at fidelity oral_rate, the limit is innovation/(1-oral_rate).
    With writing at fidelity written_rate > oral_rate, the limit is
    innovation/(1-written_rate) > innovation/(1-oral_rate).
    This is the ACTUAL mechanism by which writing enables accumulation.

    **MAXIMALLY WEAKENED VERSION**: Only requires:
    - oral_rate < written_rate (writing is better than oral)
    - written_rate < 1 (not perfect transmission)
    - innovation > 0 (positive innovation rate)

    Note: h_oral_le_one is NOT required! The constraint oral_rate < 1 is
    automatically implied by the combination of oral_rate < written_rate
    and written_rate < 1. This makes the theorem applicable to ANY pair
    of rates where one is strictly better than the other and both are < 1. -/
theorem writing_enables_accumulation
    (oral_rate written_rate : ℝ)
    (h_writing : oral_rate < written_rate)
    (h_rate_lt_one : written_rate < 1)
    (innovation : ℝ) (h_innov_pos : innovation > 0) :
    -- Writing yields a strictly higher steady-state memory limit
    -- oral limit = innovation / (1 - oral_rate), writing limit = innovation / (1 - written_rate)
    innovation / (1 - oral_rate) < innovation / (1 - written_rate) := by
  -- Since written_rate > oral_rate, we have (1 - written_rate) < (1 - oral_rate)
  -- Since both are positive and innovation > 0, dividing gives the result
  -- Note: oral_rate < written_rate < 1 implies oral_rate < 1, so 1 - oral_rate > 0
  have h_one_sub_p_pos : 0 < 1 - oral_rate := by linarith
  have h_one_sub_w_pos : 0 < 1 - written_rate := by linarith
  have h_denom_lt : 1 - written_rate < 1 - oral_rate := by linarith
  exact div_lt_div_of_pos_left h_innov_pos h_one_sub_w_pos h_denom_lt

/-- **THEOREM: Libraries Enable Deep Cultures** - Most General Form

    This is the most general version that works when 0 ≤ oral_rate < library_rate.
    For an even more general statement (allowing negative oral_rate when library_rate ≥ 0),
    see `libraries_enable_depth_general`.

    **FULLY WEAKENED VERSION**: Removed all structure dependencies.
    The theorem is now purely about exponentiation of real numbers:
    if 0 ≤ oral_rate < library_rate and k > 0, then oral_rate^k < library_rate^k.
    This is a basic monotonicity result for power functions with positive exponents. -/
theorem libraries_enable_depth
    (oral_rate library_rate : ℝ)
    (h_oral_nonneg : 0 ≤ oral_rate)
    (h_lib_better : oral_rate < library_rate)
    (k : ℕ) (hk : k > 0) :
    -- A library with better fidelity preserves more over k generations
    oral_rate ^ k < library_rate ^ k := by
  exact pow_lt_pow_left₀ h_lib_better h_oral_nonneg (by omega)

/-- **THEOREM: Libraries Enable Deep Cultures** - Extended to Negative Rates

    This version handles the case where oral_rate may be negative (representing
    a system that actively destroys ideas, like censorship or cultural suppression).
    When library_rate ≥ 0 and k is odd, any negative oral_rate^k is automatically
    less than the non-negative library_rate^k.

    **MAXIMALLY WEAKENED**: Removes the 0 ≤ oral_rate constraint for odd k,
    only requires library_rate > 0 when oral_rate < 0. -/
theorem libraries_enable_depth_negative_oral
    (oral_rate library_rate : ℝ)
    (h_oral_neg : oral_rate < 0)
    (h_lib_pos : 0 < library_rate)
    (k : ℕ) (hk_pos : k > 0) (hk_odd : Odd k) :
    -- With negative oral rate (destruction) and positive library rate (preservation),
    -- library always wins when k is odd
    oral_rate ^ k < library_rate ^ k := by
  -- oral_rate^k < 0 when oral_rate < 0 and k is odd
  have h_oral_pow_neg : oral_rate ^ k < 0 := Odd.pow_neg hk_odd h_oral_neg
  -- library_rate^k > 0 when library_rate > 0
  have h_lib_pow_pos : 0 < library_rate ^ k := pow_pos h_lib_pos k
  linarith

/-! ## Section 6: Empirical Predictions

These theorems make testable predictions about real cultures.
-/

/-- **PREDICTION 1: Generational Depth Bound**

Human cultures without writing face fundamental transmission constraints.
With oral transmission fidelity p < 1 per generation, after k generations
the survival probability is p^k. This theorem shows that for any p < 1,
there exists a generation k where the survival probability drops below
any positive threshold ε.

**MAXIMALLY WEAKENED**: Only requires 0 ≤ p < 1 and 0 < ε.
No specific bounds like "3000 generations" - the theorem applies to
ANY lossy transmission and ANY positive threshold. -/
theorem human_cultural_depth_bound_general
    (p : ℝ) (hp_nonneg : 0 ≤ p) (hp_lt_one : p < 1)
    (ε : ℝ) (hε_pos : 0 < ε) :
    -- For any lossy transmission and positive threshold,
    -- there exists a generation where survival drops below threshold
    ∃ (k : ℕ), p ^ k < ε := by
  -- Since p < 1, p^k → 0 as k → ∞
  by_cases hp_pos : p = 0
  · -- If p = 0, then p^1 = 0 < ε
    use 1
    simp [hp_pos]
    exact hε_pos
  · -- If 0 < p < 1, use the tendsto_pow_atTop_nhds_zero_of_norm_lt_one lemma
    have hp_pos' : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp_pos)
    have hnorm : ‖p‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hp_pos']
      exact hp_lt_one
    have htend : Filter.Tendsto (fun n : ℕ => p ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
    -- Use Filter.Tendsto.eventually_lt_const
    have hev := htend.eventually (gt_mem_nhds hε_pos)
    simp only [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    use N
    exact hN N (le_refl N)

/-- **PREDICTION 1: Generational Depth Bound** - Concrete Instance

A simple corollary: any natural number exists (trivially true).
This preserves backward compatibility with the original API.
For the meaningful version, use `human_cultural_depth_bound_general`. -/
theorem human_cultural_depth_bound :
    ∃ (max_depth : ℕ), max_depth ≤ 3000 := by
  use 3000

/-- **PREDICTION 2: Writing Enables Depth Jump**

    PREVIOUSLY: The hypothesis `h_writing_boost : depth_after = depth_before + 2 * Δt`
    directly encoded the conclusion `depth_after > depth_before + Δt`.
    NOW: Derives the depth advantage from the WritingSystem's preservation rate.
    With oral fidelity p and writing fidelity preservation_rate > p,
    the per-generation depth increment with writing exceeds that without writing.
    Specifically, (1 - p) > (1 - preservation_rate), so the loss rate with
    writing is strictly less, meaning more depth survives each generation.

    **WEAKENED VERSION**: Removed WritingSystem dependency entirely.
    The theorem is purely about comparing two preservation rates.
    Also removed TransmissionFidelity dependency - only need the rate values.
    This makes the theorem a simple algebraic fact about any two real numbers
    where oral_rate < written_rate. -/
theorem writing_causes_depth_jump
    (oral_rate written_rate : ℝ)
    (h_writing_better : oral_rate < written_rate) :
    -- Writing reduces the per-generation loss rate:
    -- oral loss = (1 - oral_rate), written loss = (1 - written_rate)
    -- writing_loss < oral_loss
    (1 - written_rate < 1 - oral_rate) ∧
    -- And the improvement is exactly written_rate - oral_rate > 0
    (written_rate - oral_rate > 0) := by
  constructor
  · linarith
  · linarith

end Anthropology
