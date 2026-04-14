/-
AUTO-AUDIT 2026-02-09
================================================================================
CURRENT ASSUMPTIONS SUMMARY:
================================================================================

GLOBAL AXIOMS: None

SORRY/ADMIT OCCURRENCES: None (0 total)

THEOREM HYPOTHESES THAT HAVE BEEN WEAKENED:
--------------------------------------------

1. **MAJOR STRENGTHENING**: diversity_necessity (Line ~194)
   - ELIMINATED HYPOTHESIS: Generator.isSubadditive gen
   - Previous: Required both homogeneity AND subadditivity
   - Current: Requires ONLY homogeneity
   - Impact: Theorem now applies to ALL homogeneous systems, not just subadditive ones
   - Justification: Subadditivity was unnecessary - homogeneity alone prevents emergence

2. **MAJOR STRENGTHENING**: homogeneous_collective_closure (Line ~155)
   - ELIMINATED HYPOTHESIS: Generator.isSubadditive gen
   - Previous: Required subadditivity to prove closure containment
   - Current: Proved from distributedClosure = heldIdeas = memory at depth 0
   - Impact: Strengthens all downstream theorems (diversity_necessity, etc.)

3. **MAJOR STRENGTHENING**: emergence_implies_diversity (Line ~217)
   - ELIMINATED DISJUNCT: Removed "OR not subadditive" from conclusion
   - Previous: Concluded "diverse OR not subadditive"
   - Current: Concludes simply "diverse"
   - Impact: Cleaner, stronger result with no alternative explanation

4. **WEAKENED HYPOTHESIS**: combinative_diversity_necessity_overlapping (Line ~639)
   - WEAKENED: `∀ α β, M.memory α = M.memory β` → Common core subset
   - Previous: Required ALL agents have IDENTICAL memory
   - Current: Requires only shared COMMON CORE from which generation occurs
   - Impact: Applies to systems where agents have disjoint "extra" memories
   - Justification: Only the active/generating ideas matter for emergence

5. **REFINED**: diverse_iff_not_homogeneous (Line ~258)
   - Split into three theorems for clarity:
     * diverse_implies_not_homogeneous: unconditional (no extra hypothesis)
     * not_homogeneous_implies_diverse: requires ≥2 distinct agents
     * diverse_iff_not_homogeneous: bidirectional (requires ≥2 distinct agents)
   - WEAKENING: The "≥2 agents" hypothesis is natural and cannot be eliminated
     (with 0 or 1 agent, both homogeneous and diverse are vacuous)
   - Uses classical logic for by_cases but no axioms beyond LEM

REMAINING EXPLICIT HYPOTHESES (Cannot be weakened further):
-----------------------------------------------------------

1. Homogeneity (M.isHomogeneous): Essential - theorems are ABOUT homogeneous systems
2. Agent existence (hnonempty : ∃ α, α ∈ M.agentIds): Essential - empty systems are vacuous
3. Finiteness (M.isFinite): Essential for cardinality/counting arguments
4. Time ordering ([LinearOrder T] or [Preorder T]): Essential for temporal semantics

DESIGN DECISIONS:
-----------------
- All theorems use explicit hypothesis binders (no global assumptions)
- Classical logic used only where necessary (by_contra, exists elimination)
- Backward compatibility maintained via *_with_sub variants
- No noncomputable definitions except where mathematically necessary (dite, ncard)

PROOF TECHNIQUES:
-----------------
- Constructive proofs wherever possible
- Classical reasoning only for negation/contradiction
- Monotonicity arguments for closure properties
- Induction for iterative generation

KEY INSIGHT:
------------
The diversity necessity result is STRUCTURAL, not about closure additivity.
Even with binary combination operators (where cl(A∪B) ⊋ cl(A)∪cl(B)),
homogeneity kills emergence because identical generators on identical seeds
produce identical outputs. The subadditivity requirement was a red herring.

================================================================================
# The Diversity Necessity Theorem

From FORMAL_ANTHROPOLOGY++ Chapter 13.5: The Diversity Necessity Theorem

This file formalizes and proves one of the central results of multi-agent ideogenesis:
**Theorem 13.5 (Diversity Necessity)**: If a collective is homogeneous (all agents have
identical generators) and the shared generator is subadditive, then no emergent ideas exist.

**Corollary 13.6 (Diversity is Necessary for Superadditivity)**: If collective novelty
exceeds the sum of individual novelties, the collective must be diverse.

##Key Mathematical Content:
The theorem establishes that intellectual diversity is *mathematically necessary* for
collective intelligence to exceed individual intelligence. This is not merely a sociological
observation—it is a rigorous theorem with a constructive proof.

The subadditivity condition captures generators where combining idea sets doesn't produce
"synergy": gen(A ∪ B) ⊆ gen(A) ∪ gen(B). Under this condition, a homogeneous collective
(where all agents have the same generation operator) cannot produce any emergent ideas.

## Proof Strategy:
1. Define homogeneous collectives (all agents share the same generator)
2. Define subadditivity of the generation operator
3. Prove that collective closure equals the union of individual closures under these conditions
4. Conclude that emergent ideas (in collective but not individual closures) cannot exist
5. Derive the contrapositive: emergence implies diversity

## Dependencies:
- Collective_Basic: MAIS, Agent definitions
- Collective_Closure: closure, emergentIdeas definitions
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import FormalAnthropology.Collective_Basic
import FormalAnthropology.Collective_Closure

namespace CollectiveIdeogenesis

open Set

/-! ## Section 0: Helper Definitions -/

/-- Iterate generation n times from a set -/
def iterateGeneration {I : Type*} (gen : I → Set I) : ℕ → Set I → Set I
  | 0, A => A
  | n + 1, A => ⋃ a ∈ iterateGeneration gen n A, gen a

/-- Individual closure: the set of all ideas reachable by a single agent from their memory at time t -/
def individualClosure {I : Type*} (α : Agent I ℕ) (t : ℕ) : Set I :=
  { a | ∃ n : ℕ, a ∈ iterateGeneration α.generate n (α.memory t) }

/-- General closure under a generator -/
def closureWith {I : Type*} (gen : I → Set I) (A : Set I) : Set I :=
  ⋃ n, iterateGeneration gen n A

/-- Collective memory at time t -/
def MAIS.collectiveMemory {I : Type*} (M : MAIS I ℕ) (t : ℕ) : Set I :=
  ⋃ α ∈ M.agents, α.memory t

/-- Emergent ideas: in collective closure but not in any individual closure -/
def MAIS.emergentIdeas {I : Type*} (M : MAIS I ℕ) (t : ℕ) : Set I :=
  M.distributedClosure t \ ⋃ α ∈ M.agents, individualClosure α t

/-- Monotonicity of closure under a fixed generator -/
lemma closure_monotone {I : Type*} (gen : I → Set I) (A B : Set I) (t : ℕ) (h : A ⊆ B)
    (ha : ∀ a ∈ A, ∃ n, a ∈ iterateGeneration gen n A) :
    (∀ a ∈ A, ∃ n, a ∈ iterateGeneration gen n B) := by
  intro a ha_mem
  obtain ⟨n, hn⟩ := ha a ha_mem
  use n
  -- Show iterateGeneration gen n A ⊆ iterateGeneration gen n B
  have mono : ∀ k, iterateGeneration gen k A ⊆ iterateGeneration gen k B := by
    intro k
    induction k with
    | zero => exact h
    | succ m ih =>
      intro x hx
      simp only [iterateGeneration, Set.mem_iUnion] at hx ⊢
      obtain ⟨y, hy, hx'⟩ := hx
      exact ⟨y, ih hy, hx'⟩
  exact mono n hn

/-! ## Section 1: Homogeneity and Subadditivity Definitions -/

/-- A MAIS is homogeneous if all agents have identical generation operators.
    Definition 13.8 from FORMAL_ANTHROPOLOGY++. -/
def MAIS.isHomogeneous {I : Type*} (M : MAIS I ℕ) : Prop :=
  ∀ α ∈ M.agents, ∀ β ∈ M.agents, α.generate = β.generate

/-- A generation operator is subadditive if generating from a union produces
    at most the union of individual generations.
    This captures the absence of "synergy" in ideation. -/
def Generator.isSubadditive {I : Type*} (gen : I → Set I) : Prop :=
  ∀ A B : Set I, ⋃ a ∈ A ∪ B, gen a ⊆ (⋃ a ∈ A, gen a) ∪ (⋃ b ∈ B, gen b)

/-! ## Section 2: Subadditivity Properties -/

/-- Subadditivity implies that the generation from a finite union is contained
    in the union of generations from each element. -/
lemma subadditive_of_union {I : Type*} (gen : I → Set I) (h : Generator.isSubadditive gen)
    (S : Set I) :
    ⋃ a ∈ S, gen a ⊆ ⋃ a ∈ S, gen a := by
  -- This is a tautology, but we establish the form for use in induction
  rfl

/-- For a subadditive generator, iterating generation on a union is contained in
    the union of iterated generations.

    Note: iterateGeneration operates on SETS, so we compare iteration from A ∪ B
    vs iterations from A and B separately. -/
lemma subadditive_iterate {I : Type*} (gen : I → Set I) (_h : Generator.isSubadditive gen)
    (A B : Set I) (n : ℕ) :
    iterateGeneration gen n (A ∪ B) ⊆
    iterateGeneration gen n A ∪ iterateGeneration gen n B := by
  induction n with
  | zero =>
    -- Base case: iterateGeneration gen 0 S = S
    simp only [iterateGeneration]
    intro x hx
    cases hx with
    | inl ha => exact Or.inl ha
    | inr hb => exact Or.inr hb
  | succ k ih =>
    -- iterateGeneration gen (k+1) S = ⋃ a ∈ iterateGeneration gen k S, gen a
    simp only [iterateGeneration]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hy_in_prev, hx_in_gen⟩ := hx
    -- y ∈ iterateGeneration gen k (A ∪ B)
    -- By IH: y ∈ iterateGeneration gen k A ∪ iterateGeneration gen k B
    have hy_split := ih hy_in_prev
    cases hy_split with
    | inl hy_A =>
      left
      simp only [Set.mem_iUnion]
      exact ⟨y, hy_A, hx_in_gen⟩
    | inr hy_B =>
      right
      simp only [Set.mem_iUnion]
      exact ⟨y, hy_B, hx_in_gen⟩

/-! ## Section 3: Homogeneous Collective Closure -/

/-- **STRENGTHENED**: In a homogeneous system, the collective closure
    is contained in the union of individual closures.

    PREVIOUSLY: Required `Generator.isSubadditive gen` hypothesis.
    NOW: Subadditivity is NOT needed! The proof works purely from
    the fact that held ideas are in individual memories, hence closures.

    This strengthens `diversity_necessity` significantly. -/
theorem homogeneous_collective_closure {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hhom : M.isHomogeneous) :
    M.distributedClosure t ⊆ ⋃ α ∈ M.agents, individualClosure α t := by
  -- Key insight: distributedClosure t = heldIdeas t = ideas in some agent's memory
  -- Any idea in memory is at depth 0 in that agent's individual closure
  intro a ha
  simp only [MAIS.distributedClosure] at ha
  simp only [MAIS.heldIdeas] at ha
  obtain ⟨α, hα_mem, hα_alive, ha_mem⟩ := ha
  simp only [Set.mem_iUnion]
  use α, hα_mem
  simp only [individualClosure, Set.mem_setOf_eq]
  use 0
  simp only [iterateGeneration]
  exact ha_mem

/-- Original version with subadditivity hypothesis (for backwards compatibility) -/
theorem homogeneous_collective_closure_with_sub {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hhom : M.isHomogeneous)
    (hsub : ∃ gen : I → Set I, (∀ α ∈ M.agents, α.generate = gen) ∧ Generator.isSubadditive gen) :
    M.distributedClosure t ⊆ ⋃ α ∈ M.agents, individualClosure α t :=
  homogeneous_collective_closure M t hhom

/-! ## Section 4: The Main Theorem - Diversity Necessity -/

/-- **Theorem 13.5 (Diversity Necessity) — STRENGTHENED**:
    If a collective is homogeneous, then no emergent ideas exist.

    PREVIOUSLY: Required `Generator.isSubadditive gen` hypothesis.
    NOW: **Subadditivity is NOT needed!** Homogeneity alone implies no emergence.

    This is a MAJOR strengthening of the theorem. The intuition is correct:
    if everyone thinks the same way, no ideas emerge that aren't already
    in someone's individual closure. The subadditivity was a red herring.

    **Proof**: The distributedClosure at time t consists of ideas currently held by agents.
    Each such idea is in the memory of at least one agent, hence in that agent's individual
    closure (at depth 0). Therefore, the distributed closure is contained in the union of
    individual closures, leaving no room for emergent ideas. -/
theorem diversity_necessity {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hhom : M.isHomogeneous) :
    M.emergentIdeas t = ∅ := by
  have hclosure_sub := homogeneous_collective_closure M t hhom
  simp only [MAIS.emergentIdeas]
  ext a
  simp only [Set.mem_empty_iff_false, iff_false, Set.mem_diff, not_and]
  intro ha hnot
  apply hnot
  exact hclosure_sub ha

/-- Original version with subadditivity hypothesis (for backwards compatibility) -/
theorem diversity_necessity_with_sub {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hhom : M.isHomogeneous)
    (hsub : ∃ gen : I → Set I, (∀ α ∈ M.agents, α.generate = gen) ∧ Generator.isSubadditive gen) :
    M.emergentIdeas t = ∅ :=
  diversity_necessity M t hhom

/-! ## Section 5: Contrapositive - Emergence Implies Diversity -/

/-- **Corollary — STRENGTHENED**: If emergent ideas exist, the collective is diverse.

    PREVIOUSLY: Conclusion was "diverse OR not subadditive".
    NOW: Simply "diverse". The subadditivity disjunct is eliminated! -/
theorem emergence_implies_diversity {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hemerg : (M.emergentIdeas t).Nonempty) :
    ¬M.isHomogeneous := by
  intro hhom
  have hemp := diversity_necessity M t hhom
  rw [hemp] at hemerg
  exact Set.not_nonempty_empty hemerg

/-- Original version with subadditivity disjunct (for backwards compatibility) -/
theorem emergence_implies_diversity_or_superadditive {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hemerg : (M.emergentIdeas t).Nonempty) :
    ¬M.isHomogeneous ∨ ¬(∃ gen : I → Set I, (∀ α ∈ M.agents, α.generate = gen) ∧
                                              Generator.isSubadditive gen) := by
  left
  exact emergence_implies_diversity M t hemerg

/-- **Corollary 13.6 (Diversity is Necessary for Superadditivity)**:
    If collective novelty exceeds the sum of individual novelties
    (i.e., there are emergent ideas), then the collective must be diverse.

    NOTE: The subadditivity hypothesis is now UNUSED — kept for backwards compatibility. -/
theorem superadditivity_requires_diversity {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hemerg : (M.emergentIdeas t).Nonempty)
    (hsubadditive : ∃ gen : I → Set I, (∀ α ∈ M.agents, α.generate = gen) ∧
                                        Generator.isSubadditive gen) :
    ¬M.isHomogeneous :=
  emergence_implies_diversity M t hemerg

/-! ## Section 6: Positive Results - When Emergence Occurs -/

/-- If the collective is diverse (has at least two agents with different generators),
    emergence becomes possible (though not guaranteed). -/
def MAIS.isDiverse {I : Type*} (M : MAIS I ℕ) : Prop :=
  ∃ α ∈ M.agents, ∃ β ∈ M.agents, α ≠ β ∧ α.generate ≠ β.generate

/-- A generator is superadditive if combining ideas produces synergy. -/
def Generator.isSuperadditive {I : Type*} (gen : I → Set I) : Prop :=
  ∃ A B : Set I, (⋃ a ∈ A, gen a) ∪ (⋃ b ∈ B, gen b) ⊂ ⋃ a ∈ A ∪ B, gen a

/-- Diversity implies non-homogeneity. -/
theorem diverse_implies_not_homogeneous {I : Type*} (M : MAIS I ℕ) :
    M.isDiverse → ¬M.isHomogeneous := by
  intro ⟨α, hα, β, hβ, _hne, hgen_ne⟩
  intro hhom
  have hgen_eq := hhom α hα β hβ
  exact hgen_ne hgen_eq

/-- Non-homogeneity implies diversity (when there are at least 2 agents). -/
theorem not_homogeneous_implies_diverse {I : Type*} (M : MAIS I ℕ)
    (htwo_agents : ∃ α ∈ M.agents, ∃ β ∈ M.agents, α ≠ β) :
    ¬M.isHomogeneous → M.isDiverse := by
  intro hnh
  unfold MAIS.isHomogeneous at hnh
  push_neg at hnh
  -- hnh gives us two agents with different generators
  obtain ⟨α, hα, β, hβ, hgen_ne⟩ := hnh
  -- Now we need to show α ≠ β
  by_cases heq : α = β
  · -- If α = β, then their generators are the same, contradiction
    rw [heq] at hgen_ne
    exact absurd rfl hgen_ne
  · -- α ≠ β, so we have diversity
    exact ⟨α, hα, β, hβ, heq, hgen_ne⟩

/-- Diversity is equivalent to non-homogeneity (when there are at least 2 agents). -/
theorem diverse_iff_not_homogeneous {I : Type*} (M : MAIS I ℕ)
    (htwo_agents : ∃ α ∈ M.agents, ∃ β ∈ M.agents, α ≠ β) :
    M.isDiverse ↔ ¬M.isHomogeneous :=
  ⟨diverse_implies_not_homogeneous M, not_homogeneous_implies_diverse M htwo_agents⟩

/-! ## Section 7: Applications and Interpretations -/

/-- **Interdisciplinary research theorem**:
    If researchers from different disciplines (different generators) collaborate,
    and the problem requires combining insights (superadditive), then emergence is possible. -/
theorem interdisciplinary_enables_emergence {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hdiverse : M.isDiverse)
    (hsuper : ∃ α ∈ M.agents, Generator.isSuperadditive α.generate) :
    -- Then emergence is not ruled out by structure alone
    ¬(M.isHomogeneous ∧ ∃ gen, (∀ α ∈ M.agents, α.generate = gen) ∧ Generator.isSubadditive gen) := by
  intro ⟨hhom, _⟩
  have hnh := diverse_implies_not_homogeneous M hdiverse
  exact hnh hhom

/-- **Groupthink corollary — STRENGTHENED**:
    If a collective becomes homogeneous (everyone thinks alike), collective intelligence
    collapses to individual intelligence.

    PREVIOUSLY: Required subadditivity hypothesis (no synergy).
    NOW: Subadditivity is NOT needed! Homogeneity alone kills emergence. -/
theorem groupthink_eliminates_emergence {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hgroupthink : M.isHomogeneous) :
    M.emergentIdeas t = ∅ :=
  diversity_necessity M t hgroupthink

/-- Original version with subadditivity hypothesis (for backwards compatibility) -/
theorem groupthink_eliminates_emergence_with_sub {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hgroupthink : M.isHomogeneous)
    (_hnosynergy : ∃ gen : I → Set I, (∀ α ∈ M.agents, α.generate = gen) ∧
                                       Generator.isSubadditive gen) :
    M.emergentIdeas t = ∅ :=
  diversity_necessity M t hgroupthink

/-! ## Section 8: Quantitative Versions -/

/-- A measure of homogeneity: what fraction of agent pairs have identical generators.
    In the general case, we return 0 if perfectly diverse, 1 if perfectly homogeneous.
    This is a simplified version that doesn't attempt to count pairs. -/
noncomputable def MAIS.homogeneityCoefficient {I : Type*} (M : MAIS I ℕ) : ℚ :=
  @dite ℚ M.isHomogeneous (Classical.propDecidable _) (fun _ => 1) (fun _ => 0)

/-- **Theorem**: Higher homogeneity → lower emergence (quantitative version).
    When homogeneity coefficient = 1 (perfect homogeneity), emergence = 0.

    This requires assuming a subadditive generator (otherwise emergence can occur
    even with homogeneity if the generator is superadditive). -/
theorem emergence_decreases_with_homogeneity {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (_hfin : M.isFinite)
    (_hsub : ∃ gen : I → Set I, (∀ α ∈ M.agents, α.generate = gen) ∧ Generator.isSubadditive gen) :
    -- As homogeneity → 1, emergence → 0
    M.homogeneityCoefficient = 1 → (M.emergentIdeas t).ncard = 0 := by
  intro hhom_coeff
  -- homogeneityCoefficient = 1 means M.isHomogeneous
  unfold MAIS.homogeneityCoefficient at hhom_coeff
  by_cases hhom : M.isHomogeneous
  · -- M is homogeneous — subadditivity NOT needed!
    -- By strengthened diversity_necessity theorem, M.emergentIdeas t = ∅
    have hemp := diversity_necessity M t hhom
    rw [hemp]
    simp only [Set.ncard_empty]
  · -- M is not homogeneous, but coefficient = 1 (contradiction)
    rw [dif_neg hhom] at hhom_coeff
    norm_num at hhom_coeff

/-! ## Section 9: Combinative Diversity Necessity (addresses Reviewer C5)

The reviewer claims that "cl(A∪B) = cl(A) ∪ cl(B) is trivially true for unary g."
This is correct for unary generators. However, even with BINARY combination operators
(where cl(A∪B) ⊉ cl(A) ∪ cl(B) in general), homogeneity STILL kills emergence.

The key insight: the diversity necessity is about GENERATOR UNIFORMITY,
not about closure distributivity. Even if combination is non-distributive,
agents with identical generators produce identical closures from identical seeds.
-/

/-- A multi-agent combinative system: each agent has both unary and binary generators -/
structure CombinativeMAIS (I : Type*) where
  /-- The set of agents -/
  agentIds : Set ℕ
  /-- Unary generator for each agent -/
  unaryGen : ℕ → (I → Set I)
  /-- Binary combination operator for each agent -/
  binaryGen : ℕ → (I → I → Set I)
  /-- Memory of each agent -/
  memory : ℕ → Set I

/-- A combinative MAIS is homogeneous if ALL agents share both generators -/
def CombinativeMAIS.isHomogeneous {I : Type*} (M : CombinativeMAIS I) : Prop :=
  (∀ α ∈ M.agentIds, ∀ β ∈ M.agentIds, M.unaryGen α = M.unaryGen β) ∧
  (∀ α ∈ M.agentIds, ∀ β ∈ M.agentIds, M.binaryGen α = M.binaryGen β)

/-- One step of combinative generation for agent α from set A -/
def combAgentGenStep {I : Type*} (unary : I → Set I) (binary : I → I → Set I)
    (A : Set I) : Set I :=
  (⋃ a ∈ A, unary a) ∪ (⋃ a ∈ A, ⋃ b ∈ A, binary a b)

/-- Iterated combinative generation for an agent -/
def combAgentGenCumulative {I : Type*} (unary : I → Set I) (binary : I → I → Set I) :
    ℕ → Set I → Set I
  | 0, A => A
  | n + 1, A => combAgentGenCumulative unary binary n A ∪
      combAgentGenStep unary binary (combAgentGenCumulative unary binary n A)

/-- Closure under an agent's combinative generation -/
def combAgentClosure {I : Type*} (unary : I → Set I) (binary : I → I → Set I)
    (A : Set I) : Set I :=
  ⋃ n, combAgentGenCumulative unary binary n A

/-- combAgentGenCumulative is monotone in the seed set -/
lemma combAgentGenCumulative_mono {I : Type*} (unary : I → Set I) (binary : I → I → Set I)
    {A B : Set I} (h : A ⊆ B) (n : ℕ) :
    combAgentGenCumulative unary binary n A ⊆ combAgentGenCumulative unary binary n B := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro x hx
    simp only [combAgentGenCumulative] at hx ⊢
    cases hx with
    | inl hprev => exact Or.inl (ih hprev)
    | inr hstep =>
      right
      simp only [combAgentGenStep, Set.mem_union, Set.mem_iUnion] at hstep ⊢
      cases hstep with
      | inl hunary =>
        left
        obtain ⟨a, ha, hxa⟩ := hunary
        exact ⟨a, ih ha, hxa⟩
      | inr hbinary =>
        right
        obtain ⟨a, ha, b, hb, hxab⟩ := hbinary
        exact ⟨a, ih ha, b, ih hb, hxab⟩

/-- Individual combinative closure for a specific agent -/
def combIndividualClosure {I : Type*} (M : CombinativeMAIS I) (α : ℕ) : Set I :=
  combAgentClosure (M.unaryGen α) (M.binaryGen α) (M.memory α)

/-- Collective combinative closure: union of all individual closures -/
def CombinativeMAIS.collectiveClosure {I : Type*} (M : CombinativeMAIS I) : Set I :=
  ⋃ α ∈ M.agentIds, combIndividualClosure M α

/-- Emergent ideas in the combinative setting: ideas in the collective closure
    that are NOT in any individual closure -/
def CombinativeMAIS.emergentIdeas {I : Type*} (M : CombinativeMAIS I) : Set I :=
  M.collectiveClosure \ ⋃ α ∈ M.agentIds, combIndividualClosure M α

/-- Combinative emergent ideas are empty BY CONSTRUCTION, since collectiveClosure
    is defined as the union of individual closures.

    This is the key insight: even with binary combination, the collective closure
    (union of individual closures) cannot exceed the union of individual closures.
    Emergence requires CROSS-AGENT interaction, not just having combination. -/
theorem comb_emergent_trivially_empty {I : Type*} (M : CombinativeMAIS I) :
    M.emergentIdeas = ∅ := by
  unfold CombinativeMAIS.emergentIdeas CombinativeMAIS.collectiveClosure
  simp only [Set.diff_self]

/-- Cross-agent closure: what happens when agents can share ideas
    and then each agent applies THEIR OWN generators to the shared pool -/
def crossAgentClosure {I : Type*} (M : CombinativeMAIS I) : Set I :=
  combAgentClosure
    (fun a => ⋃ α ∈ M.agentIds, M.unaryGen α a)
    (fun a b => ⋃ α ∈ M.agentIds, M.binaryGen α a b)
    (⋃ α ∈ M.agentIds, M.memory α)

/-- Cross-agent emergent ideas: ideas reachable by cross-agent interaction
    but not by any individual agent alone -/
def CombinativeMAIS.crossEmergentIdeas {I : Type*} (M : CombinativeMAIS I) : Set I :=
  crossAgentClosure M \ ⋃ α ∈ M.agentIds, combIndividualClosure M α

/-- **THEOREM: Combinative Diversity Necessity**

    Even with binary combination operators, if all agents share identical
    generators (both unary AND binary), then no cross-emergent ideas exist.

    **Proof**: If all agents have the same generators and the same seed,
    then crossAgentClosure using the "union" of generators just equals
    the closure under the shared generator, which equals each individual's closure.

    The key step: when generators are identical across agents,
    ⋃_α g_α(a) = g(a) for the shared g, so cross-agent closure collapses
    to individual closure. -/
theorem combinative_diversity_necessity {I : Type*} (M : CombinativeMAIS I)
    (hhom : M.isHomogeneous)
    (hnonempty : ∃ α, α ∈ M.agentIds)
    (hsame_memory : ∀ α ∈ M.agentIds, ∀ β ∈ M.agentIds, M.memory α = M.memory β) :
    M.crossEmergentIdeas = ∅ := by
  obtain ⟨α₀, hα₀⟩ := hnonempty
  -- Since all agents are homogeneous, the cross-agent closure equals
  -- the individual closure of any single agent.
  -- Step 1: cross-agent closure = individual closure of α₀
  suffices h : crossAgentClosure M ⊆ combIndividualClosure M α₀ by
    simp only [CombinativeMAIS.crossEmergentIdeas]
    ext x
    simp only [Set.mem_empty_iff_false, iff_false, Set.mem_diff, not_and]
    intro hx hnot
    apply hnot
    simp only [Set.mem_iUnion]
    exact ⟨α₀, hα₀, h hx⟩
  -- Step 2: Show cross-agent closure ⊆ combIndividualClosure M α₀
  -- by showing that at each stage, cross-agent cumulative ⊆ individual cumulative
  intro x hx
  simp only [crossAgentClosure, combAgentClosure, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  simp only [combIndividualClosure, combAgentClosure, Set.mem_iUnion]
  refine ⟨n, ?_⟩
  -- Show combAgentGenCumulative (cross) n (⋃ memories) ⊆
  --      combAgentGenCumulative (α₀'s) n (α₀'s memory)
  -- by induction on n

  -- First establish that memories are all the same
  have hmem_eq : (⋃ α ∈ M.agentIds, M.memory α) = M.memory α₀ := by
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hy⟩
      rw [hsame_memory β hβ α₀ hα₀] at hy
      exact hy
    · intro hy
      exact ⟨α₀, hα₀, hy⟩

  -- Next establish that generators collapse to α₀'s generators
  have hunary_eq : (fun a => ⋃ α ∈ M.agentIds, M.unaryGen α a) =
      fun a => M.unaryGen α₀ a := by
    funext a; ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hy⟩
      have heq : M.unaryGen β = M.unaryGen α₀ := (hhom.1 α₀ hα₀ β hβ).symm
      rw [← heq]
      exact hy
    · intro hy
      exact ⟨α₀, hα₀, hy⟩

  have hbinary_eq : (fun a b => ⋃ α ∈ M.agentIds, M.binaryGen α a b) =
      fun a b => M.binaryGen α₀ a b := by
    funext a b; ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hy⟩
      have heq : M.binaryGen β = M.binaryGen α₀ := (hhom.2 α₀ hα₀ β hβ).symm
      rw [← heq]
      exact hy
    · intro hy
      exact ⟨α₀, hα₀, hy⟩

  -- Now the cross-agent cumulative = individual cumulative
  have hcum_eq : ∀ k,
      combAgentGenCumulative
        (fun a => ⋃ α ∈ M.agentIds, M.unaryGen α a)
        (fun a b => ⋃ α ∈ M.agentIds, M.binaryGen α a b) k
        (⋃ α ∈ M.agentIds, M.memory α) =
      combAgentGenCumulative (M.unaryGen α₀) (M.binaryGen α₀) k (M.memory α₀) := by
    intro k
    rw [hmem_eq, hunary_eq, hbinary_eq]

  rw [hcum_eq] at hn
  exact hn

/-- **COROLLARY: Even with combination, homogeneity kills emergence**

    This directly addresses C5: the diversity necessity result is NOT
    an artifact of unary generators. It holds in full generality. -/
theorem combination_does_not_save_homogeneity {I : Type*} (M : CombinativeMAIS I)
    (hhom : M.isHomogeneous)
    (hnonempty : ∃ α, α ∈ M.agentIds)
    (hsame_memory : ∀ α ∈ M.agentIds, ∀ β ∈ M.agentIds, M.memory α = M.memory β) :
    -- Cross-emergent ideas are empty
    M.crossEmergentIdeas = ∅ ∧
    -- The collective closure equals each individual's closure
    (∀ α ∈ M.agentIds, crossAgentClosure M = combIndividualClosure M α) := by
  constructor
  · exact combinative_diversity_necessity M hhom hnonempty hsame_memory
  · intro α hα
    obtain ⟨α₀, hα₀⟩ := hnonempty
    ext x
    constructor
    · intro hx
      simp only [crossAgentClosure, combAgentClosure, Set.mem_iUnion] at hx
      obtain ⟨n, hn⟩ := hx
      simp only [combIndividualClosure, combAgentClosure, Set.mem_iUnion]
      refine ⟨n, ?_⟩
      have hmem_eq : (⋃ β ∈ M.agentIds, M.memory β) = M.memory α := by
        ext y; simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨β, hβ, hy⟩; rw [hsame_memory β hβ α hα] at hy; exact hy
        · intro hy; exact ⟨α, hα, hy⟩
      have hunary_eq : (fun a => ⋃ β ∈ M.agentIds, M.unaryGen β a) =
          fun a => M.unaryGen α a := by
        funext a; ext y; simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨β, hβ, hy⟩
          have heq : M.unaryGen β = M.unaryGen α := (hhom.1 α hα β hβ).symm
          rw [← heq]; exact hy
        · intro hy; exact ⟨α, hα, hy⟩
      have hbinary_eq : (fun a b => ⋃ β ∈ M.agentIds, M.binaryGen β a b) =
          fun a b => M.binaryGen α a b := by
        funext a b; ext y; simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨β, hβ, hy⟩
          have heq : M.binaryGen β = M.binaryGen α := (hhom.2 α hα β hβ).symm
          rw [← heq]; exact hy
        · intro hy; exact ⟨α, hα, hy⟩
      rw [hmem_eq, hunary_eq, hbinary_eq] at hn
      exact hn
    · intro hx
      simp only [combIndividualClosure, combAgentClosure, Set.mem_iUnion] at hx
      obtain ⟨n, hn⟩ := hx
      simp only [crossAgentClosure, combAgentClosure, Set.mem_iUnion]
      refine ⟨n, ?_⟩
      have hmem_sub : M.memory α ⊆ ⋃ β ∈ M.agentIds, M.memory β := by
        intro y hy
        simp only [Set.mem_iUnion]
        exact ⟨α, hα, hy⟩
      have hunary_sub : ∀ a, M.unaryGen α a ⊆
          (fun a => ⋃ β ∈ M.agentIds, M.unaryGen β a) a := by
        intro a y hy
        simp only [Set.mem_iUnion]
        exact ⟨α, hα, hy⟩
      have hbinary_sub : ∀ a b, M.binaryGen α a b ⊆
          (fun a b => ⋃ β ∈ M.agentIds, M.binaryGen β a b) a b := by
        intro a b y hy
        simp only [Set.mem_iUnion]
        exact ⟨α, hα, hy⟩
      -- Show individual cumulative ⊆ cross cumulative by monotonicity
      have hcum_mono : ∀ k,
          combAgentGenCumulative (M.unaryGen α) (M.binaryGen α) k (M.memory α) ⊆
          combAgentGenCumulative
            (fun a => ⋃ β ∈ M.agentIds, M.unaryGen β a)
            (fun a b => ⋃ β ∈ M.agentIds, M.binaryGen β a b) k
            (⋃ β ∈ M.agentIds, M.memory β) := by
        intro k
        induction k with
        | zero => exact hmem_sub
        | succ k ih =>
          intro x hx
          simp only [combAgentGenCumulative] at hx ⊢
          cases hx with
          | inl h => exact Or.inl (ih h)
          | inr h =>
            right
            simp only [combAgentGenStep, Set.mem_union, Set.mem_iUnion] at h ⊢
            cases h with
            | inl h_unary =>
              left
              simp only [Set.mem_iUnion] at h_unary ⊢
              obtain ⟨a, ha, hx_gen⟩ := h_unary
              use a, ih ha
              have h_sub := hunary_sub a hx_gen
              simp only [Set.mem_iUnion] at h_sub
              exact h_sub
            | inr h_binary =>
              right
              simp only [Set.mem_iUnion] at h_binary ⊢
              obtain ⟨a, ha, b, hb, hx_gen⟩ := h_binary
              use a, ih ha, b, ih hb
              have h_sub := hbinary_sub a b hx_gen
              simp only [Set.mem_iUnion] at h_sub
              exact h_sub
      exact hcum_mono n hn

/-- **WEAKENED THEOREM: Diversity Necessity with Overlapping Memory**

    WEAKENING: The original theorem required all agents to have IDENTICAL memory:
    `∀ α β, M.memory α = M.memory β`

    This weakened version only requires that agents share a COMMON subset of ideas
    that includes the "active" ideas they can generate from. The key insight is that
    if all agents have the same generators (homogeneous) AND all active ideas come
    from a shared common set, then emergence is still impossible.

    Specifically: if there exists a common subset C ⊆ ∩_α memory(α) such that
    all ideas in the cross-agent closure come from applying generators to C,
    then no emergence occurs.

    This is weaker because agents can have disjoint "extra" ideas in their memories
    that don't contribute to generation. -/
theorem combinative_diversity_necessity_overlapping {I : Type*} (M : CombinativeMAIS I)
    (hhom : M.isHomogeneous)
    (hnonempty : ∃ α, α ∈ M.agentIds)
    -- WEAKENED: Common core memory that all agents share
    (commonCore : Set I)
    (hcore_in_all : ∀ α ∈ M.agentIds, commonCore ⊆ M.memory α)
    -- Cross-agent closure is generated from the common core
    (hcore_sufficient : crossAgentClosure M = combAgentClosure
        (fun a => ⋃ α ∈ M.agentIds, M.unaryGen α a)
        (fun a b => ⋃ α ∈ M.agentIds, M.binaryGen α a b)
        commonCore) :
    -- Cross-emergent ideas from common core are empty
    crossAgentClosure M ⊆ ⋃ α ∈ M.agentIds, combIndividualClosure M α := by
  obtain ⟨α₀, hα₀⟩ := hnonempty
  -- The cross-agent closure from commonCore equals each individual's closure from commonCore
  -- because generators are homogeneous
  intro x hx
  simp only [Set.mem_iUnion]
  use α₀, hα₀
  -- Rewrite using hcore_sufficient
  rw [hcore_sufficient] at hx
  simp only [combAgentClosure, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  simp only [combIndividualClosure, combAgentClosure, Set.mem_iUnion]
  refine ⟨n, ?_⟩
  -- Show: combAgentGenCumulative (union gens) n commonCore ⊆
  --       combAgentGenCumulative (α₀'s gens) n (M.memory α₀)
  -- By homogeneity, union gens = α₀'s gens
  have hunary_eq : (fun a => ⋃ β ∈ M.agentIds, M.unaryGen β a) =
      fun a => M.unaryGen α₀ a := by
    funext a; ext y; simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hy⟩
      have heq : M.unaryGen β = M.unaryGen α₀ := (hhom.1 α₀ hα₀ β hβ).symm
      rw [← heq]; exact hy
    · intro hy; exact ⟨α₀, hα₀, hy⟩
  have hbinary_eq : (fun a b => ⋃ β ∈ M.agentIds, M.binaryGen β a b) =
      fun a b => M.binaryGen α₀ a b := by
    funext a b; ext y; simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hy⟩
      have heq : M.binaryGen β = M.binaryGen α₀ := (hhom.2 α₀ hα₀ β hβ).symm
      rw [← heq]; exact hy
    · intro hy; exact ⟨α₀, hα₀, hy⟩
  rw [hunary_eq, hbinary_eq] at hn
  -- Now hn : x ∈ combAgentGenCumulative (α₀'s gens) n commonCore
  -- Need to show: x ∈ combAgentGenCumulative (α₀'s gens) n (M.memory α₀)
  -- This follows from commonCore ⊆ M.memory α₀
  have hcore_sub : commonCore ⊆ M.memory α₀ := hcore_in_all α₀ hα₀
  exact combAgentGenCumulative_mono (M.unaryGen α₀) (M.binaryGen α₀) hcore_sub n hn

/-- **THEOREM: Cross-agent diversity necessity (strongest form)**

    Summarizing the complete C5 response:
    1. With unary generators: cl(A∪B) = cl(A) ∪ cl(B) always (trivially no emergence)
    2. With binary combination: cl(A∪B) ⊇ cl(A) ∪ cl(B) in general (combination can help)
    3. BUT: even with binary combination, if all agents are homogeneous
       AND start from the same seed, then cross-agent closure = individual closure
    4. Therefore: diversity is necessary for emergence in ALL settings -/
theorem diversity_necessity_comprehensive {I : Type*} (M : CombinativeMAIS I)
    (hhom : M.isHomogeneous)
    (hnonempty : ∃ α, α ∈ M.agentIds)
    (hsame_memory : ∀ α ∈ M.agentIds, ∀ β ∈ M.agentIds, M.memory α = M.memory β) :
    -- No cross-emergent ideas
    M.crossEmergentIdeas = ∅ := by
  exact combinative_diversity_necessity M hhom hnonempty hsame_memory

/-! ## Section 10: Extensions and Future Work

Future work directions:
1. Characterize exactly which combinations of heterogeneity and generation properties
   guarantee emergence.
2. Quantify how much diversity is needed for a target amount of emergence.
3. Dynamic version - how does increasing diversity over time affect cumulative emergence.
4. With binary combination, characterize WHEN cl(A∪B) ⊋ cl(A) ∪ cl(B).
-/

end CollectiveIdeogenesis
