/-
# Collective Ideogenesis: Scientific Communities

This file formalizes Scientific Communities from MULTI_AGENT_IDEOGENESIS++ Chapter 10:

- Definition 10.1: Scientific Idea
- Definition 10.2: Scientific Generation
- Definition 10.3: Scientific Transmission
- Definition 10.4: Replicated Idea
- Theorem 10.1: Replication and Redundancy
- Predictions 1-5: Testable scientific predictions

Science is modeled as a paradigmatic multi-agent ideogenetic system with
scientists as agents, papers as transmissions, and citations as channels.

## CURRENT ASSUMPTIONS AND PROOF STATUS

This file contains **0 sorries, 0 admits, 0 axioms** - all proofs are complete.

### Assumptions weakened in this version:
1. **Disciplinary coherence** (line 169-172): Weakened from "all ideas must be in discipline" to 
   "agents have a primary discipline" - scientists can do interdisciplinary work freely
2. **Replication independence** (line 246): Weakened from "completely disjoint primordials" to 
   "distinct agents" - allows shared foundational knowledge between scientists
3. **Anomaly definition** (line 355): Weakened from "contradicts ALL core ideas for ALL agents" to
   "contradicts SOME core idea for SOME agent" - much more realistic paradigm conflicts
4. **Collaboration definition** (line 234-238): Weakened from "bidirectional communication required" to
   "any communication in either direction" - captures citations, reading, asymmetric influence
5. **Finite assumptions**: Made explicit and minimized - only required where mathematically necessary
   for cardinality counting. Added qualitative versions that require NO finiteness assumptions.

### Theorems proven without sorries:
- `interdisciplinary_has_multiple_disciplines` (line 197): Qualitative version - NO finiteness required
- `interdisciplinary_higher_diversity` (line 203): Interdisciplinary boundaries have diversity > 1
- `replicated_has_multiple_sources` (line 295): Qualitative version - NO finiteness required  
- `replicated_implies_redundant` (line 307): Replicated ideas have redundancy ≥ 2  
- `established_resilient` (line 379): Well-established ideas survive agent removal
- `crisis_risk_not_established` (line 466): Crisis-risk ideas are not well-established

All theorems now apply much more broadly due to significantly weakened assumptions.
The model now captures realistic scientific communities where:
- Scientists collaborate across disciplines
- Scientists share common training and foundational knowledge
- Anomalies are specific conflicts, not universal impossibilities
- Scientific influence is asymmetric (citations, one-way reading)
- Two versions of key theorems: qualitative (no finiteness) and quantitative (with finiteness)
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import FormalAnthropology.Collective_Basic
import FormalAnthropology.Collective_Depth
import FormalAnthropology.Collective_Closure
import FormalAnthropology.Collective_Provenance

namespace CollectiveIdeogenesis

open Classical
attribute [local instance] Classical.propDecidable

/-! ## Definition 10.1: Scientific Idea

In this application, an idea is a hypothesis, theory, method, fact, result, or question.
-/

/-- The type of scientific ideas, categorized by kind -/
inductive ScientificIdeaKind where
  | hypothesis : ScientificIdeaKind
  | theory : ScientificIdeaKind
  | method : ScientificIdeaKind
  | fact : ScientificIdeaKind
  | result : ScientificIdeaKind
  | question : ScientificIdeaKind
deriving DecidableEq

/-- A scientific idea has a kind and content -/
structure ScientificIdea (Content : Type*) where
  kind : ScientificIdeaKind
  content : Content
deriving DecidableEq

/-! ## Definition 10.2: Scientific Generation

A scientist's generation function produces:
- Implications of ideas
- Questions raised by ideas
- Experiments suggested by ideas
- Applications of ideas
- Critiques of ideas
-/

/-- Type of generative relationships in science -/
inductive ScientificGenerationType where
  | implication : ScientificGenerationType
  | question : ScientificGenerationType
  | experiment : ScientificGenerationType
  | application : ScientificGenerationType
  | critique : ScientificGenerationType
deriving DecidableEq

/-- A scientific generation is a pair of ideas with a relationship type -/
structure ScientificGeneration (Content : Type*) where
  source : ScientificIdea Content
  target : ScientificIdea Content
  genType : ScientificGenerationType

/-- A scientist's generation function produces ideas through various modes -/
def scientificGeneration {Content : Type*} 
    (implications questions experiments applications critiques : 
      ScientificIdea Content → Set (ScientificIdea Content)) :
    ScientificIdea Content → Set (ScientificIdea Content) :=
  fun a => implications a ∪ questions a ∪ experiments a ∪ applications a ∪ critiques a

/-! ## Definition 10.3: Scientific Transmission

Transmission occurs via publication, teaching, collaboration, conferences,
and informal communication.
-/

/-- Modes of scientific transmission -/
inductive TransmissionMode where
  | publication : TransmissionMode    -- papers, books
  | teaching : TransmissionMode       -- lectures, mentorship
  | collaboration : TransmissionMode  -- co-authorship
  | conference : TransmissionMode     -- talks, posters
  | informal : TransmissionMode       -- conversations, emails
deriving DecidableEq

/-- Properties of transmission modes affecting reliability and speed -/
structure TransmissionModeProperties where
  /-- How formally this mode transmits (1 = highly formal, 0 = informal) -/
  formality : ℚ
  /-- Expected delay (in time units) for this mode -/
  typicalDelay : ℕ
  /-- Whether this mode is persistent (papers) vs ephemeral (conversations) -/
  isPersistent : Bool
  /-- Whether this mode is peer-reviewed -/
  isPeerReviewed : Bool

/-- Standard properties for each transmission mode -/
def standardModeProperties : TransmissionMode → TransmissionModeProperties
  | TransmissionMode.publication => 
      { formality := 1, typicalDelay := 12, isPersistent := true, isPeerReviewed := true }
  | TransmissionMode.teaching => 
      { formality := 7/10, typicalDelay := 1, isPersistent := false, isPeerReviewed := false }
  | TransmissionMode.collaboration => 
      { formality := 5/10, typicalDelay := 0, isPersistent := true, isPeerReviewed := false }
  | TransmissionMode.conference => 
      { formality := 6/10, typicalDelay := 3, isPersistent := false, isPeerReviewed := true }
  | TransmissionMode.informal => 
      { formality := 1/10, typicalDelay := 0, isPersistent := false, isPeerReviewed := false }

/-! ## Scientific MAIS: The Scientific Community as a Multi-Agent System -/

/-- A scientific community is a MAIS with scientific structure -/
structure ScientificCommunity (Content : Type*) where
  /-- The underlying MAIS structure -/
  mais : MAIS (ScientificIdea Content) ℕ
  /-- Discipline assignment for each agent (can be multi-disciplinary) -/
  discipline : Agent (ScientificIdea Content) ℕ → ℕ
  /-- WEAKENED: Agents have a primary discipline but can work interdisciplinarily.
      This is trivially satisfied - it just says the agent has *some* discipline.
      We remove the strong constraint that all ideas must come from that discipline. -/
  has_primary_discipline : ∀ α ∈ mais.agents, ∃ d, d = discipline α

/-- Two agents are in the same discipline -/
def ScientificCommunity.sameDiscipline {C : Type*} 
    (sc : ScientificCommunity C) (α β : Agent (ScientificIdea C) ℕ) : Prop :=
  sc.discipline α = sc.discipline β

/-- An interdisciplinary boundary involves agents from different disciplines -/
def ScientificCommunity.isInterdisciplinaryBoundary {C : Type*}
    (sc : ScientificCommunity C) (S : Set (Agent (ScientificIdea C) ℕ)) : Prop :=
  ∃ α β, α ∈ S ∧ β ∈ S ∧ sc.discipline α ≠ sc.discipline β

/-! ## Prediction 1: Interdisciplinary Hotspots

The highest novelty generation occurs at interdisciplinary boundaries.
-/

/-- Novelty of an idea for an agent: 1/depth (more novel if shallower depth from primordials) -/
noncomputable def ScientificCommunity.novelty {C : Type*}
    (sc : ScientificCommunity C) (α : Agent (ScientificIdea C) ℕ) 
    (a : ScientificIdea C) : ℚ :=
  if sc.mais.localDepth α a = 0 then 1 
  else 1 / sc.mais.localDepth α a

/-- Diversity of a set of agents: number of distinct disciplines -/
noncomputable def ScientificCommunity.diversity {C : Type*}
    (sc : ScientificCommunity C) (S : Set (Agent (ScientificIdea C) ℕ)) : ℕ :=
  (sc.discipline '' S).ncard

/-- QUALITATIVE VERSION: Interdisciplinary boundary contains at least two distinct disciplines.
    This version requires no finiteness assumption. -/
theorem ScientificCommunity.interdisciplinary_has_multiple_disciplines {C : Type*}
    (sc : ScientificCommunity C) (S : Set (Agent (ScientificIdea C) ℕ))
    (hinter : sc.isInterdisciplinaryBoundary S) :
    ∃ d₁ d₂, d₁ ≠ d₂ ∧ d₁ ∈ sc.discipline '' S ∧ d₂ ∈ sc.discipline '' S := by
  obtain ⟨α, β, hα, hβ, hdiff⟩ := hinter
  use sc.discipline α, sc.discipline β
  exact ⟨hdiff, Set.mem_image_of_mem sc.discipline hα, Set.mem_image_of_mem sc.discipline hβ⟩

/-- QUANTITATIVE VERSION: Interdisciplinary boundary has diversity > 1.
    Requires finiteness for cardinality counting. -/
theorem ScientificCommunity.interdisciplinary_higher_diversity {C : Type*}
    (sc : ScientificCommunity C) (S : Set (Agent (ScientificIdea C) ℕ))
    (hinter : sc.isInterdisciplinaryBoundary S)
    (hfin : (sc.discipline '' S).Finite) :
    sc.diversity S > 1 := by
  obtain ⟨α, β, hα, hβ, hdiff⟩ := hinter
  unfold diversity
  have h : {sc.discipline α, sc.discipline β} ⊆ sc.discipline '' S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    cases hx with
    | inl h => rw [h]; exact Set.mem_image_of_mem sc.discipline hα
    | inr h => rw [h]; exact Set.mem_image_of_mem sc.discipline hβ
  have h2 : ({sc.discipline α, sc.discipline β} : Set ℕ).ncard = 2 := Set.ncard_pair hdiff
  have hfin_pair : ({sc.discipline α, sc.discipline β} : Set ℕ).Finite := 
    Set.Finite.subset hfin h
  calc (sc.discipline '' S).ncard
      ≥ ({sc.discipline α, sc.discipline β} : Set ℕ).ncard := Set.ncard_le_ncard h hfin
    _ = 2 := h2
    _ > 1 := Nat.one_lt_two

/-! ## Prediction 2: Hub Scientists

Scientists with many collaborators produce disproportionate influence.
-/

/-- Collaboration count for a scientist.
    WEAKENED: We only require *some* communication between agents, not bidirectional.
    This captures any form of scientific interaction (citation, reading, discussion). -/
noncomputable def ScientificCommunity.collaboratorCount {C : Type*}
    (sc : ScientificCommunity C) (α : Agent (ScientificIdea C) ℕ) : ℕ :=
  { β ∈ sc.mais.agents | β ≠ α ∧ 
    -- There's some channel activity (in either direction)
    ((∃ a t b s, (b, s) ∈ (sc.mais.channel α β).transmit (a, t)) ∨
     (∃ a t b s, (b, s) ∈ (sc.mais.channel β α).transmit (a, t))) }.ncard

/-- A hub scientist has more than average collaborators -/
def ScientificCommunity.isHub {C : Type*}
    (sc : ScientificCommunity C) (α : Agent (ScientificIdea C) ℕ) 
    (threshold : ℕ) : Prop :=
  sc.collaboratorCount α > threshold

/-- Influence: how many agents have ideas in their memory that originated from α -/
noncomputable def ScientificCommunity.influence {C : Type*}
    (sc : ScientificCommunity C) (α : Agent (ScientificIdea C) ℕ) (t : ℕ) : ℕ :=
  { β ∈ sc.mais.agents | β ≠ α ∧ 
    -- β has an idea that α is a primary source of
    ∃ a ∈ β.memory t, sc.mais.isPrimarySource α a }.ncard

/-! ## Definition 10.4: Replicated Idea

Idea a is replicated if multiple independent agents generate a from their 
own primordials. WEAKENED: We now allow for substantially (but not completely)
overlapping primordials, reflecting that scientists share foundational knowledge.
-/

/-- An idea is replicated if multiple independent primary sources exist.
    WEAKENED: Independence now means agents are distinct, not that primordials are disjoint.
    This is much more realistic - scientists can share foundational knowledge and still
    independently verify results. -/
def ScientificCommunity.isReplicated {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C) : Prop :=
  ∃ α β : Agent (ScientificIdea C) ℕ, 
    sc.mais.isPrimarySource α a ∧ 
    sc.mais.isPrimarySource β a ∧
    α.agentId ≠ β.agentId
    -- REMOVED: requirement for disjoint primordials
    -- This makes the theorem apply to realistic scientific scenarios where
    -- scientists share training, textbooks, and foundational knowledge

/-- The replication count of an idea -/
noncomputable def ScientificCommunity.replicationCount {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C) : ℕ :=
  { α ∈ sc.mais.agents | sc.mais.isPrimarySource α a }.ncard

/-! ## Theorem 10.1: Replication and Redundancy

Replicated ideas have high redundancy by definition.
-/

/-- Redundancy: how many agents can independently derive an idea -/
noncomputable def ScientificCommunity.redundancy {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C) : ℕ :=
  sc.replicationCount a

/-- QUALITATIVE VERSION: Replicated ideas have at least two distinct primary sources.
    This version requires no finiteness assumption. -/
theorem ScientificCommunity.replicated_has_multiple_sources {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C)
    (hrep : sc.isReplicated a) :
    ∃ α β : Agent (ScientificIdea C) ℕ,
      α ≠ β ∧ 
      sc.mais.isPrimarySource α a ∧ 
      sc.mais.isPrimarySource β a := by
  obtain ⟨α, β, hα_primary, hβ_primary, hdiff⟩ := hrep
  use α, β
  have hne : α ≠ β := by
    intro heq
    apply hdiff
    rw [heq]
  exact ⟨hne, hα_primary, hβ_primary⟩

/-- QUANTITATIVE VERSION: Replicated ideas have redundancy at least 2.
    Requires finiteness for cardinality counting. -/
theorem ScientificCommunity.replicated_implies_redundant {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C)
    (hrep : sc.isReplicated a)
    (hfin_ps : { γ ∈ sc.mais.agents | sc.mais.isPrimarySource γ a }.Finite) :
    sc.redundancy a ≥ 2 := by
  obtain ⟨α, β, hα_primary, hβ_primary, hdiff⟩ := hrep
  unfold redundancy replicationCount
  -- Both α and β are in the set of primary sources
  have hα_in : α ∈ { γ ∈ sc.mais.agents | sc.mais.isPrimarySource γ a } := by
    simp only [Set.mem_setOf_eq]
    exact ⟨hα_primary.1, hα_primary⟩
  have hβ_in : β ∈ { γ ∈ sc.mais.agents | sc.mais.isPrimarySource γ a } := by
    simp only [Set.mem_setOf_eq]
    exact ⟨hβ_primary.1, hβ_primary⟩
  -- α ≠ β as agents
  have hne : α ≠ β := by
    intro heq
    apply hdiff
    rw [heq]
  have h2 : ({α, β} : Set (Agent (ScientificIdea C) ℕ)).ncard = 2 := Set.ncard_pair hne
  have hsub : ({α, β} : Set (Agent (ScientificIdea C) ℕ)) ⊆ 
      { γ ∈ sc.mais.agents | sc.mais.isPrimarySource γ a } := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    cases hx with
    | inl h => rw [h]; exact hα_in
    | inr h => rw [h]; exact hβ_in
  calc { γ ∈ sc.mais.agents | sc.mais.isPrimarySource γ a }.ncard 
      ≥ ({α, β} : Set (Agent (ScientificIdea C) ℕ)).ncard := Set.ncard_le_ncard hsub hfin_ps
    _ = 2 := h2

/-! ## Prediction 3: Paradigm Shift Dynamics

Paradigm shifts follow predictable patterns: anomaly accumulation, crisis,
revolutionary candidates, resolution, new normal.
-/

/-- Phases of a paradigm shift -/
inductive ParadigmShiftPhase where
  | normalScience : ParadigmShiftPhase      -- Stable paradigm
  | anomalyAccumulation : ParadigmShiftPhase -- Ideas that don't fit
  | crisis : ParadigmShiftPhase              -- Conflict zone expansion
  | revolutionary : ParadigmShiftPhase       -- Alternative paradigms emerge
  | resolution : ParadigmShiftPhase          -- One paradigm wins
  | newNormal : ParadigmShiftPhase           -- Stability returns
deriving DecidableEq

/-- A paradigm in a scientific community -/
structure Paradigm (C : Type*) where
  /-- Core ideas of the paradigm -/
  coreIdeas : Set (ScientificIdea C)
  /-- Methods associated with the paradigm -/
  methods : Set (ScientificIdea C)
  /-- Adherents (scientists who work within this paradigm) -/
  adherents : Set (Agent (ScientificIdea C) ℕ)

/-- An anomaly is an idea that contradicts a paradigm's core but is well-attested.
    WEAKENED: It only needs to contradict *some* core idea, not be non-derivable from all.
    This is more realistic - an anomaly is something that conflicts with the paradigm. -/
def Paradigm.isAnomaly {C : Type*} (P : Paradigm C) (sc : ScientificCommunity C) 
    (a : ScientificIdea C) : Prop :=
  -- The idea is replicated (well-attested)
  sc.isReplicated a ∧
  -- It contradicts at least one core idea (much weaker than the original)
  ∃ α ∈ P.adherents, ∃ c ∈ P.coreIdeas, a ∉ α.generate c

/-- Anomaly count in a paradigm -/
noncomputable def Paradigm.anomalyCount {C : Type*} (P : Paradigm C) 
    (sc : ScientificCommunity C) : ℕ :=
  { a : ScientificIdea C | P.isAnomaly sc a }.ncard

/-- Crisis occurs when anomaly count exceeds threshold -/
def Paradigm.inCrisis {C : Type*} (P : Paradigm C) (sc : ScientificCommunity C) 
    (threshold : ℕ) : Prop :=
  P.anomalyCount sc > threshold

/-! ## Prediction 4: Redundancy and Robustness

Well-established ideas have high redundancy—many scientists can independently verify them.
-/

/-- An idea is well-established if it has high replication count -/
def ScientificCommunity.isWellEstablished {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C) (threshold : ℕ) : Prop :=
  sc.redundancy a ≥ threshold

/-- Well-established ideas are resilient to agent removal -/
theorem ScientificCommunity.established_resilient {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C) (n : ℕ)
    (hestablished : sc.redundancy a ≥ n + 1) :
    -- Even after removing n agents, at least one primary source remains
    ∀ removed : Finset (Agent (ScientificIdea C) ℕ),
      removed.card ≤ n → 
      ∃ α, sc.mais.isPrimarySource α a ∧ α ∉ removed := by
  intro removed hremoved
  -- If redundancy ≥ n+1 and we remove ≤ n agents, at least 1 remains
  by_contra h
  push_neg at h
  -- h : ∀ α, sc.mais.isPrimarySource α a → α ∈ removed
  -- All primary sources are in removed
  have hall : ∀ α, sc.mais.isPrimarySource α a → α ∈ removed := fun α hprim => h α hprim
  -- This means |primary sources| ≤ |removed| ≤ n
  unfold redundancy replicationCount at hestablished
  have hfin_removed : (↑removed : Set (Agent (ScientificIdea C) ℕ)).Finite := Finset.finite_toSet removed
  have hps_finite : { α ∈ sc.mais.agents | sc.mais.isPrimarySource α a }.ncard ≤ removed.card := by
    have hsub : { α ∈ sc.mais.agents | sc.mais.isPrimarySource α a } ⊆ ↑removed := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      exact hall x hx.2
    calc { α ∈ sc.mais.agents | sc.mais.isPrimarySource α a }.ncard 
        ≤ (↑removed : Set (Agent (ScientificIdea C) ℕ)).ncard := Set.ncard_le_ncard hsub hfin_removed
      _ = removed.card := Set.ncard_coe_Finset removed
  omega

/-! ## Prediction 5: Speed-Quality Trade-off

Faster publication leads to lower average quality but higher variance.
-/

/-- Quality of an idea: based on replication and depth -/
noncomputable def ScientificCommunity.ideaQuality {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C) : ℚ :=
  -- Higher replication = higher quality
  -- This is a simplified model
  sc.redundancy a

/-- A community's publication speed (inverse of typical delay) -/
noncomputable def ScientificCommunity.publicationSpeed {C : Type*}
    (_sc : ScientificCommunity C) : ℚ :=
  -- Simplified: based on the speed of the fastest channel mode
  1 / (standardModeProperties TransmissionMode.publication).typicalDelay

/-- Fast publication communities have higher variance (modeled as range of quality) -/
structure QualityDistribution (C : Type*) where
  _sc : ScientificCommunity C
  /-- Minimum quality observed -/
  minQuality : ℚ
  /-- Maximum quality observed -/  
  maxQuality : ℚ
  /-- Variance proxy: range -/
  variance : ℚ := maxQuality - minQuality

/-! ## The Replication Crisis as Ideogenetic Failure

Low-quality ideas spread via herding and noise, not via legitimate replication.
-/

/-- Herding: adopting ideas because others adopted them, not from verification -/
def ScientificCommunity.isHerding {C : Type*}
    (sc : ScientificCommunity C) (β : Agent (ScientificIdea C) ℕ) 
    (a : ScientificIdea C) (t : ℕ) : Prop :=
  -- β has the idea
  a ∈ β.memory t ∧
  -- β is not a primary source
  ¬sc.mais.isPrimarySource β a ∧
  -- β received it from others (not derived independently)
  ∃ α ∈ sc.mais.agents, α ≠ β ∧ 
    ∃ s < t, ∃ b, (a, t) ∈ (sc.mais.channel α β).transmit (b, s)

/-- Proportion of herding adoptions for an idea -/
noncomputable def ScientificCommunity.herdingProportion {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C) (t : ℕ) : ℚ :=
  let holders := { β ∈ sc.mais.agents | a ∈ β.memory t }
  let herders := { β ∈ sc.mais.agents | sc.isHerding β a t }
  if holders.ncard = 0 then 0 else herders.ncard / holders.ncard

/-- Ideas with high herding proportion but low replication are at crisis risk -/
def ScientificCommunity.isAtCrisisRisk {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C) (t : ℕ)
    (herdingThreshold : ℚ) (replicationThreshold : ℕ) : Prop :=
  sc.herdingProportion a t > herdingThreshold ∧
  sc.redundancy a < replicationThreshold

/-- Ideas at crisis risk are not well-established -/
theorem ScientificCommunity.crisis_risk_not_established {C : Type*}
    (sc : ScientificCommunity C) (a : ScientificIdea C) (t : ℕ)
    (herdThresh : ℚ) (repThresh : ℕ)
    (hrisk : sc.isAtCrisisRisk a t herdThresh repThresh) :
    ¬sc.isWellEstablished a repThresh := by
  unfold isWellEstablished isAtCrisisRisk at *
  obtain ⟨_, hlow⟩ := hrisk
  omega

end CollectiveIdeogenesis
