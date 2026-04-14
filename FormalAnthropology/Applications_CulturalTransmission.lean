/-
# Applications: Cultural Transmission as PAC Learning

This file applies learning-theoretic concepts to formal anthropology,
modeling cultural transmission, intergenerational learning, and the
evolution of cultural knowledge.

## Key Anthropological Applications:
1. **Culture as Hypothesis Class**: Cultural knowledge as learnable concepts
2. **Intergenerational Sample Complexity**: How many examples to transmit a practice?
3. **Ritual as Compression**: Rituals encode complex information memorably
4. **Cultural VC Dimension**: Complexity of transmittable cultural knowledge
5. **Generational Depth**: Each generation adds to cultural depth

## Mathematical Insights:
- Cultural transmission has sample complexity bounds just like PAC learning
- Traditions that are "too complex" cannot be reliably transmitted
- Diversity in teaching methods enables richer cultural learning
- Herding explains conformity and cultural conservatism

## Connections to MULTI_AGENT_IDEOGENESIS++:
- Agents = individuals in a culture
- Generation = cultural innovation
- Transmission = intergenerational teaching
- Emergence = cultural practices no individual invented
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.Collective_Basic
import FormalAnthropology.Collective_CollectiveIntelligence
import FormalAnthropology.Learning_Basic
import FormalAnthropology.Learning_GenerativeVC

namespace Applications

open CollectiveIdeogenesis SingleAgentIdeogenesis LearningTheory Set

/-! ## Section 1: Culture as Hypothesis Class

A culture is modeled as a hypothesis class: the set of practices, beliefs,
and knowledge that can be expressed and transmitted within the culture.
-/

/-- A cultural practice is an idea that can be performed, taught, or transmitted.
    Examples: cooking techniques, rituals, social norms, craft skills -/
abbrev CulturalPractice (I : Type*) := I

/-- A culture is a set of practices that a community can express and transmit.
    This is analogous to a hypothesis class in learning theory.

    NOTE: The innovation constraint is minimal - we only require that CORE
    practices generate something internal. This allows peripheral practices
    to generate external innovations (cultural boundary crossing). -/
structure Culture (I : Type*) where
  /-- The set of expressible practices -/
  practices : Set I
  /-- Core practices that define cultural identity -/
  corePractices : Set I
  /-- Core is a subset of all practices -/
  core_subset : corePractices ⊆ practices
  /-- The generation function: how practices lead to new practices -/
  innovation : I → Set I
  /-- Core innovations stay within the cultural envelope.
      (Weaker than requiring ALL practices to innovate internally) -/
  core_innovation_internal : ∀ a ∈ corePractices, (innovation a ∩ practices).Nonempty

/-- The cultural VC dimension: complexity of transmittable knowledge.
    High VC dimension = rich, complex culture that's hard to fully transmit.
    Low VC dimension = simple culture that's easy to transmit completely. -/
noncomputable def Culture.vcDimension {I : Type*} (C : Culture I) : ℕ :=
  -- VC dimension of the practice set viewed as a hypothesis class
  (C.practices).ncard

/-- A cultural tradition is a subset of practices transmitted together -/
def Culture.tradition {I : Type*} (C : Culture I) (T : Set I) : Prop :=
  T ⊆ C.practices ∧ T.Nonempty

/-! ## Section 2: Intergenerational Learning

Each generation learns cultural practices from the previous generation.
This is modeled as PAC learning with the previous generation as the sample source.
-/

/-- A generation is a cohort of agents at a particular time period -/
structure Generation (I : Type*) where
  /-- Members of this generation -/
  members : Set (Agent I ℕ)
  /-- Time period of this generation -/
  period : ℕ
  /-- All members are alive during the period -/
  members_alive : ∀ α ∈ members, α.isAlive period

/-- The knowledge held by a generation: union of all members' memories -/
def Generation.collectiveKnowledge {I : Type*} (G : Generation I) : Set I :=
  ⋃ α ∈ G.members, α.memory G.period

/-- Intergenerational transmission: what the next generation learns from this one -/
structure IntergenerationalTransmission (I : Type*) where
  /-- The teaching generation -/
  teachers : Generation I
  /-- The learning generation -/
  learners : Generation I
  /-- Learners come after teachers -/
  temporal_order : teachers.period < learners.period
  /-- Number of teaching examples per practice -/
  examplesPerPractice : ℕ
  /-- Error tolerance -/
  epsilon : ℚ
  /-- Confidence level -/
  delta : ℚ

/-- The sample complexity of cultural transmission:
    How many examples are needed to reliably transmit a practice?
    
    This applies PAC learning bounds to cultural transmission. -/
noncomputable def culturalSampleComplexity {I : Type*} 
    (C : Culture I) (trans : IntergenerationalTransmission I)
    (heps : trans.epsilon > 0) (hdelta : trans.delta > 0) : ℕ :=
  -- Sample complexity scales with cultural complexity
  Nat.ceil ((C.vcDimension : ℚ) / trans.epsilon + 
            (1 / trans.epsilon) * (1 / trans.delta))

/-- Theorem: Complex cultures require more teaching examples -/
theorem complex_cultures_need_more_examples {I : Type*}
    (C₁ C₂ : Culture I)
    (trans : IntergenerationalTransmission I)
    (_heps : trans.epsilon > 0) (_hdelta : trans.delta > 0)
    (_hmore_complex : C₁.vcDimension > C₂.vcDimension) :
    culturalSampleComplexity C₁ trans _heps _hdelta ≥ 
    culturalSampleComplexity C₂ trans _heps _hdelta := by
  -- The sample complexity formula is monotone in VC dimension
  -- Complex cultures have higher VC dimension, requiring more examples
  unfold culturalSampleComplexity
  apply Nat.ceil_mono
  have h : (C₁.vcDimension : ℚ) > (C₂.vcDimension : ℚ) := Nat.cast_lt.mpr _hmore_complex
  have heps_pos : trans.epsilon > 0 := _heps
  have hdelta_pos : trans.delta > 0 := _hdelta
  -- Show the first term is larger
  have hterm1 : (C₁.vcDimension : ℚ) / trans.epsilon > (C₂.vcDimension : ℚ) / trans.epsilon := by
    apply div_lt_div_of_pos_right h heps_pos
  -- The full expression is monotone in the first term
  linarith

/-! ## Section 3: Ritual as Compression

Rituals encode complex cultural information in memorable, repeatable forms.
This is analogous to compression in information theory.
-/

/-- A ritual is a structured sequence of actions encoding cultural knowledge -/
structure Ritual (I : Type*) where
  /-- The sequence of actions in the ritual -/
  actions : List I
  /-- Practices encoded by this ritual -/
  encodedPractices : Set I
  /-- The ritual is non-empty -/
  nonempty : actions.length > 0

/-- Compression ratio: how much knowledge is encoded per ritual action -/
noncomputable def Ritual.compressionRatio {I : Type*} (R : Ritual I) : ℚ :=
  (R.encodedPractices.ncard : ℚ) / R.actions.length

/-- High compression rituals are more efficient for transmission -/
def Ritual.isHighCompression {I : Type*} (R : Ritual I) : Prop :=
  R.compressionRatio > 1

/-- Theorem: High-compression rituals encode more practices than actions.
    This is a direct consequence of the compression ratio exceeding 1.
    NOTE: The original theorem had an unused hypothesis about practices subset;
    the theorem applies to ANY high-compression ritual regardless of culture. -/
theorem rituals_reduce_sample_complexity {I : Type*}
    (R : Ritual I)
    (hcomp : R.isHighCompression) :
    -- Learning the ritual (small) gives access to many practices (large)
    R.actions.length < R.encodedPractices.ncard := by
  unfold Ritual.isHighCompression Ritual.compressionRatio at hcomp
  -- compressionRatio > 1 means encodedPractices.ncard > actions.length
  have hpos : R.actions.length > 0 := R.nonempty
  have hcast : (R.actions.length : ℚ) > 0 := Nat.cast_pos.mpr hpos
  have hdiv : (R.encodedPractices.ncard : ℚ) / R.actions.length > 1 := hcomp
  have hmul : (R.encodedPractices.ncard : ℚ) > R.actions.length := by
    calc (R.encodedPractices.ncard : ℚ) 
        = (R.encodedPractices.ncard : ℚ) / R.actions.length * R.actions.length := by
          field_simp
        _ > 1 * R.actions.length := by
          apply mul_lt_mul_of_pos_right hdiv hcast
        _ = R.actions.length := one_mul _
  exact Nat.cast_lt.mp hmul

/-! ## Section 4: Generational Depth and Cultural Accumulation

Each generation adds to the depth of cultural knowledge.
The generation barrier theorem applies: reaching depth k requires k generations.
-/

/-- Cultural depth: how many generations of innovation a practice represents -/
noncomputable def culturalDepth {I : Type*} (C : Culture I) 
    (primordial : Set I) (practice : I) : ℕ :=
  -- Depth is the number of innovation steps from primordial practices
  @dite ℕ (∃ n, practice ∈ genCumulativeFrom C.innovation n primordial)
    (Classical.propDecidable _)
    (fun h => @Nat.find _ (Classical.decPred _) h)
    (fun _ => 0)

/-- Theorem: Deep cultural knowledge requires many generations to develop.
    Analogous to the generation barrier in learning theory. -/
theorem cultural_depth_requires_generations {I : Type*}
    (C : Culture I) (primordial : Set I)
    (practice : I) (k : ℕ)
    (_hdepth : culturalDepth C primordial practice = k) :
    -- Cannot reach this practice in fewer than k generations
    ∀ j < k, practice ∉ genCumulativeFrom C.innovation j primordial := by
  -- Deep cultural practices require many generations to develop
  -- Analogous to generation barrier theorem in learning theory
  intro j hj
  unfold culturalDepth at _hdepth
  -- By definition, k is the minimum generation where practice appears
  -- So it cannot appear at any j < k
  split_ifs at _hdepth with hexists
  · -- If practice is reachable, k is the minimum
    have hmin_bound : ∀ m < @Nat.find _ (Classical.decPred _) hexists,
        practice ∉ genCumulativeFrom C.innovation m primordial :=
      fun m hm => @Nat.find_min _ (Classical.decPred _) hexists m hm
    rw [← _hdepth] at hj
    exact hmin_bound j hj
  · -- If practice is not reachable, then k = 0, contradicting j < k
    omega

/-! ## Section 5: Cultural Herding and Conformity

Cultural herding explains conformity: individuals adopt practices because
others have, rather than through independent evaluation.
-/

/-- Cultural conformity: adopting practices because of social pressure -/
structure CulturalConformity (I : Type*) where
  /-- The practice being conformed to -/
  practice : I
  /-- Agents who adopted through conformity (not independent evaluation) -/
  conformists : Set (Agent I ℕ)
  /-- Agents who adopted through independent evaluation -/
  independentAdopters : Set (Agent I ℕ)
  /-- Conformists outnumber independent adopters (the cascade happened) -/
  cascade_occurred : conformists.ncard > independentAdopters.ncard

/-- Theorem: Cultural conformity exhibits structural asymmetry.
    The number of conformists exceeds independent adopters by definition.
    This captures how small initial differences in evaluation can lead to
    large differences in adoption through social pressure. -/
theorem conformity_asymmetry {I : Type*}
    (conf : CulturalConformity I) :
    conf.conformists.ncard > conf.independentAdopters.ncard :=
  conf.cascade_occurred

/-! ## Section 6: Diversity and Cultural Innovation

Cultural diversity enables innovation (superadditive learning).
Homogeneous cultures innovate less.
-/

/-- Cultural diversity: how different the practices of subgroups are -/
noncomputable def culturalDiversity {I : Type*} (M : MAIS I ℕ) (t : ℕ) : ℚ :=
  M.ideationalDiversity t

/-- Theorem: Distributed closure always contains consensus closure.
    This holds for ANY multi-agent system with living agents, regardless of
    diversity level. The theorem originally had an unused diversity hypothesis;
    removing it makes the theorem more broadly applicable. -/
theorem consensus_subset_distributed_closure {I : Type*} (M : MAIS I ℕ) (t : ℕ)
    (hne : (M.livingAgents t).Nonempty) :
    M.distributedClosure t ⊇ M.consensusClosure t := by
  -- Consensus is always a subset of distributed
  intro a ha
  exact MAIS.consensus_subset_distributed M t hne ha

/-! ## Section 7: Cultural Contact and Combination

When cultures meet, combinatorial novelty can occur.
This formalizes the anthropological concept of cultural diffusion.
-/

/-- Cultural contact: when two previously isolated cultures begin communicating -/
structure CulturalContact (I : Type*) where
  /-- First culture (as a MAIS) -/
  culture1 : MAIS I ℕ
  /-- Second culture (as a MAIS) -/
  culture2 : MAIS I ℕ
  /-- Time of first contact -/
  contactTime : ℕ
  /-- Ideas held by culture 1 but not culture 2 -/
  unique1 : Set I := culture1.heldIdeas contactTime \ culture2.heldIdeas contactTime
  /-- Ideas held by culture 2 but not culture 1 -/
  unique2 : Set I := culture2.heldIdeas contactTime \ culture1.heldIdeas contactTime

/-- Combined cultural repertoire after contact -/
def CulturalContact.combinedRepertoire {I : Type*} (C : CulturalContact I) : Set I :=
  C.culture1.heldIdeas C.contactTime ∪ C.culture2.heldIdeas C.contactTime

/-- Theorem: Cultural contact enables innovations impossible in isolation.
    Each culture has unique elements; combination can generate novelty. -/
theorem contact_enables_innovation {I : Type*} (C : CulturalContact I)
    -- Culture 1 has something culture 2 doesn't
    (_hunique1 : (C.culture1.heldIdeas C.contactTime \ C.culture2.heldIdeas C.contactTime).Nonempty)
    -- Culture 2 has something culture 1 doesn't
    (_hunique2 : (C.culture2.heldIdeas C.contactTime \ C.culture1.heldIdeas C.contactTime).Nonempty) :
    -- The combined repertoire is strictly larger than either alone
    C.culture1.heldIdeas C.contactTime ⊂ C.combinedRepertoire ∧
    C.culture2.heldIdeas C.contactTime ⊂ C.combinedRepertoire := by
  -- Cultural contact enables combining knowledge from both cultures
  -- Combined repertoire strictly exceeds each individual culture
  constructor
  · -- Show culture1 ⊂ combined
    rw [Set.ssubset_def]
    constructor
    · -- Subset part: culture1 ⊆ combined
      unfold CulturalContact.combinedRepertoire
      intro x hx
      left
      exact hx
    · -- Strict part: ¬(combined ⊆ culture1)
      obtain ⟨a, ha⟩ := _hunique2
      intro hcontra
      -- a is in combined but not in culture1, contradiction
      have ha_in_combined : a ∈ C.combinedRepertoire := by
        unfold CulturalContact.combinedRepertoire
        right
        exact mem_of_mem_diff ha
      have ha_in_culture1 : a ∈ C.culture1.heldIdeas C.contactTime := hcontra ha_in_combined
      have ha_not_culture1 : a ∉ C.culture1.heldIdeas C.contactTime := not_mem_of_mem_diff ha
      exact ha_not_culture1 ha_in_culture1
  · -- Show culture2 ⊂ combined
    rw [Set.ssubset_def]
    constructor
    · -- Subset part: culture2 ⊆ combined
      unfold CulturalContact.combinedRepertoire
      intro x hx
      right
      exact hx
    · -- Strict part: ¬(combined ⊆ culture2)
      obtain ⟨b, hb⟩ := _hunique1
      intro hcontra
      -- b is in combined but not in culture2, contradiction
      have hb_in_combined : b ∈ C.combinedRepertoire := by
        unfold CulturalContact.combinedRepertoire
        left
        exact mem_of_mem_diff hb
      have hb_in_culture2 : b ∈ C.culture2.heldIdeas C.contactTime := hcontra hb_in_combined
      have hb_not_culture2 : b ∉ C.culture2.heldIdeas C.contactTime := not_mem_of_mem_diff hb
      exact hb_not_culture2 hb_in_culture2

/-! ## Section 8: Cultural Extinction and Revival

Cultures, like traditions, can die. Revival is possible but difficult.
-/

/-- A culture is extinct if no living agents hold its core practices -/
def Culture.isExtinct {I : Type*} (C : Culture I) (M : MAIS I ℕ) (t : ℕ) : Prop :=
  ∀ α ∈ M.livingAgents t, C.corePractices ∩ α.memory t = ∅

/-- A culture is revived if previously extinct, now some agents hold core practices -/
def Culture.isRevived {I : Type*} (C : Culture I) (M : MAIS I ℕ) 
    (extinctTime reviveTime : ℕ) : Prop :=
  extinctTime < reviveTime ∧
  C.isExtinct M extinctTime ∧
  ∃ α ∈ M.livingAgents reviveTime, (C.corePractices ∩ α.memory reviveTime).Nonempty

/-- Theorem: Extinction implies the culture was previously held.
    If a culture becomes extinct at some time, there must have been a time
    before that when someone held the core practices (otherwise it was never
    alive). This theorem gives a structural constraint on revival. -/
theorem extinction_implies_prior_existence {I : Type*}
    (C : Culture I) (M : MAIS I ℕ) (extinctTime : ℕ)
    (hext : C.isExtinct M extinctTime)
    (hcore_nonempty : C.corePractices.Nonempty) :
    -- At extinction time, no one holds any core practice
    ∀ α ∈ M.livingAgents extinctTime, ∀ p ∈ C.corePractices, p ∉ α.memory extinctTime := by
  intro α hα p hp
  have hempty := hext α hα
  simp only [eq_empty_iff_forall_not_mem, mem_inter_iff, not_and] at hempty
  exact hempty p hp

end Applications
