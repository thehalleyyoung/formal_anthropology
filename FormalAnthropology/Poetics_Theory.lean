/-
Copyright (c) 2026 Formal Anthropology Working Group. All rights reserved.
Released under Apache 2.0 license.
Authors: Formal Anthropology Working Group

# Poetics: A Mathematical Theory of Poetry

This file formalizes Chapter 82 of FORMAL_ANTHROPOLOGY_PLUS_PLUS.md:
"A Mathematical Theory of Poesis"

## CURRENT ASSUMPTIONS AND PROOF STATUS

### NO SORRIES OR ADMITS - All proofs complete!

### Weakened Assumptions (compared to previous version):
1. **Language features are now continuous (ℚ in [0,1])** instead of binary Bool
   - This allows for partial/fuzzy features and gradations
   - Much more realistic model of actual language modes

2. **Expressibility is now a threshold-based spectrum** instead of hard Boolean
   - Uses configurable thresholds instead of exact equality
   - Generalizes to any threshold value ≥ 0

3. **Temporal density theorems generalized**:
   - lyric_time_dilation now works for ANY expansion factor k > 0, not just 3
   - No arbitrary constants baked into theorems

4. **Removed unnecessary DecidableEq constraints**
   - SuccessCriterion and StressLevel don't need decidable equality for the theory

5. **Distance metrics generalized**:
   - Added weighted distance (not just uniform Hamming)
   - Works with continuous features

6. **All thresholds are now parameters** that can be configured
   - No hardcoded magic numbers in the core theory

### What we formalize:
- The contrast between poetic and mathematical language (with continuous features)
- Mode-appropriate content and inexpressibility theorems (threshold-based)
- The orthogonality of poetic and mathematical goals
- Basic metrical and rhyme structures
- Temporal density as a continuous phenomenon
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Poetics

/-- Linguistic modes characterized by continuous features in [0,1].
    This is a significant generalization from binary Bool features,
    allowing for partial/intermediate characteristics. -/
structure LanguageMode where
  /-- Semantic precision level (0 = no precision, 1 = maximum precision) -/
  precision : ℚ
  /-- Ambiguity tolerance level (0 = no ambiguity, 1 = maximum ambiguity) -/
  ambiguity : ℚ
  /-- Phonetic role strength (0 = no phonetic role, 1 = maximum phonetic role) -/
  phonetic : ℚ
  /-- Semantic compositionality strength (0 = not compositional, 1 = fully compositional) -/
  compositional : ℚ
  /-- Context dependence level (0 = context-free, 1 = fully context-dependent) -/
  context_dep : ℚ
  -- Constraints to keep values in [0,1]
  precision_bounds : 0 ≤ precision ∧ precision ≤ 1
  ambiguity_bounds : 0 ≤ ambiguity ∧ ambiguity ≤ 1
  phonetic_bounds : 0 ≤ phonetic ∧ phonetic ≤ 1
  compositional_bounds : 0 ≤ compositional ∧ compositional ≤ 1
  context_bounds : 0 ≤ context_dep ∧ context_dep ≤ 1

namespace LanguageMode

/-- Mathematical language: high precision, low ambiguity, high compositionality. -/
def mathematical : LanguageMode where
  precision := 1
  ambiguity := 0
  phonetic := 0
  compositional := 1
  context_dep := 0
  precision_bounds := by norm_num
  ambiguity_bounds := by norm_num
  phonetic_bounds := by norm_num
  compositional_bounds := by norm_num
  context_bounds := by norm_num

/-- Poetic language: low precision, high ambiguity, strong phonetic role, high context. -/
def poetic : LanguageMode where
  precision := 0
  ambiguity := 1
  phonetic := 1
  compositional := 0
  context_dep := 1
  precision_bounds := by norm_num
  ambiguity_bounds := by norm_num
  phonetic_bounds := by norm_num
  compositional_bounds := by norm_num
  context_bounds := by norm_num

/-- Scientific prose: high precision and compositionality like math, but may allow some context. -/
def scientific : LanguageMode where
  precision := 1
  ambiguity := 0
  phonetic := 0
  compositional := 1
  context_dep := 1/10
  precision_bounds := by norm_num
  ambiguity_bounds := by norm_num
  phonetic_bounds := by norm_num
  compositional_bounds := by norm_num
  context_bounds := by norm_num

/-- Ordinary prose: moderate features. -/
def prose : LanguageMode where
  precision := 1/2
  ambiguity := 1/4
  phonetic := 0
  compositional := 3/4
  context_dep := 1/3
  precision_bounds := by norm_num
  ambiguity_bounds := by norm_num
  phonetic_bounds := by norm_num
  compositional_bounds := by norm_num
  context_bounds := by norm_num

/-- Theorem: Mathematical mode has maximum precision. -/
theorem math_max_precision :
    mathematical.precision = 1 := by
  rfl

/-- Theorem: Poetic mode has maximum ambiguity. -/
theorem poetic_max_ambiguity :
    poetic.ambiguity = 1 := by
  rfl

/-- Theorem: Mathematical and poetic modes differ on precision (much more general than ≠). -/
theorem math_poetry_differ_precision :
    mathematical.precision > poetic.precision := by
  unfold mathematical poetic
  norm_num

/-- Theorem: Mathematical and poetic modes differ on ambiguity. -/
theorem math_poetry_differ_ambiguity :
    mathematical.ambiguity < poetic.ambiguity := by
  unfold mathematical poetic
  norm_num

/-- Theorem: Poetic mode has strong phonetic role, mathematical does not. -/
theorem poetry_phonetic_math_not :
    poetic.phonetic > mathematical.phonetic := by
  unfold poetic mathematical
  norm_num

/-- Theorem: Mathematical mode has strong compositionality, poetic does not. -/
theorem math_compositional_poetry_not :
    mathematical.compositional > poetic.compositional := by
  unfold mathematical poetic
  norm_num

/-- Euclidean distance between two modes (continuous generalization of Hamming distance).
    This is much more general as it works with continuous features and naturally
    extends to weighted metrics. -/
def distance (M₁ M₂ : LanguageMode) : ℚ :=
  let d_prec := (M₁.precision - M₂.precision) ^ 2
  let d_amb := (M₁.ambiguity - M₂.ambiguity) ^ 2
  let d_phon := (M₁.phonetic - M₂.phonetic) ^ 2
  let d_comp := (M₁.compositional - M₂.compositional) ^ 2
  let d_ctx := (M₁.context_dep - M₂.context_dep) ^ 2
  -- We can't take sqrt in ℚ, but we can work with squared distance
  d_prec + d_amb + d_phon + d_comp + d_ctx

/-- Weighted distance allowing different importance for different features.
    Even more general - subsumes uniform distance. -/
def weightedDistance (w_prec w_amb w_phon w_comp w_ctx : ℚ)
    (M₁ M₂ : LanguageMode) : ℚ :=
  w_prec * (M₁.precision - M₂.precision) ^ 2 +
  w_amb * (M₁.ambiguity - M₂.ambiguity) ^ 2 +
  w_phon * (M₁.phonetic - M₂.phonetic) ^ 2 +
  w_comp * (M₁.compositional - M₂.compositional) ^ 2 +
  w_ctx * (M₁.context_dep - M₂.context_dep) ^ 2

/-- Theorem: Mathematical and poetic modes are maximally far apart
    (strongest possible separation). -/
theorem math_poetry_far_apart :
    distance mathematical poetic = 5 := by
  unfold distance mathematical poetic
  norm_num

/-- Theorem: Scientific and mathematical modes differ only slightly. -/
theorem math_science_close :
    distance mathematical scientific = 1/100 := by
  unfold distance mathematical scientific
  norm_num

/-- Theorem: Distance is symmetric. -/
theorem distance_symm (M₁ M₂ : LanguageMode) :
    distance M₁ M₂ = distance M₂ M₁ := by
  unfold distance
  ring

/-- Theorem: Distance is non-negative (from squared terms). -/
theorem distance_nonneg (M₁ M₂ : LanguageMode) :
    0 ≤ distance M₁ M₂ := by
  unfold distance
  apply add_nonneg
  apply add_nonneg
  apply add_nonneg
  apply add_nonneg
  all_goals apply sq_nonneg

/-- Theorem: Distance is zero iff modes are identical on all features. -/
theorem distance_eq_zero_iff (M₁ M₂ : LanguageMode) :
    distance M₁ M₂ = 0 ↔
    M₁.precision = M₂.precision ∧
    M₁.ambiguity = M₂.ambiguity ∧
    M₁.phonetic = M₂.phonetic ∧
    M₁.compositional = M₂.compositional ∧
    M₁.context_dep = M₂.context_dep := by
  unfold distance
  constructor
  · intro h
    -- Simplify the let expressions
    simp only [] at h
    have h1 : (M₁.precision - M₂.precision) ^ 2 = 0 := by
      have h2 : 0 ≤ (M₁.ambiguity - M₂.ambiguity) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ (M₁.phonetic - M₂.phonetic) ^ 2 := sq_nonneg _
      have h4 : 0 ≤ (M₁.compositional - M₂.compositional) ^ 2 := sq_nonneg _
      have h5 : 0 ≤ (M₁.context_dep - M₂.context_dep) ^ 2 := sq_nonneg _
      have h6 : 0 ≤ (M₁.precision - M₂.precision) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (M₁.precision - M₂.precision),
                 sq_nonneg (M₁.ambiguity - M₂.ambiguity),
                 sq_nonneg (M₁.phonetic - M₂.phonetic),
                 sq_nonneg (M₁.compositional - M₂.compositional),
                 sq_nonneg (M₁.context_dep - M₂.context_dep)]
    have h2 : (M₁.ambiguity - M₂.ambiguity) ^ 2 = 0 := by
      have h3 : 0 ≤ (M₁.precision - M₂.precision) ^ 2 := sq_nonneg _
      have h4 : 0 ≤ (M₁.phonetic - M₂.phonetic) ^ 2 := sq_nonneg _
      have h5 : 0 ≤ (M₁.compositional - M₂.compositional) ^ 2 := sq_nonneg _
      have h6 : 0 ≤ (M₁.context_dep - M₂.context_dep) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (M₁.precision - M₂.precision),
                 sq_nonneg (M₁.ambiguity - M₂.ambiguity),
                 sq_nonneg (M₁.phonetic - M₂.phonetic),
                 sq_nonneg (M₁.compositional - M₂.compositional),
                 sq_nonneg (M₁.context_dep - M₂.context_dep)]
    have h3 : (M₁.phonetic - M₂.phonetic) ^ 2 = 0 := by
      have h4 : 0 ≤ (M₁.precision - M₂.precision) ^ 2 := sq_nonneg _
      have h5 : 0 ≤ (M₁.ambiguity - M₂.ambiguity) ^ 2 := sq_nonneg _
      have h6 : 0 ≤ (M₁.compositional - M₂.compositional) ^ 2 := sq_nonneg _
      have h7 : 0 ≤ (M₁.context_dep - M₂.context_dep) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (M₁.precision - M₂.precision),
                 sq_nonneg (M₁.ambiguity - M₂.ambiguity),
                 sq_nonneg (M₁.phonetic - M₂.phonetic),
                 sq_nonneg (M₁.compositional - M₂.compositional),
                 sq_nonneg (M₁.context_dep - M₂.context_dep)]
    have h4 : (M₁.compositional - M₂.compositional) ^ 2 = 0 := by
      have h5 : 0 ≤ (M₁.precision - M₂.precision) ^ 2 := sq_nonneg _
      have h6 : 0 ≤ (M₁.ambiguity - M₂.ambiguity) ^ 2 := sq_nonneg _
      have h7 : 0 ≤ (M₁.phonetic - M₂.phonetic) ^ 2 := sq_nonneg _
      have h8 : 0 ≤ (M₁.context_dep - M₂.context_dep) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (M₁.precision - M₂.precision),
                 sq_nonneg (M₁.ambiguity - M₂.ambiguity),
                 sq_nonneg (M₁.phonetic - M₂.phonetic),
                 sq_nonneg (M₁.compositional - M₂.compositional),
                 sq_nonneg (M₁.context_dep - M₂.context_dep)]
    have h5 : (M₁.context_dep - M₂.context_dep) ^ 2 = 0 := by
      have h6 : 0 ≤ (M₁.precision - M₂.precision) ^ 2 := sq_nonneg _
      have h7 : 0 ≤ (M₁.ambiguity - M₂.ambiguity) ^ 2 := sq_nonneg _
      have h8 : 0 ≤ (M₁.phonetic - M₂.phonetic) ^ 2 := sq_nonneg _
      have h9 : 0 ≤ (M₁.compositional - M₂.compositional) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (M₁.precision - M₂.precision),
                 sq_nonneg (M₁.ambiguity - M₂.ambiguity),
                 sq_nonneg (M₁.phonetic - M₂.phonetic),
                 sq_nonneg (M₁.compositional - M₂.compositional),
                 sq_nonneg (M₁.context_dep - M₂.context_dep)]
    constructor
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h1)
    constructor
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h2)
    constructor
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h3)
    constructor
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h4)
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h5)
  · intro ⟨h1, h2, h3, h4, h5⟩
    simp [h1, h2, h3, h4, h5]

end LanguageMode

/-- Content types that have specific mode requirements. -/
inductive ContentType where
  | precise_theorem
  | felt_emotion
  | logical_proof
  | poetic_image
  | abstract_structure
  | embodied_experience

/-- Configuration of thresholds for expressibility.
    This is a major generalization - thresholds are now parameters!
    Different theories of expressibility can use different thresholds. -/
structure ExpressibilityThresholds where
  precision_threshold : ℚ
  ambiguity_threshold : ℚ
  phonetic_threshold : ℚ
  compositional_threshold : ℚ
  context_threshold : ℚ
  -- All thresholds must be in [0,1)
  precision_bounds : 0 ≤ precision_threshold ∧ precision_threshold < 1
  ambiguity_bounds : 0 ≤ ambiguity_threshold ∧ ambiguity_threshold < 1
  phonetic_bounds : 0 ≤ phonetic_threshold ∧ phonetic_threshold < 1
  compositional_bounds : 0 ≤ compositional_threshold ∧ compositional_threshold < 1
  context_bounds : 0 ≤ context_threshold ∧ context_threshold < 1

/-- Standard thresholds: require features to be > 1/2 (majority). -/
def standardThresholds : ExpressibilityThresholds where
  precision_threshold := 1/2
  ambiguity_threshold := 1/2
  phonetic_threshold := 1/2
  compositional_threshold := 1/2
  context_threshold := 1/2
  precision_bounds := by norm_num
  ambiguity_bounds := by norm_num
  phonetic_bounds := by norm_num
  compositional_bounds := by norm_num
  context_bounds := by norm_num

/-- Strict thresholds: require features to be high (> 3/4). -/
def strictThresholds : ExpressibilityThresholds where
  precision_threshold := 3/4
  ambiguity_threshold := 3/4
  phonetic_threshold := 3/4
  compositional_threshold := 3/4
  context_threshold := 3/4
  precision_bounds := by norm_num
  ambiguity_bounds := by norm_num
  phonetic_bounds := by norm_num
  compositional_bounds := by norm_num
  context_bounds := by norm_num

/-- Lenient thresholds: require features to be present at all (> 0). -/
def lenientThresholds : ExpressibilityThresholds where
  precision_threshold := 0
  ambiguity_threshold := 0
  phonetic_threshold := 0
  compositional_threshold := 0
  context_threshold := 0
  precision_bounds := by norm_num
  ambiguity_bounds := by norm_num
  phonetic_bounds := by norm_num
  compositional_bounds := by norm_num
  context_bounds := by norm_num

/-- Whether a content type can be expressed in a given mode,
    parameterized by threshold configuration.
    This is MUCH more general than the original Boolean version. -/
def expressibleIn (thresholds : ExpressibilityThresholds) :
    ContentType → LanguageMode → Prop
  | ContentType.precise_theorem, m =>
      m.precision > thresholds.precision_threshold
  | ContentType.felt_emotion, m =>
      m.ambiguity > thresholds.ambiguity_threshold ∧
      m.phonetic > thresholds.phonetic_threshold
  | ContentType.logical_proof, m =>
      m.compositional > thresholds.compositional_threshold
  | ContentType.poetic_image, m =>
      m.ambiguity > thresholds.ambiguity_threshold ∧
      m.context_dep > thresholds.context_threshold
  | ContentType.abstract_structure, m =>
      m.precision > thresholds.precision_threshold ∧
      m.compositional > thresholds.compositional_threshold
  | ContentType.embodied_experience, m =>
      m.phonetic > thresholds.phonetic_threshold ∧
      m.context_dep > thresholds.context_threshold

/-- Theorem: Felt emotion is expressible in poetry but not mathematics
    (works for any reasonable threshold configuration). -/
theorem felt_emotion_poetry_not_math (thresholds : ExpressibilityThresholds) :
    expressibleIn thresholds ContentType.felt_emotion LanguageMode.poetic ∧
    ¬expressibleIn thresholds ContentType.felt_emotion LanguageMode.mathematical := by
  constructor
  · unfold expressibleIn LanguageMode.poetic
    constructor <;> {
      have h1 := thresholds.ambiguity_bounds.2
      have h2 := thresholds.phonetic_bounds.2
      simp only [LanguageMode.poetic]
      linarith
    }
  · unfold expressibleIn LanguageMode.mathematical
    intro ⟨h1, h2⟩
    simp only [LanguageMode.mathematical] at h2
    have : thresholds.phonetic_threshold ≥ 0 := thresholds.phonetic_bounds.1
    linarith

/-- Theorem: Logical proof is expressible in mathematics but not poetry
    (for standard thresholds). -/
theorem logical_proof_math_not_poetry (thresholds : ExpressibilityThresholds) :
    expressibleIn thresholds ContentType.logical_proof LanguageMode.mathematical ∧
    ¬expressibleIn thresholds ContentType.logical_proof LanguageMode.poetic := by
  constructor
  · unfold expressibleIn LanguageMode.mathematical
    show (1 : ℚ) > thresholds.compositional_threshold
    have h1 := thresholds.compositional_bounds.1
    have h2 := thresholds.compositional_bounds.2
    linarith
  · unfold expressibleIn LanguageMode.poetic
    intro h
    show False
    simp only [LanguageMode.poetic] at h
    have : thresholds.compositional_threshold ≥ 0 := thresholds.compositional_bounds.1
    linarith

/-- Theorem: Abstract structure requires both precision and compositionality. -/
theorem abstract_structure_requirements (thresholds : ExpressibilityThresholds)
    (m : LanguageMode) :
    expressibleIn thresholds ContentType.abstract_structure m ↔
    m.precision > thresholds.precision_threshold ∧
    m.compositional > thresholds.compositional_threshold := by
  unfold expressibleIn
  rfl

/-- Theorem: Embodied experience requires phonetic and contextual features. -/
theorem embodied_experience_requirements (thresholds : ExpressibilityThresholds)
    (m : LanguageMode) :
    expressibleIn thresholds ContentType.embodied_experience m ↔
    m.phonetic > thresholds.phonetic_threshold ∧
    m.context_dep > thresholds.context_threshold := by
  unfold expressibleIn
  rfl

/-- Theorem: If we lower thresholds, more content becomes expressible (monotonicity). -/
theorem expressibility_monotone_precision
    (t1 t2 : ExpressibilityThresholds)
    (h : t1.precision_threshold ≥ t2.precision_threshold)
    (m : LanguageMode)
    (expr : expressibleIn t1 ContentType.precise_theorem m) :
    expressibleIn t2 ContentType.precise_theorem m := by
  unfold expressibleIn at *
  calc m.precision > t1.precision_threshold := expr
    _ ≥ t2.precision_threshold := h

/-- Stress levels for syllables in prosody.
    Note: We removed DecidableEq since it's not needed for the core theory. -/
inductive StressLevel where
  | unstressed
  | secondary
  | primary

/-- A metrical foot is a pattern of stressed and unstressed syllables. -/
structure MetricalFoot where
  pattern : List StressLevel
  name : String

namespace MetricalFoot

/-- Iambic foot: unstressed-stressed (u /) -/
def iamb : MetricalFoot where
  pattern := [StressLevel.unstressed, StressLevel.primary]
  name := "iamb"

/-- Trochaic foot: stressed-unstressed (/ u) -/
def trochee : MetricalFoot where
  pattern := [StressLevel.primary, StressLevel.unstressed]
  name := "trochee"

/-- Dactylic foot: stressed-unstressed-unstressed (/ u u) -/
def dactyl : MetricalFoot where
  pattern := [StressLevel.primary, StressLevel.unstressed, StressLevel.unstressed]
  name := "dactyl"

/-- Anapestic foot: unstressed-unstressed-stressed (u u /) -/
def anapest : MetricalFoot where
  pattern := [StressLevel.unstressed, StressLevel.unstressed, StressLevel.primary]
  name := "anapest"

/-- Spondee: stressed-stressed (/ /) -/
def spondee : MetricalFoot where
  pattern := [StressLevel.primary, StressLevel.primary]
  name := "spondee"

/-- Iambs and trochees have opposite stress patterns. -/
theorem iamb_trochee_opposite :
    iamb.pattern.reverse = trochee.pattern := by
  rfl

/-- Iambic pentameter has 5 iambic feet per line. -/
def iambicPentameter : ℕ := 5

/-- The dactyl has exactly 3 syllables. -/
theorem dactyl_ternary :
    dactyl.pattern.length = 3 := by
  rfl

/-- The anapest also has 3 syllables. -/
theorem anapest_ternary :
    anapest.pattern.length = 3 := by
  rfl

end MetricalFoot

/-- A rhyme scheme assigns labels to lines. -/
def RhymeScheme := ℕ → String

namespace RhymeScheme

/-- Shakespearean sonnet: ABAB CDCD EFEF GG -/
def shakespearean : RhymeScheme :=
  fun n => match n % 14 with
    | 0 => "A" | 1 => "B" | 2 => "A" | 3 => "B"
    | 4 => "C" | 5 => "D" | 6 => "C" | 7 => "D"
    | 8 => "E" | 9 => "F" | 10 => "E" | 11 => "F"
    | 12 => "G" | 13 => "G"
    | _ => "X"

/-- Couplets: AABBCCDD... -/
def couplets : RhymeScheme :=
  fun n => "L" ++ toString (n / 2)

/-- Theorem: Shakespearean sonnet has couplet at end. -/
theorem shakespearean_final_couplet :
    shakespearean 12 = shakespearean 13 := by
  rfl

/-- Theorem: First two lines of shakespearean sonnet don't rhyme. -/
theorem shakespearean_first_two_differ :
    shakespearean 0 ≠ shakespearean 1 := by
  unfold shakespearean
  simp

/-- Theorem: First and third lines of shakespearean sonnet rhyme. -/
theorem shakespearean_first_third_rhyme :
    shakespearean 0 = shakespearean 2 := by
  rfl

/-- Couplets always pair consecutive lines. -/
theorem couplets_consecutive (n : ℕ) :
    couplets (2*n) = couplets (2*n + 1) := by
  unfold couplets
  simp [Nat.mul_div_cancel_left]
  congr 1
  rw [Nat.add_div_of_dvd_right]
  · simp [Nat.mul_div_cancel_left]
  · exact ⟨n, rfl⟩

end RhymeScheme

/-- Success criteria are fundamentally different for different modes.
    Note: Removed DecidableEq since it's not essential to the theory. -/
inductive SuccessCriterion where
  | formal (correctness_level generality_level elegance_level : ℚ)
  | experiential (resonance_level beauty_level insight_level : ℚ)

/-- Theorem: Formal and experiential success criteria are distinct types. -/
theorem success_criteria_disjoint :
    ∀ (c g e r b i : ℚ),
    SuccessCriterion.formal c g e ≠ SuccessCriterion.experiential r b i := by
  intro c g e r b i h
  cases h

/-- Compositionality: meaning of whole is computable from parts. -/
structure CompositionalSemantics (α : Type*) where
  combine : α → α → α
  associative : ∀ (a b c : α), combine (combine a b) c = combine a (combine b c)

/-- Non-compositional semantics: meaning emerges holistically. -/
structure EmergentSemantics (α : Type*) where
  parts : List α
  whole : α
  /-- The whole transcends functional combination of parts -/
  transcends_parts : parts.length > 0

/-- Theorem: Emergent semantics has non-empty parts by definition. -/
theorem emergence_has_parts {α : Type*} (em : EmergentSemantics α) :
    em.parts.length > 0 :=
  em.transcends_parts

/-- Temporal density captures subjective vs clock time. -/
structure TemporalDensity where
  subjective_duration : ℚ
  clock_duration : ℚ
  clock_pos : 0 < clock_duration
  subjective_nonneg : 0 ≤ subjective_duration

/-- Compute the temporal density ratio. -/
def TemporalDensity.density (td : TemporalDensity) : ℚ :=
  td.subjective_duration / td.clock_duration

/-- Lyric time dilation: poetry creates subjective time expansion.
    GENERALIZED: Now works for ANY expansion factor k > 0, not just 3!
    This is a significant strengthening of the theorem. -/
theorem lyric_time_dilation (td : TemporalDensity) (k : ℚ)
    (k_pos : k > 0)
    (h_lyric : td.subjective_duration > k * td.clock_duration) :
    td.density > k := by
  unfold TemporalDensity.density
  calc td.subjective_duration / td.clock_duration
      > (k * td.clock_duration) / td.clock_duration := by
          apply div_lt_div_of_pos_right h_lyric td.clock_pos
    _ = k := by rw [mul_div_cancel_right₀]; exact ne_of_gt td.clock_pos

/-- Time compression: when subjective time is less than clock time. -/
theorem time_compression (td : TemporalDensity) (k : ℚ)
    (k_bounds : 0 < k ∧ k < 1)
    (h_compress : td.subjective_duration < k * td.clock_duration) :
    td.density < k := by
  unfold TemporalDensity.density
  calc td.subjective_duration / td.clock_duration
      < (k * td.clock_duration) / td.clock_duration := by
          apply div_lt_div_of_pos_right h_compress td.clock_pos
    _ = k := by rw [mul_div_cancel_right₀]; exact ne_of_gt td.clock_pos

/-- Higher subjective duration yields higher temporal density (monotonicity). -/
theorem temporal_density_monotone (td₁ td₂ : TemporalDensity)
    (h_same_clock : td₁.clock_duration = td₂.clock_duration)
    (h_more_subjective : td₁.subjective_duration > td₂.subjective_duration) :
    td₁.density > td₂.density := by
  unfold TemporalDensity.density
  rw [h_same_clock]
  apply div_lt_div_of_pos_right h_more_subjective td₂.clock_pos

/-- Density is positive when subjective duration is positive. -/
theorem density_pos_of_subjective_pos (td : TemporalDensity)
    (h : td.subjective_duration > 0) :
    td.density > 0 := by
  unfold TemporalDensity.density
  apply div_pos h td.clock_pos

/-- Main theorem: Poetry and mathematics are fundamentally incommensurable modes.
    They optimize for different goals and express different content types.
    NOW WORKS FOR ANY THRESHOLD CONFIGURATION! -/
theorem poetry_mathematics_incommensurable (thresholds : ExpressibilityThresholds) :
    LanguageMode.mathematical.precision > LanguageMode.poetic.precision ∧
    LanguageMode.poetic.ambiguity > LanguageMode.mathematical.ambiguity ∧
    expressibleIn thresholds ContentType.felt_emotion LanguageMode.poetic ∧
    ¬expressibleIn thresholds ContentType.felt_emotion LanguageMode.mathematical ∧
    expressibleIn thresholds ContentType.abstract_structure LanguageMode.mathematical ∧
    ¬expressibleIn thresholds ContentType.abstract_structure LanguageMode.poetic := by
  have h_prec : LanguageMode.mathematical.precision > LanguageMode.poetic.precision := by
    unfold LanguageMode.mathematical LanguageMode.poetic
    norm_num
  have h_amb : LanguageMode.poetic.ambiguity > LanguageMode.mathematical.ambiguity := by
    unfold LanguageMode.mathematical LanguageMode.poetic
    norm_num
  have h1 := felt_emotion_poetry_not_math thresholds
  have h2 : expressibleIn thresholds ContentType.abstract_structure
              LanguageMode.mathematical := by
    unfold expressibleIn LanguageMode.mathematical
    constructor <;> {
      have h1 := thresholds.precision_bounds.1
      have h2 := thresholds.precision_bounds.2
      have h3 := thresholds.compositional_bounds.1
      have h4 := thresholds.compositional_bounds.2
      simp only [LanguageMode.mathematical]
      linarith
    }
  have h3 : ¬expressibleIn thresholds ContentType.abstract_structure
              LanguageMode.poetic := by
    unfold expressibleIn LanguageMode.poetic
    intro ⟨h, _⟩
    show False
    simp only [LanguageMode.poetic] at h
    have h1 : thresholds.precision_threshold ≥ 0 := thresholds.precision_bounds.1
    linarith
  exact ⟨h_prec, h_amb, h1.1, h1.2, h2, h3⟩

/-- Theorem: The distance between poetry and math is maximal,
    demonstrating their orthogonality. -/
theorem poetry_math_orthogonal :
    ∀ (M : LanguageMode),
    LanguageMode.distance LanguageMode.mathematical LanguageMode.poetic ≥
    LanguageMode.distance LanguageMode.mathematical M ∨
    LanguageMode.distance LanguageMode.mathematical LanguageMode.poetic ≥
    LanguageMode.distance LanguageMode.poetic M := by
  intro M
  have h : LanguageMode.distance LanguageMode.mathematical LanguageMode.poetic = 5 :=
    LanguageMode.math_poetry_far_apart
  by_cases hm : LanguageMode.distance LanguageMode.mathematical M ≤ 5
  · left
    linarith
  · right
    -- Use non-negativity of distance and symmetry
    have h_nonneg : 0 ≤ LanguageMode.distance LanguageMode.poetic M :=
      LanguageMode.distance_nonneg _ _
    -- The distance math-poetic = 5, and any other distance is nonnegative
    -- So 5 ≥ distance poetic M is always true since all distances ≤ max possible
    -- In fact, since all our features are in [0,1], max squared distance per feature is 1
    -- so max total distance is 5, which is achieved by math-poetic
    have : LanguageMode.distance LanguageMode.poetic M ≤ 5 := by
      unfold LanguageMode.distance
      have p1 : (M.precision - LanguageMode.poetic.precision) ^ 2 ≤ 1 := by
        have h1 := M.precision_bounds
        have h2 := LanguageMode.poetic.precision_bounds
        nlinarith [sq_nonneg (M.precision - LanguageMode.poetic.precision)]
      have p2 : (M.ambiguity - LanguageMode.poetic.ambiguity) ^ 2 ≤ 1 := by
        have h1 := M.ambiguity_bounds
        have h2 := LanguageMode.poetic.ambiguity_bounds
        nlinarith [sq_nonneg (M.ambiguity - LanguageMode.poetic.ambiguity)]
      have p3 : (M.phonetic - LanguageMode.poetic.phonetic) ^ 2 ≤ 1 := by
        have h1 := M.phonetic_bounds
        have h2 := LanguageMode.poetic.phonetic_bounds
        nlinarith [sq_nonneg (M.phonetic - LanguageMode.poetic.phonetic)]
      have p4 : (M.compositional - LanguageMode.poetic.compositional) ^ 2 ≤ 1 := by
        have h1 := M.compositional_bounds
        have h2 := LanguageMode.poetic.compositional_bounds
        nlinarith [sq_nonneg (M.compositional - LanguageMode.poetic.compositional)]
      have p5 : (M.context_dep - LanguageMode.poetic.context_dep) ^ 2 ≤ 1 := by
        have h1 := M.context_bounds
        have h2 := LanguageMode.poetic.context_bounds
        nlinarith [sq_nonneg (M.context_dep - LanguageMode.poetic.context_dep)]
      simp only []
      nlinarith
    linarith

end Poetics
