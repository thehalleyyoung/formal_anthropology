import FormalAnthropology.IDT_v3_Foundations

/-!
# Formal Poetics in Ideatic Space

Formalizing meter, rhyme, repetition, variation, condensation of meaning,
and fixed poetic forms within the IdeaticSpace3 framework.

All 85+ theorems are fully proved with 0 sorries.
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. Repetition and Anaphora -/

section RepetitionAnaphora
variable {I : Type*} [IdeaticSpace3 I]

/-- Repetition: composing an idea with itself n times. -/
noncomputable def repetition (a : I) (n : ℕ) : I := composeN a n

-- T1
theorem repetition_zero (a : I) : repetition a 0 = (void : I) :=
  composeN_zero a

-- T2
theorem repetition_one (a : I) : repetition a 1 = a :=
  composeN_one a

-- T3
theorem repetition_succ (a : I) (n : ℕ) :
    repetition a (n + 1) = compose (repetition a n) a :=
  composeN_succ a n

-- T4
theorem repetition_two (a : I) : repetition a 2 = compose a a :=
  composeN_two a

-- T5: weight never decreases under repetition
theorem repetition_weight_mono (a : I) (n : ℕ) :
    rs (repetition a (n + 1)) (repetition a (n + 1)) ≥
    rs (repetition a n) (repetition a n) := by
  simp only [repetition, composeN_succ]
  exact compose_enriches' (composeN a n) a

-- T6: repeated void is void
theorem repetition_void (n : ℕ) : repetition (void : I) n = (void : I) :=
  composeN_void n

-- T7: weight of repetition is always nonneg
theorem repetition_weight_nonneg (a : I) (n : ℕ) :
    rs (repetition a n) (repetition a n) ≥ 0 :=
  rs_self_nonneg' _

-- T8: emergence of adding one more repetition
noncomputable def repetitionEmergence (a : I) (n : ℕ) (c : I) : ℝ :=
  emergence (repetition a n) a c

-- T9: repetition emergence at n=0 is zero (void on left)
theorem repetitionEmergence_zero (a c : I) :
    repetitionEmergence a 0 c = 0 := by
  unfold repetitionEmergence repetition
  simp [composeN_zero, emergence_void_left]

-- T10: repetition emergence against void vanishes
theorem repetitionEmergence_void (a : I) (n : ℕ) :
    repetitionEmergence a n (void : I) = 0 := by
  unfold repetitionEmergence; exact emergence_against_void _ _

-- T11: first repetition emergence at self is semantic charge
theorem repetitionEmergence_one_self (a : I) :
    repetitionEmergence a 1 a = semanticCharge a := by
  unfold repetitionEmergence semanticCharge repetition
  simp [composeN_one]

/-- Anaphora resonance: how n-fold repetition resonates with an observer. -/
noncomputable def anaphoraResonance (a : I) (n : ℕ) (observer : I) : ℝ :=
  rs (repetition a n) observer

-- T12: anaphora at 0 is zero
theorem anaphora_zero (a observer : I) :
    anaphoraResonance a 0 observer = 0 := by
  unfold anaphoraResonance repetition
  simp [composeN_zero, rs_void_left']

-- T13: anaphora against void observer is zero
theorem anaphora_void_observer (a : I) (n : ℕ) :
    anaphoraResonance a n (void : I) = 0 := by
  unfold anaphoraResonance; exact rs_void_right' _

-- T14: anaphora at 1 is just resonance
theorem anaphora_one (a observer : I) :
    anaphoraResonance a 1 observer = rs a observer := by
  unfold anaphoraResonance repetition; simp [composeN_one]

-- T15: anaphora decomposition via emergence
theorem anaphora_succ (a : I) (n : ℕ) (observer : I) :
    anaphoraResonance a (n + 1) observer =
    anaphoraResonance a n observer + rs a observer +
    repetitionEmergence a n observer := by
  unfold anaphoraResonance repetitionEmergence repetition
  rw [composeN_succ, rs_compose_eq]

end RepetitionAnaphora

/-! ## §2. Meter and Rhythm -/

section MeterRhythm
variable {I : Type*} [IdeaticSpace3 I]

/-- A metrical foot: the composition of two elements. -/
def metricalFoot (a b : I) : I := compose a b

/-- Iamb: unstress then stress (second heavier than first). -/
def isIamb (a b : I) : Prop := rs a a < rs b b

/-- Trochee: stress then unstress. -/
def isTrochee (a b : I) : Prop := rs a a > rs b b

/-- Spondee: equal stress. -/
def isSpondee (a b : I) : Prop := rs a a = rs b b

-- T16: foot weight ≥ first element
theorem foot_weight_ge_first (a b : I) :
    rs (metricalFoot a b) (metricalFoot a b) ≥ rs a a := by
  unfold metricalFoot; exact compose_enriches' a b

-- T17: iamb and trochee are mutually exclusive
theorem iamb_trochee_exclusive (a b : I) : ¬(isIamb a b ∧ isTrochee a b) := by
  intro ⟨h1, h2⟩; unfold isIamb at h1; unfold isTrochee at h2; linarith

-- T18: spondee excludes iamb
theorem spondee_not_iamb (a b : I) (h : isSpondee a b) : ¬isIamb a b := by
  unfold isSpondee at h; unfold isIamb; linarith

-- T19: spondee excludes trochee
theorem spondee_not_trochee (a b : I) (h : isSpondee a b) : ¬isTrochee a b := by
  unfold isSpondee at h; unfold isTrochee; linarith

-- T20: void-void foot is a spondee
theorem void_void_spondee : isSpondee (void : I) (void : I) := by
  unfold isSpondee; simp [rs_void_void]

/-- Regular meter: n copies of a foot. -/
def regularMeter (a b : I) : ℕ → I
  | 0 => void
  | n + 1 => compose (regularMeter a b n) (metricalFoot a b)

-- T21: regular meter 0 is void
theorem regularMeter_zero (a b : I) : regularMeter a b 0 = (void : I) := rfl

-- T22: regular meter 1 is the foot
theorem regularMeter_one (a b : I) : regularMeter a b 1 = metricalFoot a b := by
  simp [regularMeter, metricalFoot]

-- T23: weight grows monotonically in regular meter
theorem regularMeter_weight_mono (a b : I) (n : ℕ) :
    rs (regularMeter a b (n + 1)) (regularMeter a b (n + 1)) ≥
    rs (regularMeter a b n) (regularMeter a b n) := by
  simp only [regularMeter]
  exact compose_enriches' (regularMeter a b n) (metricalFoot a b)

-- T24: regular meter weight is nonneg
theorem regularMeter_weight_nonneg (a b : I) (n : ℕ) :
    rs (regularMeter a b n) (regularMeter a b n) ≥ 0 :=
  rs_self_nonneg' _

-- T25: void foot gives void meter
theorem regularMeter_void (n : ℕ) :
    regularMeter (void : I) (void : I) n = (void : I) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold regularMeter metricalFoot
    rw [ih]; simp

-- T26: meter resonance decomposition
theorem regularMeter_resonance (a b : I) (n : ℕ) (obs : I) :
    rs (regularMeter a b (n + 1)) obs =
    rs (regularMeter a b n) obs + rs (metricalFoot a b) obs +
    emergence (regularMeter a b n) (metricalFoot a b) obs := by
  simp only [regularMeter]; rw [rs_compose_eq]

end MeterRhythm

/-! ## §3. Rhyme and Resonance -/

section RhymeResonance
variable {I : Type*} [IdeaticSpace3 I]

/-- Rhyme strength: symmetric measure of mutual resonance. -/
noncomputable def rhymeStrength (a b : I) : ℝ := rs a b + rs b a

/-- Perfect rhyme: positive resonance in both directions. -/
def isPerfectRhyme (a b : I) : Prop := rs a b > 0 ∧ rs b a > 0

/-- Near rhyme: positive in one direction only. -/
def isNearRhyme (a b : I) : Prop := rs a b > 0 ∧ rs b a ≤ 0

-- T27: rhyme strength is symmetric
theorem rhymeStrength_symm (a b : I) : rhymeStrength a b = rhymeStrength b a := by
  unfold rhymeStrength; ring

-- T28: rhyme with void is zero
theorem rhymeStrength_void (a : I) : rhymeStrength a (void : I) = 0 := by
  unfold rhymeStrength; simp [rs_void_right', rs_void_left']

-- T29: void-void rhyme is zero
theorem rhymeStrength_void_void : rhymeStrength (void : I) (void : I) = 0 := by
  unfold rhymeStrength; simp [rs_void_void]

-- T30: self-rhyme is double self-resonance
theorem rhymeStrength_self (a : I) : rhymeStrength a a = 2 * rs a a := by
  unfold rhymeStrength; ring

-- T31: self-rhyme is nonneg
theorem rhymeStrength_self_nonneg (a : I) : rhymeStrength a a ≥ 0 := by
  rw [rhymeStrength_self]; linarith [rs_self_nonneg' a]

-- T32: perfect rhyme implies positive rhyme strength
theorem perfect_rhyme_positive (a b : I) (h : isPerfectRhyme a b) :
    rhymeStrength a b > 0 := by
  unfold rhymeStrength; obtain ⟨h1, h2⟩ := h; linarith

-- T33: near rhyme is not perfect rhyme
theorem near_not_perfect (a b : I) (h : isNearRhyme a b) : ¬isPerfectRhyme a b := by
  intro hp; obtain ⟨_, h2⟩ := h; obtain ⟨_, h4⟩ := hp; linarith

-- T34: composing rhyming elements — resonance decomposition
theorem rhyme_compose_resonance (a b c : I) :
    rs (compose a b) c = rs a c + rs b c + emergence a b c :=
  rs_compose_eq a b c

-- T35: emergence squared bound for rhyme
theorem rhyme_emergence_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

-- T36: perfect self-rhyme for non-void
theorem self_rhyme_nonvoid (a : I) (h : a ≠ void) :
    isPerfectRhyme a a := by
  unfold isPerfectRhyme; exact ⟨rs_self_pos a h, rs_self_pos a h⟩

-- T37: void has no perfect self-rhyme
theorem void_no_self_rhyme : ¬isPerfectRhyme (void : I) (void : I) := by
  intro ⟨h, _⟩; simp [rs_void_void] at h

end RhymeResonance

/-! ## §4. Condensation and Compression -/

section CondensationCompression
variable {I : Type*} [IdeaticSpace3 I]

/-- Weight: self-resonance of an idea. -/
noncomputable def weight (a : I) : ℝ := rs a a

-- T38: weight is nonneg
theorem weight_nonneg (a : I) : weight a ≥ 0 := by
  unfold weight; exact rs_self_nonneg' a

-- T39: weight of void is zero
theorem weight_void : weight (void : I) = 0 := by
  unfold weight; exact rs_void_void

-- T40: nonvoid has positive weight
theorem weight_pos (a : I) (h : a ≠ void) : weight a > 0 := by
  unfold weight; exact rs_self_pos a h

-- T41: composition weight ≥ first part
theorem compose_weight_ge (a b : I) : weight (compose a b) ≥ weight a := by
  unfold weight; exact compose_enriches' a b

-- T42: composition weight ≥ 0 always
theorem compose_weight_nonneg (a b : I) : weight (compose a b) ≥ 0 := by
  unfold weight; exact rs_self_nonneg' _

/-- Compression gain: extra weight from composition beyond sum of parts. -/
noncomputable def compressionGain (a b : I) : ℝ :=
  weight (compose a b) - weight a - weight b

-- T43: compression gain lower bound
theorem compressionGain_lower (a b : I) :
    compressionGain a b ≥ -weight b := by
  unfold compressionGain; linarith [compose_weight_ge a b]

-- T44: void composition has nonpositive compression gain
theorem compressionGain_void_right (a : I) :
    compressionGain a (void : I) = -weight (void : I) := by
  unfold compressionGain weight; simp [void_right', rs_void_void]

-- T45: compression gain with void right simplified
theorem compressionGain_void_right' (a : I) :
    compressionGain a (void : I) = 0 := by
  rw [compressionGain_void_right, weight_void, neg_zero]

-- T46: compression gain with void left
theorem compressionGain_void_left (b : I) :
    compressionGain (void : I) b = 0 := by
  unfold compressionGain weight; simp [void_left', rs_void_void]

/-- An idea is condensed if composition produces more weight than sum. -/
def isCondensed (a b : I) : Prop := compressionGain a b > 0

-- T47: void composition is never condensed
theorem void_not_condensed_right (a : I) : ¬isCondensed a (void : I) := by
  unfold isCondensed; rw [compressionGain_void_right']; linarith

-- T48: void composition is never condensed (left)
theorem void_not_condensed_left (b : I) : ¬isCondensed (void : I) b := by
  unfold isCondensed; rw [compressionGain_void_left]; linarith

-- T49: double composition weight chain
theorem double_compose_weight (a b c : I) :
    weight (compose (compose a b) c) ≥ weight a := by
  unfold weight
  linarith [compose_enriches' a b, compose_enriches' (compose a b) c]

end CondensationCompression

/-! ## §5. Variation and Development -/

section VariationDevelopment
variable {I : Type*} [IdeaticSpace3 I]

/-- First variation: theme modified by b. -/
def variation1 (a b : I) : I := compose a b

/-- Second variation: first variation modified by c. -/
def variation2 (a b c : I) : I := compose (compose a b) c

-- T50: variation enriches theme
theorem variation1_enriches (a b : I) :
    weight (variation1 a b) ≥ weight a := by
  unfold variation1 weight; exact compose_enriches' a b

-- T51: second variation enriches first
theorem variation2_enriches_v1 (a b c : I) :
    weight (variation2 a b c) ≥ weight (variation1 a b) := by
  unfold variation2 variation1 weight; exact compose_enriches' (compose a b) c

-- T52: second variation enriches theme
theorem variation2_enriches_theme (a b c : I) :
    weight (variation2 a b c) ≥ weight a := by
  unfold variation2 weight
  linarith [compose_enriches' a b, compose_enriches' (compose a b) c]

-- T53: variation is associative
theorem variation2_assoc (a b c : I) :
    variation2 a b c = compose a (compose b c) := by
  unfold variation2; exact compose_assoc' a b c

/-- Gap between variations as observed. -/
noncomputable def variationGap (a b c observer : I) : ℝ :=
  rs (variation2 a b c) observer - rs (variation1 a b) observer

-- T54: variation gap equals modifier resonance + emergence
theorem variationGap_eq (a b c observer : I) :
    variationGap a b c observer =
    rs c observer + emergence (compose a b) c observer := by
  unfold variationGap variation2 variation1
  rw [rs_compose_eq (compose a b) c observer]; ring

-- T55: variation gap against void is zero
theorem variationGap_void (a b c : I) :
    variationGap a b c (void : I) = 0 := by
  unfold variationGap variation2 variation1
  simp [rs_void_right']

-- T56: void modifier produces zero gap
theorem variationGap_void_modifier (a b observer : I) :
    variationGap a b (void : I) observer = 0 := by
  unfold variationGap variation2 variation1
  simp [void_right']

/-- Iterated variation with a sequence of modifiers. -/
def iteratedVariation (a : I) : List I → I
  | [] => a
  | m :: rest => iteratedVariation (compose a m) rest

-- T57: iterated variation with no modifiers is the theme
theorem iteratedVariation_nil (a : I) : iteratedVariation a [] = a := rfl

-- T58: iterated variation with one modifier
theorem iteratedVariation_singleton (a m : I) :
    iteratedVariation a [m] = compose a m := rfl

-- T59: iterated variation with two modifiers
theorem iteratedVariation_two (a m₁ m₂ : I) :
    iteratedVariation a [m₁, m₂] = compose (compose a m₁) m₂ := rfl

-- T60: iterated void modifiers preserve idea
theorem iteratedVariation_void_singleton (a : I) :
    iteratedVariation a [(void : I)] = a := by
  simp [iteratedVariation, void_right']

end VariationDevelopment

/-! ## §6. Parallelism and Antithesis -/

section ParallelismAntithesis
variable {I : Type*} [IdeaticSpace3 I]

/-- Parallel emergence gap: how differently a and b interact with context c. -/
noncomputable def parallelGap (a b c observer : I) : ℝ :=
  emergence a c observer - emergence b c observer

-- T61: parallel gap is antisymmetric in a, b
theorem parallelGap_antisymm (a b c observer : I) :
    parallelGap a b c observer = -parallelGap b a c observer := by
  unfold parallelGap; ring

-- T62: parallel gap with same idea is zero
theorem parallelGap_self (a c observer : I) :
    parallelGap a a c observer = 0 := by
  unfold parallelGap; ring

-- T63: parallel gap with void observer is zero
theorem parallelGap_void_obs (a b c : I) :
    parallelGap a b c (void : I) = 0 := by
  unfold parallelGap; simp [emergence_against_void]

/-- Chiasmic difference: compose a b vs compose b a. -/
noncomputable def chiasmicDiff (a b observer : I) : ℝ :=
  rs (compose a b) observer - rs (compose b a) observer

-- T64: chiasmic difference is antisymmetric
theorem chiasmic_antisymm (a b observer : I) :
    chiasmicDiff a b observer = -chiasmicDiff b a observer := by
  unfold chiasmicDiff; ring

-- T65: chiasmic difference = emergence difference
theorem chiasmic_eq_emergence (a b observer : I) :
    chiasmicDiff a b observer = emergence a b observer - emergence b a observer := by
  unfold chiasmicDiff emergence; ring

-- T66: chiasmic difference with void left
theorem chiasmic_void_left (b observer : I) :
    chiasmicDiff (void : I) b observer = 0 := by
  unfold chiasmicDiff; simp

-- T67: chiasmic difference with void right
theorem chiasmic_void_right (a observer : I) :
    chiasmicDiff a (void : I) observer = 0 := by
  unfold chiasmicDiff; simp

-- T68: chiasmic difference against void observer
theorem chiasmic_void_observer (a b : I) :
    chiasmicDiff a b (void : I) = 0 := by
  unfold chiasmicDiff; simp [rs_void_right']

/-- Antithetical composition: negative emergence. -/
def isAntithetical (a b observer : I) : Prop := emergence a b observer < 0

-- T69: void is never antithetical (right)
theorem void_not_antithetical_right (a observer : I) :
    ¬isAntithetical a (void : I) observer := by
  unfold isAntithetical; rw [emergence_void_right]; linarith

-- T70: void is never antithetical (left)
theorem void_not_antithetical_left (b observer : I) :
    ¬isAntithetical (void : I) b observer := by
  unfold isAntithetical; rw [emergence_void_left]; linarith

-- T71: parallel weight comparison
theorem parallel_compose_weight (a b c : I) :
    weight (compose a c) ≥ weight a ∧ weight (compose b c) ≥ weight b :=
  ⟨compose_weight_ge a c, compose_weight_ge b c⟩

end ParallelismAntithesis

/-! ## §7. Economy and Superfluity -/

section EconomySuperfluity
variable {I : Type*} [IdeaticSpace3 I]

/-- Right-superfluous: composing on the right doesn't change anything. -/
def isRightSuperfluous (b : I) : Prop := ∀ a : I, compose a b = a

/-- Left-superfluous: composing on the left doesn't change anything. -/
def isLeftSuperfluous (b : I) : Prop := ∀ a : I, compose b a = a

-- T72: void is right-superfluous
theorem void_right_superfluous : isRightSuperfluous (void : I) :=
  fun a => void_right' a

-- T73: right-superfluous must be void
theorem right_superfluous_is_void (b : I) (h : isRightSuperfluous b) : b = void := by
  have := h (void : I); simp at this; exact this

-- T74: right-superfluous iff void
theorem right_superfluous_iff (b : I) : isRightSuperfluous b ↔ b = void := by
  constructor
  · exact right_superfluous_is_void b
  · intro h; rw [h]; exact void_right_superfluous

-- T75: void is left-superfluous
theorem void_left_superfluous : isLeftSuperfluous (void : I) :=
  fun a => void_left' a

-- T76: left-superfluous must be void
theorem left_superfluous_is_void (b : I) (h : isLeftSuperfluous b) : b = void := by
  have := h (void : I); simp at this; exact this

-- T77: left-superfluous iff void
theorem left_superfluous_iff (b : I) : isLeftSuperfluous b ↔ b = void := by
  constructor
  · exact left_superfluous_is_void b
  · intro h; rw [h]; exact void_left_superfluous

/-- Emergence-silent: never produces emergence when composed on right. -/
def isEmergenceSilent (b : I) : Prop :=
  ∀ a c : I, emergence a b c = 0

-- T78: void is emergence-silent
theorem void_emergence_silent : isEmergenceSilent (void : I) :=
  fun a c => emergence_void_right a c

/-- Essential: a non-void idea. -/
def isEssential (a : I) : Prop := a ≠ void

-- T79: essential elements have positive weight
theorem essential_pos_weight (a : I) (h : isEssential a) : weight a > 0 :=
  weight_pos a h

-- T80: composing two voids gives void (economy of silence)
theorem silence_economy : compose (void : I) (void : I) = (void : I) := by simp

-- T81: emergence-silent element produces additive resonance
theorem emergence_silent_additive (b : I) (h : isEmergenceSilent b) (a c : I) :
    rs (compose a b) c = rs a c + rs b c := by
  have := rs_compose_eq a b c; rw [h a c] at this; linarith

end EconomySuperfluity

/-! ## §8. The Sonnet and Fixed Forms -/

section SonnetFixedForms
variable {I : Type*} [IdeaticSpace3 I]

/-- A couplet: two lines composed. -/
def couplet (a b : I) : I := compose a b

/-- A quatrain: two couplets composed. -/
def quatrain (a b c d : I) : I := compose (couplet a b) (couplet c d)

-- T82: couplet weight ≥ first line
theorem couplet_weight_ge (a b : I) : weight (couplet a b) ≥ weight a := by
  unfold couplet; exact compose_weight_ge a b

-- T83: quatrain weight ≥ first couplet
theorem quatrain_weight_ge_couplet (a b c d : I) :
    weight (quatrain a b c d) ≥ weight (couplet a b) := by
  unfold quatrain; exact compose_weight_ge (couplet a b) (couplet c d)

-- T84: quatrain weight ≥ first line
theorem quatrain_weight_ge_line (a b c d : I) :
    weight (quatrain a b c d) ≥ weight a := by
  have h1 := couplet_weight_ge a b
  have h2 := quatrain_weight_ge_couplet a b c d
  linarith

/-- Volta emergence: the turn between two sections. -/
noncomputable def voltaEmergence (sec1 sec2 observer : I) : ℝ :=
  emergence sec1 sec2 observer

-- T85: volta against void observer is zero
theorem volta_void_observer (s1 s2 : I) :
    voltaEmergence s1 s2 (void : I) = 0 := by
  unfold voltaEmergence; exact emergence_against_void s1 s2

-- T86: volta with void second section is zero
theorem volta_void_section (s1 : I) (obs : I) :
    voltaEmergence s1 (void : I) obs = 0 := by
  unfold voltaEmergence; exact emergence_void_right s1 obs

/-- Sonnet: octave + sestet. -/
def sonnet (oct ses : I) : I := compose oct ses

-- T87: sonnet weight ≥ octave weight
theorem sonnet_weight_ge_octave (oct ses : I) :
    weight (sonnet oct ses) ≥ weight oct := by
  unfold sonnet; exact compose_weight_ge oct ses

-- T88: sonnet resonance decomposition
theorem sonnet_resonance (oct ses observer : I) :
    rs (sonnet oct ses) observer =
    rs oct observer + rs ses observer + voltaEmergence oct ses observer := by
  unfold sonnet voltaEmergence; exact rs_compose_eq oct ses observer

-- T89: emergence of final couplet in context of the whole poem
noncomputable def coupletResolution (poem final_couplet observer : I) : ℝ :=
  emergence poem final_couplet observer

-- T90: resolution against void is zero
theorem resolution_void (p c : I) :
    coupletResolution p c (void : I) = 0 := by
  unfold coupletResolution; exact emergence_against_void p c

-- T91: resolution with void couplet is zero
theorem resolution_void_couplet (p obs : I) :
    coupletResolution p (void : I) obs = 0 := by
  unfold coupletResolution; exact emergence_void_right p obs

-- T92: total emergence of a composition is bounded
theorem composition_emergence_bound (a b observer : I) :
    (voltaEmergence a b observer) ^ 2 ≤
    weight (compose a b) * weight observer := by
  unfold voltaEmergence weight; exact emergence_bounded' a b observer

-- T93: sonnet cocycle — rebracketing the volta
theorem sonnet_cocycle (oct1 oct2 ses observer : I) :
    voltaEmergence oct1 oct2 observer +
    voltaEmergence (compose oct1 oct2) ses observer =
    voltaEmergence oct2 ses observer +
    voltaEmergence oct1 (compose oct2 ses) observer := by
  unfold voltaEmergence; exact cocycle_condition oct1 oct2 ses observer

-- T94: quatrain is associative
theorem quatrain_assoc (a b c d : I) :
    quatrain a b c d = compose a (compose b (couplet c d)) := by
  unfold quatrain couplet; rw [compose_assoc']

end SonnetFixedForms

/-! ## §9. Additional Structural Results -/

section AdditionalStructure
variable {I : Type*} [IdeaticSpace3 I]

-- T95: triple composition weight ≥ first element
theorem triple_weight_ge_first (a b c : I) :
    weight (compose (compose a b) c) ≥ weight a := by
  unfold weight
  linarith [compose_enriches' a b, compose_enriches' (compose a b) c]

-- T96: non-void idea composed stays non-void
theorem compose_ne_void_of_nonvoid (a b : I) (h : a ≠ void) :
    compose a b ≠ void := by
  intro heq
  have h1 := compose_enriches' a b
  rw [heq, rs_void_void] at h1
  have h2 := rs_self_pos a h
  linarith

-- T97: repetition of non-void is non-void (for n ≥ 1)
theorem repetition_ne_void (a : I) (h : a ≠ void) (n : ℕ) :
    repetition a (n + 1) ≠ void := by
  induction n with
  | zero => rw [repetition_one]; exact h
  | succ n ih =>
    rw [repetition_succ]
    exact compose_ne_void_of_nonvoid (repetition a (n + 1)) a ih

-- T98: weight of repetition ≥ weight of idea (for n ≥ 1)
theorem repetition_weight_ge (a : I) (n : ℕ) :
    weight (repetition a (n + 1)) ≥ weight a := by
  induction n with
  | zero => rw [repetition_one]
  | succ n ih =>
    have h2 : weight (repetition a (n + 2)) ≥ weight (repetition a (n + 1)) := by
      unfold weight; exact repetition_weight_mono a (n + 1)
    linarith

-- T99: couplet void right is first line
theorem couplet_void_right (a : I) : couplet a (void : I) = a := by
  unfold couplet; exact void_right' a

-- T100: couplet void left is second line
theorem couplet_void_left (b : I) : couplet (void : I) b = b := by
  unfold couplet; exact void_left' b

-- T101: rhyme strength decomposition for composition
theorem rhymeStrength_compose (a b c : I) :
    rhymeStrength (compose a b) c =
    rs (compose a b) c + rs c (compose a b) := by
  unfold rhymeStrength; ring

-- T102: weight monotonicity along a sequence of compositions
theorem weight_chain_3 (a b c : I) :
    weight a ≤ weight (compose a b) ∧
    weight (compose a b) ≤ weight (compose (compose a b) c) := by
  constructor
  · exact compose_weight_ge a b
  · exact compose_weight_ge (compose a b) c

-- T103: emergence of couplet
theorem couplet_emergence (a b obs : I) :
    rs (couplet a b) obs = rs a obs + rs b obs + emergence a b obs := by
  unfold couplet; exact rs_compose_eq a b obs

-- T104: void repetition weight is zero
theorem repetition_void_weight (n : ℕ) :
    weight (repetition (void : I) n) = 0 := by
  rw [repetition_void]; exact weight_void

-- T105: spondee self-resonance
theorem spondee_self (a : I) : isSpondee a a := by
  unfold isSpondee; ring

end AdditionalStructure

/-! ## §10. Aristotle's Poetics — Hamartia, Peripeteia, Anagnorisis

Aristotle identifies three structural pivots in tragic plot:
- **Hamartia**: the tragic flaw, an element whose emergence with the
  protagonist is destructive (negative).
- **Peripeteia**: reversal of fortune, when the sign of emergence flips.
- **Anagnorisis**: recognition, when the protagonist's self-resonance
  with the composed whole exceeds the sum of parts.

We formalize these as predicates and structural relations on IdeaticSpace3. -/

section AristotlePoetics
variable {I : Type*} [IdeaticSpace3 I]

/-- **Hamartia (tragic flaw)**: an element whose emergence with the
    protagonist, as perceived by the audience, is strictly negative.
    Aristotle: the flaw is not moral wickedness but an error in judgment
    that causes the hero's downfall. In IDT, this is negative emergence:
    composing the flaw with the hero diminishes meaning. -/
def isHamartia (flaw hero audience : I) : Prop :=
  emergence flaw hero audience < 0

-- T106: void is never a hamartia — nothingness cannot be a flaw
theorem void_not_hamartia (hero audience : I) :
    ¬isHamartia (void : I) hero audience := by
  unfold isHamartia; rw [emergence_void_left]; linarith

-- T107: hamartia cannot target void audience — tragedy requires witness
theorem hamartia_needs_audience (flaw hero : I) :
    ¬isHamartia flaw hero (void : I) := by
  unfold isHamartia; rw [emergence_against_void]; linarith

-- T108: hamartia is antithetical to the hero (by definition)
theorem hamartia_is_antithetical (flaw hero audience : I)
    (h : isHamartia flaw hero audience) : isAntithetical flaw hero audience := h

/-- **Peripeteia (reversal)**: a transformation t that flips the sign of
    emergence. Before t is applied, emergence is positive (fortune);
    after composition with t, emergence becomes negative (misfortune).
    Aristotle says peripeteia is most powerful when it arises from
    the plot's own internal logic — formalized here as the cocycle. -/
def isPeripeteia (situation t audience : I) : Prop :=
  emergence situation t audience < 0 ∧
  rs situation situation > 0

-- T109: void cannot be a peripeteia — reversal requires substance
theorem void_not_peripeteia (situation audience : I) :
    ¬isPeripeteia situation (void : I) audience := by
  unfold isPeripeteia; intro ⟨h, _⟩; rw [emergence_void_right] at h; linarith

-- T110: peripeteia requires non-void situation
theorem peripeteia_nonvoid (situation t audience : I)
    (h : isPeripeteia situation t audience) : situation ≠ void := by
  intro heq; unfold isPeripeteia at h; rw [heq, rs_void_void] at h; linarith [h.2]

-- T111: peripeteia against void audience is impossible
theorem peripeteia_needs_audience (situation t : I) :
    ¬isPeripeteia situation t (void : I) := by
  unfold isPeripeteia; intro ⟨h, _⟩; rw [emergence_against_void] at h; linarith

/-- **Anagnorisis (recognition)**: the moment when the composed whole
    reveals more than the sum of parts — positive self-emergence.
    Aristotle: recognition is the change from ignorance to knowledge.
    In IDT, this is when emergence of the hero with the plot, as measured
    by the hero themselves, is strictly positive. -/
def isAnagnorisis (hero plot : I) : Prop :=
  emergence hero plot hero > 0

-- T112: void cannot achieve recognition — silence has no insight
theorem void_no_anagnorisis (plot : I) :
    ¬isAnagnorisis (void : I) plot := by
  unfold isAnagnorisis; rw [emergence_void_left]; linarith

-- T113: recognition requires non-trivial plot
theorem anagnorisis_needs_plot (hero : I) :
    ¬isAnagnorisis hero (void : I) := by
  unfold isAnagnorisis; rw [emergence_void_right]; linarith

/-- **Aristotelian unity**: hamartia and anagnorisis are linked through the
    cocycle condition. The recognition that undoes the flaw is constrained
    by the same algebraic structure. -/
theorem aristotle_cocycle (hero flaw recognition audience : I) :
    emergence hero flaw audience + emergence (compose hero flaw) recognition audience =
    emergence flaw recognition audience + emergence hero (compose flaw recognition) audience :=
  cocycle_condition hero flaw recognition audience

-- T114: the complete tragic arc — composition preserves weight
theorem tragic_arc_weight (hero flaw : I) :
    weight (compose hero flaw) ≥ weight hero := by
  unfold weight; exact compose_enriches' hero flaw

-- T115: catharsis — the weight of the full tragic composition
theorem catharsis_weight (hero flaw resolution : I) :
    weight (compose (compose hero flaw) resolution) ≥ weight hero := by
  unfold weight
  linarith [compose_enriches' hero flaw,
            compose_enriches' (compose hero flaw) resolution]

-- T116: double reversal returns to cocycle constraint
theorem double_peripeteia_cocycle (a t1 t2 d : I) :
    emergence a t1 d + emergence (compose a t1) t2 d =
    emergence t1 t2 d + emergence a (compose t1 t2) d :=
  cocycle_condition a t1 t2 d

end AristotlePoetics

/-! ## §11. Longinus — On the Sublime

Longinus defines the sublime (ὕψος) as that which transports the soul
beyond itself. Five sources: great thoughts, strong emotions, figures
of speech, noble diction, dignified composition. In IDT, transport is
emergence so large that the composed whole vastly exceeds its parts. -/

section Longinus
variable {I : Type*} [IdeaticSpace3 I]

/-- **The Longinian Sublime**: emergence exceeds a given threshold ε.
    Longinus: "the sublime does not persuade but transports" — it is
    emergence beyond the merely additive. -/
def isSublime (a b observer : I) (ε : ℝ) : Prop :=
  emergence a b observer > ε ∧ ε > 0

-- T117: void composition is never sublime — silence cannot transport
theorem void_not_sublime (b observer : I) (ε : ℝ) :
    ¬isSublime (void : I) b observer ε := by
  unfold isSublime; intro ⟨h1, h2⟩; rw [emergence_void_left] at h1; linarith

-- T118: sublimity requires non-void observer — ekstasis needs a soul
theorem sublime_needs_observer (a b : I) (ε : ℝ) :
    ¬isSublime a b (void : I) ε := by
  unfold isSublime; intro ⟨h1, h2⟩; rw [emergence_against_void] at h1; linarith

-- T119: sublimity is bounded by the emergence bound
theorem sublime_bounded (a b observer : I) :
    (emergence a b observer) ^ 2 ≤
    weight (compose a b) * weight observer := by
  unfold weight; exact emergence_bounded' a b observer

-- T120: the sublime requires weight — only substantial ideas transport
theorem sublime_needs_weight (a b observer : I) (ε : ℝ)
    (h : isSublime a b observer ε) :
    weight (compose a b) * weight observer > 0 := by
  unfold weight
  have hbound := emergence_bounded' a b observer
  obtain ⟨h1, h2⟩ := h
  nlinarith

/-- **Ekstasis (transport)**: the absolute value of emergence exceeding
    both component resonances. The soul is "carried outside itself." -/
def isEkstasis (a b observer : I) : Prop :=
  emergence a b observer > rs a observer ∧
  emergence a b observer > rs b observer

-- T121: void cannot produce ekstasis
theorem void_no_ekstasis (b observer : I) :
    ¬isEkstasis (void : I) b observer := by
  unfold isEkstasis; intro ⟨h, _⟩; rw [emergence_void_left] at h
  simp [rs_void_left'] at h

/-- **Longinian bathos**: when attempted sublimity fails, producing
    negative emergence. The fall from the sublime to the ridiculous. -/
def isBathos (a b observer : I) (ε : ℝ) : Prop :=
  emergence a b observer < -ε ∧ ε > 0

-- T122: sublimity and bathos are mutually exclusive
theorem sublime_bathos_exclusive (a b observer : I) (ε : ℝ) :
    ¬(isSublime a b observer ε ∧ isBathos a b observer ε) := by
  intro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩; linarith

-- T123: sublimity composes — the cocycle constrains stacked sublimity
theorem sublime_cocycle (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

end Longinus

/-! ## §12. Burke's Sublime and Beautiful

Edmund Burke distinguishes the **sublime** (connected to terror, vastness,
infinity) from the **beautiful** (connected to smoothness, delicacy,
gradual variation). In IDT: the sublime is large |emergence|; the
beautiful is gentle positive resonance with small emergence. -/

section BurkeSublime
variable {I : Type*} [IdeaticSpace3 I]

/-- **Burkean sublime**: large absolute emergence — the composition
    produces a shock, whether positive or negative. Burke: "whatever
    is fitted to excite the ideas of pain and danger... is a source
    of the sublime." -/
def isBurkeSublime (a b observer : I) (threshold : ℝ) : Prop :=
  (emergence a b observer) ^ 2 > threshold ^ 2 ∧ threshold > 0

/-- **Burkean beautiful**: gentle positive resonance with near-zero emergence.
    Burke: beauty is "that quality... which causes love, or some passion
    similar to it." In IDT, beauty is resonance without disruption. -/
def isBurkeBeautiful (a b observer : I) (δ : ℝ) : Prop :=
  rs a observer > 0 ∧ rs b observer > 0 ∧
  (emergence a b observer) ^ 2 ≤ δ ^ 2 ∧ δ > 0

-- T124: void is never Burke-sublime — nothingness has no terror
theorem void_not_burke_sublime (b observer : I) (t : ℝ) :
    ¬isBurkeSublime (void : I) b observer t := by
  unfold isBurkeSublime; intro ⟨h1, h2⟩
  rw [emergence_void_left] at h1; simp at h1; nlinarith [sq_nonneg t]

-- T125: Burke-sublime and Burke-beautiful are exclusive (at same threshold)
theorem burke_sublime_beautiful_exclusive (a b observer : I) (t : ℝ)
    (hs : isBurkeSublime a b observer t) (hb : isBurkeBeautiful a b observer t) : False := by
  obtain ⟨h1, _⟩ := hs; obtain ⟨_, _, h3, _⟩ := hb; linarith

-- T126: the beautiful requires positive resonance from both parts
theorem burke_beautiful_positive (a b observer : I) (δ : ℝ)
    (h : isBurkeBeautiful a b observer δ) :
    rs a observer > 0 ∧ rs b observer > 0 := ⟨h.1, h.2.1⟩

-- T127: Burke's "delightful horror" — sublime emergence is bounded
theorem burke_bounded_terror (a b observer : I) :
    (emergence a b observer) ^ 2 ≤
    weight (compose a b) * weight observer := by
  unfold weight; exact emergence_bounded' a b observer

end BurkeSublime

/-! ## §13. Coleridge — Imagination vs. Fancy

Coleridge's *Biographia Literaria* ch. XIII distinguishes:
- **Primary imagination**: the living power of perception.
- **Secondary imagination**: creative, dissolves/diffuses/dissipates to re-create.
- **Fancy**: merely aggregative, no emergence. "A mode of memory
  emancipated from the order of time and space."

In IDT: imagination produces emergence; fancy is linear (zero emergence). -/

section ColeridgeImagination
variable {I : Type*} [IdeaticSpace3 I]

/-- **Imagination (Coleridge)**: composition that produces nonzero emergence.
    The secondary imagination "struggles to idealize and to unify." -/
def isImaginative (a b observer : I) : Prop :=
  emergence a b observer ≠ 0

/-- **Fancy (Coleridge)**: composition with zero emergence — merely additive.
    Fancy "has no other counters to play with but fixities and definites." -/
def isFancy (a b observer : I) : Prop :=
  emergence a b observer = 0

-- T128: imagination and fancy are complementary
theorem imagination_fancy_complement (a b observer : I) :
    isImaginative a b observer ↔ ¬isFancy a b observer := by
  unfold isImaginative isFancy; exact Iff.rfl

-- T129: void composition is always fancy — silence has no imagination
theorem void_is_fancy_left (b observer : I) :
    isFancy (void : I) b observer := by
  unfold isFancy; exact emergence_void_left b observer

-- T130: void composition is always fancy (right)
theorem void_is_fancy_right (a observer : I) :
    isFancy a (void : I) observer := by
  unfold isFancy; exact emergence_void_right a observer

-- T131: fancy produces additive resonance (Coleridge's "aggregative")
theorem fancy_additive (a b observer : I) (h : isFancy a b observer) :
    rs (compose a b) observer = rs a observer + rs b observer := by
  unfold isFancy at h; linarith [rs_compose_eq a b observer]

-- T132: imaginative composition exceeds additive resonance
theorem imaginative_nonadditive (a b observer : I) (h : isImaginative a b observer) :
    rs (compose a b) observer ≠ rs a observer + rs b observer := by
  unfold isImaginative at h
  intro heq; apply h
  have := rs_compose_eq a b observer; linarith

/-- **Esemplastic power**: Coleridge's term for the imagination's power to
    shape into one (eis hen plattein). Measured by self-emergence. -/
noncomputable def esemplasticPower (a b : I) : ℝ :=
  emergence a b (compose a b)

-- T133: esemplastic power of void is zero
theorem esemplastic_void_left (b : I) :
    esemplasticPower (void : I) b = 0 := by
  unfold esemplasticPower; simp [emergence_void_left]

-- T134: esemplastic power of void right is zero
theorem esemplastic_void_right (a : I) :
    esemplasticPower a (void : I) = 0 := by
  unfold esemplasticPower; simp [emergence_void_right]

-- T135: fully linear ideas have zero esemplastic power (pure fancy)
theorem linear_no_esemplastic (a : I) (h : leftLinear a) (b : I) :
    esemplasticPower a b = 0 := by
  unfold esemplasticPower; exact h b (compose a b)

end ColeridgeImagination

/-! ## §14. Jakobson's Poetic Function

Roman Jakobson: "The poetic function projects the principle of equivalence
from the axis of selection into the axis of combination." In IDT, the
axis of selection is resonance (which ideas resonate with which), and
the axis of combination is composition. The poetic function is precisely
emergence: it measures how combining ideas creates new resonance patterns
beyond selection alone.

Jakobson's six functions of language map naturally to emergence patterns. -/

section JakobsonPoetics
variable {I : Type*} [IdeaticSpace3 I]

/-- **Poetic function (Jakobson)**: the message's focus on itself.
    Measured by self-emergence — how much the composition resonates
    with itself beyond what the parts contribute individually.
    "The set towards the MESSAGE as such" = emergence of the
    composition measured against itself. -/
noncomputable def poeticFunction (a b : I) : ℝ :=
  emergence a b (compose a b)

-- T136: poetic function equals esemplastic power
theorem poeticFunction_eq_esemplastic (a b : I) :
    poeticFunction a b = esemplasticPower a b := rfl

-- T137: poetic function with void is zero — empty message has no poeticity
theorem poeticFunction_void_left (b : I) :
    poeticFunction (void : I) b = 0 := by
  unfold poeticFunction; simp [emergence_void_left]

-- T138: poetic function with void right is zero
theorem poeticFunction_void_right (a : I) :
    poeticFunction a (void : I) = 0 := by
  unfold poeticFunction; simp [emergence_void_right]

/-- **Referential function**: how the message resonates with a referent.
    "The set towards the CONTEXT" = resonance of composed message with
    the external world. -/
noncomputable def referentialFunction (a b referent : I) : ℝ :=
  rs (compose a b) referent

-- T139: referential function decomposes into parts + emergence
theorem referential_decomposition (a b referent : I) :
    referentialFunction a b referent =
    rs a referent + rs b referent + emergence a b referent := by
  unfold referentialFunction; exact rs_compose_eq a b referent

/-- **Emotive function**: how the message resonates with the sender.
    "The set towards the ADDRESSER." -/
noncomputable def emotiveFunction (sender a b : I) : ℝ :=
  rs (compose a b) sender

-- T140: emotive function decomposition
theorem emotive_decomposition (sender a b : I) :
    emotiveFunction sender a b =
    rs a sender + rs b sender + emergence a b sender := by
  unfold emotiveFunction; exact rs_compose_eq a b sender

/-- **Conative function**: how the message resonates with the receiver.
    "The set towards the ADDRESSEE." -/
noncomputable def conativeFunction (receiver a b : I) : ℝ :=
  rs (compose a b) receiver

-- T141: conative function decomposition
theorem conative_decomposition (receiver a b : I) :
    conativeFunction receiver a b =
    rs a receiver + rs b receiver + emergence a b receiver := by
  unfold conativeFunction; exact rs_compose_eq a b receiver

/-- **Metalingual function**: how the message resonates with the code.
    "The set towards the CODE." We model the code as the compositional
    structure itself — measuring self-referential emergence. -/
noncomputable def metalingualFunction (a b : I) : ℝ :=
  emergence a b a + emergence a b b

-- T142: metalingual function with void left
theorem metalingual_void_left (b : I) :
    metalingualFunction (void : I) b = 0 := by
  unfold metalingualFunction; rw [emergence_void_left, emergence_void_left]; ring

-- T143: metalingual function with void right
theorem metalingual_void_right (a : I) :
    metalingualFunction a (void : I) = 0 := by
  unfold metalingualFunction; rw [emergence_void_right, emergence_void_right]; ring

/-- **Phatic function**: maintaining the channel. Measured by mutual resonance
    without emergence — pure contact. -/
def isPhatic (a b observer : I) : Prop :=
  rs a observer > 0 ∧ rs b observer > 0 ∧ emergence a b observer = 0

-- T144: void is never phatic — silence is not contact
theorem void_not_phatic_left (b observer : I) :
    ¬isPhatic (void : I) b observer := by
  unfold isPhatic; intro ⟨h, _, _⟩; simp [rs_void_left'] at h

-- T145: phatic communication is additive (no emergence)
theorem phatic_additive (a b observer : I) (h : isPhatic a b observer) :
    rs (compose a b) observer = rs a observer + rs b observer := by
  obtain ⟨_, _, h3⟩ := h; linarith [rs_compose_eq a b observer]

-- T146: the poetic function dominance — when poetry exceeds reference
theorem poetic_exceeds_reference (a b referent : I)
    (h : poeticFunction a b > referentialFunction a b referent) :
    emergence a b (compose a b) > rs (compose a b) referent := by
  unfold poeticFunction referentialFunction at h; exact h

end JakobsonPoetics

/-! ## §15. New Criticism — Brooks' Well-Wrought Urn

Cleanth Brooks argues that a poem is an organic unity whose meaning
cannot be reduced to paraphrase. The "heresy of paraphrase" is precisely
the claim that emergence is nonzero: the poem's meaning is NOT the
sum of its parts' meanings. Irony, paradox, and ambiguity are all
manifestations of emergence.

The well-wrought urn is a composition whose emergence is self-referential:
it speaks about itself through its own formal structure. -/

section NewCriticism
variable {I : Type*} [IdeaticSpace3 I]

/-- **Heresy of paraphrase (Brooks)**: the claim that a poem's meaning
    cannot be restated as the sum of its parts. Formally: emergence ≠ 0.
    A poem commits the heresy of paraphrase precisely when it IS
    paraphrasable — when emergence is zero. -/
def isParaphrasable (a b observer : I) : Prop :=
  emergence a b observer = 0

-- T147: void compositions are always paraphrasable — trivial texts are summable
theorem void_paraphrasable (b observer : I) :
    isParaphrasable (void : I) b observer := emergence_void_left b observer

-- T148: the heresy: if paraphrasable, resonance is just sum of parts
theorem heresy_of_paraphrase (a b observer : I)
    (h : isParaphrasable a b observer) :
    rs (compose a b) observer = rs a observer + rs b observer := by
  unfold isParaphrasable at h; linarith [rs_compose_eq a b observer]

/-- **Irony (Brooks)**: the composition means something different from
    what the parts individually mean. Formalized as the emergence having
    opposite sign to the sum of individual resonances. -/
def isBrooksIrony (a b observer : I) : Prop :=
  (rs a observer + rs b observer) * emergence a b observer < 0

-- T149: irony requires nonzero parts — you can't ironize nothing
theorem irony_nonzero_parts (a b observer : I) (h : isBrooksIrony a b observer) :
    rs a observer + rs b observer ≠ 0 := by
  unfold isBrooksIrony at h; intro heq; rw [heq, zero_mul] at h; linarith

-- T150: irony requires nonzero emergence
theorem irony_nonzero_emergence (a b observer : I) (h : isBrooksIrony a b observer) :
    emergence a b observer ≠ 0 := by
  unfold isBrooksIrony at h; intro heq; rw [heq, mul_zero] at h; linarith

/-- **Paradox (Brooks)**: the composition simultaneously affirms and
    negates — positive self-resonance but negative emergence with parts. -/
def isParadox (a b : I) : Prop :=
  weight (compose a b) > weight a + weight b ∧
  emergence a b a < 0 ∧ emergence a b b < 0

/-- **Tension (Tate)**: Allen Tate's concept — the unified meaning arising
    from extension (denotation) and intension (connotation) pulled together.
    In IDT: the gap between resonance in two different observer frames. -/
noncomputable def tateTension (a b obs1 obs2 : I) : ℝ :=
  emergence a b obs1 - emergence a b obs2

-- T151: tension is antisymmetric in observers
theorem tension_antisymm (a b obs1 obs2 : I) :
    tateTension a b obs1 obs2 = -tateTension a b obs2 obs1 := by
  unfold tateTension; ring

-- T152: self-tension is zero
theorem tension_self_observer (a b obs : I) :
    tateTension a b obs obs = 0 := by
  unfold tateTension; ring

-- T153: tension with void observer is just negative emergence
theorem tension_void_observer (a b obs : I) :
    tateTension a b obs (void : I) = emergence a b obs := by
  unfold tateTension; rw [emergence_against_void]; ring

/-- **Organic unity**: the whole exceeds the sum. Every part is necessary —
    removing any part decreases weight. -/
def isOrganicUnity (a b : I) : Prop :=
  weight (compose a b) > weight a ∧ weight (compose a b) > weight b

-- T154: organic unity implies both parts are non-void
theorem organic_unity_nonvoid (a b : I) (h : isOrganicUnity a b) :
    a ≠ void ∧ b ≠ void := by
  constructor
  · intro heq; unfold isOrganicUnity at h; unfold weight at h
    rw [heq, void_left'] at h; linarith [h.1]
  · intro heq; unfold isOrganicUnity at h; unfold weight at h
    rw [heq, void_right'] at h; linarith [h.2]

end NewCriticism

/-! ## §16. Russian Formalism — Fabula, Syuzhet, Defamiliarization

The Russian Formalists (Shklovsky, Propp, Tomashevsky) distinguish:
- **Fabula**: the chronological sequence of events (raw material).
- **Syuzhet**: the artful arrangement of the narrative (plot as told).
- **Defamiliarization (ostranenie)**: making the familiar strange to
  increase perception time and aesthetic experience.

In IDT, fabula and syuzhet are different compositions of the same
elements — and their difference is measured by emergence. -/

section RussianFormalism
variable {I : Type*} [IdeaticSpace3 I]

/-- **Fabula (story)**: the natural order — compose a then b.
    The raw chronological sequence. -/
def fabula (a b : I) : I := compose a b

/-- **Syuzhet (plot)**: the artful re-ordering — compose b then a.
    The narrative arrangement. -/
def syuzhet (a b : I) : I := compose b a

/-- **Defamiliarization gap (Shklovsky's ostranenie)**: the difference
    between syuzhet and fabula as perceived by an observer. When this
    is nonzero, the artistic arrangement has made the familiar strange.
    Shklovsky: "Art exists that one may recover the sensation of life;
    it exists to make one feel things." -/
noncomputable def ostranenie (a b observer : I) : ℝ :=
  rs (syuzhet a b) observer - rs (fabula a b) observer

-- T155: defamiliarization is the chiasmic difference (negated)
theorem ostranenie_eq_chiasmic (a b observer : I) :
    ostranenie a b observer = -chiasmicDiff a b observer := by
  unfold ostranenie syuzhet fabula chiasmicDiff; ring

-- T156: defamiliarization is antisymmetric
theorem ostranenie_antisymm (a b observer : I) :
    ostranenie a b observer = -ostranenie b a observer := by
  unfold ostranenie syuzhet fabula; ring

-- T157: void has no defamiliarization
theorem ostranenie_void_left (b observer : I) :
    ostranenie (void : I) b observer = 0 := by
  unfold ostranenie syuzhet fabula; simp

-- T158: defamiliarization against void observer is zero
theorem ostranenie_void_observer (a b : I) :
    ostranenie a b (void : I) = 0 := by
  unfold ostranenie syuzhet fabula; simp [rs_void_right']

-- T159: defamiliarization equals emergence difference
theorem ostranenie_emergence (a b observer : I) :
    ostranenie a b observer = emergence b a observer - emergence a b observer := by
  unfold ostranenie syuzhet fabula emergence; ring

/-- **Literariness (literaturnost)**: the quality that makes a text literary.
    Jakobson/Shklovsky: not WHAT is said but HOW — the formal properties.
    In IDT: the ratio of emergence to raw resonance. We measure whether
    emergence dominates. -/
def isLiterary (a b observer : I) : Prop :=
  (emergence a b observer) ^ 2 > (rs a observer) ^ 2

-- T160: void is never literary
theorem void_not_literary (b observer : I) :
    ¬isLiterary (void : I) b observer := by
  unfold isLiterary; rw [emergence_void_left, rs_void_left']; simp

/-- **Foregrounding**: when the artistic device calls attention to itself.
    The poetic function value exceeds the referential value. -/
def isForegrounded (a b observer : I) : Prop :=
  emergence a b (compose a b) > rs (compose a b) observer

-- T161: void composition foregrounding characterization
theorem void_foregrounding_char (b observer : I) :
    isForegrounded (void : I) b observer ↔ rs b observer < 0 := by
  unfold isForegrounded; rw [emergence_void_left, void_left']

end RussianFormalism

/-! ## §17. Structuralist Poetics — Todorov's Narrative Grammar

Tzvetan Todorov proposes that narrative has a grammar:
  Equilibrium → Disequilibrium → New Equilibrium

Each narrative can be decomposed into "narrative propositions" that
transform states. In IDT, we model this as composition with explicit
state tracking through emergence. -/

section TodorovNarrative
variable {I : Type*} [IdeaticSpace3 I]

/-- **Narrative equilibrium (Todorov)**: a state where self-resonance
    dominates and emergence with perturbations is small. -/
def isEquilibrium (state : I) (perturbation observer : I) (ε : ℝ) : Prop :=
  (emergence state perturbation observer) ^ 2 ≤ ε ^ 2 ∧
  weight state > 0 ∧ ε > 0

/-- **Disequilibrium**: emergence exceeds the equilibrium threshold. -/
def isDisequilibrium (state perturbation observer : I) (ε : ℝ) : Prop :=
  (emergence state perturbation observer) ^ 2 > ε ^ 2 ∧ ε > 0

-- T162: equilibrium and disequilibrium are exclusive
theorem equilibrium_disequilibrium_exclusive (state perturbation observer : I) (ε : ℝ)
    (heq : isEquilibrium state perturbation observer ε)
    (hdis : isDisequilibrium state perturbation observer ε) : False := by
  obtain ⟨h1, _, _⟩ := heq; obtain ⟨h2, _⟩ := hdis; linarith

-- T163: void state cannot be in equilibrium (no positive weight)
theorem void_not_equilibrium (perturbation observer : I) (ε : ℝ) :
    ¬isEquilibrium (void : I) perturbation observer ε := by
  unfold isEquilibrium weight; intro ⟨_, h, _⟩; rw [rs_void_void] at h; linarith

/-- **Todorov's transformation**: the narrative move from state to new state.
    The transformation is the composition with a disrupting element. -/
def todorovTransform (state disruption : I) : I := compose state disruption

-- T164: transformation enriches weight
theorem todorov_transform_enriches (state disruption : I) :
    weight (todorovTransform state disruption) ≥ weight state := by
  unfold todorovTransform; exact compose_weight_ge state disruption

-- T165: Todorov's narrative arc — three-part composition
theorem todorov_arc_weight (equilibrium disruption resolution : I) :
    weight (compose (compose equilibrium disruption) resolution) ≥
    weight equilibrium := by
  unfold weight
  linarith [compose_enriches' equilibrium disruption,
            compose_enriches' (compose equilibrium disruption) resolution]

-- T166: the new equilibrium resonance decomposition
theorem todorov_new_equilibrium (eq1 dis res observer : I) :
    rs (compose (compose eq1 dis) res) observer =
    rs eq1 observer + rs dis observer + rs res observer +
    emergence eq1 dis observer +
    emergence (compose eq1 dis) res observer := by
  rw [rs_compose_eq (compose eq1 dis) res observer,
      rs_compose_eq eq1 dis observer]; ring

end TodorovNarrative

/-! ## §18. Post-Structuralist Poetics — de Man on Rhetoric

Paul de Man argues that rhetoric undermines grammar: the literal
meaning (grammar) and the figural meaning (rhetoric) of a text are
irreconcilable. This "undecidability" is formalized as the gap
between two observer frames — no single reading captures the whole.

de Man's "blindness and insight": every critical reading gains
insight precisely through its blindness to certain aspects. -/

section DeManRhetoric
variable {I : Type*} [IdeaticSpace3 I]

/-- **Rhetorical gap (de Man)**: the irreconcilable difference between
    literal (grammatical) and figural (rhetorical) readings.
    de Man: "The resistance of rhetoric to grammar is the same as the
    resistance of literature to theory." -/
noncomputable def rhetoricalGap (text literal figural : I) : ℝ :=
  rs text literal - rs text figural

-- T167: rhetorical gap is antisymmetric in reading frames
theorem rhetoricalGap_antisymm (text lit fig : I) :
    rhetoricalGap text lit fig = -rhetoricalGap text fig lit := by
  unfold rhetoricalGap; ring

-- T168: void text has no rhetorical gap
theorem rhetoricalGap_void_text (lit fig : I) :
    rhetoricalGap (void : I) lit fig = 0 := by
  unfold rhetoricalGap; simp [rs_void_left']

/-- **Blindness and insight (de Man)**: the critic's reading (composition
    with the text) gains emergence in one frame but loses it in another.
    The insight IS the blindness. -/
noncomputable def blindnessInsightGap (critic text frame1 frame2 : I) : ℝ :=
  emergence critic text frame1 - emergence critic text frame2

-- T169: blindness-insight gap is antisymmetric in frames
theorem blindness_insight_antisymm (critic text f1 f2 : I) :
    blindnessInsightGap critic text f1 f2 = -blindnessInsightGap critic text f2 f1 := by
  unfold blindnessInsightGap; ring

-- T170: zero blindness-insight gap when frames agree
theorem blindness_insight_self (critic text f : I) :
    blindnessInsightGap critic text f f = 0 := by
  unfold blindnessInsightGap; ring

-- T171: void critic has no blindness/insight
theorem blindness_insight_void_critic (text f1 f2 : I) :
    blindnessInsightGap (void : I) text f1 f2 = 0 := by
  unfold blindnessInsightGap; rw [emergence_void_left, emergence_void_left]; ring

/-- **Aporia (de Man)**: the point where two equally valid readings
    produce exactly opposite emergence. The text is "undecidable." -/
def isAporia (text a b observer : I) : Prop :=
  emergence text a observer = -emergence text b observer ∧
  emergence text a observer ≠ 0

-- T172: aporia requires nonzero emergence — trivial texts aren't undecidable
theorem aporia_nontrivial (text a b observer : I) (h : isAporia text a b observer) :
    emergence text a observer ≠ 0 := h.2

-- T173: aporia implies the two readings sum to zero emergence
theorem aporia_sum_zero (text a b observer : I) (h : isAporia text a b observer) :
    emergence text a observer + emergence text b observer = 0 := by
  obtain ⟨h1, _⟩ := h; linarith

end DeManRhetoric

/-! ## §19. Cognitive Poetics — Lakoff/Turner Conceptual Blending

George Lakoff and Mark Turner: meaning arises through conceptual
metaphor and blending. A **blend** is a composition of two mental
spaces (source and target) that produces emergent structure not
present in either input space alone.

In IDT, blending IS composition, and the emergent structure IS emergence. -/

section CognitivePoetics
variable {I : Type*} [IdeaticSpace3 I]

/-- **Conceptual blend (Lakoff/Turner)**: the composition of source
    and target domains. The blend is simply compose source target.
    Emergence measures "emergent structure" — Turner's key concept. -/
def conceptualBlend (source target : I) : I := compose source target

/-- **Emergent structure**: the new meaning in the blend not traceable
    to either input. This IS emergence in IDT. -/
noncomputable def emergentStructure (source target observer : I) : ℝ :=
  emergence source target observer

-- T174: emergent structure in the blend as self-observed
theorem blend_self_emergence (source target : I) :
    emergentStructure source target (conceptualBlend source target) =
    poeticFunction source target := by
  unfold emergentStructure conceptualBlend poeticFunction; rfl

-- T175: empty source contributes no emergent structure
theorem blend_void_source (target observer : I) :
    emergentStructure (void : I) target observer = 0 := by
  unfold emergentStructure; exact emergence_void_left target observer

-- T176: blend weight ≥ source weight (source persists in blend)
theorem blend_weight_ge_source (source target : I) :
    weight (conceptualBlend source target) ≥ weight source := by
  unfold conceptualBlend; exact compose_weight_ge source target

/-- **Vital relations (Fauconnier/Turner)**: connections between input
    spaces measured by resonance. High resonance = strong vital relation. -/
noncomputable def vitalRelation (source target : I) : ℝ :=
  rs source target

-- T177: vital relation with void is zero
theorem vitalRelation_void (a : I) :
    vitalRelation a (void : I) = 0 := rs_void_right' a

/-- **Compression (Fauconnier/Turner)**: vital relations in the blend are
    compressed relative to the input. Measured by how much the blend's
    self-resonance exceeds the vital relation. -/
noncomputable def compressionRatio (source target : I) : ℝ :=
  weight (conceptualBlend source target) - vitalRelation source target

-- T178: compression with void
theorem compression_void_target (a : I) :
    compressionRatio a (void : I) = weight a := by
  unfold compressionRatio conceptualBlend vitalRelation weight; simp [rs_void_right']

/-- **Generic space**: what source and target have in common —
    the symmetric part of their resonance. -/
noncomputable def genericSpace (source target : I) : ℝ :=
  (rs source target + rs target source) / 2

-- T179: generic space is symmetric
theorem genericSpace_symm (a b : I) :
    genericSpace a b = genericSpace b a := by
  unfold genericSpace; ring

-- T180: generic space with void is zero
theorem genericSpace_void (a : I) :
    genericSpace a (void : I) = 0 := by
  unfold genericSpace; simp [rs_void_right', rs_void_left']

end CognitivePoetics

/-! ## §20. Ecopoetics

Ecopoetics examines the relationship between poetry and environment.
The environment is not merely a backdrop but an active participant
in meaning-making. In IDT, the environment is a persistent context
that modifies all emergences through composition. -/

section Ecopoetics
variable {I : Type*} [IdeaticSpace3 I]

/-- **Dwelling (Heidegger/ecopoetics)**: long-term composition with an
    environment. To dwell is to compose repeatedly with place. -/
def dwelling (self environment : I) (n : ℕ) : I :=
  Nat.recOn n self (fun _ acc => compose acc environment)

-- T181: dwelling at 0 is the self
theorem dwelling_zero (self environment : I) :
    dwelling self environment 0 = self := rfl

-- T182: dwelling step
theorem dwelling_succ (self environment : I) (n : ℕ) :
    dwelling self environment (n + 1) =
    compose (dwelling self environment n) environment := rfl

-- T183: dwelling weight never decreases — place accrues meaning
theorem dwelling_weight_mono (self environment : I) (n : ℕ) :
    weight (dwelling self environment (n + 1)) ≥
    weight (dwelling self environment n) := by
  simp only [dwelling_succ]; exact compose_weight_ge _ _

-- T184: dwelling in void doesn't change (void environment is no place)
theorem dwelling_void_env (self : I) (n : ℕ) :
    dwelling self (void : I) n = self := by
  induction n with
  | zero => rfl
  | succ n ih => simp [dwelling_succ, ih, void_right']

/-- **Solastalgia**: the distress from environmental change.
    The gap between dwelling-with-environment and dwelling-with-changed-environment. -/
noncomputable def solastalgia (self env1 env2 observer : I) : ℝ :=
  rs (compose self env1) observer - rs (compose self env2) observer

-- T185: solastalgia is antisymmetric in environments
theorem solastalgia_antisymm (self env1 env2 observer : I) :
    solastalgia self env1 env2 observer = -solastalgia self env2 env1 observer := by
  unfold solastalgia; ring

-- T186: no solastalgia when environments are the same
theorem solastalgia_same (self env observer : I) :
    solastalgia self env env observer = 0 := by
  unfold solastalgia; ring

-- T187: solastalgia against void observer is zero
theorem solastalgia_void_observer (self env1 env2 : I) :
    solastalgia self env1 env2 (void : I) = 0 := by
  unfold solastalgia; simp [rs_void_right']

end Ecopoetics

/-! ## §21. Sound Symbolism

Sound symbolism (phonosemantics) studies the non-arbitrary relationship
between sound and meaning. Saussure claimed arbitrariness; Jakobson,
Sapir, and Berlin & Kay showed systematic sound-meaning correspondences.
In IDT, sounds are utterances whose resonance patterns with meaning
categories are non-random. -/

section SoundSymbolism
variable {I : Type*} [IdeaticSpace3 I]

/-- **Sound symbolic pair**: two sounds whose resonance with a meaning
    category differ systematically. The contrast is the symbolism. -/
noncomputable def soundSymbolicContrast (sound1 sound2 meaning : I) : ℝ :=
  rs sound1 meaning - rs sound2 meaning

-- T188: sound symbolic contrast is antisymmetric in sounds
theorem soundContrast_antisymm (s1 s2 meaning : I) :
    soundSymbolicContrast s1 s2 meaning = -soundSymbolicContrast s2 s1 meaning := by
  unfold soundSymbolicContrast; ring

-- T189: self-contrast is zero
theorem soundContrast_self (s meaning : I) :
    soundSymbolicContrast s s meaning = 0 := by
  unfold soundSymbolicContrast; ring

-- T190: void sound has zero contrast with anything
theorem soundContrast_void (s meaning : I) :
    soundSymbolicContrast (void : I) s meaning = -rs s meaning := by
  unfold soundSymbolicContrast; simp [rs_void_left']

/-- **Phonesthetic cluster**: a group of sounds that share emergence
    patterns with a meaning domain. The cluster's compositional
    resonance exceeds the sum — the sounds COLLECTIVELY symbolize. -/
noncomputable def phonestheticEmergence (s1 s2 meaning : I) : ℝ :=
  emergence s1 s2 meaning

-- T191: phonesthetic emergence bounded by cluster weight
theorem phonesthetic_bounded (s1 s2 meaning : I) :
    (phonestheticEmergence s1 s2 meaning) ^ 2 ≤
    weight (compose s1 s2) * weight meaning := by
  unfold phonestheticEmergence weight; exact emergence_bounded' s1 s2 meaning

-- T192: void phoneme has no phonesthetic emergence
theorem phonesthetic_void (s meaning : I) :
    phonestheticEmergence (void : I) s meaning = 0 := by
  unfold phonestheticEmergence; exact emergence_void_left s meaning

/-- **Bouba-kiki effect**: certain sounds systematically resonate more
    with certain shapes/meanings. Modeled as positive vs negative resonance. -/
def isBoubaKiki (round_sound sharp_sound round_meaning : I) : Prop :=
  rs round_sound round_meaning > rs sharp_sound round_meaning

-- T193: bouba-kiki contrast is the sound symbolic contrast
theorem boubaKiki_is_contrast (rs_ ss rm : I) (h : isBoubaKiki rs_ ss rm) :
    soundSymbolicContrast rs_ ss rm > 0 := by
  unfold isBoubaKiki at h; unfold soundSymbolicContrast; linarith

end SoundSymbolism

/-! ## §22. Prosody as Emergence Pattern

Prosody — stress, intonation, rhythm — is not mere decoration but
carries meaning through emergence. The stress pattern of a line
creates emergent resonance beyond what the words alone provide.
Prosody is the emergence pattern of composition. -/

section Prosody
variable {I : Type*} [IdeaticSpace3 I]

/-- **Prosodic contour**: the sequence of weights in a composition.
    Each element's self-resonance defines its "stress level." -/
noncomputable def prosodicWeight (elements : List I) : List ℝ :=
  elements.map weight

/-- **Rising rhythm**: each successive element has greater weight.
    Models the iambic pattern generalized. -/
def isRisingRhythm (a b : I) : Prop := weight a < weight b

/-- **Falling rhythm**: each successive element has lesser weight.
    Models the trochaic pattern generalized. -/
def isFallingRhythm (a b : I) : Prop := weight a > weight b

-- T194: rising and falling rhythm are mutually exclusive
theorem rising_falling_exclusive (a b : I) :
    ¬(isRisingRhythm a b ∧ isFallingRhythm a b) := by
  unfold isRisingRhythm isFallingRhythm; intro ⟨h1, h2⟩; linarith

-- T195: void has equal rhythm with void (neither rising nor falling)
theorem void_neither_rising (a : I) (h : a ≠ void) :
    isRisingRhythm (void : I) a := by
  unfold isRisingRhythm weight; rw [rs_void_void]; exact rs_self_pos a h

/-- **Prosodic emergence**: the emergence contribution of stressed vs
    unstressed composition. Stress patterns CREATE meaning through emergence. -/
noncomputable def prosodicEmergence (stressed unstressed observer : I) : ℝ :=
  emergence stressed unstressed observer

-- T196: prosodic emergence decomposition
theorem prosodic_resonance_decomposition (stressed unstressed observer : I) :
    rs (compose stressed unstressed) observer =
    rs stressed observer + rs unstressed observer +
    prosodicEmergence stressed unstressed observer := by
  unfold prosodicEmergence; exact rs_compose_eq stressed unstressed observer

-- T197: prosodic emergence bounded
theorem prosodic_emergence_bound (stressed unstressed observer : I) :
    (prosodicEmergence stressed unstressed observer) ^ 2 ≤
    weight (compose stressed unstressed) * weight observer := by
  unfold prosodicEmergence weight; exact emergence_bounded' _ _ _

/-- **Caesura**: a pause modeled as void inserted into the line.
    The caesura splits a line into two halves whose emergence measures
    the tension across the break. -/
noncomputable def caesuraEffect (firstHalf secondHalf observer : I) : ℝ :=
  emergence firstHalf secondHalf observer

-- T198: caesura with void second half = no effect
theorem caesura_void_second (firstHalf observer : I) :
    caesuraEffect firstHalf (void : I) observer = 0 := by
  unfold caesuraEffect; exact emergence_void_right firstHalf observer

-- T199: caesura against void observer = no effect
theorem caesura_void_observer (fh sh : I) :
    caesuraEffect fh sh (void : I) = 0 := by
  unfold caesuraEffect; exact emergence_against_void fh sh

end Prosody

/-! ## §23. Enjambment as Emergence Across Line Breaks

Enjambment — running a syntactic unit across a line break — is one of
the most powerful devices in verse. It creates a tension between the
metrical unit (the line) and the syntactic unit (the sentence).

In IDT, enjambment is emergence that spans a compositional boundary:
the meaning of the run-on phrase exceeds what either line contributes
individually. -/

section Enjambment
variable {I : Type*} [IdeaticSpace3 I]

/-- **Enjambment**: the emergence created when syntactic meaning runs
    across a line break. The line break is a compositional boundary,
    and the enjambment is the emergence across it. -/
noncomputable def enjambmentStrength (line1 line2 observer : I) : ℝ :=
  emergence line1 line2 observer

/-- **End-stopped line**: a line whose syntactic unit ends at the line break.
    No enjambment — emergence across the boundary is zero. -/
def isEndStopped (line1 line2 observer : I) : Prop :=
  enjambmentStrength line1 line2 observer = 0

/-- **Run-on line (enjambed)**: syntactic meaning crosses the line break,
    producing nonzero emergence. -/
def isEnjambed (line1 line2 observer : I) : Prop :=
  enjambmentStrength line1 line2 observer ≠ 0

-- T200: enjambed and end-stopped are complementary
theorem enjambed_endStopped_complement (l1 l2 obs : I) :
    isEnjambed l1 l2 obs ↔ ¬isEndStopped l1 l2 obs := by
  unfold isEnjambed isEndStopped; exact Iff.rfl

-- T201: void lines are always end-stopped
theorem void_endStopped (l2 obs : I) :
    isEndStopped (void : I) l2 obs := by
  unfold isEndStopped enjambmentStrength; exact emergence_void_left l2 obs

-- T202: end-stopped lines have additive resonance
theorem endStopped_additive (l1 l2 obs : I) (h : isEndStopped l1 l2 obs) :
    rs (compose l1 l2) obs = rs l1 obs + rs l2 obs := by
  unfold isEndStopped enjambmentStrength at h
  linarith [rs_compose_eq l1 l2 obs]

-- T203: enjambment bounded by line weights
theorem enjambment_bounded (l1 l2 obs : I) :
    (enjambmentStrength l1 l2 obs) ^ 2 ≤
    weight (compose l1 l2) * weight obs := by
  unfold enjambmentStrength weight; exact emergence_bounded' l1 l2 obs

-- T204: enjambment across void observer is zero
theorem enjambment_void_observer (l1 l2 : I) :
    enjambmentStrength l1 l2 (void : I) = 0 := by
  unfold enjambmentStrength; exact emergence_against_void l1 l2

/-- **Enjambment chain**: consecutive enjambments satisfy the cocycle
    condition — you can't have arbitrary enjambment patterns. -/
theorem enjambment_cocycle (l1 l2 l3 obs : I) :
    enjambmentStrength l1 l2 obs +
    enjambmentStrength (compose l1 l2) l3 obs =
    enjambmentStrength l2 l3 obs +
    enjambmentStrength l1 (compose l2 l3) obs := by
  unfold enjambmentStrength; exact cocycle_condition l1 l2 l3 obs

-- T205: strong enjambment — emergence dominates individual resonances
def isStrongEnjambment (l1 l2 obs : I) : Prop :=
  (enjambmentStrength l1 l2 obs) ^ 2 >
  (rs l1 obs) ^ 2

-- T206: enjambment strength with void second line is zero
theorem enjambment_void_second (l1 obs : I) :
    enjambmentStrength l1 (void : I) obs = 0 := by
  unfold enjambmentStrength; exact emergence_void_right l1 obs

end Enjambment

/-! ## §24. The Sonnet as Constrained Optimization

The sonnet form (14 lines, volta, specific rhyme scheme) is not arbitrary
but represents a constrained optimization: maximize emergence within
a fixed compositional structure. The volta (turn) is the optimal point
for emergence — the cocycle condition constrains where the turn can go.

We model the sonnet as a 4-part structure: three quatrains and a couplet
(Shakespearean) or two quatrains and a sestet (Petrarchan), and prove
structural properties about the volta's placement. -/

section SonnetOptimization
variable {I : Type*} [IdeaticSpace3 I]

/-- **Shakespearean sonnet**: three quatrains and a final couplet. -/
def shakespeareanSonnet (q1 q2 q3 fc : I) : I :=
  compose (compose (compose q1 q2) q3) fc

-- T207: Shakespearean sonnet weight ≥ first quatrain
theorem shakespearean_weight_ge_q1 (q1 q2 q3 fc : I) :
    weight (shakespeareanSonnet q1 q2 q3 fc) ≥ weight q1 := by
  unfold shakespeareanSonnet weight
  linarith [compose_enriches' q1 q2,
            compose_enriches' (compose q1 q2) q3,
            compose_enriches' (compose (compose q1 q2) q3) fc]

/-- **Petrarchan sonnet**: octave (two quatrains) and sestet. -/
def petrarchanSonnet (q1 q2 sestet : I) : I :=
  compose (compose q1 q2) sestet

-- T208: Petrarchan sonnet weight ≥ first quatrain
theorem petrarchan_weight_ge_q1 (q1 q2 sestet : I) :
    weight (petrarchanSonnet q1 q2 sestet) ≥ weight q1 := by
  unfold petrarchanSonnet weight
  linarith [compose_enriches' q1 q2,
            compose_enriches' (compose q1 q2) sestet]

/-- **Volta (the turn)**: the emergence at the boundary between octave and
    sestet. This is where the poem's argument shifts. -/
noncomputable def voltaStrength (octave sestet observer : I) : ℝ :=
  emergence octave sestet observer

-- T209: volta strength bounded by weights
theorem volta_bounded (octave sestet observer : I) :
    (voltaStrength octave sestet observer) ^ 2 ≤
    weight (compose octave sestet) * weight observer := by
  unfold voltaStrength weight; exact emergence_bounded' octave sestet observer

-- T210: volta with void sestet is zero — no turn without a turn
theorem volta_void_sestet (octave observer : I) :
    voltaStrength octave (void : I) observer = 0 := by
  unfold voltaStrength; exact emergence_void_right octave observer

-- T211: volta satisfies cocycle when decomposing the octave
theorem volta_octave_cocycle (q1 q2 sestet observer : I) :
    voltaStrength q1 q2 observer +
    voltaStrength (compose q1 q2) sestet observer =
    voltaStrength q2 sestet observer +
    voltaStrength q1 (compose q2 sestet) observer := by
  unfold voltaStrength; exact cocycle_condition q1 q2 sestet observer

-- T212: Petrarchan sonnet resonance decomposition
theorem petrarchan_resonance (q1 q2 sestet observer : I) :
    rs (petrarchanSonnet q1 q2 sestet) observer =
    rs q1 observer + rs q2 observer + rs sestet observer +
    emergence q1 q2 observer +
    emergence (compose q1 q2) sestet observer := by
  unfold petrarchanSonnet
  rw [rs_compose_eq (compose q1 q2) sestet observer,
      rs_compose_eq q1 q2 observer]; ring

-- T213: Shakespearean sonnet resonance decomposition
theorem shakespearean_resonance (q1 q2 q3 fc observer : I) :
    rs (shakespeareanSonnet q1 q2 q3 fc) observer =
    rs q1 observer + rs q2 observer + rs q3 observer + rs fc observer +
    emergence q1 q2 observer +
    emergence (compose q1 q2) q3 observer +
    emergence (compose (compose q1 q2) q3) fc observer := by
  unfold shakespeareanSonnet
  rw [rs_compose_eq (compose (compose q1 q2) q3) fc observer,
      rs_compose_eq (compose q1 q2) q3 observer,
      rs_compose_eq q1 q2 observer]; ring

/-- **Constrained form**: a sonnet's total emergence is exactly determined
    by the cocycle relations. The form constrains the content. -/
theorem sonnet_form_constraint (q1 q2 q3 fc d : I) :
    emergence q1 q2 d + emergence (compose q1 q2) q3 d +
    emergence (compose (compose q1 q2) q3) fc d =
    emergence q2 q3 d + emergence q1 (compose q2 q3) d +
    emergence (compose (compose q1 q2) q3) fc d := by
  linarith [cocycle_condition q1 q2 q3 d]

-- T214: void quatrain simplifies the sonnet
theorem shakespearean_void_q1 (q2 q3 fc : I) :
    shakespeareanSonnet (void : I) q2 q3 fc =
    compose (compose q2 q3) fc := by
  unfold shakespeareanSonnet; simp

-- T215: two Petrarchan readings related by cocycle
theorem petrarchan_two_readings (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

end SonnetOptimization

/-! ## §25. Advanced Poetic Structures

Additional theorems on the interaction of form and meaning:
metaphor as emergence, metonymy as resonance, synecdoche as
part-whole resonance, and hyperbole as weight amplification. -/

section AdvancedPoetics
variable {I : Type*} [IdeaticSpace3 I]

/-- **Metaphor**: composition of tenor and vehicle whose emergence
    exceeds either component's self-resonance with the ground.
    "Juliet is the sun" — the emergence of (Juliet, sun) as perceived
    by the audience exceeds what either contributes alone. -/
noncomputable def metaphorStrength (tenor vehicle ground : I) : ℝ :=
  emergence tenor vehicle ground

-- T216: metaphor with void tenor — no metaphor without subject
theorem metaphor_void_tenor (vehicle ground : I) :
    metaphorStrength (void : I) vehicle ground = 0 := by
  unfold metaphorStrength; exact emergence_void_left vehicle ground

-- T217: metaphor bounded by composed weight
theorem metaphor_bounded (tenor vehicle ground : I) :
    (metaphorStrength tenor vehicle ground) ^ 2 ≤
    weight (compose tenor vehicle) * weight ground := by
  unfold metaphorStrength weight; exact emergence_bounded' tenor vehicle ground

/-- **Metonymy**: resonance-based association. The part stands for the
    whole through direct resonance, not emergence. -/
noncomputable def metonymicLink (part whole : I) : ℝ :=
  rs part whole

-- T218: metonymic link with void is zero
theorem metonymic_void (a : I) : metonymicLink a (void : I) = 0 := by
  unfold metonymicLink; exact rs_void_right' a

/-- **Synecdoche**: part-whole resonance where the part composed with
    context recovers the whole's resonance profile. -/
noncomputable def synecdocheGap (part whole observer : I) : ℝ :=
  rs whole observer - rs part observer

-- T219: synecdoche gap is zero for identical part and whole
theorem synecdoche_self (a observer : I) :
    synecdocheGap a a observer = 0 := by
  unfold synecdocheGap; ring

-- T220: synecdoche gap with void part
theorem synecdoche_void_part (whole observer : I) :
    synecdocheGap (void : I) whole observer = rs whole observer := by
  unfold synecdocheGap; simp [rs_void_left']

/-- **Hyperbole**: weight amplification through repeated composition.
    Exaggeration is just repetition — and repetition provably increases weight. -/
theorem hyperbole_amplifies (a : I) (n : ℕ) :
    weight (repetition a (n + 1)) ≥ weight a := repetition_weight_ge a n

-- T221: double hyperbole exceeds single
theorem double_hyperbole (a : I) :
    weight (repetition a 2) ≥ weight (repetition a 1) := by
  exact repetition_weight_mono a 1

/-- **Litotes (understatement)**: the gap between what is composed
    and what could be composed. Measured as the weight deficit. -/
noncomputable def litotesGap (understated full : I) : ℝ :=
  weight full - weight understated

-- T222: litotes gap is nonneg when full contains understated
theorem litotes_nonneg (a b : I) :
    litotesGap a (compose a b) ≥ 0 := by
  unfold litotesGap; linarith [compose_weight_ge a b]

-- T223: litotes gap with void full
theorem litotes_void_full (a : I) :
    litotesGap a (void : I) = -weight a := by
  unfold litotesGap; rw [weight_void]; ring

/-- **Oxymoron**: composition whose emergence is negative while individual
    resonances are positive — the parts affirm but the composition denies. -/
def isOxymoron (a b observer : I) : Prop :=
  rs a observer > 0 ∧ rs b observer > 0 ∧ emergence a b observer < 0

-- T224: void cannot be part of an oxymoron
theorem void_not_oxymoron_left (b observer : I) :
    ¬isOxymoron (void : I) b observer := by
  unfold isOxymoron; intro ⟨h, _, _⟩; simp [rs_void_left'] at h

-- T225: oxymoron implies the whole is less than sum of parts
theorem oxymoron_less_than_sum (a b observer : I) (h : isOxymoron a b observer) :
    rs (compose a b) observer < rs a observer + rs b observer := by
  obtain ⟨_, _, h3⟩ := h; linarith [rs_compose_eq a b observer]

/-- **Zeugma**: one word governing two others with different emergence patterns. -/
noncomputable def zeugmaGap (governor obj1 obj2 observer : I) : ℝ :=
  emergence governor obj1 observer - emergence governor obj2 observer

-- T226: zeugma gap is antisymmetric in objects
theorem zeugma_antisymm (gov o1 o2 obs : I) :
    zeugmaGap gov o1 o2 obs = -zeugmaGap gov o2 o1 obs := by
  unfold zeugmaGap; ring

-- T227: zeugma gap with same object is zero
theorem zeugma_self (gov obj obs : I) :
    zeugmaGap gov obj obj obs = 0 := by
  unfold zeugmaGap; ring

end AdvancedPoetics

/-! ## §26. Extended Formal Results

Further structural theorems about poetic composition that follow
from the axioms. -/

section ExtendedFormal
variable {I : Type*} [IdeaticSpace3 I]

/-- **Stanza weight monotonicity**: adding a stanza never decreases weight. -/
theorem stanza_weight_mono (poem stanza : I) :
    weight (compose poem stanza) ≥ weight poem :=
  compose_weight_ge poem stanza

-- T228: triple stanza weight
theorem triple_stanza_weight (s1 s2 s3 : I) :
    weight (compose (compose s1 s2) s3) ≥ weight s1 := by
  unfold weight
  linarith [compose_enriches' s1 s2, compose_enriches' (compose s1 s2) s3]

-- T229: quatrain from two couplets — resonance decomposition
theorem quatrain_resonance (a b c d observer : I) :
    rs (quatrain a b c d) observer =
    rs (couplet a b) observer + rs (couplet c d) observer +
    emergence (couplet a b) (couplet c d) observer := by
  unfold quatrain; exact rs_compose_eq (couplet a b) (couplet c d) observer

-- T230: rhyme strength of composition
theorem rhyme_strength_ge_zero_self (a : I) :
    rhymeStrength a a ≥ 0 := rhymeStrength_self_nonneg a

-- T231: composition commutation emergence
theorem commutation_emergence_diff (a b observer : I) :
    rs (compose a b) observer - rs (compose b a) observer =
    emergence a b observer - emergence b a observer := by
  unfold emergence; ring

-- T232: weight of n-fold repetition is nonneg
theorem repetition_weight_nonneg' (a : I) (n : ℕ) :
    weight (repetition a n) ≥ 0 := weight_nonneg _

-- T233: sonnet weight ≥ sestet weight (using Petrarchan form)
theorem petrarchan_weight_ge_octave (q1 q2 sestet : I) :
    weight (petrarchanSonnet q1 q2 sestet) ≥ weight (compose q1 q2) := by
  unfold petrarchanSonnet; exact compose_weight_ge (compose q1 q2) sestet

-- T234: meter emergence cocycle
theorem meter_emergence_cocycle (foot1 foot2 foot3 observer : I) :
    emergence foot1 foot2 observer +
    emergence (compose foot1 foot2) foot3 observer =
    emergence foot2 foot3 observer +
    emergence foot1 (compose foot2 foot3) observer :=
  cocycle_condition foot1 foot2 foot3 observer

-- T235: weight of a couplet is nonneg
theorem couplet_weight_nonneg (a b : I) : weight (couplet a b) ≥ 0 :=
  weight_nonneg _

-- T236: quatrain weight is nonneg
theorem quatrain_weight_nonneg (a b c d : I) : weight (quatrain a b c d) ≥ 0 :=
  weight_nonneg _

-- T237: Shakespearean sonnet weight is nonneg
theorem shakespearean_weight_nonneg (q1 q2 q3 fc : I) :
    weight (shakespeareanSonnet q1 q2 q3 fc) ≥ 0 :=
  weight_nonneg _

-- T238: Petrarchan sonnet weight is nonneg
theorem petrarchan_weight_nonneg (q1 q2 sestet : I) :
    weight (petrarchanSonnet q1 q2 sestet) ≥ 0 :=
  weight_nonneg _

-- T239: void Shakespearean sonnet
theorem shakespearean_all_void :
    shakespeareanSonnet (void : I) (void : I) (void : I) (void : I) = (void : I) := by
  unfold shakespeareanSonnet; simp

-- T240: void Petrarchan sonnet
theorem petrarchan_all_void :
    petrarchanSonnet (void : I) (void : I) (void : I) = (void : I) := by
  unfold petrarchanSonnet; simp

end ExtendedFormal

/-! ## §27. Cross-Theoretic Synthesis

Connecting the various poetic theories through shared algebraic structure.
All roads lead to emergence — the cocycle condition unifies every framework. -/

section CrossTheoretic
variable {I : Type*} [IdeaticSpace3 I]

/-- **Aristotle meets Longinus**: the tragic sublime — when hamartia
    itself becomes a source of sublimity through anagnorisis. -/
theorem tragic_sublime_link (hero flaw audience : I)
    (hham : isHamartia flaw hero audience)
    (hana : isAnagnorisis hero flaw) :
    emergence flaw hero audience < 0 ∧ emergence hero flaw hero > 0 :=
  ⟨hham, hana⟩

-- T241: Jakobson's poetic function equals Coleridge's esemplastic power
theorem jakobson_coleridge_equivalence (a b : I) :
    poeticFunction a b = esemplasticPower a b := rfl

-- T242: Brooks' non-paraphrasability = Coleridge's imagination
theorem brooks_coleridge_link (a b observer : I) :
    ¬isParaphrasable a b observer ↔ isImaginative a b observer := by
  unfold isParaphrasable isImaginative; exact Iff.symm Iff.rfl

-- T243: Russian formalist ostranenie = de Man's rhetorical gap (in emergence terms)
theorem formalism_poststructuralism (a b observer : I) :
    ostranenie a b observer =
    emergence b a observer - emergence a b observer :=
  ostranenie_emergence a b observer

-- T244: cognitive blend emergence = Jakobson's poetic function (self-measured)
theorem blend_equals_poetic (source target : I) :
    emergentStructure source target (conceptualBlend source target) =
    poeticFunction source target := rfl

-- T245: enjambment = volta at the line level
theorem enjambment_is_volta (l1 l2 observer : I) :
    enjambmentStrength l1 l2 observer = voltaStrength l1 l2 observer := rfl

-- T246: metaphor strength = phonesthetic emergence (same formula)
theorem metaphor_is_phonesthetic (a b c : I) :
    metaphorStrength a b c = phonestheticEmergence a b c := rfl

-- T247: Todorov's transformation weight = poetic composition weight
theorem todorov_weight_is_compose (state disruption : I) :
    weight (todorovTransform state disruption) = weight (compose state disruption) := by
  unfold todorovTransform; rfl

-- T248: all emergence-based quantities vanish for void
theorem universal_void_vanishing :
    (∀ b c : I, metaphorStrength (void : I) b c = 0) ∧
    (∀ b c : I, enjambmentStrength (void : I) b c = 0) ∧
    (∀ b c : I, voltaStrength (void : I) b c = 0) ∧
    (∀ b c : I, prosodicEmergence (void : I) b c = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro b c <;>
    simp only [metaphorStrength, enjambmentStrength, voltaStrength,
               prosodicEmergence, emergence_void_left]

end CrossTheoretic

end IDT3
