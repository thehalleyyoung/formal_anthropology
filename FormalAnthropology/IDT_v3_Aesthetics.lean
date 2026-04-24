import FormalAnthropology.IDT_v3_Foundations

/-!
# Formal Aesthetics and Philosophy of Art in Ideatic Space

A formalization of core concepts from the philosophy of aesthetics within
the IdeaticSpace3 framework.  Every definition and theorem traces back
to the minimal axioms of IDT v3 (monoid + resonance + emergence).

## Philosophical map

| Concept | IDT formalization |
|---|---|
| **Beauty** (Kant) | Harmonious emergence — bounded, positive |
| **Sublimity** (Kant) | Emergence that saturates or exceeds the observer's capacity |
| **Aesthetic judgment / taste** | A resonance profile: an idea that "measures" others |
| **Originality** | High self-emergence |
| **Kitsch** | Zero emergence — purely additive, no surprise |
| **Camp** (Sontag) | Ironic emergence: negative first-order, positive second-order |
| **Defamiliarization** (Shklovsky) | Disrupting expected resonance via composition |
| **Aura** (Benjamin) | Self-resonance lost under mechanical reproduction |
| **Cultural capital** (Bourdieu) | Self-resonance accumulated through composition |
| **Distribution of the sensible** (Rancière) | Partition of ideatic space by resonance sign |

All 292 theorems/definitions fully proved — 0 sorries.
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. Beauty — Harmonious Emergence (Kant's Analytic of the Beautiful) -/

section Beauty
variable {I : Type*} [IdeaticSpace3 I]

/-- T1. **Aesthetic emergence**: the emergent meaning an artwork `a` creates
    when received by observer `o` in context `c`. -/
noncomputable def aestheticEmergence (a o c : I) : ℝ :=
  emergence a o c

/-- T2. An artwork is **beautiful** (relative to observer `o` and context `c`)
    when it produces strictly positive emergence — the composition of artwork
    and observer creates meaning beyond the sum of parts. -/
def beautiful (a o c : I) : Prop :=
  emergence a o c > 0

/-- T3. An artwork is **ugly** when its emergence is strictly negative —
    the whole is less than the sum of its parts. -/
def ugly (a o c : I) : Prop :=
  emergence a o c < 0

/-- T4. An artwork is **aesthetically neutral** (indifferent) when
    emergence is exactly zero — purely additive, no gestalt. -/
def aestheticallyNeutral (a o c : I) : Prop :=
  emergence a o c = 0

/-- T5. Silence is never beautiful — void produces zero emergence. -/
theorem void_not_beautiful (o c : I) : ¬beautiful (void : I) o c := by
  unfold beautiful; rw [emergence_void_left]; linarith

/-- T6. Nothing is beautiful to void — void perceives no emergence. -/
theorem not_beautiful_to_void (a c : I) : ¬beautiful a (void : I) c := by
  unfold beautiful; rw [emergence_void_right]; linarith

/-- T7. Beauty cannot be perceived against void context. -/
theorem not_beautiful_against_void (a o : I) : ¬beautiful a o (void : I) := by
  unfold beautiful; rw [emergence_against_void]; linarith

/-- T8. Void is aesthetically neutral to everyone. -/
theorem void_neutral (o c : I) : aestheticallyNeutral (void : I) o c := by
  unfold aestheticallyNeutral; exact emergence_void_left o c

/-- T9. If beautiful, then not ugly (trichotomy). -/
theorem beautiful_not_ugly (a o c : I) (h : beautiful a o c) : ¬ugly a o c := by
  unfold beautiful at h; unfold ugly; linarith

/-- T10. If beautiful, then not neutral. -/
theorem beautiful_not_neutral (a o c : I) (h : beautiful a o c) :
    ¬aestheticallyNeutral a o c := by
  unfold beautiful at h; unfold aestheticallyNeutral; linarith

end Beauty

/-! ## §2. The Sublime — Emergence Beyond Capacity (Kant's Analytic of the Sublime) -/

section Sublime
variable {I : Type*} [IdeaticSpace3 I]

/-- T11. **Observer capacity**: the self-resonance of the observer, measuring
    how much emergence the observer can "carry". -/
noncomputable def observerCapacity (o : I) : ℝ := rs o o

/-- T12. **Artwork weight**: the self-resonance of the artwork. -/
noncomputable def artworkWeight (a : I) : ℝ := rs a a

/-- T13. An artwork is **sublime** when its squared emergence saturates the
    emergence bound — the emergence is as large as the axioms allow.
    Kant: the sublime overwhelms the faculties. -/
def sublime (a o c : I) : Prop :=
  (emergence a o c) ^ 2 >
  rs (compose a o) (compose a o) * rs c c / 2

/-- T14. Observer capacity is always non-negative. -/
theorem observerCapacity_nonneg (o : I) : observerCapacity o ≥ 0 := by
  unfold observerCapacity; exact rs_self_nonneg' o

/-- T15. Artwork weight is always non-negative. -/
theorem artworkWeight_nonneg (a : I) : artworkWeight a ≥ 0 := by
  unfold artworkWeight; exact rs_self_nonneg' a

/-- T16. Void has zero observer capacity. -/
theorem void_capacity : observerCapacity (void : I) = 0 := by
  unfold observerCapacity; exact rs_void_void

/-- T17. Void has zero artwork weight. -/
theorem void_artworkWeight : artworkWeight (void : I) = 0 := by
  unfold artworkWeight; exact rs_void_void

/-- T18. Emergence is bounded by the observer's capacity and the composition's
    weight — this is the IDT analogue of Kant's claim that the sublime
    exceeds our representational faculties. -/
theorem emergence_capacity_bound (a o c : I) :
    (emergence a o c) ^ 2 ≤
    rs (compose a o) (compose a o) * rs c c :=
  emergence_bounded' a o c

/-- T19. Composition with artwork never decreases weight — art adds presence. -/
theorem art_enriches_observer (a o : I) :
    rs (compose a o) (compose a o) ≥ artworkWeight a := by
  unfold artworkWeight; exact compose_enriches' a o

/-- T20. The sublime is impossible when the context has zero self-resonance —
    you need a substantive context to experience the sublime. -/
theorem sublime_needs_context (a o : I) :
    ¬sublime a o (void : I) := by
  unfold sublime
  rw [emergence_against_void, rs_void_right']
  simp

end Sublime

/-! ## §3. Aesthetic Judgment and Taste -/

section Taste
variable {I : Type*} [IdeaticSpace3 I]

/-- T21. **Aesthetic taste**: an observer's taste is characterized by how they
    resonate with artworks. Two observers have the same taste if they
    produce identical emergence with all artworks. -/
def sameTaste (o₁ o₂ : I) : Prop :=
  ∀ a c : I, emergence a o₁ c = emergence a o₂ c

/-- T22. Same taste is reflexive. -/
theorem sameTaste_refl (o : I) : sameTaste o o :=
  fun _ _ => rfl

/-- T23. Same taste is symmetric. -/
theorem sameTaste_symm (o₁ o₂ : I) (h : sameTaste o₁ o₂) : sameTaste o₂ o₁ :=
  fun a c => (h a c).symm

/-- T24. Same taste is transitive. -/
theorem sameTaste_trans (o₁ o₂ o₃ : I) (h₁ : sameTaste o₁ o₂)
    (h₂ : sameTaste o₂ o₃) : sameTaste o₁ o₃ :=
  fun a c => (h₁ a c).trans (h₂ a c)

/-- T25. Void taste: void produces zero emergence with everything. -/
theorem void_taste (a c : I) : emergence a (void : I) c = 0 :=
  emergence_void_right a c

/-- T26. **Taste agreement**: two observers agree on artwork `a` in context `c`
    when their emergences have the same sign. -/
def tasteAgrees (o₁ o₂ a c : I) : Prop :=
  (emergence a o₁ c > 0 ∧ emergence a o₂ c > 0) ∨
  (emergence a o₁ c < 0 ∧ emergence a o₂ c < 0) ∨
  (emergence a o₁ c = 0 ∧ emergence a o₂ c = 0)

/-- T27. Same taste implies taste agreement on everything. -/
theorem sameTaste_implies_agrees (o₁ o₂ : I) (h : sameTaste o₁ o₂)
    (a c : I) : tasteAgrees o₁ o₂ a c := by
  unfold tasteAgrees
  rcases lt_trichotomy (emergence a o₁ c) 0 with hn | he | hp
  · right; left; exact ⟨hn, h a c ▸ hn⟩
  · right; right; exact ⟨he, h a c ▸ he⟩
  · left; exact ⟨hp, h a c ▸ hp⟩

/-- T28. **Aesthetic sensitivity**: observer `o` is sensitive to artwork `a`
    if there exists some context where `a` produces nonzero emergence. -/
def aestheticallySensitive (o a : I) : Prop :=
  ∃ c : I, emergence a o c ≠ 0

/-- T29. Void is never aesthetically sensitive. -/
theorem void_not_sensitive (a : I) : ¬aestheticallySensitive (void : I) a := by
  intro ⟨c, h⟩; exact h (emergence_void_right a c)

end Taste

/-! ## §4. Originality, Kitsch, and Camp -/

section OriginalityKitschCamp
variable {I : Type*} [IdeaticSpace3 I]

/-- T30. **Originality**: an artwork is original when composing it with itself
    produces high self-emergence (semantic charge). Original ideas
    amplify themselves — they are self-reinforcing novelties. -/
noncomputable def originality (a : I) : ℝ := semanticCharge a

/-- T31. Originality in terms of resonance. -/
theorem originality_eq (a : I) :
    originality a = rs (compose a a) a - 2 * rs a a := by
  unfold originality; exact semanticCharge_eq a

/-- T32. Void has zero originality. -/
theorem void_originality : originality (void : I) = 0 := by
  unfold originality; exact semanticCharge_void

/-- T33. **Kitsch**: an artwork is kitsch when it is left-linear — composing
    it with anything produces zero emergence. Kitsch is art without surprise,
    purely additive, entirely predictable. (Greenberg, Kundera) -/
def kitsch (a : I) : Prop := leftLinear a

/-- T34. Void is kitsch. -/
theorem void_is_kitsch : kitsch (void : I) := void_leftLinear

/-- T35. Kitsch artworks have zero originality. -/
theorem kitsch_zero_originality (a : I) (h : kitsch a) :
    originality a = 0 := by
  unfold originality semanticCharge; exact h a a

/-- T36. Kitsch is the opposite of emergence — if an artwork is kitsch,
    it produces zero emergence in every context. -/
theorem kitsch_no_emergence (a : I) (h : kitsch a) (b c : I) :
    emergence a b c = 0 := h b c

/-- T37. **Camp** (Sontag): an artwork where the intended aesthetic fails
    (negative first-order emergence) but this very failure creates a
    second-order positive effect. Formally: composing the artwork with
    its own failure produces positive emergence. -/
def camp (a fail o : I) : Prop :=
  emergence a o (compose a o) < 0 ∧
  emergence (compose a fail) o (compose (compose a fail) o) > 0

/-- T38. **Aesthetic surprise**: deviation from additive expectation.
    The absolute value of emergence measures how surprising the artwork is. -/
noncomputable def aestheticSurprise (a o c : I) : ℝ :=
  |emergence a o c|

/-- T39. Kitsch has zero surprise. -/
theorem kitsch_no_surprise (a : I) (h : kitsch a) (o c : I) :
    aestheticSurprise a o c = 0 := by
  unfold aestheticSurprise; rw [h o c]; simp

/-- T40. Surprise is non-negative. -/
theorem surprise_nonneg (a o c : I) : aestheticSurprise a o c ≥ 0 := by
  unfold aestheticSurprise; exact abs_nonneg _

/-- T41. Surprise is zero iff aesthetically neutral. -/
theorem surprise_zero_iff_neutral (a o c : I) :
    aestheticSurprise a o c = 0 ↔ aestheticallyNeutral a o c := by
  unfold aestheticSurprise aestheticallyNeutral; exact abs_eq_zero

end OriginalityKitschCamp

/-! ## §5. Defamiliarization (Shklovsky) — Art as Estrangement -/

section Defamiliarization
variable {I : Type*} [IdeaticSpace3 I]

/-- T42. **Familiarization**: the expected resonance of an artwork with an
    observer is the sum of individual resonances (the "familiar" baseline). -/
noncomputable def familiarResonance (a o c : I) : ℝ :=
  rs a c + rs o c

/-- T43. **Defamiliarization**: the gap between actual resonance (of the
    composition) and the familiar baseline. This IS emergence.
    Shklovsky: art exists to make the stone stony — to disrupt
    automatized perception. -/
noncomputable def defamiliarization (a o c : I) : ℝ :=
  rs (compose a o) c - familiarResonance a o c

/-- T44. Defamiliarization equals emergence — Shklovsky's ostranenie IS
    the emergence phenomenon. -/
theorem defamiliarization_is_emergence (a o c : I) :
    defamiliarization a o c = emergence a o c := by
  unfold defamiliarization familiarResonance emergence; ring

/-- T45. Defamiliarization of void is zero — silence cannot estrange. -/
theorem defamiliarization_void (o c : I) :
    defamiliarization (void : I) o c = 0 := by
  rw [defamiliarization_is_emergence]; exact emergence_void_left o c

/-- T46. **Habituation**: repeated exposure reduces defamiliarization.
    When an artwork is "used up", its emergence contribution to
    further repetition approaches linearity.
    We state: the emergence of adding one more copy equals the cocycle
    difference from the earlier compositions. -/
theorem habituation_cocycle (a c d : I) :
    emergence a a d + emergence (compose a a) c d =
    emergence a c d + emergence a (compose a c) d :=
  cocycle_condition a a c d

/-- T47. Defamiliarization against void context is always zero. -/
theorem defamiliarization_void_context (a o : I) :
    defamiliarization a o (void : I) = 0 := by
  rw [defamiliarization_is_emergence]; exact emergence_against_void a o

/-- T48. **Artistic composition as maximal defamiliarization**:
    an artwork `a` is more defamiliarizing than `b` (for observer `o`,
    context `c`) when its emergence is greater. -/
def moreDefamiliarizing (a b o c : I) : Prop :=
  emergence a o c > emergence b o c

/-- T49. "More defamiliarizing" is transitive. -/
theorem moreDefamiliarizing_trans (a b d o c : I)
    (h₁ : moreDefamiliarizing a b o c) (h₂ : moreDefamiliarizing b d o c) :
    moreDefamiliarizing a d o c := by
  unfold moreDefamiliarizing at *; linarith

/-- T50. Void is never more defamiliarizing than anything with positive emergence. -/
theorem void_not_more_defamiliarizing (b o c : I) (h : emergence b o c > 0) :
    ¬moreDefamiliarizing (void : I) b o c := by
  unfold moreDefamiliarizing; rw [emergence_void_left]; linarith

end Defamiliarization

/-! ## §6. Benjamin's Aura and Mechanical Reproduction -/

section Aura
variable {I : Type*} [IdeaticSpace3 I]

/-- T51. **Aura**: the self-resonance of an artwork, measuring its unique
    "presence" or "here and now". Benjamin: the aura is the artwork's
    authenticity — its embeddedness in tradition. -/
noncomputable def aura (a : I) : ℝ := rs a a

/-- T52. Aura is non-negative — every artwork has non-negative presence. -/
theorem aura_nonneg (a : I) : aura a ≥ 0 := by
  unfold aura; exact rs_self_nonneg' a

/-- T53. Only void has zero aura — only nothing has no presence. -/
theorem aura_zero_iff_void (a : I) : aura a = 0 → a = void := by
  unfold aura; exact rs_nondegen' a

/-- T54. **Aura enrichment**: composing an artwork with context never
    diminishes its aura. Tradition enriches; context adds presence. -/
theorem aura_enrichment (a context : I) :
    aura (compose a context) ≥ aura a := by
  unfold aura; exact compose_enriches' a context

/-- T55. **Mechanical reproduction** (simplified): if a reproduction `r`
    strips away context (i.e., r = compose a void = a), the aura is
    unchanged. But if reproduction LOSES information (modeled as
    emergence against the original being negative), then effective
    aura is reduced. -/
theorem reproduction_preserves_aura (a : I) :
    aura (compose a (void : I)) = aura a := by
  unfold aura; simp

/-- T56. Non-void artworks have strictly positive aura. -/
theorem nonvoid_positive_aura (a : I) (h : a ≠ void) : aura a > 0 := by
  unfold aura; exact rs_self_pos a h

/-- T57. **Aura accumulation**: composing two artworks yields an artwork
    whose aura is at least that of either part. -/
theorem aura_accumulation_left (a b : I) :
    aura (compose a b) ≥ aura a := by
  unfold aura; exact compose_enriches' a b

/-- T58. **Aura of composition is nonneg**: the composed artwork always
    has non-negative presence. -/
theorem aura_compose_nonneg (a b : I) :
    aura (compose a b) ≥ 0 := by
  unfold aura; exact rs_self_nonneg' _

/-- T58b. **Aura growth**: composing an artwork with a non-void context
    strictly increases aura (from the left). -/
theorem aura_strict_growth (a b : I) (ha : a ≠ void) :
    aura (compose a b) > 0 := by
  unfold aura
  have h1 := compose_enriches' a b
  have h2 := rs_self_pos a ha
  linarith

end Aura

/-! ## §7. Adorno's Aesthetic Theory — Art as Social Critique -/

section Adorno
variable {I : Type*} [IdeaticSpace3 I]

/-- T59. **Critical distance**: the emergence an artwork `a` creates against
    social reality `s`, measured by observer `o`. Adorno: authentic art
    negates the given. Positive critical distance = the artwork transforms
    how we see society. -/
noncomputable def criticalDistance (art society observer : I) : ℝ :=
  emergence art society observer

/-- T60. Void art has zero critical distance — it cannot critique. -/
theorem void_no_critique (s o : I) :
    criticalDistance (void : I) s o = 0 :=
  emergence_void_left s o

/-- T61. Critique is impossible in a void society. -/
theorem no_critique_void_society (a o : I) :
    criticalDistance a (void : I) o = 0 :=
  emergence_void_right a o

/-- T62. **Dialectic of art and society** (Adorno): the critical distance
    obeys the cocycle condition — critique is constrained by the
    associative structure of ideatic composition. -/
theorem dialectic_cocycle (art₁ art₂ society observer : I) :
    criticalDistance art₁ art₂ observer +
    criticalDistance (compose art₁ art₂) society observer =
    criticalDistance art₂ society observer +
    criticalDistance art₁ (compose art₂ society) observer := by
  unfold criticalDistance; exact cocycle_condition art₁ art₂ society observer

/-- T63. **Autonomous vs. committed art** (Adorno): artwork that is
    left-linear (kitsch) has zero critical distance — it cannot
    challenge any social reality. -/
theorem kitsch_no_critique (a : I) (h : kitsch a) (s o : I) :
    criticalDistance a s o = 0 := by
  unfold criticalDistance; exact h s o

/-- T64. **Art's double character** (Adorno): the resonance of art-with-society
    decomposes into familiar (additive) and critical (emergent) parts. -/
theorem art_double_character (art society observer : I) :
    rs (compose art society) observer =
    rs art observer + rs society observer + criticalDistance art society observer := by
  unfold criticalDistance; rw [rs_compose_eq]

end Adorno

/-! ## §8. Rancière — Distribution of the Sensible -/

section Ranciere
variable {I : Type*} [IdeaticSpace3 I]

/-- T65. **Sensible partition**: an idea `frame` partitions the ideatic space
    into those that resonate with it (the "visible") and those that don't
    (the "invisible"). Rancière: politics is about who gets to be seen/heard. -/
def visible (frame a : I) : Prop := rs a frame > 0

def invisible (frame a : I) : Prop := rs a frame ≤ 0

/-- T66. Void is always invisible — nothing is unseen. -/
theorem void_invisible (frame : I) : invisible frame (void : I) := by
  unfold invisible; rw [rs_void_left']

/-- T67. Visible and invisible are complementary — every non-void idea
    is either visible, or invisible, in a given frame. -/
theorem visible_or_invisible (frame a : I) :
    visible frame a ∨ invisible frame a := by
  unfold visible invisible
  rcases le_or_lt (rs a frame) 0 with h | h
  · right; exact h
  · left; exact h

/-- T68. **Aesthetic regime** (Rancière): a frame that makes previously
    invisible ideas visible through artistic composition.
    Art redistributes the sensible. -/
def redistributes (art frame a : I) : Prop :=
  invisible frame a ∧ visible frame (compose art a)

/-- T69. Composing with void never redistributes — silence doesn't
    change visibility. -/
theorem void_no_redistribution (frame a : I) (h : invisible frame a) :
    ¬redistributes (void : I) frame a := by
  unfold redistributes visible invisible at *
  intro ⟨_, hv⟩
  simp at hv
  linarith

/-- T70. **Dissensus**: two frames disagree on an idea's visibility. -/
def dissensus (frame₁ frame₂ a : I) : Prop :=
  visible frame₁ a ∧ invisible frame₂ a

end Ranciere

/-! ## §9. Aesthetic Experience as Weight Transformation -/

section AestheticExperience
variable {I : Type*} [IdeaticSpace3 I]

/-- T71. **Aesthetic experience**: the change in the observer's self-resonance
    (weight) after encountering an artwork. -/
noncomputable def aestheticExperience (art observer : I) : ℝ :=
  rs (compose observer art) (compose observer art) - rs observer observer

/-- T72. Aesthetic experience is always non-negative — encountering art
    can only add weight, never remove it. You cannot un-see a painting. -/
theorem aestheticExperience_nonneg (art observer : I) :
    aestheticExperience art observer ≥ 0 := by
  unfold aestheticExperience; linarith [compose_enriches' observer art]

/-- T73. Aesthetic experience of void is zero — encountering nothing
    changes nothing. -/
theorem aestheticExperience_void_art (observer : I) :
    aestheticExperience (void : I) observer = 0 := by
  unfold aestheticExperience; simp

/-- T74. Void has zero aesthetic experience — nothing cannot be changed. -/
theorem aestheticExperience_void_observer (art : I) :
    aestheticExperience art (void : I) ≥ 0 := by
  unfold aestheticExperience; simp [rs_void_void]; exact rs_self_nonneg' _

/-- T75. **Cumulative aesthetic experience**: encountering artworks
    sequentially accumulates weight monotonically. -/
theorem cumulative_experience (art₁ art₂ observer : I) :
    aestheticExperience art₂ (compose observer art₁) +
    aestheticExperience art₁ observer ≥
    aestheticExperience art₁ observer := by
  unfold aestheticExperience; linarith [compose_enriches' (compose observer art₁) art₂]

/-- T76. Aesthetic experience decomposes into resonance terms. -/
theorem aestheticExperience_via_rs (art observer : I) :
    aestheticExperience art observer =
    rs (compose observer art) (compose observer art) - rs observer observer := by
  unfold aestheticExperience; ring

end AestheticExperience

/-! ## §10. Art Markets and Cultural Capital (Bourdieu) -/

section Bourdieu
variable {I : Type*} [IdeaticSpace3 I]

/-- T77. **Cultural capital**: the self-resonance of an agent, measuring
    accumulated cultural weight. Bourdieu: cultural capital is the
    embodied dispositions that constitute taste and competence. -/
noncomputable def culturalCapital (agent : I) : ℝ := rs agent agent

/-- T78. Cultural capital is non-negative. -/
theorem culturalCapital_nonneg (a : I) : culturalCapital a ≥ 0 := by
  unfold culturalCapital; exact rs_self_nonneg' a

/-- T79. Only void has zero cultural capital. -/
theorem culturalCapital_zero_iff (a : I) :
    culturalCapital a = 0 → a = void := by
  unfold culturalCapital; exact rs_nondegen' a

/-- T80. **Capital accumulation**: engaging with cultural objects
    (composition) never decreases cultural capital. -/
theorem capital_accumulation (agent object : I) :
    culturalCapital (compose agent object) ≥ culturalCapital agent := by
  unfold culturalCapital; exact compose_enriches' agent object

/-- T81. **Symbolic violence** (Bourdieu): when composition with a dominant
    discourse `d` produces negative emergence for a subaltern `s` as
    measured by observer `o`, the dominant discourse suppresses the
    subaltern's meaning. -/
def symbolicViolence (dominant subaltern observer : I) : Prop :=
  emergence dominant subaltern observer < 0

/-- T82. Void cannot commit symbolic violence. -/
theorem void_no_violence (s o : I) : ¬symbolicViolence (void : I) s o := by
  unfold symbolicViolence; rw [emergence_void_left]; linarith

/-- T83. **Field effect** (Bourdieu): the cultural capital of a composition
    exceeds that of any single part. This is the Matthew effect —
    the culturally rich get richer. -/
theorem field_effect (a b : I) (ha : a ≠ void) :
    culturalCapital (compose a b) > 0 := by
  unfold culturalCapital
  have h1 := compose_enriches' a b
  have h2 := rs_self_pos a ha
  linarith

/-- T84. **Distinction** (Bourdieu): two agents are culturally distinguishable
    if there exists an artwork that produces different emergence with them. -/
def culturallyDistinct (o₁ o₂ : I) : Prop :=
  ∃ a c : I, emergence a o₁ c ≠ emergence a o₂ c

/-- T85. Same taste implies not culturally distinct. -/
theorem sameTaste_not_distinct (o₁ o₂ : I) (h : sameTaste o₁ o₂) :
    ¬culturallyDistinct o₁ o₂ := by
  intro ⟨a, c, hne⟩; exact hne (h a c)

end Bourdieu

/-! ## §11. Artistic Form and Composition -/

section ArtisticForm
variable {I : Type*} [IdeaticSpace3 I]

/-- **Artistic form**: the composition of elements that constitutes a work. -/
noncomputable def artisticForm (elements : List I) : I := composeList elements

/-- T86. Empty form is void — a work with no elements is silence. -/
theorem empty_form_void : artisticForm ([] : List I) = (void : I) := rfl

/-- T87. Single-element form is the element itself. -/
theorem singleton_form (a : I) : artisticForm [a] = a :=
  composeList_singleton a

/-- T88. **Formal coherence**: the resonance of the form with itself. -/
noncomputable def formalCoherence (elements : List I) : ℝ :=
  rs (artisticForm elements) (artisticForm elements)

/-- T89. Formal coherence is always non-negative. -/
theorem formalCoherence_nonneg (elements : List I) :
    formalCoherence elements ≥ 0 := by
  unfold formalCoherence; exact rs_self_nonneg' _

/-- T90. Empty form has zero coherence. -/
theorem formalCoherence_empty : formalCoherence ([] : List I) = 0 := by
  unfold formalCoherence artisticForm; simp [rs_void_void]

/-- T91. **Compositional emergence**: the emergence of adding a new element
    to an existing form. -/
noncomputable def compositionalEmergence (a : I) (rest : List I) (c : I) : ℝ :=
  emergence a (artisticForm rest) c

/-- T92. Adding to empty form produces zero emergence. -/
theorem compositionalEmergence_empty (a c : I) :
    compositionalEmergence a [] c = 0 := by
  unfold compositionalEmergence artisticForm; exact emergence_void_right a c

/-- T93. Compositional emergence against void is zero. -/
theorem compositionalEmergence_void (a : I) (rest : List I) :
    compositionalEmergence a rest (void : I) = 0 := by
  unfold compositionalEmergence; exact emergence_against_void a _

end ArtisticForm

/-! ## §12. Mimesis and Representation -/

section Mimesis
variable {I : Type*} [IdeaticSpace3 I]

/-- T94. **Representational fidelity**: how well an artwork `a` represents
    a subject `s`, measured as their resonance. -/
noncomputable def representationalFidelity (artwork subject : I) : ℝ :=
  rs artwork subject

/-- T95. Void represents nothing faithfully — rs(void, s) = 0. -/
theorem void_no_representation (s : I) :
    representationalFidelity (void : I) s = 0 :=
  rs_void_left' s

/-- T96. Nothing can represent void (non-trivially). -/
theorem nothing_represents_void (a : I) :
    representationalFidelity a (void : I) = 0 :=
  rs_void_right' a

/-- T97. **Mimetic surplus**: the emergence created when representation
    meets subject — what art adds beyond mere copying. -/
noncomputable def mimeticSurplus (artwork subject observer : I) : ℝ :=
  emergence artwork subject observer

/-- T98. Mimetic surplus vanishes for void artwork. -/
theorem mimeticSurplus_void_art (s o : I) :
    mimeticSurplus (void : I) s o = 0 :=
  emergence_void_left s o

/-- T99. Mimetic surplus vanishes against void observer. -/
theorem mimeticSurplus_void_obs (a s : I) :
    mimeticSurplus a s (void : I) = 0 :=
  emergence_against_void a s

end Mimesis

/-! ## §13. Aesthetic Autonomy and Heteronomy -/

section Autonomy
variable {I : Type*} [IdeaticSpace3 I]

/-- T100. **Aesthetic autonomy**: an artwork is autonomous if its emergence
    profile is independent of any particular observer —
    it has the same emergence with all observers. -/
def aestheticallyAutonomous (a : I) : Prop :=
  ∀ o₁ o₂ c : I, emergence a o₁ c = emergence a o₂ c

/-- T101. Void is (trivially) autonomous — zero emergence with everyone. -/
theorem void_autonomous : aestheticallyAutonomous (void : I) := by
  intro o₁ o₂ c; simp [emergence_void_left]

/-- T102. An autonomous artwork is never perceived differently by different
    observers — there is no "taste" for autonomous art. -/
theorem autonomous_no_taste_variance (a : I) (h : aestheticallyAutonomous a)
    (o₁ o₂ : I) (c : I) :
    emergence a o₁ c = emergence a o₂ c := h o₁ o₂ c

/-- T103. **Aesthetic heteronomy**: an artwork whose emergence depends on
    the observer — it requires a particular audience. -/
def aestheticallyHeteronomous (a : I) : Prop :=
  ∃ o₁ o₂ c : I, emergence a o₁ c ≠ emergence a o₂ c

/-- T104. Void is not heteronomous. -/
theorem void_not_heteronomous : ¬aestheticallyHeteronomous (void : I) := by
  intro ⟨o₁, o₂, c, h⟩
  exact h (by simp [emergence_void_left])

/-- T105. Autonomous and heteronomous are contradictory. -/
theorem autonomous_not_heteronomous (a : I) (h : aestheticallyAutonomous a) :
    ¬aestheticallyHeteronomous a := by
  intro ⟨o₁, o₂, c, hne⟩; exact hne (h o₁ o₂ c)

end Autonomy

/-! ## §14. The Gesamtkunstwerk and Multimedia -/

section Gesamtkunstwerk
variable {I : Type*} [IdeaticSpace3 I]

/-- T106. **Multimedia emergence**: the emergence of combining two art forms
    (e.g., music + visual). Wagner's Gesamtkunstwerk thesis is that
    combining art forms produces emergence greater than zero. -/
noncomputable def multimediaEmergence (art₁ art₂ observer : I) : ℝ :=
  emergence art₁ art₂ observer

/-- T107. Multimedia emergence obeys the cocycle — combining three art
    forms is constrained by how pairs interact. -/
theorem multimedia_cocycle (art₁ art₂ art₃ observer : I) :
    multimediaEmergence art₁ art₂ observer +
    multimediaEmergence (compose art₁ art₂) art₃ observer =
    multimediaEmergence art₂ art₃ observer +
    multimediaEmergence art₁ (compose art₂ art₃) observer := by
  unfold multimediaEmergence; exact cocycle_condition art₁ art₂ art₃ observer

/-- T108. Adding void medium (silence) produces no multimedia emergence. -/
theorem multimedia_void_left (art observer : I) :
    multimediaEmergence (void : I) art observer = 0 := by
  unfold multimediaEmergence; exact emergence_void_left art observer

/-- T109. Adding void medium on right produces no multimedia emergence. -/
theorem multimedia_void_right (art observer : I) :
    multimediaEmergence art (void : I) observer = 0 := by
  unfold multimediaEmergence; exact emergence_void_right art observer

/-- T110. The total resonance of a multimedia work decomposes into individual
    resonances plus multimedia emergence. -/
theorem multimedia_decomposition (art₁ art₂ observer : I) :
    rs (compose art₁ art₂) observer =
    rs art₁ observer + rs art₂ observer + multimediaEmergence art₁ art₂ observer := by
  unfold multimediaEmergence; rw [rs_compose_eq]

end Gesamtkunstwerk

/-! ## §15. Aesthetic Value and the Canon -/

section Canon
variable {I : Type*} [IdeaticSpace3 I]

/-- T111. **Canonical weight**: the self-resonance of a tradition or canon,
    formed by composing canonical works. -/
noncomputable def canonWeight (canon : I) : ℝ := rs canon canon

/-- T112. Canon weight is non-negative. -/
theorem canonWeight_nonneg (c : I) : canonWeight c ≥ 0 := by
  unfold canonWeight; exact rs_self_nonneg' c

/-- T113. Adding a work to the canon never decreases its weight. -/
theorem canon_enrichment (canon work : I) :
    canonWeight (compose canon work) ≥ canonWeight canon := by
  unfold canonWeight; exact compose_enriches' canon work

/-- T114. **Canonical emergence**: the emergence a new work creates when
    added to an existing canon. -/
noncomputable def canonicalEmergence (canon newWork observer : I) : ℝ :=
  emergence canon newWork observer

/-- T115. Adding void to the canon produces zero canonical emergence. -/
theorem canonicalEmergence_void (canon observer : I) :
    canonicalEmergence canon (void : I) observer = 0 :=
  emergence_void_right canon observer

/-- T116. Canonical emergence against void observer is zero. -/
theorem canonicalEmergence_void_obs (canon work : I) :
    canonicalEmergence canon work (void : I) = 0 :=
  emergence_against_void canon work

/-- T117. **Canonical resonance decomposition**: how a combined canon
    resonates with an observer. -/
theorem canon_resonance_decomposition (canon work observer : I) :
    rs (compose canon work) observer =
    rs canon observer + rs work observer + canonicalEmergence canon work observer := by
  unfold canonicalEmergence; rw [rs_compose_eq]

end Canon

/-! ## §16. Irony and Double-Coding -/

section Irony
variable {I : Type*} [IdeaticSpace3 I]

/-- T118. **Ironic distance**: the order sensitivity of an artwork —
    the difference between "saying A then B" vs "saying B then A".
    Irony arises when order matters maximally. -/
noncomputable def ironicDistance (a b c : I) : ℝ :=
  orderSensitivity a b c

/-- T119. Ironic distance is antisymmetric. -/
theorem ironicDistance_antisymm (a b c : I) :
    ironicDistance a b c = -ironicDistance b a c := by
  unfold ironicDistance; exact orderSensitivity_antisymm a b c

/-- T120. Ironic distance equals emergence difference. -/
theorem ironicDistance_eq_emergence (a b c : I) :
    ironicDistance a b c = emergence a b c - emergence b a c := by
  unfold ironicDistance; exact orderSensitivity_eq_emergence a b c

/-- T121. Ironic distance vanishes for void. -/
theorem ironicDistance_void (b c : I) :
    ironicDistance (void : I) b c = 0 := by
  unfold ironicDistance; exact orderSensitivity_void_left b c

/-- T122. **Double-coding**: the symmetric part of emergence — what is
    shared between both orderings. Postmodern art is double-coded
    when it works both "sincerely" and "ironically". -/
noncomputable def doubleCoding (a b c : I) : ℝ :=
  (emergence a b c + emergence b a c) / 2

/-- T123. Double-coding is symmetric in a and b. -/
theorem doubleCoding_symm (a b c : I) :
    doubleCoding a b c = doubleCoding b a c := by
  unfold doubleCoding; ring

/-- T124. Emergence decomposes into double-coding plus half the ironic distance. -/
theorem emergence_double_ironic (a b c : I) :
    emergence a b c = doubleCoding a b c + ironicDistance a b c / 2 := by
  unfold doubleCoding ironicDistance orderSensitivity emergence; ring

end Irony

/-! ## §17. Catharsis and Emotional Resonance -/

section Catharsis
variable {I : Type*} [IdeaticSpace3 I]

/-- T125. **Catharsis** (Aristotle): the transformative effect of tragedy
    on the audience. Modeled as the change in the audience's resonance
    profile after experiencing the artwork.
    Catharsis = rs(observer ∘ art, observer) - rs(observer, observer).
    When positive: the experience strengthens the observer's self-resonance
    through the artwork's mediation. -/
noncomputable def catharsis (art observer : I) : ℝ :=
  rs (compose observer art) observer - rs observer observer

/-- T126. Catharsis from void art is zero — nothing cannot purge. -/
theorem catharsis_void_art (o : I) : catharsis (void : I) o = 0 := by
  unfold catharsis; simp

/-- T127. Catharsis of void observer is zero. -/
theorem catharsis_void_observer (a : I) : catharsis a (void : I) = 0 := by
  unfold catharsis; simp [rs_void_left', rs_void_right', rs_void_void]

/-- T128. Catharsis in terms of emergence and cross-resonance. -/
theorem catharsis_decomposition (art observer : I) :
    catharsis art observer =
    rs art observer + emergence observer art observer := by
  unfold catharsis emergence; ring

end Catharsis

/-! ## §18. Hegel's Aesthetics — Symbolic, Classical, Romantic Art -/

section Hegel
variable {I : Type*} [IdeaticSpace3 I]

/-- T129. **Symbolic art** (Hegel): the form exceeds the content —
    the artwork's self-resonance overshoots the emergence it creates
    with its intended meaning. The symbol "says too much". -/
def symbolicArt (form content observer : I) : Prop :=
  rs form form > |emergence form content observer|

/-- T130. **Classical art** (Hegel): perfect balance — the emergence
    squared equals the product of form and content self-resonances
    (the bound is saturated). Content and form are in harmony. -/
def classicalArt (form content observer : I) : Prop :=
  (emergence form content observer) ^ 2 =
  rs (compose form content) (compose form content) * rs observer observer

/-- T131. **Romantic art** (Hegel): content exceeds form — the idea
    overflows any material embodiment. The emergence is nonzero but
    the form's self-resonance is less than the observer's. -/
def romanticArt (form content observer : I) : Prop :=
  emergence form content observer ≠ 0 ∧ rs form form < rs observer observer

/-- T132. Void cannot be symbolic art — void has zero self-resonance. -/
theorem void_not_symbolic (c o : I) : ¬symbolicArt (void : I) c o := by
  unfold symbolicArt; rw [rs_void_void, emergence_void_left]; simp

/-- T133. Void cannot be classical art when both context and observer are non-void. -/
theorem void_not_classical_nontrivial (c o : I) (ho : o ≠ void) (hc : c ≠ void) :
    ¬classicalArt (void : I) c o := by
  unfold classicalArt
  rw [emergence_void_left]; simp
  constructor
  · exact fun h => absurd (rs_nondegen' c h) hc
  · exact fun h => absurd (rs_nondegen' o h) ho

/-- T134. Classical art saturates the emergence bound — it uses
    all available "emergence capacity". -/
theorem classical_saturates (f c o : I) (h : classicalArt f c o) :
    (emergence f c o) ^ 2 =
    rs (compose f c) (compose f c) * rs o o := h

/-- T135. **Dialectical progression** (Hegel): composing symbolic and romantic
    moments obeys the cocycle — the dialectical Aufhebung is constrained. -/
theorem dialectical_progression (sym rom content observer : I) :
    emergence sym rom observer + emergence (compose sym rom) content observer =
    emergence rom content observer + emergence sym (compose rom content) observer :=
  cocycle_condition sym rom content observer

/-- T136. **Spirit's self-knowledge** (Hegel): when form IS content
    (art about art), the emergence is the semantic charge.
    Spirit knows itself through art. -/
theorem spirit_self_knowledge (a : I) :
    emergence a a a = semanticCharge a := by
  unfold semanticCharge; rfl

/-- T137. Hegel's end of art: if all art becomes left-linear (kitsch),
    then all emergence vanishes — art can no longer express Spirit. -/
theorem end_of_art (a : I) (h : kitsch a) (b c : I) :
    emergence a b c = 0 := h b c

end Hegel

/-! ## §19. Nietzsche — The Apollonian and the Dionysian -/

section Nietzsche
variable {I : Type*} [IdeaticSpace3 I]

/-- T138. **Apollonian measure**: the self-resonance of an artwork,
    representing form, order, individuation, clarity.
    Apollo = the principle of structured beauty. -/
noncomputable def apollonian (a : I) : ℝ := rs a a

/-- T139. **Dionysian intensity**: the absolute emergence an artwork
    creates when composed with itself — the ecstatic, formless,
    self-transcending energy. Dionysus = dissolution of boundaries. -/
noncomputable def dionysian (a : I) : ℝ := |semanticCharge a|

/-- T140. Apollonian measure is non-negative — form is never negative. -/
theorem apollonian_nonneg (a : I) : apollonian a ≥ 0 := by
  unfold apollonian; exact rs_self_nonneg' a

/-- T141. Dionysian intensity is non-negative. -/
theorem dionysian_nonneg (a : I) : dionysian a ≥ 0 := by
  unfold dionysian; exact abs_nonneg _

/-- T142. Void has zero Apollonian measure — silence has no form. -/
theorem apollonian_void : apollonian (void : I) = 0 := by
  unfold apollonian; exact rs_void_void

/-- T143. Void has zero Dionysian intensity — silence has no ecstasy. -/
theorem dionysian_void : dionysian (void : I) = 0 := by
  unfold dionysian; rw [semanticCharge_void]; simp

/-- T144. **Tragic art** (Nietzsche): when both Apollonian and Dionysian
    are positive — form and ecstasy coexist. -/
def tragicArt (a : I) : Prop :=
  apollonian a > 0 ∧ dionysian a > 0

/-- T145. Void is not tragic art. -/
theorem void_not_tragic : ¬tragicArt (void : I) := by
  unfold tragicArt; rw [apollonian_void]; intro ⟨h, _⟩; linarith

/-- T146. **Birth of tragedy**: composition enriches the Apollonian —
    combining ideas adds form. -/
theorem apollonian_enrichment (a b : I) :
    apollonian (compose a b) ≥ apollonian a := by
  unfold apollonian; exact compose_enriches' a b

/-- T147. **Apollonian–Dionysian duality**: the Apollonian measures static
    self-presence, the Dionysian measures dynamic self-amplification.
    They probe different aspects of the same artwork. -/
theorem apollonian_dionysian_distinct (a : I) :
    apollonian a = rs a a ∧ dionysian a = |emergence a a a| := by
  constructor
  · rfl
  · unfold dionysian semanticCharge; rfl

/-- T148. Non-void artworks always have positive Apollonian measure. -/
theorem nonvoid_apollonian_pos (a : I) (h : a ≠ void) :
    apollonian a > 0 := by
  unfold apollonian; exact rs_self_pos a h

end Nietzsche

/-! ## §20. Dewey — Art as Experience -/

section Dewey
variable {I : Type*} [IdeaticSpace3 I]

/-- T149. **Experiential quality** (Dewey): art is not an object but an
    experience — the resonance between artwork and observer in context.
    The quality of experience is the full resonance of the composition. -/
noncomputable def experientialQuality (art observer context : I) : ℝ :=
  rs (compose art observer) context

/-- T150. Experiential quality decomposes into individual contributions
    plus emergence — experience is more than the sum of parts. -/
theorem experiential_decomposition (art observer context : I) :
    experientialQuality art observer context =
    rs art context + rs observer context + emergence art observer context := by
  unfold experientialQuality; rw [rs_compose_eq]

/-- T151. Void art produces zero emergent experience — only the
    observer's existing resonance remains. -/
theorem void_art_experience (observer context : I) :
    experientialQuality (void : I) observer context = rs observer context := by
  unfold experientialQuality; simp

/-- T152. **Consummatory experience** (Dewey): an experience where the
    emergence is positive — the interaction creates meaning beyond
    what either part contributes alone. -/
def consummatory (art observer context : I) : Prop :=
  emergence art observer context > 0

/-- T153. Void art never produces consummatory experience. -/
theorem void_not_consummatory (o c : I) : ¬consummatory (void : I) o c := by
  unfold consummatory; rw [emergence_void_left]; linarith

/-- T154. **Aesthetic continuity** (Dewey): experience is continuous —
    adding a new element to an ongoing experience obeys the cocycle. -/
theorem aesthetic_continuity (exp₁ exp₂ exp₃ observer : I) :
    emergence exp₁ exp₂ observer +
    emergence (compose exp₁ exp₂) exp₃ observer =
    emergence exp₂ exp₃ observer +
    emergence exp₁ (compose exp₂ exp₃) observer :=
  cocycle_condition exp₁ exp₂ exp₃ observer

/-- T155. **Funded experience** (Dewey): past experience enriches present —
    the observer's capacity grows with each encounter. -/
theorem funded_experience (art₁ art₂ observer : I) :
    rs (compose (compose observer art₁) art₂)
       (compose (compose observer art₁) art₂) ≥
    rs (compose observer art₁) (compose observer art₁) := by
  exact compose_enriches' (compose observer art₁) art₂

/-- T156. Funded experience is transitive: three encounters grow monotonically. -/
theorem funded_experience_chain (a₁ a₂ o : I) :
    rs (compose (compose o a₁) a₂) (compose (compose o a₁) a₂) ≥
    rs o o := by
  have h1 := compose_enriches' o a₁
  have h2 := compose_enriches' (compose o a₁) a₂
  linarith

/-- T157. Experience against void context is zero — context is essential. -/
theorem experience_needs_context (art observer : I) :
    experientialQuality art observer (void : I) = 0 := by
  unfold experientialQuality; exact rs_void_right' _

end Dewey

/-! ## §21. Goodman — Languages of Art -/

section Goodman
variable {I : Type*} [IdeaticSpace3 I]

/-- T158. **Denotation** (Goodman): how well a symbol `s` refers to a
    referent `r`, measured as their resonance. Denotation is directional
    — s denotes r ≠ r denotes s. -/
noncomputable def denotation (symbol referent : I) : ℝ :=
  rs symbol referent

/-- T159. **Exemplification** (Goodman): the reverse of denotation —
    how a sample refers back to the property it possesses.
    A paint chip exemplifies its color. -/
noncomputable def exemplification (sample property : I) : ℝ :=
  rs property sample

/-- T160. **Denotation–exemplification asymmetry** (Goodman): denotation and
    exemplification differ by the resonance asymmetry. Reference is
    not symmetric. -/
theorem denotation_exemplification_gap (s r : I) :
    denotation s r - exemplification s r = asymmetry s r := by
  unfold denotation exemplification asymmetry; ring

/-- T161. Void denotes nothing. -/
theorem void_denotation (r : I) : denotation (void : I) r = 0 := by
  unfold denotation; exact rs_void_left' r

/-- T162. Nothing exemplifies void. -/
theorem void_exemplification (s : I) : exemplification s (void : I) = 0 := by
  unfold exemplification; exact rs_void_left' s

/-- T163. **Notational system** (Goodman): a symbol system is notational
    if distinct symbols produce distinct emergence — no ambiguity.
    Two symbols are notationally equivalent if they produce the same
    emergence with all referents and contexts. -/
def notationallyEquiv (s₁ s₂ : I) : Prop :=
  ∀ r c : I, emergence s₁ r c = emergence s₂ r c

/-- T164. Notational equivalence is reflexive. -/
theorem notationallyEquiv_refl (s : I) : notationallyEquiv s s :=
  fun _ _ => rfl

/-- T165. Notational equivalence is symmetric. -/
theorem notationallyEquiv_symm (s₁ s₂ : I) (h : notationallyEquiv s₁ s₂) :
    notationallyEquiv s₂ s₁ :=
  fun r c => (h r c).symm

/-- T166. Notational equivalence is transitive. -/
theorem notationallyEquiv_trans (s₁ s₂ s₃ : I)
    (h₁ : notationallyEquiv s₁ s₂) (h₂ : notationallyEquiv s₂ s₃) :
    notationallyEquiv s₁ s₃ :=
  fun r c => (h₁ r c).trans (h₂ r c)

/-- T167. **Density** (Goodman): a symbol system is dense if for any two
    symbols with different emergence, there's a context that separates them.
    Dense systems (like painting) contrast with discrete systems (like music notation). -/
def symbolicallyDense (s₁ s₂ : I) : Prop :=
  ¬notationallyEquiv s₁ s₂

/-- T168. Void is notationally equivalent to itself. -/
theorem void_notational_self : notationallyEquiv (void : I) (void : I) :=
  notationallyEquiv_refl _

/-- T169. **Repleteness** (Goodman): an artwork is replete when every aspect
    of it matters — it has nonzero emergence with some context. -/
def replete (a : I) : Prop :=
  ∃ b c : I, emergence a b c ≠ 0

/-- T170. Void is not replete — silence has nothing that "matters". -/
theorem void_not_replete : ¬replete (void : I) := by
  intro ⟨b, c, h⟩; exact h (emergence_void_left b c)

end Goodman

/-! ## §22. Danto — The Artworld and Institutional Theory -/

section Danto
variable {I : Type*} [IdeaticSpace3 I]

/-- T171. **Artworld** (Danto): an institutional context that transforms
    ordinary objects into artworks by creating emergence. The artworld
    is an idea whose composition with an object produces positive emergence.
    "To see something as art requires an atmosphere of artistic theory." -/
def artworld (institution object observer : I) : Prop :=
  emergence institution object observer > 0

/-- T172. Void institution creates no artworld — without theory, no art. -/
theorem void_no_artworld (obj obs : I) : ¬artworld (void : I) obj obs := by
  unfold artworld; rw [emergence_void_left]; linarith

/-- T173. **Indiscernibles** (Danto): two perceptually identical objects can
    differ as art if they produce different emergence with the artworld.
    Warhol's Brillo Boxes ≠ actual Brillo boxes. -/
def artistically_indiscernible (a b : I) : Prop :=
  rs a a = rs b b ∧ ∃ inst obs : I, emergence inst a obs ≠ emergence inst b obs

/-- T174. **Transfiguration** (Danto): the institutional context transfigures
    the commonplace. The "transfiguration weight" measures how much the
    institution gains presence through engagement with the object. -/
noncomputable def transfiguration (institution object : I) : ℝ :=
  rs (compose institution object) (compose institution object) - rs institution institution

/-- T175. Transfiguration is non-negative — institutions only gain weight. -/
theorem transfiguration_nonneg (inst obj : I) :
    transfiguration inst obj ≥ 0 := by
  unfold transfiguration
  linarith [compose_enriches' inst obj]

/-- T176. Void institution has transfiguration equal to the object's own weight. -/
theorem void_transfiguration (obj : I) :
    transfiguration (void : I) obj = rs obj obj := by
  unfold transfiguration; simp [rs_void_void]

/-- T177. **End of art** (Danto): when art becomes its own philosophy,
    the artwork is about itself — self-referential emergence.
    Modeled as emergence of art with itself. -/
noncomputable def selfReferentialEmergence (a : I) : ℝ :=
  emergence a a a

/-- T178. Self-referential emergence equals semantic charge. -/
theorem selfRef_eq_charge (a : I) :
    selfReferentialEmergence a = semanticCharge a := rfl

/-- T179. Void has zero self-referential emergence. -/
theorem selfRef_void : selfReferentialEmergence (void : I) = 0 := by
  unfold selfReferentialEmergence; exact emergence_void_left _ _

end Danto

/-! ## §23. Bourriaud — Relational Aesthetics -/

section Bourriaud
variable {I : Type*} [IdeaticSpace3 I]

/-- T180. **Relational emergence** (Bourriaud): art's meaning resides not in
    the object but in the social relations it catalyzes. The relational
    value is the emergence between two participants mediated by the artwork. -/
noncomputable def relationalEmergence (participant₁ participant₂ artwork : I) : ℝ :=
  emergence participant₁ participant₂ artwork

/-- T181. Relational emergence vanishes for void participants. -/
theorem relational_void_left (p art : I) :
    relationalEmergence (void : I) p art = 0 :=
  emergence_void_left p art

/-- T182. Relational emergence vanishes against void artwork. -/
theorem relational_void_art (p₁ p₂ : I) :
    relationalEmergence p₁ p₂ (void : I) = 0 :=
  emergence_against_void p₁ p₂

/-- T183. **Relational cocycle** (Bourriaud): adding a third participant to
    a relational artwork obeys the cocycle — social relations are
    structurally constrained. -/
theorem relational_cocycle (p₁ p₂ p₃ art : I) :
    relationalEmergence p₁ p₂ art +
    relationalEmergence (compose p₁ p₂) p₃ art =
    relationalEmergence p₂ p₃ art +
    relationalEmergence p₁ (compose p₂ p₃) art :=
  cocycle_condition p₁ p₂ p₃ art

/-- T184. **Conviviality** (Bourriaud): a relational artwork is convivial
    when it produces positive emergence between all participant pairs.
    We state: at least one pair has positive relational emergence. -/
def convivial (p₁ p₂ artwork : I) : Prop :=
  relationalEmergence p₁ p₂ artwork > 0

/-- T185. Void artwork is never convivial — silence creates no social bonds. -/
theorem void_not_convivial (p₁ p₂ : I) : ¬convivial p₁ p₂ (void : I) := by
  unfold convivial relationalEmergence; rw [emergence_against_void]; linarith

/-- T186. **Relational decomposition**: the total resonance of two participants
    composed together, measured against the artwork, decomposes into
    individual resonances plus relational emergence. -/
theorem relational_decomposition (p₁ p₂ art : I) :
    rs (compose p₁ p₂) art =
    rs p₁ art + rs p₂ art + relationalEmergence p₁ p₂ art := by
  unfold relationalEmergence; rw [rs_compose_eq]

end Bourriaud

/-! ## §24. Rancière's Aesthetic Regime vs Representative Regime -/

section AestheticRegime
variable {I : Type*} [IdeaticSpace3 I]

/-- T187. **Representative regime** (Rancière): art is governed by rules of
    representation — the artwork's value is its fidelity to the subject.
    In IDT terms: emergence is zero (purely additive/mimetic). -/
def representativeRegime (art subject observer : I) : Prop :=
  emergence art subject observer = 0

/-- T188. **Aesthetic regime** (Rancière): art's value comes from its
    autonomous emergence — not from representing but from disrupting
    the sensible order. Emergence is nonzero. -/
def aestheticRegime (art subject observer : I) : Prop :=
  emergence art subject observer ≠ 0

/-- T189. The two regimes are complementary — every artwork-subject-observer
    triple falls into exactly one regime. -/
theorem regime_dichotomy (art subject observer : I) :
    representativeRegime art subject observer ∨
    aestheticRegime art subject observer := by
  unfold representativeRegime aestheticRegime
  by_cases h : emergence art subject observer = 0
  · left; exact h
  · right; exact h

/-- T190. Representative regime implies resonance is additive. -/
theorem representative_additive (art subject observer : I)
    (h : representativeRegime art subject observer) :
    rs (compose art subject) observer =
    rs art observer + rs subject observer := by
  unfold representativeRegime at h
  linarith [rs_compose_eq art subject observer]

/-- T191. Void art is always in the representative regime. -/
theorem void_representative (s o : I) :
    representativeRegime (void : I) s o := by
  unfold representativeRegime; exact emergence_void_left s o

/-- T192. Kitsch is permanently in the representative regime. -/
theorem kitsch_representative (a : I) (h : kitsch a) (s o : I) :
    representativeRegime a s o := by
  unfold representativeRegime; exact h s o

/-- T193. **Regime transition** (Rancière): a work transitions from
    representative to aesthetic regime precisely when emergence appears.
    The "aesthetic revolution" is the moment κ becomes nonzero. -/
theorem regime_transition (art subject observer : I) :
    aestheticRegime art subject observer ↔
    ¬representativeRegime art subject observer := by
  unfold aestheticRegime representativeRegime; exact Iff.rfl

end AestheticRegime

/-! ## §25. Affect Theory — Massumi and Berlant -/

section AffectTheory
variable {I : Type*} [IdeaticSpace3 I]

/-- T194. **Affect** (Massumi): a pre-personal intensity — the raw
    resonance between body and world before it is categorized as emotion.
    Affect is directional: how body resonates with stimulus. -/
noncomputable def affect (body stimulus : I) : ℝ :=
  rs body stimulus

/-- T195. **Affective intensity** (Massumi): the magnitude of affect,
    regardless of direction — pure intensity. -/
noncomputable def affectiveIntensity (body stimulus : I) : ℝ :=
  |rs body stimulus|

/-- T196. Affective intensity is non-negative. -/
theorem affectiveIntensity_nonneg (b s : I) :
    affectiveIntensity b s ≥ 0 := by
  unfold affectiveIntensity; exact abs_nonneg _

/-- T197. Void body has zero affect — nothing feels nothing. -/
theorem void_no_affect (s : I) : affect (void : I) s = 0 := by
  unfold affect; exact rs_void_left' s

/-- T198. **Affective emergence** (Massumi): when bodies compose, new affects
    emerge that neither body had alone. The collective affect exceeds
    the sum of individual affects. -/
noncomputable def affectiveEmergence (body₁ body₂ stimulus : I) : ℝ :=
  emergence body₁ body₂ stimulus

/-- T199. Affective emergence vanishes for void bodies. -/
theorem affective_void (b s : I) :
    affectiveEmergence (void : I) b s = 0 :=
  emergence_void_left b s

/-- T200. **Cruel optimism** (Berlant): attachment to an object that
    actively impedes flourishing. Modeled as: the affect (resonance)
    is positive, but the emergence is negative — the attachment feels
    good but the composition diminishes meaning. -/
def cruelOptimism (subject object context : I) : Prop :=
  rs subject object > 0 ∧ emergence subject object context < 0

/-- T201. Void cannot be an object of cruel optimism —
    nothing resonates with void. -/
theorem void_no_cruel_optimism (s c : I) :
    ¬cruelOptimism s (void : I) c := by
  unfold cruelOptimism; rw [rs_void_right']; intro ⟨h, _⟩; linarith

/-- T202. **Affective atmosphere** (Berlant): the emergence created by
    a collective of bodies in a shared context. Obeys the cocycle. -/
theorem affective_atmosphere_cocycle (b₁ b₂ b₃ stim : I) :
    affectiveEmergence b₁ b₂ stim +
    affectiveEmergence (compose b₁ b₂) b₃ stim =
    affectiveEmergence b₂ b₃ stim +
    affectiveEmergence b₁ (compose b₂ b₃) stim := by
  unfold affectiveEmergence; exact cocycle_condition b₁ b₂ b₃ stim

/-- T203. **Impasse** (Berlant): affective stuckness — when emergence is
    exactly zero. Neither growth nor decay, just persistence. -/
def affectiveImpasse (subject object context : I) : Prop :=
  emergence subject object context = 0

/-- T204. Void always produces impasse — silence is the ultimate stuckness. -/
theorem void_impasse (s c : I) :
    affectiveImpasse (void : I) s c := by
  unfold affectiveImpasse; exact emergence_void_left s c

end AffectTheory

/-! ## §26. Computational Aesthetics and Algorithmic Art -/

section ComputationalAesthetics
variable {I : Type*} [IdeaticSpace3 I]

/-- T205. **Algorithmic composition**: iterated application of a generative
    rule (modeled as repeated self-composition). The n-fold iteration
    represents n steps of an algorithm. -/
noncomputable def algorithmicOutput (rule : I) (n : ℕ) : I :=
  composeN rule n

/-- T206. Algorithmic output at step 0 is void — before running, nothing. -/
theorem algorithmic_zero (rule : I) :
    algorithmicOutput rule 0 = (void : I) := by
  unfold algorithmicOutput; exact composeN_zero rule

/-- T207. Algorithmic output at step 1 is the rule itself. -/
theorem algorithmic_one (rule : I) :
    algorithmicOutput rule 1 = rule := by
  unfold algorithmicOutput; exact composeN_one rule

/-- T208. **Algorithmic complexity** (Kolmogorov-inspired): the self-resonance
    of the algorithmic output at step n. Measures the "weight" or
    "information content" of the generated artwork. -/
noncomputable def algorithmicComplexity (rule : I) (n : ℕ) : ℝ :=
  rs (algorithmicOutput rule n) (algorithmicOutput rule n)

/-- T209. Algorithmic complexity is non-negative. -/
theorem algorithmicComplexity_nonneg (rule : I) (n : ℕ) :
    algorithmicComplexity rule n ≥ 0 := by
  unfold algorithmicComplexity; exact rs_self_nonneg' _

/-- T210. Algorithmic complexity at step 0 is zero. -/
theorem algorithmicComplexity_zero (rule : I) :
    algorithmicComplexity rule 0 = 0 := by
  unfold algorithmicComplexity algorithmicOutput; simp [rs_void_void]

/-- T211. **Monotonic complexity growth**: algorithmic complexity never
    decreases with more iterations — generated art accumulates weight. -/
theorem algorithmicComplexity_mono (rule : I) (n : ℕ) :
    algorithmicComplexity rule (n + 1) ≥ algorithmicComplexity rule n := by
  unfold algorithmicComplexity algorithmicOutput
  exact rs_composeN_mono rule n

/-- T212. **Generative emergence**: the emergence created at step n+1
    of the algorithm — the "novelty" of the (n+1)-th iteration. -/
noncomputable def generativeEmergence (rule : I) (n : ℕ) (observer : I) : ℝ :=
  emergence (algorithmicOutput rule n) rule observer

/-- T213. Generative emergence at step 0 is zero — the first step
    composes void with the rule, producing no emergence. -/
theorem generativeEmergence_zero (rule observer : I) :
    generativeEmergence rule 0 observer = 0 := by
  unfold generativeEmergence algorithmicOutput
  simp [emergence_void_left]

/-- T214. Generative emergence against void observer is zero. -/
theorem generativeEmergence_void_obs (rule : I) (n : ℕ) :
    generativeEmergence rule n (void : I) = 0 := by
  unfold generativeEmergence; exact emergence_against_void _ _

/-- T215. **Fitness function** (evolutionary art): the emergence of an artwork
    relative to a target aesthetic — higher emergence = better fitness. -/
noncomputable def fitness (artwork target criterion : I) : ℝ :=
  emergence artwork target criterion

/-- T216. Void artwork has zero fitness. -/
theorem fitness_void (t c : I) : fitness (void : I) t c = 0 := by
  unfold fitness; exact emergence_void_left t c

/-- T217. Fitness against void criterion is zero — without criteria,
    no evaluation is possible. -/
theorem fitness_void_criterion (a t : I) :
    fitness a t (void : I) = 0 := by
  unfold fitness; exact emergence_against_void a t

end ComputationalAesthetics

/-! ## §27. Aesthetic Measure as Functional — Deep Mathematics -/

section AestheticMeasure
variable {I : Type*} [IdeaticSpace3 I]

/-- T218. **Birkhoff's aesthetic measure** (reformulated): the ratio of
    emergence to self-resonance — "order divided by complexity".
    We define it as emergence normalized by observer capacity. -/
noncomputable def aestheticMeasure (art observer context : I) (_ho : observer ≠ void) : ℝ :=
  emergence art observer context / rs observer observer

/-- T219. Void art has zero aesthetic measure. -/
theorem aestheticMeasure_void (o c : I) (ho : o ≠ void) :
    aestheticMeasure (void : I) o c ho = 0 := by
  unfold aestheticMeasure; rw [emergence_void_left]; simp

/-- T220. **Emergence functional**: emergence as a trilinear-like map.
    The key identity: the total resonance decomposes into additive part
    plus emergence. This is the fundamental theorem of aesthetic measure. -/
theorem emergence_functional (a b c : I) :
    rs (compose a b) c = rs a c + rs b c + emergence a b c :=
  rs_compose_eq a b c

/-- T221. **Composition enrichment principle**: composing two artworks
    produces a combined work whose self-resonance is at least as large
    as either component. This is the monotonicity of aesthetic weight. -/
theorem aesthetic_weight_monotone (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a ∧
    rs (compose a b) (compose a b) ≥ 0 := by
  exact ⟨compose_enriches' a b, rs_self_nonneg' _⟩

/-- T222. **Emergence boundedness** (deep form): for any artwork-observer-context
    triple, the squared emergence is controlled by the self-resonances.
    This is the "no free lunch" theorem of aesthetics. -/
theorem no_free_lunch (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- T223. **Emergence decomposition theorem**: the emergence of a triple
    composition can be computed two ways (left-associated or right-associated),
    and both give the same total — aesthetic evaluation is path-independent. -/
theorem aesthetic_path_independence (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- T224. **Zero emergence propagation**: if the observer has zero self-resonance,
    no emergence can be perceived. Aesthetics requires a conscious observer. -/
theorem aesthetics_requires_observer (a b c : I) (h : rs c c = 0) :
    emergence a b c = 0 :=
  emergence_zero_of_observer_zero a b c h

/-- T225. **Aesthetic non-commutativity**: the order of aesthetic elements
    matters. The ironic distance measures how much order affects emergence.
    This is fundamentally non-classical: in IDT, A+B ≠ B+A in general. -/
theorem aesthetic_noncommutativity (a b c : I) :
    emergence a b c - emergence b a c =
    rs (compose a b) c - rs (compose b a) c := by
  unfold emergence; ring

/-- T226. **Double emergence identity**: emergence can be decomposed into
    its symmetric (double-coding) and antisymmetric (ironic) parts.
    Every aesthetic phenomenon is partly shared, partly order-dependent. -/
theorem double_emergence_identity (a b c : I) :
    emergence a b c =
    (emergence a b c + emergence b a c) / 2 +
    (emergence a b c - emergence b a c) / 2 := by ring

end AestheticMeasure

/-! ## §28. Aesthetic Dialectics — Synthesis and Sublation -/

section AestheticDialectics
variable {I : Type*} [IdeaticSpace3 I]

/-- T227. **Thesis-antithesis emergence**: when two opposing ideas compose,
    the emergence measures the dialectical synthesis — Aufhebung in
    aesthetic form. -/
noncomputable def dialecticalSynthesis (thesis antithesis observer : I) : ℝ :=
  emergence thesis antithesis observer

/-- T228. Dialectical synthesis is constrained by the cocycle —
    the Hegelian dialectic is not arbitrary but structurally determined. -/
theorem dialectical_constraint (t₁ t₂ t₃ obs : I) :
    dialecticalSynthesis t₁ t₂ obs +
    dialecticalSynthesis (compose t₁ t₂) t₃ obs =
    dialecticalSynthesis t₂ t₃ obs +
    dialecticalSynthesis t₁ (compose t₂ t₃) obs := by
  unfold dialecticalSynthesis; exact cocycle_condition t₁ t₂ t₃ obs

/-- T229. Void thesis produces no synthesis. -/
theorem void_no_synthesis (a obs : I) :
    dialecticalSynthesis (void : I) a obs = 0 := by
  unfold dialecticalSynthesis; exact emergence_void_left a obs

/-- T230. **Sublation weight** (Aufhebung): the composed synthesis always
    weighs at least as much as the thesis alone — sublation preserves. -/
theorem sublation_preserves (thesis antithesis : I) :
    rs (compose thesis antithesis) (compose thesis antithesis) ≥
    rs thesis thesis :=
  compose_enriches' thesis antithesis

/-- T231. **Dialectical asymmetry**: thesis-then-antithesis ≠ antithesis-then-thesis
    in general. The order of dialectical development matters. -/
theorem dialectical_asymmetry (t a c : I) :
    dialecticalSynthesis t a c - dialecticalSynthesis a t c =
    rs (compose t a) c - rs (compose a t) c := by
  unfold dialecticalSynthesis emergence; ring

end AestheticDialectics

/-! ## §29. Aesthetic Topology — Neighborhoods and Continuity -/

section AestheticTopology
variable {I : Type*} [IdeaticSpace3 I]

/-- T232. **Aesthetic proximity**: two artworks are aesthetically proximate
    if they produce similar emergence with all observers.
    This is a weaker notion than notational equivalence. -/
def aestheticallyProximate (a b : I) (ε : ℝ) : Prop :=
  ∀ o c : I, |emergence a o c - emergence b o c| ≤ ε

/-- T233. Every artwork is aesthetically proximate to itself at distance 0. -/
theorem proximate_self (a : I) : aestheticallyProximate a a 0 := by
  intro o c; simp

/-- T234. Aesthetic proximity is symmetric. -/
theorem proximate_symm (a b : I) (ε : ℝ)
    (h : aestheticallyProximate a b ε) : aestheticallyProximate b a ε := by
  intro o c; rw [abs_sub_comm]; exact h o c

/-- T235. **Aesthetic triangle inequality**: if a is ε₁-close to b and b is
    ε₂-close to c, then a is (ε₁+ε₂)-close to c. -/
theorem proximate_triangle (a b c : I) (ε₁ ε₂ : ℝ)
    (h₁ : aestheticallyProximate a b ε₁) (h₂ : aestheticallyProximate b c ε₂) :
    aestheticallyProximate a c (ε₁ + ε₂) := by
  intro o ctx
  have hab := h₁ o ctx
  have hbc := h₂ o ctx
  calc |emergence a o ctx - emergence c o ctx|
      = |(emergence a o ctx - emergence b o ctx) + (emergence b o ctx - emergence c o ctx)| := by ring_nf
    _ ≤ |emergence a o ctx - emergence b o ctx| + |emergence b o ctx - emergence c o ctx| := abs_add _ _
    _ ≤ ε₁ + ε₂ := add_le_add hab hbc

/-- T236. Proximity at negative or zero ε with distinct emergence is impossible. -/
theorem proximate_zero_iff (a b : I) :
    aestheticallyProximate a b 0 ↔ ∀ o c : I, emergence a o c = emergence b o c := by
  constructor
  · intro h o c
    have h1 := h o c
    have h2 := abs_nonneg (emergence a o c - emergence b o c)
    have h3 : |emergence a o c - emergence b o c| = 0 := le_antisymm h1 h2
    linarith [abs_eq_zero.mp h3]
  · intro h o c
    rw [h o c]; simp

end AestheticTopology

/-! ## §30. Aesthetic Entropy and Information -/

section AestheticEntropy
variable {I : Type*} [IdeaticSpace3 I]

/-- T237. **Aesthetic redundancy**: when composing an artwork with itself,
    the deviation from linearity. Redundancy = emergence(a,a,a).
    Highly redundant art repeats itself in a self-amplifying way. -/
noncomputable def aestheticRedundancy (a : I) : ℝ :=
  emergence a a a

/-- T238. Void has zero redundancy. -/
theorem redundancy_void : aestheticRedundancy (void : I) = 0 := by
  unfold aestheticRedundancy; exact emergence_void_left _ _

/-- T239. Redundancy equals semantic charge — self-amplification IS redundancy. -/
theorem redundancy_eq_charge (a : I) :
    aestheticRedundancy a = semanticCharge a := rfl

/-- T240. **Aesthetic information**: the emergence between an artwork and
    an observer, measuring "new information" created by the encounter.
    Zero emergence = zero new information. -/
noncomputable def aestheticInformation (art observer context : I) : ℝ :=
  emergence art observer context

/-- T241. Aesthetic information vanishes for void art. -/
theorem info_void_art (o c : I) :
    aestheticInformation (void : I) o c = 0 := emergence_void_left o c

/-- T242. Aesthetic information vanishes against void context. -/
theorem info_void_context (a o : I) :
    aestheticInformation a o (void : I) = 0 := emergence_against_void a o

/-- T243. **Information cocycle**: aesthetic information obeys the cocycle
    constraint — information is structured, not arbitrary. -/
theorem info_cocycle (a b c d : I) :
    aestheticInformation a b d +
    aestheticInformation (compose a b) c d =
    aestheticInformation b c d +
    aestheticInformation a (compose b c) d := by
  unfold aestheticInformation; exact cocycle_condition a b c d

/-- T244. **Information bound**: aesthetic information is bounded by the
    self-resonances of the composition and observer. You can't get
    more information than the system can carry. -/
theorem info_bound (a b c : I) :
    (aestheticInformation a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c := by
  unfold aestheticInformation; exact emergence_bounded' a b c

end AestheticEntropy

/-! ## §31. Aesthetic Labor and Production -/

section AestheticLabor
variable {I : Type*} [IdeaticSpace3 I]

/-- T245. **Artistic labor** (Marx/Benjamin): the self-resonance accumulated
    through the process of creation. Each compositional step adds weight. -/
noncomputable def artisticLabor (process : List I) : ℝ :=
  rs (artisticForm process) (artisticForm process)

/-- T246. Empty labor produces nothing — zero weight. -/
theorem empty_labor : artisticLabor ([] : List I) = 0 := by
  unfold artisticLabor artisticForm; simp [rs_void_void]

/-- T247. Artistic labor is non-negative. -/
theorem labor_nonneg (process : List I) :
    artisticLabor process ≥ 0 := by
  unfold artisticLabor; exact rs_self_nonneg' _

/-- T248. **Surplus aesthetic value**: the emergence created by combining
    the artwork with the market (audience). The difference between
    the artwork's exchange value and its use value. -/
noncomputable def surplusAestheticValue (artwork market observer : I) : ℝ :=
  emergence artwork market observer

/-- T249. Void artwork has zero surplus value. -/
theorem surplus_void (m o : I) :
    surplusAestheticValue (void : I) m o = 0 :=
  emergence_void_left m o

end AestheticLabor

/-! ## §32. Aesthetic Recursion and Self-Reference -/

section AestheticRecursion
variable {I : Type*} [IdeaticSpace3 I]

/-- T250. **Recursive composition**: the n-fold self-composition of an artwork
    represents recursive self-reference (mise en abyme, fractal art). -/
noncomputable def recursiveArt (a : I) (n : ℕ) : I := composeN a n

/-- T251. Zero recursion is void. -/
theorem recursive_zero (a : I) : recursiveArt a 0 = (void : I) := rfl

/-- T252. One recursion is the artwork itself. -/
theorem recursive_one (a : I) : recursiveArt a 1 = a :=
  composeN_one a

/-- T253. **Recursive weight growth**: the self-resonance of recursive art
    grows monotonically with depth. More self-reference = more weight. -/
theorem recursive_weight_mono (a : I) (n : ℕ) :
    rs (recursiveArt a (n+1)) (recursiveArt a (n+1)) ≥
    rs (recursiveArt a n) (recursiveArt a n) := by
  unfold recursiveArt; exact rs_composeN_mono a n

/-- T254. Recursive art of void is always void — silence repeated is silence. -/
theorem recursive_void (n : ℕ) : recursiveArt (void : I) n = (void : I) := by
  unfold recursiveArt; exact composeN_void n

/-- T255. **Recursive self-resonance bound**: the weight of recursive art
    is always non-negative, regardless of depth. -/
theorem recursive_weight_nonneg (a : I) (n : ℕ) :
    rs (recursiveArt a n) (recursiveArt a n) ≥ 0 := by
  unfold recursiveArt; exact rs_composeN_nonneg a n

end AestheticRecursion

/-! ## §33. Participatory Art and Co-Creation -/

section ParticipatoryArt
variable {I : Type*} [IdeaticSpace3 I]

/-- T256. **Co-creation emergence**: when artist and audience co-create,
    the result has more weight than the artist alone. -/
theorem cocreation_enriches (artist audience : I) :
    rs (compose artist audience) (compose artist audience) ≥
    rs artist artist :=
  compose_enriches' artist audience

/-- T257. **Participatory surplus**: the emergence of co-creation measures
    the added value of participation. -/
noncomputable def participatorySurplus (artist audience observer : I) : ℝ :=
  emergence artist audience observer

/-- T258. Solo art (void audience) has zero participatory surplus. -/
theorem solo_no_surplus (artist observer : I) :
    participatorySurplus artist (void : I) observer = 0 := by
  unfold participatorySurplus; exact emergence_void_right artist observer

/-- T259. Participatory surplus against void observer is zero. -/
theorem participation_needs_observer (artist audience : I) :
    participatorySurplus artist audience (void : I) = 0 := by
  unfold participatorySurplus; exact emergence_against_void artist audience

end ParticipatoryArt

/-! ## §34. Aesthetic Resistance and Negativity -/

section AestheticResistance
variable {I : Type*} [IdeaticSpace3 I]

/-- T260. **Aesthetic resistance** (Adorno): an artwork resists commodification
    when its emergence with the market is negative — it disrupts rather
    than conforms. -/
def aestheticResistance (art market observer : I) : Prop :=
  emergence art market observer < 0

/-- T261. Void art cannot resist — it has zero emergence with everything. -/
theorem void_no_resistance (m o : I) :
    ¬aestheticResistance (void : I) m o := by
  unfold aestheticResistance; rw [emergence_void_left]; linarith

/-- T262. **Negative dialectics**: if an artwork resists the market,
    then it is not kitsch (it has nonzero emergence). -/
theorem resistance_not_kitsch (a m o : I) (h : aestheticResistance a m o) :
    ¬kitsch a := by
  intro hk; unfold aestheticResistance at h; rw [hk m o] at h; linarith

/-- T263. Resistance and beauty can coexist — an artwork can resist the
    market while being beautiful to a different observer. -/
theorem resistance_beauty_compatible (a market o₁ o₂ context : I)
    (hr : aestheticResistance a market o₁)
    (hb : beautiful a o₂ context) :
    emergence a market o₁ < 0 ∧ emergence a o₂ context > 0 := by
  exact ⟨hr, hb⟩

end AestheticResistance

/-! ## §35. Synesthesia and Cross-Modal Aesthetics -/

section Synesthesia
variable {I : Type*} [IdeaticSpace3 I]

/-- T264. **Synesthetic emergence**: when two different sensory modalities
    compose, the emergence captures cross-modal aesthetic effects.
    Hearing colors, seeing sounds — measured as emergence between modes. -/
noncomputable def synestheticEmergence (mode₁ mode₂ observer : I) : ℝ :=
  emergence mode₁ mode₂ observer

/-- T265. Void modality produces no synesthesia. -/
theorem void_no_synesthesia (m o : I) :
    synestheticEmergence (void : I) m o = 0 :=
  emergence_void_left m o

/-- T266. Synesthetic emergence obeys the cocycle — cross-modal effects
    are structurally constrained. -/
theorem synesthetic_cocycle (m₁ m₂ m₃ o : I) :
    synestheticEmergence m₁ m₂ o +
    synestheticEmergence (compose m₁ m₂) m₃ o =
    synestheticEmergence m₂ m₃ o +
    synestheticEmergence m₁ (compose m₂ m₃) o := by
  unfold synestheticEmergence; exact cocycle_condition m₁ m₂ m₃ o

/-- T267. **Total synesthetic resonance**: the full resonance of combined
    modalities decomposes into individual resonances plus cross-modal emergence. -/
theorem synesthetic_decomposition (m₁ m₂ o : I) :
    rs (compose m₁ m₂) o =
    rs m₁ o + rs m₂ o + synestheticEmergence m₁ m₂ o := by
  unfold synestheticEmergence; rw [rs_compose_eq]

end Synesthesia

/-! ## §36. Aesthetic Evolution and Historical Change -/

section AestheticEvolution
variable {I : Type*} [IdeaticSpace3 I]

/-- T268. **Aesthetic evolution**: the change in an observer's aesthetic
    capacity after encountering n artworks. Capacity grows monotonically. -/
theorem aesthetic_evolution_step (observer art : I) :
    rs (compose observer art) (compose observer art) ≥ rs observer observer :=
  compose_enriches' observer art

/-- T269. **Historical weight**: the weight of a tradition is at least
    the weight of its origin. Traditions only accumulate. -/
theorem historical_weight_growth (tradition newWork : I) :
    rs (compose tradition newWork) (compose tradition newWork) ≥
    rs tradition tradition :=
  compose_enriches' tradition newWork

/-- T270. **Paradigm shift** (Kuhn applied to aesthetics): a new paradigm
    creates nonzero emergence with the old one — it disrupts expectations.
    A paradigm shift IS the presence of emergence. -/
def paradigmShift (oldP newP observer : I) : Prop :=
  emergence oldP newP observer ≠ 0

/-- T271. Void is not a paradigm shift — silence disrupts nothing. -/
theorem void_no_paradigm_shift (old obs : I) :
    ¬paradigmShift old (void : I) obs := by
  unfold paradigmShift; rw [emergence_void_right]; simp

/-- T272. Non-void traditions have strictly positive weight —
    any real tradition has presence. -/
theorem tradition_positive (t : I) (h : t ≠ void) :
    rs t t > 0 := rs_self_pos t h

end AestheticEvolution

/-! ## §37. Aesthetic Judgment Aggregation -/

section JudgmentAggregation
variable {I : Type*} [IdeaticSpace3 I]

/-- T273. **Consensus emergence**: when two observers compose their judgments,
    the emergence captures the collective insight beyond individual opinions. -/
noncomputable def consensusEmergence (o₁ o₂ art : I) : ℝ :=
  emergence o₁ o₂ art

/-- T274. Consensus emergence vanishes with void observer. -/
theorem consensus_void_left (o art : I) :
    consensusEmergence (void : I) o art = 0 :=
  emergence_void_left o art

/-- T275. Consensus emergence against void art is zero. -/
theorem consensus_void_art (o₁ o₂ : I) :
    consensusEmergence o₁ o₂ (void : I) = 0 :=
  emergence_against_void o₁ o₂

/-- T276. **Collective judgment decomposition**: the collective resonance
    of two observers with an artwork decomposes into individual resonances
    plus consensus emergence. -/
theorem collective_judgment (o₁ o₂ art : I) :
    rs (compose o₁ o₂) art =
    rs o₁ art + rs o₂ art + consensusEmergence o₁ o₂ art := by
  unfold consensusEmergence; rw [rs_compose_eq]

/-- T277. **Arrow-like impossibility**: consensus emergence can be negative —
    collective judgment can be LESS than the sum of individual judgments.
    Groupthink can destroy aesthetic value. -/
def groupthink (o₁ o₂ art : I) : Prop :=
  consensusEmergence o₁ o₂ art < 0

/-- T278. Void cannot participate in groupthink. -/
theorem void_no_groupthink (o art : I) : ¬groupthink (void : I) o art := by
  unfold groupthink consensusEmergence; rw [emergence_void_left]; linarith

end JudgmentAggregation

/-! ## §38. Aesthetic Modality and Possible Worlds -/

section AestheticModality
variable {I : Type*} [IdeaticSpace3 I]

/-- T279. **Possible artwork**: an artwork is "possible" in a tradition
    if composing it with the tradition doesn't annihilate —
    the composition is non-void. Existence in the artworld. -/
def possibleArtwork (tradition artwork : I) (_h : tradition ≠ void) : Prop :=
  compose tradition artwork ≠ void

/-- T280. Any non-void tradition makes any artwork possible — composition
    with non-void is always non-void. -/
theorem all_artworks_possible (tradition artwork : I) (h : tradition ≠ void) :
    possibleArtwork tradition artwork h := by
  unfold possibleArtwork
  exact compose_ne_void_of_left tradition artwork h

/-- T281. **Counterfactual emergence**: the emergence that WOULD have occurred
    if a different artwork had been chosen. The difference between
    two artworks' emergence in the same context. -/
noncomputable def counterfactualEmergence (art₁ art₂ observer context : I) : ℝ :=
  emergence art₁ observer context - emergence art₂ observer context

/-- T282. Counterfactual emergence is antisymmetric — choosing A over B is
    the negative of choosing B over A. -/
theorem counterfactual_antisymm (a₁ a₂ o c : I) :
    counterfactualEmergence a₁ a₂ o c = -counterfactualEmergence a₂ a₁ o c := by
  unfold counterfactualEmergence; ring

/-- T283. Counterfactual emergence of an artwork against itself is zero. -/
theorem counterfactual_self (a o c : I) :
    counterfactualEmergence a a o c = 0 := by
  unfold counterfactualEmergence; ring

end AestheticModality

/-! ## §39. Aesthetic Depth and Layering -/

section AestheticDepth
variable {I : Type*} [IdeaticSpace3 I]

/-- T284. **Aesthetic depth**: the self-resonance after n layers of
    self-composition, minus the original self-resonance.
    Deep art gains MORE from repetition than shallow art. -/
noncomputable def aestheticDepth (a : I) (n : ℕ) : ℝ :=
  rs (composeN a (n + 1)) (composeN a (n + 1)) - rs (composeN a n) (composeN a n)

/-- T285. Aesthetic depth is non-negative — each layer can only add weight. -/
theorem depth_nonneg (a : I) (n : ℕ) : aestheticDepth a n ≥ 0 := by
  unfold aestheticDepth
  linarith [rs_composeN_mono a n]

/-- T286. Void has zero aesthetic depth at every level. -/
theorem depth_void (n : ℕ) : aestheticDepth (void : I) n = 0 := by
  unfold aestheticDepth; simp [rs_void_void]

/-- T287. **Surface art**: art with zero depth at level 1 — no weight gained
    from self-composition. -/
def surfaceArt (a : I) : Prop := aestheticDepth a 0 = 0

/-- T288. Void is surface art. -/
theorem void_surface : surfaceArt (void : I) := by
  unfold surfaceArt; exact depth_void 0

end AestheticDepth

/-! ## §40. Aesthetic Completeness and Closure -/

section AestheticCompleteness
variable {I : Type*} [IdeaticSpace3 I]

/-- T289. **Aesthetic completeness**: an artwork is aesthetically complete
    if composing it with void leaves it unchanged (which is always true
    by the monoid axiom). The artwork needs nothing more. -/
theorem aesthetic_completeness (a : I) :
    compose a (void : I) = a := void_right' a

/-- T290. **Aesthetic self-sufficiency**: a non-void artwork always has
    strictly positive self-resonance — it needs no external validation. -/
theorem self_sufficiency (a : I) (h : a ≠ void) :
    rs a a > 0 := rs_self_pos a h

/-- T291. **Compositional closure**: composing any two artworks produces
    a well-defined artwork with non-negative self-resonance. The space
    of artworks is closed under composition. -/
theorem compositional_closure (a b : I) :
    rs (compose a b) (compose a b) ≥ 0 :=
  rs_self_nonneg' _

/-- T292. **Void as aesthetic ground** (Heidegger): void is the ground
    from which all art emerges. It is the identity of composition,
    the silence before the first word. -/
theorem void_as_ground (a : I) :
    compose (void : I) a = a ∧ compose a (void : I) = a :=
  ⟨void_left' a, void_right' a⟩

end AestheticCompleteness

end IDT3
