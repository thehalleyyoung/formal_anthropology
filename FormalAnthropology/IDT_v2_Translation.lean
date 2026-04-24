import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Translation Theory — Benjamin, Derrida, Venuti

Translation is one of the deepest problems in literary and cultural theory.
Walter Benjamin argued that every translation chases an unreachable "pure language"
(die reine Sprache) — the untranslatable residue that separates any translation
from its source. Derrida radicalized this: translation reveals that the "original"
is itself already a translation, caught in an infinite chain of signification.
Lawrence Venuti distinguished **domesticating** translations (which assimilate the
foreign into the target culture's norms) from **foreignizing** ones (which preserve
the alien character of the source).

In IDT v2, we formalize these ideas using resonance strength:

- A **translation** is a map `τ : I → I` on the idea space.
- **Fidelity** = `rs(source, τ source)` — how well the translation resonates
  with the original.
- **Untranslatable residue** (Benjamin) = `squaredDistance(source, τ source)` —
  the gap that no translation can fully close.
- **Domestication** (Venuti) = `rs(τ source, targetCulture)` — resonance of the
  translation with the target culture.
- **Foreignization** = `squaredDistance(τ source, targetCulture)` — how far the
  translation stays from the target culture's norms.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Translation

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2 IDT2

/-! ## §1. Core Definitions -/

/-- A translation's **fidelity**: resonance between the source and its image.
    High fidelity = the translation "rings true" to the original. -/
noncomputable def translationFidelity (τ : I → I) (source : I) : ℝ :=
  resonanceStrength source (τ source)

/-- Translation **distance** (squared): how far the translation departs from
    the original in the resonance metric. -/
noncomputable def translationDistance (τ : I → I) (source : I) : ℝ :=
  squaredDistance source (τ source)

/-- A **faithful** translation preserves positive resonance with the source.
    The translation may alter, but it does not annihilate. -/
def isFaithful (τ : I → I) (source : I) : Prop :=
  resonanceStrength source (τ source) > 0

/-- A **perfect** translation maps an idea to itself — the unachievable ideal
    that Benjamin's translator perpetually approaches. -/
def isPerfectTranslation (τ : I → I) (source : I) : Prop :=
  τ source = source

/-- A translation **preserves composition** if it is a monoid homomorphism:
    τ(a ∘ b) = τ(a) ∘ τ(b). This captures structural fidelity. -/
def preservesComposition (τ : I → I) : Prop :=
  ∀ a b : I, τ (compose a b) = compose (τ a) (τ b)

/-- The **translator's voice**: the difference in self-resonance between
    translation and source. Positive = the translator adds richness;
    zero = perfect fidelity of weight. -/
noncomputable def translatorVoice (τ : I → I) (source : I) : ℝ :=
  resonanceStrength (τ source) (τ source) - resonanceStrength source source

/-- The **untranslatable residue** (Benjamin's das Unübersetzbare):
    the squared distance from source to translation.
    "It is the task of the translator to release in his own language
    that pure language which is under the spell of another." -/
noncomputable def untranslatableResidue (τ : I → I) (source : I) : ℝ :=
  squaredDistance source (τ source)

/-- Two translations **converge** on a source if their outputs resonate
    positively — multiple translations approach the "pure language"
    from different directions. -/
def translationsConverge (τ₁ τ₂ : I → I) (source : I) : Prop :=
  resonanceStrength (τ₁ source) (τ₂ source) > 0

/-- **Domestication** degree (Venuti): how much the translation resonates
    with the target culture. A domesticating translation sounds "natural"
    to the target audience. -/
noncomputable def domestication (τ : I → I) (source targetCulture : I) : ℝ :=
  resonanceStrength (τ source) targetCulture

/-- **Foreignization** degree (Venuti): the squared distance of the translation
    from the target culture. A foreignizing translation retains the alien
    character of the source. -/
noncomputable def foreignization (τ : I → I) (source targetCulture : I) : ℝ :=
  squaredDistance (τ source) targetCulture

/-- A translation is **domesticating** if it resonates MORE with the target
    culture than the untranslated source does. -/
def isDomesticating (τ : I → I) (source targetCulture : I) : Prop :=
  domestication τ source targetCulture > resonanceStrength source targetCulture

/-- **Retranslation**: applying a translation twice. Each retranslation
    drifts further from the source — the "telephone game" of translation. -/
def retranslate (τ : I → I) (source : I) : I := τ (τ source)

/-- **Normalized fidelity**: the squared cosine similarity between source
    and translation, ranging in [0, 1]. -/
noncomputable def normalizedFidelity (τ : I → I) (source : I) : ℝ :=
  normalizedRS source (τ source)

/-! ## §2. Fidelity Theorems -/

/-- **Theorem 1** (Perfect fidelity): A perfect translation achieves
    maximum fidelity — it resonates with the source as strongly as
    the source resonates with itself. -/
theorem perfect_translation_max_fidelity {τ : I → I} {a : I}
    (h : isPerfectTranslation τ a) :
    translationFidelity τ a = resonanceStrength a a := by
  unfold translationFidelity isPerfectTranslation at *
  rw [h]

/-- **Theorem 2** (Perfect translation = zero distance): A perfect translation
    has zero squared distance from the source. -/
theorem perfect_translation_zero_distance {τ : I → I} {a : I}
    (h : isPerfectTranslation τ a) :
    translationDistance τ a = 0 := by
  unfold translationDistance isPerfectTranslation at *
  rw [h]; exact squaredDistance_self a

/-- **Theorem 3** (Cauchy-Schwarz for fidelity): Translation fidelity squared
    is bounded by the product of self-resonances — no translation can resonate
    with its source more than the geometric mean allows. -/
theorem fidelity_cauchy_schwarz (τ : I → I) (a : I) :
    translationFidelity τ a ^ 2 ≤
    resonanceStrength a a * resonanceStrength (τ a) (τ a) := by
  unfold translationFidelity
  rw [sq]
  exact IdeaticSpace2.rs_cauchy_schwarz a (τ a)

/-- **Theorem 4** (Fidelity is non-negative): Resonance can never be negative,
    so fidelity ≥ 0. -/
theorem fidelity_nonneg (τ : I → I) (a : I) :
    translationFidelity τ a ≥ 0 := by
  unfold translationFidelity
  exact IdeaticSpace2.rs_nonneg a (τ a)

/-- **Theorem 5** (Faithful → positive fidelity): A faithful translation
    has strictly positive fidelity, by definition. -/
theorem faithful_positive_fidelity {τ : I → I} {a : I}
    (h : isFaithful τ a) :
    translationFidelity τ a > 0 := h

/-- **Theorem 6** (Identity is faithful): The identity "translation"
    (keeping the source unchanged) is always faithful. -/
theorem identity_is_faithful (a : I) :
    isFaithful (id : I → I) a := by
  unfold isFaithful
  simp [id]
  exact IdeaticSpace2.rs_self_pos a

/-- **Theorem 7** (Identity fidelity): The identity translation achieves
    the source's full self-resonance. -/
theorem identity_fidelity (a : I) :
    translationFidelity (id : I → I) a = resonanceStrength a a := by
  unfold translationFidelity
  simp [id]

/-! ## §3. Benjamin's Pure Language (Das Reine Sprache) -/

/-- **Theorem 8** (Residue non-negativity): The untranslatable residue
    is always non-negative — you can never "over-translate". -/
theorem untranslatable_nonneg (τ : I → I) (a : I) :
    untranslatableResidue τ a ≥ 0 := by
  unfold untranslatableResidue
  exact squaredDistance_nonneg a (τ a)

/-- **Theorem 9** (Perfect translation ↔ zero residue, forward direction):
    Benjamin's impossible dream — a perfect translation leaves no residue. -/
theorem perfect_implies_zero_residue {τ : I → I} {a : I}
    (h : isPerfectTranslation τ a) :
    untranslatableResidue τ a = 0 := by
  unfold untranslatableResidue isPerfectTranslation at *
  rw [h]; exact squaredDistance_self a

/-- **Theorem 10** (Residue decomposition): The untranslatable residue
    equals the sum of self-resonances minus twice the fidelity.
    This connects Benjamin's residue to the translator's concrete choices. -/
theorem residue_eq_self_minus_fidelity (τ : I → I) (a : I) :
    untranslatableResidue τ a =
    resonanceStrength a a + resonanceStrength (τ a) (τ a) -
    2 * translationFidelity τ a := by
  unfold untranslatableResidue translationFidelity squaredDistance
  ring

/-- **Theorem 11** (Faithful implies bounded residue): If a translation is
    faithful, the untranslatable residue is strictly less than the sum
    of self-resonances — faithfulness constrains the residue. -/
theorem faithful_implies_bounded_residue {τ : I → I} {a : I}
    (h : isFaithful τ a) :
    untranslatableResidue τ a <
    resonanceStrength a a + resonanceStrength (τ a) (τ a) := by
  unfold untranslatableResidue squaredDistance isFaithful at *
  linarith

/-- **Theorem 12** (Fidelity symmetry): Resonance between source and
    translation equals resonance between translation and source —
    Derrida's point that translation is a two-way relationship. -/
theorem fidelity_symm (τ : I → I) (a : I) :
    translationFidelity τ a = resonanceStrength (τ a) a := by
  unfold translationFidelity
  exact IdeaticSpace2.rs_symm a (τ a)

/-- **Theorem 13** (Distance symmetry): The residue is symmetric —
    the distance from source to translation equals the distance from
    translation to source. -/
theorem residue_symm (τ : I → I) (a : I) :
    untranslatableResidue τ a = squaredDistance (τ a) a := by
  unfold untranslatableResidue
  exact squaredDistance_symm a (τ a)

/-! ## §4. Composition-Preserving Translations (Structural Fidelity) -/

/-- **Theorem 14** (Identity preserves composition): The identity function
    is trivially composition-preserving. -/
theorem identity_preserves_composition :
    preservesComposition (id : I → I) := by
  intro a b; rfl

/-- **Theorem 15** (Composition of preserving maps): If τ₁ and τ₂ each
    preserve composition, so does τ₂ ∘ τ₁. Translation can be chained. -/
theorem composition_of_preserving {τ₁ τ₂ : I → I}
    (h₁ : preservesComposition τ₁) (h₂ : preservesComposition τ₂) :
    preservesComposition (τ₂ ∘ τ₁) := by
  intro a b
  simp [Function.comp]
  rw [h₁ a b, h₂ (τ₁ a) (τ₁ b)]

/-- **Theorem 16** (Preserving map → structural resonance): A composition-
    preserving translation lets us rewrite resonance of composed images. -/
theorem preserving_translation_rs {τ : I → I} (hτ : preservesComposition τ)
    (a b c : I) :
    resonanceStrength (τ (compose a b)) c =
    resonanceStrength (compose (τ a) (τ b)) c := by
  rw [hτ a b]

/-- **Theorem 17** (Preserving fidelity of composition): When τ preserves
    composition, fidelity of a composed idea equals resonance between
    the composition and the translated composition. -/
theorem preserving_fidelity_compose {τ : I → I} (hτ : preservesComposition τ)
    (a b : I) :
    translationFidelity τ (compose a b) =
    resonanceStrength (compose a b) (compose (τ a) (τ b)) := by
  unfold translationFidelity
  rw [hτ a b]

/-- **Theorem 18** (Preserving map enriches): A composition-preserving
    translation of a composed idea is at least as "weighty" as either
    component's translation. -/
theorem preserving_compose_enriches {τ : I → I} (hτ : preservesComposition τ)
    (a b : I) :
    resonanceStrength (τ (compose a b)) (τ (compose a b)) ≥
    resonanceStrength (τ a) (τ a) := by
  rw [hτ a b]
  exact rs_compose_self_right (τ a) (τ b)

/-! ## §5. Venuti: Foreignization vs Domestication -/

/-- **Theorem 19** (Domestication of identity): The identity "translation"
    domesticates to exactly the source's natural resonance with the
    target culture. -/
theorem domestication_of_identity (source targetCulture : I) :
    domestication (id : I → I) source targetCulture =
    resonanceStrength source targetCulture := by
  unfold domestication; simp [id]

/-- **Theorem 20** (Foreignization is non-negative): The foreignization
    degree is always ≥ 0 — every translation has some distance from
    the target culture. -/
theorem foreignization_nonneg (τ : I → I) (source targetCulture : I) :
    foreignization τ source targetCulture ≥ 0 := by
  unfold foreignization
  exact squaredDistance_nonneg (τ source) targetCulture

/-- **Theorem 21** (Domesticating → stronger resonance): A domesticating
    translation, by definition, resonates more with the target culture
    than the raw source does. -/
theorem domesticating_increases_resonance {τ : I → I} {source tc : I}
    (h : isDomesticating τ source tc) :
    domestication τ source tc > resonanceStrength source tc := h

/-- **Theorem 22** (Domestication is non-negative): Resonance with the
    target culture is always non-negative. -/
theorem domestication_nonneg (τ : I → I) (source targetCulture : I) :
    domestication τ source targetCulture ≥ 0 := by
  unfold domestication
  exact IdeaticSpace2.rs_nonneg (τ source) targetCulture

/-- **Theorem 23** (Identity is never domesticating): The identity
    translation cannot domesticate — it leaves resonance unchanged,
    so it cannot strictly increase it. -/
theorem identity_not_domesticating (source tc : I) :
    ¬isDomesticating (id : I → I) source tc := by
  unfold isDomesticating domestication
  simp [id]

/-- **Theorem 24** (Domestication bounded by Cauchy-Schwarz): The
    domestication degree squared is bounded by the product of
    self-resonances — a fundamental limit on cultural assimilation. -/
theorem domestication_cauchy_schwarz (τ : I → I) (source tc : I) :
    domestication τ source tc ^ 2 ≤
    resonanceStrength (τ source) (τ source) * resonanceStrength tc tc := by
  unfold domestication
  rw [sq]
  exact IdeaticSpace2.rs_cauchy_schwarz (τ source) tc

/-! ## §6. Retranslation and Iterated Translation -/

set_option linter.unusedSectionVars false in
/-- **Theorem 25** (Identity retranslation): Retranslating with the
    identity yields the source unchanged. -/
theorem identity_retranslation (source : I) :
    retranslate (id : I → I) source = source := by
  unfold retranslate; rfl

set_option linter.unusedSectionVars false in
/-- **Theorem 26** (Perfect retranslation): If τ is perfect on a,
    then retranslating a also yields a. -/
theorem perfect_retranslation {τ : I → I} {a : I}
    (h : isPerfectTranslation τ a) :
    retranslate τ a = a := by
  unfold retranslate isPerfectTranslation at *
  rw [h, h]

/-- **Theorem 27** (Retranslation fidelity): The fidelity of a
    double translation equals rs(source, τ(τ source)). -/
theorem retranslation_fidelity (τ : I → I) (source : I) :
    resonanceStrength source (retranslate τ source) =
    translationFidelity (fun x => τ (τ x)) source := by
  unfold retranslate translationFidelity
  rfl

/-- **Theorem 28** (Retranslation distance non-negative): The squared
    distance from source to retranslation is non-negative. -/
theorem retranslation_distance_nonneg (τ : I → I) (source : I) :
    squaredDistance source (retranslate τ source) ≥ 0 := by
  exact squaredDistance_nonneg source (retranslate τ source)

/-! ## §7. Translator's Voice and Normalized Fidelity -/

/-- **Theorem 29** (Identity has no voice): The identity translation
    adds nothing — the translator's voice is zero. -/
theorem translatorVoice_identity (a : I) :
    translatorVoice (id : I → I) a = 0 := by
  unfold translatorVoice; simp [id]

/-- **Theorem 30** (Normalized fidelity ≤ 1): No translation can have
    normalized fidelity exceeding 1 — a ceiling on semantic overlap. -/
theorem normalizedFidelity_le_one (τ : I → I) (a : I) :
    normalizedFidelity τ a ≤ 1 := by
  unfold normalizedFidelity
  exact normalizedRS_le_one a (τ a)

/-- **Theorem 31** (Normalized fidelity ≥ 0): Normalized fidelity is
    non-negative. -/
theorem normalizedFidelity_nonneg (τ : I → I) (a : I) :
    normalizedFidelity τ a ≥ 0 := by
  unfold normalizedFidelity
  exact normalizedRS_nonneg a (τ a)

/-- **Theorem 32** (Identity has perfect normalized fidelity): The identity
    translation achieves normalized fidelity = 1. -/
theorem normalizedFidelity_identity (a : I) :
    normalizedFidelity (id : I → I) a = 1 := by
  unfold normalizedFidelity
  simp [id]
  exact normalizedRS_self a

/-! ## §8. Composing Source with Translation (Derrida's Supplement) -/

/-- **Theorem 33** (Supplementation enriches): Composing the source with
    its translation always enriches self-resonance — Derrida's insight
    that translation is a **supplement** that adds to the original. -/
theorem supplement_enriches (τ : I → I) (source : I) :
    resonanceStrength (compose source (τ source)) (compose source (τ source)) ≥
    resonanceStrength source source := by
  exact rs_compose_self_right source (τ source)

/-- **Theorem 34** (Supplementation absorbs translation): The supplement
    also absorbs the translation's weight. -/
theorem supplement_absorbs_translation (τ : I → I) (source : I) :
    resonanceStrength (compose source (τ source)) (compose source (τ source)) ≥
    resonanceStrength (τ source) (τ source) := by
  exact rs_compose_self_left (τ source) source

/-- **Theorem 35** (Supplementation depth bound): The depth of the
    supplemented idea is bounded. -/
theorem supplement_depth_bound (τ : I → I) (source : I) :
    depth (compose source (τ source)) ≤ depth source + depth (τ source) := by
  exact IdeaticSpace2.depth_subadditive source (τ source)

/-- **Theorem 36** (Shared context translation): When two ideas are placed
    in the same translational context (composed with the same element on
    the right), their mutual resonance is preserved — Even-Zohar's insight
    that translations within a polysystem maintain relational structure. -/
theorem shared_context_preserves (a b context : I) :
    resonanceStrength (compose a context) (compose b context) ≥
    resonanceStrength a b := by
  exact IdeaticSpace2.rs_compose_right_mono a b context

/-! ## §9. Additional Translation Theorems -/

/-- **Theorem 37** (Shared translation preserves resonance): If two ideas
    are translated by the same map, their mutual resonance is preserved.
    This formalizes the idea that a consistent translation practice
    maintains the "system" of relationships (Even-Zohar). -/
theorem shared_translation_preserves_resonance (τ : I → I) (a b context : I) :
    resonanceStrength (compose (τ a) context) (compose (τ b) context) ≥
    resonanceStrength (τ a) (τ b) := by
  exact IdeaticSpace2.rs_compose_right_mono (τ a) (τ b) context

set_option linter.unusedSectionVars false in
/-- **Theorem 38** (Translation composition is associative): Chaining
    three translations respects composition order. -/
theorem translation_chain_assoc (τ₁ τ₂ τ₃ : I → I) (a : I) :
    (τ₃ ∘ τ₂ ∘ τ₁) a = τ₃ (τ₂ (τ₁ a)) := rfl

/-- **Theorem 39** (Voice of perfect translation is zero): A perfect
    translation adds nothing — the translator's voice vanishes. -/
theorem perfect_translation_zero_voice {τ : I → I} {a : I}
    (h : isPerfectTranslation τ a) :
    translatorVoice τ a = 0 := by
  unfold translatorVoice isPerfectTranslation at *
  rw [h]; ring

/-- **Theorem 40** (Fidelity–distance duality): High fidelity implies
    low residue — these measure the same phenomenon from opposite sides.
    Specifically: residue = rs(a,a) + rs(τa,τa) - 2·fidelity. -/
theorem fidelity_distance_duality (τ : I → I) (a : I) :
    translationDistance τ a + 2 * translationFidelity τ a =
    resonanceStrength a a + resonanceStrength (τ a) (τ a) := by
  unfold translationDistance translationFidelity squaredDistance
  ring

end IDT2.Translation
