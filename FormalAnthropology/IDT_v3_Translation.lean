import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Translation Theory

Translation between languages — or between any two "ideatic systems" —
is a morphism between ideatic spaces. Perfect translation preserves
all resonance structure; imperfect translation preserves some but
introduces "translation emergence" (the untranslatable residue).

## The Key Insight

A translation map φ : I → J between ideatic spaces (I, rs_I) and (J, rs_J)
satisfies rs_J(φ(a), φ(b)) ≈ rs_I(a, b). The gap
  δ(a, b) := rs_J(φ(a), φ(b)) - rs_I(a, b)
is the "translation distortion" — positive when the target language
AMPLIFIES a resonance, negative when it attenuates.

Since we work within a SINGLE ideatic space (the v3 axioms give us one),
we model translation as an endofunction φ : I → I that "reframes" ideas.

## NO SORRIES
-/

namespace IDT3

section Translation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-! ## §1. Translation Maps -/

-- A translation map is any function I → I. The interesting properties
-- come from what it preserves.

/-- Translation fidelity: how much resonance structure φ preserves
    for a particular pair. -/
noncomputable def translationFidelity (φ : I → I) (a b : I) : ℝ :=
  rs (φ a) (φ b) - rs a b

/-- A faithful translation preserves all resonances exactly. -/
def faithful (φ : I → I) : Prop :=
  ∀ a b, rs (φ a) (φ b) = rs a b

/-- Faithful translations have zero distortion everywhere. -/
theorem faithful_zero_fidelity (φ : I → I) (h : faithful φ) (a b : I) :
    translationFidelity φ a b = 0 := by
  unfold translationFidelity; linarith [h a b]

/-- A void-preserving translation maps silence to silence. -/
def voidPreserving (φ : I → I) : Prop := φ void = void

/-- The identity is always a faithful, void-preserving translation. -/
theorem id_faithful : faithful (id : I → I) :=
  fun _ _ => rfl

theorem id_voidPreserving : voidPreserving (id : I → I) := rfl

/-- Composition of faithful translations is faithful. -/
theorem faithful_comp (φ ψ : I → I) (hφ : faithful φ) (hψ : faithful ψ) :
    faithful (φ ∘ ψ) := by
  intro a b
  simp only [Function.comp]
  calc rs (φ (ψ a)) (φ (ψ b)) = rs (ψ a) (ψ b) := hφ (ψ a) (ψ b)
    _ = rs a b := hψ a b

/-! ## §2. Translation Distortion -/

/-- Total self-distortion: how much translation changes self-resonance. -/
noncomputable def selfDistortion (φ : I → I) (a : I) : ℝ :=
  rs (φ a) (φ a) - rs a a

/-- A faithful translation has zero self-distortion. -/
theorem faithful_zero_selfDistortion (φ : I → I) (h : faithful φ) (a : I) :
    selfDistortion φ a = 0 := by
  unfold selfDistortion; linarith [h a a]

/-- An amplifying translation increases self-resonance. -/
def amplifying (φ : I → I) (a : I) : Prop := selfDistortion φ a > 0

/-- An attenuating translation decreases self-resonance. -/
def attenuating (φ : I → I) (a : I) : Prop := selfDistortion φ a < 0

/-- Identity never amplifies or attenuates. -/
theorem id_not_amplifying (a : I) : ¬amplifying (id : I → I) a := by
  unfold amplifying selfDistortion; simp

theorem id_not_attenuating (a : I) : ¬attenuating (id : I → I) a := by
  unfold attenuating selfDistortion; simp

/-! ## §3. Compositionality of Translation

The key question: does translation commute with composition?
φ(a ∘ b) vs φ(a) ∘ φ(b) — when these differ, we have
"translation emergence": new meaning that appears IN the translation. -/

/-- A compositional translation commutes with compose. -/
def compositional (φ : I → I) : Prop :=
  ∀ a b, φ (compose a b) = compose (φ a) (φ b)

/-- The translation emergence: the gap between translating a composition
    and composing translations. Measured via resonance against an observer. -/
noncomputable def translationEmergence (φ : I → I) (a b c : I) : ℝ :=
  rs (φ (compose a b)) c - rs (compose (φ a) (φ b)) c

/-- Compositional translations have zero translation emergence. -/
theorem compositional_zero_emergence (φ : I → I) (h : compositional φ)
    (a b c : I) : translationEmergence φ a b c = 0 := by
  unfold translationEmergence; rw [h a b]; ring

/-- Identity is compositional. -/
theorem id_compositional : compositional (id : I → I) := fun _ _ => rfl

/-- Composition of compositional translations is compositional. -/
theorem compositional_comp (φ ψ : I → I) (hφ : compositional φ)
    (hψ : compositional ψ) : compositional (φ ∘ ψ) := by
  intro a b
  simp [Function.comp]
  rw [hψ a b, hφ (ψ a) (ψ b)]

/-! ## §4. Synonymy and Translation

Two translations are synonymous if they produce the same idea
(same emergence pattern) for every input. -/

/-- Two translations are equivalent if they preserve all resonances identically. -/
def translationEquiv (φ ψ : I → I) : Prop :=
  ∀ a b, rs (φ a) b = rs (ψ a) b

theorem translationEquiv_refl (φ : I → I) : translationEquiv φ φ :=
  fun _ _ => rfl

theorem translationEquiv_symm (φ ψ : I → I) (h : translationEquiv φ ψ) :
    translationEquiv ψ φ :=
  fun a b => (h a b).symm

theorem translationEquiv_trans (φ ψ χ : I → I)
    (h1 : translationEquiv φ ψ) (h2 : translationEquiv ψ χ) :
    translationEquiv φ χ :=
  fun a b => (h1 a b).trans (h2 a b)

/-- If two translations are equivalent, they have the same left-fidelity. -/
theorem translationEquiv_leftFidelity (φ ψ : I → I) (h : translationEquiv φ ψ)
    (a : I) (c : I) : rs (φ a) c = rs (ψ a) c :=
  h a c

/-- Stronger notion: two translations are fully equivalent. -/
def fullTranslationEquiv (φ ψ : I → I) : Prop :=
  (∀ a b, rs (φ a) b = rs (ψ a) b) ∧ (∀ a b, rs a (φ b) = rs a (ψ b))

theorem fullTranslationEquiv_fidelity (φ ψ : I → I) (h : fullTranslationEquiv φ ψ)
    (a b : I) : translationFidelity φ a b = translationFidelity ψ a b := by
  unfold translationFidelity
  have h1 := h.1 a (φ b)
  have h2 := h.2 (ψ a) b
  linarith

/-! ## §5. The Untranslatable

Some ideas resist translation — their emergence pattern changes
fundamentally under any non-identity translation. -/

/-- An idea is translation-invariant under φ if φ(a) has the same
    emergence pattern as a. -/
def translationInvariant (φ : I → I) (a : I) : Prop :=
  ∀ c d, emergence (φ a) c d = emergence a c d

-- An idea is untranslatable if it is not translation-invariant
-- under any non-identity translation φ.
-- This is too strong to formalize directly; instead we measure degree.

/-- The untranslatability measure: maximum emergence change. -/
noncomputable def emergenceShift (φ : I → I) (a c d : I) : ℝ :=
  emergence (φ a) c d - emergence a c d

/-- Translation-invariant ideas have zero emergence shift. -/
theorem translationInvariant_zero_shift (φ : I → I) (a : I)
    (h : translationInvariant φ a) (c d : I) :
    emergenceShift φ a c d = 0 := by
  unfold emergenceShift; linarith [h c d]

/-- Identity preserves all ideas. -/
theorem id_translationInvariant (a : I) :
    translationInvariant (id : I → I) a :=
  fun _ _ => rfl

/-- Void is invariant under any void-preserving translation. -/
theorem void_invariant (φ : I → I) (h : voidPreserving φ) :
    translationInvariant φ (void : I) := by
  intro c d
  unfold emergence
  rw [h]

/-! ## §6. Back-Translation and Round-Trip Fidelity -/

/-- Round-trip distortion: translate and translate back. -/
noncomputable def roundTripDistortion (φ ψ : I → I) (a b : I) : ℝ :=
  rs (ψ (φ a)) (ψ (φ b)) - rs a b

/-- If both φ and ψ are faithful, round-trip has zero distortion. -/
theorem faithful_roundTrip (φ ψ : I → I) (hφ : faithful φ) (hψ : faithful ψ)
    (a b : I) : roundTripDistortion φ ψ a b = 0 := by
  unfold roundTripDistortion
  have h1 := hψ (φ a) (φ b)
  have h2 := hφ a b
  linarith

/-- A literal translation maps void to void and is compositional. -/
def literal (φ : I → I) : Prop :=
  voidPreserving φ ∧ compositional φ

/-- Identity is literal. -/
theorem id_literal : literal (id : I → I) :=
  ⟨id_voidPreserving, id_compositional⟩

/-- Composition of literal translations is literal. -/
theorem literal_comp (φ ψ : I → I) (hφ : literal φ) (hψ : literal ψ) :
    literal (φ ∘ ψ) := by
  refine ⟨?_, compositional_comp φ ψ hφ.2 hψ.2⟩
  show (φ ∘ ψ) void = void
  change φ (ψ void) = void
  rw [hψ.1, hφ.1]

end Translation

/-! ## §7. Translation Chains — Benjamin's "Task of the Translator"

Walter Benjamin argued that translation reveals the "pure language"
(reine Sprache) latent in all languages. A chain of translations
A → B → C converges toward this pure language. We formalize this
as the composition of translation maps and study the distortion
accumulation along chains. -/

section TranslationChains
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A translation chain is the composition of two translation maps.
    φ translates from A to B, ψ from B to C; the chain is ψ ∘ φ. -/
noncomputable def chainDistortion (φ ψ : I → I) (a b : I) : ℝ :=
  translationFidelity (ψ ∘ φ) a b

/-- Chain distortion decomposes into two layers of fidelity.
    Benjamin: every retranslation adds its own interpretive layer. -/
theorem chain_distortion_decompose (φ ψ : I → I) (a b : I) :
    chainDistortion φ ψ a b =
    translationFidelity ψ (φ a) (φ b) + translationFidelity φ a b := by
  unfold chainDistortion translationFidelity
  simp only [Function.comp]
  ring

/-- If the first translation is faithful, chain distortion equals
    the second translation's distortion on the translated pair. -/
theorem chain_faithful_first (φ ψ : I → I) (hφ : faithful φ) (a b : I) :
    chainDistortion φ ψ a b = translationFidelity ψ (φ a) (φ b) := by
  rw [chain_distortion_decompose]
  have h := faithful_zero_fidelity φ hφ a b
  linarith

/-- If the second translation is faithful, chain distortion equals
    the first translation's distortion. -/
theorem chain_faithful_second (φ ψ : I → I) (hψ : faithful ψ) (a b : I) :
    chainDistortion φ ψ a b = translationFidelity φ a b := by
  rw [chain_distortion_decompose]
  have h := faithful_zero_fidelity ψ hψ (φ a) (φ b)
  linarith

/-- A three-link translation chain: φ → ψ → χ.
    Derrida's point: each link adds its own "relevant" distortion. -/
noncomputable def tripleChainDistortion (φ ψ χ : I → I) (a b : I) : ℝ :=
  translationFidelity (χ ∘ ψ ∘ φ) a b

/-- Triple chain distortion decomposes into three layers.
    Venuti: translation is always a chain of interpretive acts. -/
theorem triple_chain_decompose (φ ψ χ : I → I) (a b : I) :
    tripleChainDistortion φ ψ χ a b =
    translationFidelity χ (ψ (φ a)) (ψ (φ b)) +
    translationFidelity ψ (φ a) (φ b) +
    translationFidelity φ a b := by
  unfold tripleChainDistortion translationFidelity
  simp only [Function.comp]
  ring

/-- Faithful chains have zero total distortion.
    Benjamin's reine Sprache: the "perfect" translation chain. -/
theorem faithful_chain_zero (φ ψ : I → I) (hφ : faithful φ) (hψ : faithful ψ)
    (a b : I) : chainDistortion φ ψ a b = 0 := by
  rw [chain_distortion_decompose]
  have h1 := faithful_zero_fidelity φ hφ a b
  have h2 := faithful_zero_fidelity ψ hψ (φ a) (φ b)
  linarith

/-- Composing a chain with another faithful translation does not change
    the chain's total distortion. -/
theorem chain_absorb_faithful (φ ψ χ : I → I)
    (hχ : faithful χ) (a b : I) :
    tripleChainDistortion φ ψ χ a b = chainDistortion φ ψ a b := by
  rw [triple_chain_decompose, chain_distortion_decompose]
  have h := faithful_zero_fidelity χ hχ (ψ (φ a)) (ψ (φ b))
  linarith

end TranslationChains

/-! ## §8. Round-Trip Fidelity and Back-Translation

Back-translation (translating from B back to A) is a classical test
of translation quality. Perfect round-trip fidelity means the
composed map φ⁻¹ ∘ φ preserves all resonances — but this is rare.
The "round-trip residue" captures what is lost in translation. -/

section RoundTrip
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Round-trip self-distortion: how much self-resonance changes
    after a round trip through φ and back through ψ. -/
noncomputable def roundTripSelfDistortion (φ ψ : I → I) (a : I) : ℝ :=
  rs (ψ (φ a)) (ψ (φ a)) - rs a a

/-- A faithful round trip preserves self-resonance. -/
theorem faithful_roundTrip_self (φ ψ : I → I) (hφ : faithful φ)
    (hψ : faithful ψ) (a : I) :
    roundTripSelfDistortion φ ψ a = 0 := by
  unfold roundTripSelfDistortion
  have h1 := hψ (φ a) (φ a)
  have h2 := hφ a a
  linarith

/-- Round-trip distortion is a chain distortion.
    Formalizes: back-translation is just another translation chain. -/
theorem roundTrip_is_chain (φ ψ : I → I) (a b : I) :
    roundTripDistortion φ ψ a b = chainDistortion φ ψ a b := by
  unfold roundTripDistortion chainDistortion translationFidelity
  simp [Function.comp]

/-- The round-trip residue: the emergence shift created by going
    there and back. Captures what is "lost in translation." -/
noncomputable def roundTripEmergenceShift (φ ψ : I → I) (a c d : I) : ℝ :=
  emergence (ψ (φ a)) c d - emergence a c d

/-- Identity round-trip (φ = ψ = id) has zero emergence shift. -/
theorem id_roundTrip_emergence (a c d : I) :
    roundTripEmergenceShift (id : I → I) (id : I → I) a c d = 0 := by
  unfold roundTripEmergenceShift; simp

/-- Self-distortion is non-negative for any non-void idea under the identity
    back-translation: id-round-trip trivially preserves everything. -/
theorem id_roundTrip_selfDistortion (a : I) :
    roundTripSelfDistortion (id : I → I) (id : I → I) a = 0 := by
  unfold roundTripSelfDistortion; simp

end RoundTrip

/-! ## §9. Domestication vs. Foreignization — Venuti's Dichotomy

Lawrence Venuti's central distinction: a domesticating translation
makes the foreign text conform to target-language norms (reducing
emergence), while a foreignizing translation preserves the alien
emergence patterns. We formalize this via emergence preservation. -/

section DomesticationForeignization
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A domesticating translation reduces emergence: it flattens
    the compositional surprises of the source. -/
def domesticating (φ : I → I) (a b c : I) : Prop :=
  |translationEmergence φ a b c| ≤ |emergence a b c|

/-- A foreignizing translation amplifies or preserves emergence:
    it brings the source's compositional surprises into the target. -/
def foreignizing (φ : I → I) (a b c : I) : Prop :=
  |translationEmergence φ a b c| ≥ |emergence a b c|

/-- Identity is trivially domesticating: it has zero translation emergence,
    which is ≤ any absolute value. -/
theorem id_domesticating (a b c : I) :
    domesticating (id : I → I) a b c := by
  unfold domesticating translationEmergence; simp

/-- Identity is foreignizing only when emergence vanishes.
    The zero-degree translation preserves nothing beyond the trivial. -/
theorem id_foreignizing_of_zero_emergence (a b c : I)
    (h : emergence a b c = 0) :
    foreignizing (id : I → I) a b c := by
  unfold foreignizing translationEmergence
  simp only [id]; rw [sub_self]; simp [h]

/-- A compositional translation is always domesticating (zero emergence gap). -/
theorem compositional_domesticating (φ : I → I) (h : compositional φ)
    (a b c : I) : domesticating φ a b c := by
  unfold domesticating
  rw [compositional_zero_emergence φ h a b c]
  simp

/-- Domestication strength: how much emergence is lost. -/
noncomputable def domesticationDegree (φ : I → I) (a b c : I) : ℝ :=
  |emergence a b c| - |translationEmergence φ a b c|

/-- Foreignization strength: how much extra emergence the translation adds. -/
noncomputable def foreignizationDegree (φ : I → I) (a b c : I) : ℝ :=
  |translationEmergence φ a b c| - |emergence a b c|

/-- Domestication and foreignization degrees sum to zero.
    Venuti: these are two sides of the same coin. -/
theorem domestication_foreignization_dual (φ : I → I) (a b c : I) :
    domesticationDegree φ a b c + foreignizationDegree φ a b c = 0 := by
  unfold domesticationDegree foreignizationDegree; ring

end DomesticationForeignization

/-! ## §10. Nida's Dynamic vs. Formal Equivalence

Eugene Nida distinguished:
- Formal equivalence: preserving the structure (compositionality)
- Dynamic equivalence: preserving the effect (resonance with audience)

We formalize: formal = compositional + faithful; dynamic = preserving
resonance with a specific observer. -/

section NidaEquivalence
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Formal equivalence: the translation is both faithful and compositional.
    Nida: "word-for-word" translation that preserves linguistic form. -/
def formalEquivalence (φ : I → I) : Prop :=
  faithful φ ∧ compositional φ

/-- Dynamic equivalence relative to an observer c: the translation preserves
    resonance with c. Nida: "thought-for-thought" — same effect on the reader. -/
def dynamicEquivalence (φ : I → I) (c : I) : Prop :=
  ∀ a, rs (φ a) c = rs a c

/-- If φ is faithful AND fixes the observer c, then φ achieves
    dynamic equivalence at c. The fixed-point condition is necessary:
    faithful alone maps rs(φ a, φ c) = rs(a, c), not rs(φ a, c) = rs(a, c). -/
theorem formal_dynamic_at_fixed (φ : I → I) (h : formalEquivalence φ)
    (c : I) (hc : φ c = c) : dynamicEquivalence φ c := by
  intro a; have hf := h.1 a c; rw [hc] at hf; exact hf

/-- Identity achieves formal equivalence. -/
theorem id_formalEquivalence : formalEquivalence (id : I → I) :=
  ⟨id_faithful, id_compositional⟩

/-- Identity achieves dynamic equivalence for all observers. -/
theorem id_dynamicEquivalence (c : I) : dynamicEquivalence (id : I → I) c :=
  fun _ => rfl

/-- A translation is dynamically void-equivalent if it preserves
    resonance with void (trivially true). -/
theorem dynamic_void_trivial (φ : I → I) :
    dynamicEquivalence φ (void : I) := by
  intro a; simp [rs_void_right']

/-- Dynamic equivalence composes: if φ is dynamic-equivalent for c
    and ψ is dynamic-equivalent for c, then ψ ∘ φ is too. -/
theorem dynamic_equiv_comp (φ ψ : I → I) (c : I)
    (hφ : dynamicEquivalence φ c) (hψ : dynamicEquivalence ψ c) :
    dynamicEquivalence (ψ ∘ φ) c := by
  intro a; simp [Function.comp]; rw [hψ (φ a), hφ a]

/-- Dynamic equivalence with the void observer is trivially satisfied.
    Nida: an audience of "no one" can't tell translations apart. -/
theorem dynamic_equiv_void_observer (φ : I → I) :
    dynamicEquivalence φ (void : I) :=
  dynamic_void_trivial φ

end NidaEquivalence

/-! ## §11. The Untranslatability Spectrum

Not all ideas can be faithfully translated. The "untranslatability"
of an idea under φ measures how much its entire resonance profile
shifts. This connects to Cassin's "Dictionary of Untranslatables"
and the Sapir-Whorf hypothesis. -/

section Untranslatability
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Pairwise untranslatability: how much a specific resonance pair
    changes under translation. -/
noncomputable def pairwiseUntranslatability (φ : I → I) (a b : I) : ℝ :=
  |translationFidelity φ a b|

/-- Faithful translations have zero pairwise untranslatability. -/
theorem faithful_zero_untranslatability (φ : I → I) (h : faithful φ)
    (a b : I) : pairwiseUntranslatability φ a b = 0 := by
  unfold pairwiseUntranslatability
  rw [faithful_zero_fidelity φ h a b]; simp

/-- Identity has zero pairwise untranslatability. -/
theorem id_zero_untranslatability (a b : I) :
    pairwiseUntranslatability (id : I → I) a b = 0 :=
  faithful_zero_untranslatability id id_faithful a b

/-- Void-pair untranslatability is zero for void-preserving translations. -/
theorem void_pair_untranslatability (φ : I → I) (hφ : voidPreserving φ) (a : I) :
    pairwiseUntranslatability φ a void = 0 := by
  unfold pairwiseUntranslatability translationFidelity
  rw [rs_void_right', hφ, rs_void_right']; simp

/-- Emergence untranslatability: how much the emergence pattern of
    an idea changes under translation. Formalizes Sapir-Whorf:
    different languages structure thought differently. -/
noncomputable def emergenceUntranslatability (φ : I → I) (a c d : I) : ℝ :=
  |emergenceShift φ a c d|

/-- Identity has zero emergence untranslatability (trivially). -/
theorem id_zero_emergence_untranslatable (a c d : I) :
    emergenceUntranslatability (id : I → I) a c d = 0 := by
  unfold emergenceUntranslatability emergenceShift; simp

/-- Translation-invariant ideas have zero emergence untranslatability. -/
theorem invariant_zero_emergence_untranslatable (φ : I → I) (a : I)
    (h : translationInvariant φ a) (c d : I) :
    emergenceUntranslatability φ a c d = 0 := by
  unfold emergenceUntranslatability
  rw [translationInvariant_zero_shift φ a h c d]; simp

end Untranslatability

/-! ## §12. Pidgins, Creoles, and Partial Translation

A pidgin is a simplified contact language — a "partial translation"
that loses emergence structure. A creole is what happens when a
pidgin becomes a full language — emergence returns. We formalize
pidginization as emergence-flattening translation and creolization
as emergence restoration. -/

section PidginCreole
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A pidginizing translation flattens ALL emergence: it is compositional.
    Pidgins lack the rich metaphorical structure of full languages. -/
def pidginizing (φ : I → I) : Prop := compositional φ

/-- A pidginizing translation has zero translation emergence everywhere. -/
theorem pidginizing_zero_emergence (φ : I → I) (h : pidginizing φ)
    (a b c : I) : translationEmergence φ a b c = 0 :=
  compositional_zero_emergence φ h a b c

/-- Pidginization is preserved under composition.
    Two rounds of pidginization remain pidginized. -/
theorem pidginizing_comp (φ ψ : I → I) (hφ : pidginizing φ)
    (hψ : pidginizing ψ) : pidginizing (φ ∘ ψ) :=
  compositional_comp φ ψ hφ hψ

/-- The "creolization gap": how much emergence a translation adds
    back beyond what a pidginizing baseline would give.
    Positive means the translation is RICHER than a pidgin. -/
noncomputable def creolizationGap (φ : I → I) (a b c : I) : ℝ :=
  translationEmergence φ a b c

/-- The creolization gap of a pidginizing translation is zero.
    A pidgin has nothing to creolize. -/
theorem pidgin_zero_creolization (φ : I → I) (h : pidginizing φ)
    (a b c : I) : creolizationGap φ a b c = 0 :=
  pidginizing_zero_emergence φ h a b c

/-- The identity (speaking one's own language) has zero creolization gap. -/
theorem id_zero_creolization (a b c : I) :
    creolizationGap (id : I → I) a b c = 0 := by
  unfold creolizationGap translationEmergence; simp

end PidginCreole

/-! ## §13. Code-Switching as Alternating Translation

Code-switching — alternating between languages within a single
discourse — can be modeled as alternating application of
translation maps. The emergence of code-switching reveals
the creative potential of multilingual composition. -/

section CodeSwitching
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Code-switched composition: φ is applied to a, identity to b.
    Models saying a in language-φ and b in the base language. -/
noncomputable def codeSwitchedCompose (φ : I → I) (a b : I) : I :=
  compose (φ a) b

/-- Code-switching emergence: the surplus resonance created by
    composing across languages. -/
noncomputable def codeSwitchEmergence (φ : I → I) (a b c : I) : ℝ :=
  rs (codeSwitchedCompose φ a b) c - rs (φ a) c - rs b c

/-- Code-switching with identity is just composition. -/
theorem codeSwitch_id (a b : I) :
    codeSwitchedCompose (id : I → I) a b = compose a b := rfl

/-- Code-switching emergence with identity equals standard emergence. -/
theorem codeSwitchEmergence_id (a b c : I) :
    codeSwitchEmergence (id : I → I) a b c = emergence a b c := by
  unfold codeSwitchEmergence codeSwitchedCompose emergence; simp

/-- Code-switching void into any language produces just the continuation. -/
theorem codeSwitch_void (φ : I → I) (hφ : voidPreserving φ) (b : I) :
    codeSwitchedCompose φ void b = b := by
  unfold codeSwitchedCompose; rw [hφ]; simp

/-- Code-switching anything with void just translates. -/
theorem codeSwitch_void_right (φ : I → I) (a : I) :
    codeSwitchedCompose φ a void = φ a := by
  unfold codeSwitchedCompose; simp

/-- Alternating code-switch: φ on a, ψ on b. Models switching between
    two non-native languages. -/
noncomputable def doubleCodeSwitch (φ ψ : I → I) (a b : I) : I :=
  compose (φ a) (ψ b)

/-- Double code-switch with both identities is standard composition. -/
theorem doubleCodeSwitch_id (a b : I) :
    doubleCodeSwitch (id : I → I) (id : I → I) a b = compose a b := rfl

/-- Double code-switch void left with void-preserving φ. -/
theorem doubleCodeSwitch_void_left (φ ψ : I → I) (hφ : voidPreserving φ)
    (b : I) : doubleCodeSwitch φ ψ void b = ψ b := by
  unfold doubleCodeSwitch; rw [hφ]; simp

/-- Double code-switch void right with void-preserving ψ. -/
theorem doubleCodeSwitch_void_right (φ ψ : I → I) (hψ : voidPreserving ψ)
    (a : I) : doubleCodeSwitch φ ψ a void = φ a := by
  unfold doubleCodeSwitch; rw [hψ]; simp

end CodeSwitching

/-! ## §14. Lingua Franca as Shared Projection

A lingua franca L is a common ground — an idea such that translation
into L-composed forms preserves mutual intelligibility. We model this
via a "grounding" composition: project both ideas onto L before
comparing. -/

section LinguaFranca
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Lingua-franca resonance: how much a and b resonate when both are
    "spoken through" the medium L. -/
noncomputable def linguaFrancaRS (L a b : I) : ℝ :=
  rs (compose L a) (compose L b)

/-- Lingua franca resonance with void: silence through any medium
    resonates as just the medium itself. -/
theorem linguaFrancaRS_void_right (L a : I) :
    linguaFrancaRS L a void = rs (compose L a) L := by
  unfold linguaFrancaRS; simp

theorem linguaFrancaRS_void_left (L b : I) :
    linguaFrancaRS L void b = rs L (compose L b) := by
  unfold linguaFrancaRS; simp

/-- Void as lingua franca: communication without medium
    is just direct resonance. -/
theorem void_linguaFranca (a b : I) :
    linguaFrancaRS (void : I) a b = rs a b := by
  unfold linguaFrancaRS; simp

/-- Lingua franca self-resonance is at least the medium's self-resonance.
    Speaking THROUGH a medium always carries the medium's weight. -/
theorem linguaFrancaRS_enriched (L a : I) :
    linguaFrancaRS L a a ≥ rs L L := by
  unfold linguaFrancaRS
  exact compose_enriches' L a

/-- The lingua franca distortion: how much the medium alters resonance. -/
noncomputable def linguaFrancaDistortion (L a b : I) : ℝ :=
  linguaFrancaRS L a b - rs a b

/-- Void lingua franca has zero distortion. -/
theorem void_linguaFranca_distortion (a b : I) :
    linguaFrancaDistortion (void : I) a b = 0 := by
  unfold linguaFrancaDistortion; rw [void_linguaFranca]; ring

end LinguaFranca

/-! ## §15. Sapir-Whorf Hypothesis Formalized

The Sapir-Whorf hypothesis claims that language shapes thought.
In IDT, this means: the ideatic space's resonance structure constrains
which emergence patterns are accessible. A "language" is modeled
as a translation map φ; Sapir-Whorf says different φ's reveal
different emergence patterns. -/

section SapirWhorf
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Two translations are emergence-distinct on a triple (a,b,c) if they
    produce different emergence shifts. Sapir-Whorf: different languages
    structure the "same" content differently. -/
def emergenceDistinct (φ ψ : I → I) (a c d : I) : Prop :=
  emergenceShift φ a c d ≠ emergenceShift ψ a c d

/-- No translation is emergence-distinct from itself. -/
theorem emergenceDistinct_irrefl (φ : I → I) (a c d : I) :
    ¬emergenceDistinct φ φ a c d := by
  unfold emergenceDistinct; simp

/-- Emergence distinctness is symmetric. -/
theorem emergenceDistinct_symm (φ ψ : I → I) (a c d : I)
    (h : emergenceDistinct φ ψ a c d) :
    emergenceDistinct ψ φ a c d := by
  unfold emergenceDistinct at *; exact Ne.symm h

/-- The Whorfian gap: difference in emergence shift between two languages. -/
noncomputable def whorfianGap (φ ψ : I → I) (a c d : I) : ℝ :=
  emergenceShift φ a c d - emergenceShift ψ a c d

/-- Whorfian gap is antisymmetric in the two languages. -/
theorem whorfianGap_antisymm (φ ψ : I → I) (a c d : I) :
    whorfianGap φ ψ a c d = -whorfianGap ψ φ a c d := by
  unfold whorfianGap; ring

/-- Whorfian gap of a language with itself is zero. -/
theorem whorfianGap_self (φ : I → I) (a c d : I) :
    whorfianGap φ φ a c d = 0 := by
  unfold whorfianGap; ring

/-- Whorfian gap decomposes into emergence differences.
    The gap between how φ and ψ see the world. -/
theorem whorfianGap_eq (φ ψ : I → I) (a c d : I) :
    whorfianGap φ ψ a c d =
    emergence (φ a) c d - emergence (ψ a) c d := by
  unfold whorfianGap emergenceShift; ring

/-- Whorfian gap transitivity: the gap φ→χ equals φ→ψ plus ψ→χ. -/
theorem whorfianGap_trans (φ ψ χ : I → I) (a c d : I) :
    whorfianGap φ χ a c d =
    whorfianGap φ ψ a c d + whorfianGap ψ χ a c d := by
  unfold whorfianGap; ring

end SapirWhorf

/-! ## §16. Universal Grammar as Shared Emergence Structure

Chomsky's Universal Grammar hypothesis: all human languages share
a deep structure. In IDT, this means: for certain "core" compositions,
ALL translation maps produce the same emergence. We formalize this
as emergence invariance across all translations. -/

section UniversalGrammar
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An idea triple (a,b,c) is universally grammatical if every
    void-preserving translation produces the same emergence shift. -/
def universallyGrammatical (a c d : I) : Prop :=
  ∀ (φ : I → I), voidPreserving φ → emergenceShift φ a c d = 0

/-- If a is universally grammatical, the Whorfian gap is always zero.
    UG contradicts strong Sapir-Whorf for these triples. -/
theorem ug_zero_whorfian (a c d : I) (h : universallyGrammatical a c d)
    (φ ψ : I → I) (hφ : voidPreserving φ) (hψ : voidPreserving ψ) :
    whorfianGap φ ψ a c d = 0 := by
  unfold whorfianGap; rw [h φ hφ, h ψ hψ]; ring

/-- Void is always universally grammatical: silence needs no grammar. -/
theorem void_universallyGrammatical (c d : I) :
    universallyGrammatical (void : I) c d := by
  intro φ hφ
  unfold emergenceShift emergence
  rw [hφ]; ring

/-- Translation-invariant ideas are universally grammatical (by definition). -/
theorem invariant_universallyGrammatical (a : I) (c d : I)
    (h : ∀ (φ : I → I), voidPreserving φ → translationInvariant φ a) :
    universallyGrammatical a c d := by
  intro φ hφ
  exact translationInvariant_zero_shift φ a (h φ hφ) c d

end UniversalGrammar

/-! ## §17. Derrida's "Relevant" Translation

Derrida argues that translation is always a matter of "relevance" —
choosing which resonances to preserve and which to sacrifice.
A translation cannot preserve everything; it must make choices.
We formalize this as a trade-off between different observers. -/

section DerridaRelevance
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A translation is c-relevant if it preserves resonance with observer c. -/
def relevant (φ : I → I) (c : I) : Prop :=
  ∀ a, rs (φ a) c = rs a c

/-- Identity is relevant for all observers. -/
theorem id_relevant (c : I) : relevant (id : I → I) c := fun _ => rfl

/-- Any translation is void-relevant (trivially). -/
theorem void_relevant (φ : I → I) : relevant φ (void : I) := by
  intro a; simp [rs_void_right']

/-- Relevance composes: if φ and ψ are both c-relevant, so is ψ ∘ φ. -/
theorem relevant_comp (φ ψ : I → I) (c : I) (hφ : relevant φ c)
    (hψ : relevant ψ c) : relevant (ψ ∘ φ) c := by
  intro a; simp [Function.comp]; rw [hψ (φ a), hφ a]

/-- The relevance gap: how much resonance with c changes under φ. -/
noncomputable def relevanceGap (φ : I → I) (a c : I) : ℝ :=
  rs (φ a) c - rs a c

/-- Identity has zero relevance gap. -/
theorem id_zero_relevanceGap (a c : I) :
    relevanceGap (id : I → I) a c = 0 := by
  unfold relevanceGap; simp

/-- Relevance gap with void observer is always zero.
    Derrida: the absent audience imposes no relevance constraints. -/
theorem relevanceGap_void_observer (φ : I → I) (a : I) :
    relevanceGap φ a (void : I) = 0 := by
  unfold relevanceGap; simp [rs_void_right']

/-- Relevance gap with void source: translating silence.
    For void-preserving translations, the gap is zero. -/
theorem relevanceGap_void_source (φ : I → I) (hφ : voidPreserving φ)
    (c : I) : relevanceGap φ (void : I) c = 0 := by
  unfold relevanceGap; rw [hφ]; ring

/-- Relevance gap of a chain decomposes into two gaps. -/
theorem relevanceGap_chain (φ ψ : I → I) (a c : I) :
    relevanceGap (ψ ∘ φ) a c =
    relevanceGap ψ (φ a) c + relevanceGap φ a c := by
  unfold relevanceGap
  simp only [Function.comp]
  ring

end DerridaRelevance

/-! ## §18. Benjamin's Pure Language (Reine Sprache)

Benjamin posited that behind all languages lies a "pure language"
that translation asymptotically approaches. In IDT, we formalize
this as the limit of iterated translations: the fixed point of
the translation map. -/

section PureLanguage
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A fixed point of φ is an idea unchanged by translation.
    Benjamin: the fragment of "pure language" visible through φ. -/
def isFixedPoint (φ : I → I) (a : I) : Prop := φ a = a

/-- Void is a fixed point of every void-preserving translation. -/
theorem void_fixedPoint (φ : I → I) (hφ : voidPreserving φ) :
    isFixedPoint φ (void : I) := hφ

/-- Fixed points are translation-invariant. -/
theorem fixedPoint_invariant (φ : I → I) (a : I) (h : isFixedPoint φ a) :
    translationInvariant φ a := by
  intro c d
  unfold emergence; rw [h]

/-- Fixed points have zero emergence shift. -/
theorem fixedPoint_zero_shift (φ : I → I) (a : I) (h : isFixedPoint φ a)
    (c d : I) : emergenceShift φ a c d = 0 := by
  exact translationInvariant_zero_shift φ a (fixedPoint_invariant φ a h) c d

/-- Fixed points have zero self-distortion. -/
theorem fixedPoint_zero_selfDistortion (φ : I → I) (a : I)
    (h : isFixedPoint φ a) : selfDistortion φ a = 0 := by
  unfold selfDistortion; rw [h]; ring

/-- Fixed points have zero pairwise untranslatability with themselves. -/
theorem fixedPoint_zero_self_untranslatable (φ : I → I) (a : I)
    (h : isFixedPoint φ a) : pairwiseUntranslatability φ a a = 0 := by
  unfold pairwiseUntranslatability translationFidelity; rw [h]; simp

/-- If a and b are both fixed points, fidelity between them is zero. -/
theorem fixedPoints_zero_fidelity (φ : I → I) (a b : I)
    (ha : isFixedPoint φ a) (hb : isFixedPoint φ b) :
    translationFidelity φ a b = 0 := by
  unfold translationFidelity; rw [ha, hb]; ring

/-- Fixed points of a compositional translation are closed under compose.
    Benjamin: the "pure language" is itself a language. -/
theorem fixedPoint_compose_closed (φ : I → I) (hcomp : compositional φ)
    (a b : I) (ha : isFixedPoint φ a) (hb : isFixedPoint φ b) :
    isFixedPoint φ (compose a b) := by
  unfold isFixedPoint at *
  rw [hcomp a b, ha, hb]

/-- Iterated application of a translation: φ^n. -/
def iterateTranslation (φ : I → I) : ℕ → I → I
  | 0 => id
  | n + 1 => φ ∘ (iterateTranslation φ n)

set_option linter.unusedSectionVars false in
/-- φ^0 = id -/
theorem iterateTranslation_zero (φ : I → I) (a : I) :
    iterateTranslation φ 0 a = a := rfl

set_option linter.unusedSectionVars false in
/-- φ^1 = φ -/
theorem iterateTranslation_one (φ : I → I) (a : I) :
    iterateTranslation φ 1 a = φ a := rfl

set_option linter.unusedSectionVars false in
/-- Fixed points are invariant under all iterations. -/
theorem fixedPoint_iterate (φ : I → I) (a : I) (h : isFixedPoint φ a)
    (n : ℕ) : iterateTranslation φ n a = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [iterateTranslation, Function.comp, ih]
    exact h

end PureLanguage

/-! ## §19. Translation Loss and Entropy

Every non-faithful translation loses something. We define translation
loss as the absolute value of fidelity change and study its accumulation
through translation chains. -/

section TranslationLoss
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Asymmetric translation fidelity: how φ shifts the directional
    resonance from a to b. -/
noncomputable def directionalFidelity (φ : I → I) (a b : I) : ℝ :=
  rs (φ a) (φ b) - rs a b

/-- Directional fidelity equals translationFidelity (definitional). -/
theorem directionalFidelity_eq (φ : I → I) (a b : I) :
    directionalFidelity φ a b = translationFidelity φ a b := by
  unfold directionalFidelity translationFidelity; rfl

/-- Self-directional fidelity equals self-distortion. -/
theorem directionalFidelity_self (φ : I → I) (a : I) :
    directionalFidelity φ a a = selfDistortion φ a := by
  unfold directionalFidelity selfDistortion; rfl

/-- Composition of directional fidelity: the chain rule. -/
theorem directionalFidelity_comp (φ ψ : I → I) (a b : I) :
    directionalFidelity (ψ ∘ φ) a b =
    directionalFidelity ψ (φ a) (φ b) +
    directionalFidelity φ a b := by
  unfold directionalFidelity
  simp only [Function.comp]
  ring

/-- Faithful translations are precisely those with zero directional
    fidelity everywhere. -/
theorem faithful_iff_zero_directional (φ : I → I) :
    faithful φ ↔ ∀ a b, directionalFidelity φ a b = 0 := by
  constructor
  · intro h a b; unfold directionalFidelity; linarith [h a b]
  · intro h a b; unfold directionalFidelity at h; linarith [h a b]

end TranslationLoss

/-! ## §20. Hermeneutic Circle: Interpretation Affects Translation

Gadamer's hermeneutic circle: understanding the parts requires
understanding the whole, and vice versa. In IDT, this means
the act of translation (a morphism) is itself an idea that
composes with what it translates. -/

section HermeneuticCircle
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Hermeneutic resonance: how the "lens" of context L affects
    the resonance of a with b. Models reading a through the lens of L. -/
noncomputable def hermeneuticRS (L a b : I) : ℝ :=
  rs (compose L a) b

/-- Reading through the void lens is just direct resonance. -/
theorem hermeneuticRS_void_lens (a b : I) :
    hermeneuticRS (void : I) a b = rs a b := by
  unfold hermeneuticRS; simp

/-- Reading void through any lens produces zero resonance with void. -/
theorem hermeneuticRS_void_text (L : I) :
    hermeneuticRS L (void : I) (void : I) = 0 := by
  unfold hermeneuticRS; simp [rs_void_right']

/-- The hermeneutic gap: how much the lens L changes resonance. -/
noncomputable def hermeneuticGap (L a b : I) : ℝ :=
  hermeneuticRS L a b - rs a b

/-- Void lens creates zero hermeneutic gap. Gadamer: pre-understanding
    of "nothing" adds nothing. -/
theorem hermeneuticGap_void_lens (a b : I) :
    hermeneuticGap (void : I) a b = 0 := by
  unfold hermeneuticGap hermeneuticRS; simp

/-- The hermeneutic gap relates to emergence plus the lens's direct resonance.
    The gap IS emergence plus what the lens directly contributes. -/
theorem hermeneuticGap_eq_emergence_plus (L a b : I) :
    hermeneuticGap L a b = emergence L a b + rs L b := by
  unfold hermeneuticGap hermeneuticRS emergence; ring

/-- Hermeneutic gap with void observer is always zero. -/
theorem hermeneuticGap_void_observer (L a : I) :
    hermeneuticGap L a (void : I) = 0 := by
  rw [hermeneuticGap_eq_emergence_plus]
  rw [emergence_against_void, rs_void_right']; ring

end HermeneuticCircle

/-! ## §21. Translation Symmetry and Asymmetry

A crucial observation: translation from A to B is NOT the same as
translation from B to A. The asymmetry of resonance means that
what A loses in translation to B is different from what B loses
in translation to A. This is the formal content of Berman's
"ethnocentrism of translation." -/

section TranslationAsymmetry
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Translation asymmetry: the difference between φ-fidelity and
    reverse fidelity. Measures the directionality of translation loss. -/
noncomputable def translationAsymmetry (φ : I → I) (a b : I) : ℝ :=
  translationFidelity φ a b - translationFidelity φ b a

/-- Translation asymmetry is antisymmetric. -/
theorem translationAsymmetry_antisymm (φ : I → I) (a b : I) :
    translationAsymmetry φ a b = -translationAsymmetry φ b a := by
  unfold translationAsymmetry; ring

/-- Translation asymmetry vanishes for self-pairs. -/
theorem translationAsymmetry_self (φ : I → I) (a : I) :
    translationAsymmetry φ a a = 0 := by
  unfold translationAsymmetry; ring

/-- Faithful translations have zero asymmetry. -/
theorem faithful_zero_asymmetry (φ : I → I) (h : faithful φ) (a b : I) :
    translationAsymmetry φ a b = 0 := by
  unfold translationAsymmetry translationFidelity
  rw [h a b, h b a]; ring

/-- The asymmetry gap: how much the source resonance's asymmetry
    differs from the target resonance's asymmetry. -/
noncomputable def asymmetryPreservation (φ : I → I) (a b : I) : ℝ :=
  (rs (φ a) (φ b) - rs (φ b) (φ a)) - (rs a b - rs b a)

/-- Faithful translations preserve asymmetry exactly. -/
theorem faithful_preserves_asymmetry (φ : I → I) (h : faithful φ) (a b : I) :
    asymmetryPreservation φ a b = 0 := by
  unfold asymmetryPreservation; rw [h a b, h b a]; ring

/-- Identity preserves asymmetry. -/
theorem id_preserves_asymmetry (a b : I) :
    asymmetryPreservation (id : I → I) a b = 0 := by
  unfold asymmetryPreservation; simp

end TranslationAsymmetry

/-! ## §22. Machine Translation Limits

Machine translation operates by optimizing for a specific loss function,
which corresponds to relevance for a particular observer (or set of
observers). We formalize the inherent limits: optimizing for one
observer necessarily creates gaps for others. -/

section MachineTranslation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A machine translation optimized for observer c: it minimizes
    relevance gap for c (i.e., achieves zero gap for c). -/
def optimizedFor (φ : I → I) (c : I) : Prop :=
  ∀ a, rs (φ a) c = rs a c

/-- An MT system optimized for void is trivially correct. -/
theorem mt_void_trivial (φ : I → I) : optimizedFor φ (void : I) := by
  intro a; simp [rs_void_right']

/-- An MT system optimized for c has zero relevance gap at c. -/
theorem mt_zero_gap (φ : I → I) (c : I) (h : optimizedFor φ c)
    (a : I) : relevanceGap φ a c = 0 := by
  unfold relevanceGap; linarith [h a]

/-- If φ is optimized for c, then ψ ∘ φ is optimized for c
    iff ψ is also optimized for c. Forward direction: -/
theorem mt_compose_optimized (φ ψ : I → I) (c : I)
    (hφ : optimizedFor φ c) (hψ : optimizedFor ψ c) :
    optimizedFor (ψ ∘ φ) c := by
  intro a; simp [Function.comp]; rw [hψ (φ a), hφ a]

/-- Identity is trivially optimized for every observer. -/
theorem id_optimized (c : I) : optimizedFor (id : I → I) c :=
  fun _ => rfl

end MachineTranslation

/-! ## §23. Skopos Theory: Purpose-Driven Translation

Skopos theory (Vermeer, Reiss): the purpose (skopos) of a translation
determines its strategy. A translation aimed at children vs. scholars
will differ. In IDT, the skopos IS the observer c for which the
translation is relevant. -/

section SkoposTheory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A skopos-adequate translation: it achieves relevance for observer c.
    This is just optimizedFor, but philosophically motivated differently. -/
def skoposAdequate (φ : I → I) (skopos : I) : Prop :=
  optimizedFor φ skopos

/-- Every translation is skopos-adequate for void.
    The "purposeless" translation is always adequate. -/
theorem skopos_void (φ : I → I) : skoposAdequate φ (void : I) :=
  mt_void_trivial φ

/-- Identity is adequate for every skopos. -/
theorem id_skoposAdequate (skopos : I) :
    skoposAdequate (id : I → I) skopos :=
  id_optimized skopos

/-- Skopos-adequate translations compose. -/
theorem skopos_comp (φ ψ : I → I) (skopos : I)
    (hφ : skoposAdequate φ skopos) (hψ : skoposAdequate ψ skopos) :
    skoposAdequate (ψ ∘ φ) skopos :=
  mt_compose_optimized φ ψ skopos hφ hψ

/-- The skopos gap between two translations: how much they differ
    in adequacy for a given purpose. -/
noncomputable def skoposGap (φ ψ : I → I) (a skopos : I) : ℝ :=
  rs (φ a) skopos - rs (ψ a) skopos

/-- Skopos gap is antisymmetric in the translations. -/
theorem skoposGap_antisymm (φ ψ : I → I) (a skopos : I) :
    skoposGap φ ψ a skopos = -skoposGap ψ φ a skopos := by
  unfold skoposGap; ring

/-- If both are skopos-adequate, the gap is zero. -/
theorem skopos_adequate_zero_gap (φ ψ : I → I) (skopos : I)
    (hφ : skoposAdequate φ skopos) (hψ : skoposAdequate ψ skopos)
    (a : I) : skoposGap φ ψ a skopos = 0 := by
  unfold skoposGap; rw [hφ a, hψ a]; ring

end SkoposTheory

/-! ## §24. Translation Memory and Iterative Refinement

Professional translators use "translation memory" — previously
translated pairs. Each round of editing refines the translation.
We model this as iterated application of a "correction" map. -/

section TranslationMemory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The fidelity improvement from applying correction ψ after φ. -/
noncomputable def fidelityImprovement (φ ψ : I → I) (a b : I) : ℝ :=
  |translationFidelity φ a b| - |translationFidelity (ψ ∘ φ) a b|

/-- If ψ ∘ φ is faithful, the improvement equals the original error. -/
theorem perfect_correction (φ ψ : I → I) (hψφ : faithful (ψ ∘ φ)) (a b : I) :
    fidelityImprovement φ ψ a b = |translationFidelity φ a b| := by
  unfold fidelityImprovement
  rw [faithful_zero_fidelity (ψ ∘ φ) hψφ a b]; simp

/-- Self-correction: applying φ as its own correction. -/
noncomputable def selfCorrectionFidelity (φ : I → I) (a b : I) : ℝ :=
  translationFidelity (φ ∘ φ) a b

/-- Self-correction of a faithful translation is still faithful. -/
theorem faithful_selfCorrection (φ : I → I) (hφ : faithful φ) (a b : I) :
    selfCorrectionFidelity φ a b = 0 := by
  unfold selfCorrectionFidelity
  exact faithful_zero_fidelity (φ ∘ φ) (faithful_comp φ φ hφ hφ) a b

end TranslationMemory

/-! ## §25. Calque and Loan-Translation

A calque (loan translation) translates morpheme-by-morpheme:
φ(a ∘ b) = φ(a) ∘ φ(b). This is exactly compositionality.
We derive further consequences specific to linguistic calques. -/

section Calque
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A calque preserves compositional structure. -/
def isCalque (φ : I → I) : Prop := compositional φ

/-- A calque preserves the resonance of compositions against any observer,
    modulo the fidelity of the parts. -/
theorem calque_resonance (φ : I → I) (hφ : isCalque φ) (a b c : I) :
    rs (φ (compose a b)) c = rs (compose (φ a) (φ b)) c := by
  rw [hφ a b]

/-- Calques preserve triple compositions. -/
theorem calque_triple (φ : I → I) (hφ : isCalque φ) (a b c : I) :
    φ (compose (compose a b) c) = compose (compose (φ a) (φ b)) (φ c) := by
  rw [hφ (compose a b) c, hφ a b]

/-- Calques preserve iterated self-composition (requires void-preserving). -/
theorem calque_composeN (φ : I → I) (hφ : isCalque φ) (hv : voidPreserving φ)
    (a : I) : ∀ n, φ (composeN a n) = composeN (φ a) n := by
  intro n; induction n with
  | zero =>
    simp [composeN]; exact hv
  | succ n ih =>
    simp [composeN]; rw [hφ (composeN a n) a, ih]

end Calque

/-! ## §26. Translation as Interpretation: Schleiermacher's Dictum

Schleiermacher: "Either the translator leaves the author in peace
and moves the reader towards him, or he leaves the reader in peace
and moves the author towards him." This is the domestication vs.
foreignization dichotomy formalized differently: as a choice of
which resonance endpoint to preserve. -/

section Schleiermacher
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Author-oriented translation: preserves resonance FROM the idea.
    "Moving the reader to the author." -/
def authorOriented (φ : I → I) : Prop :=
  ∀ a b, rs (φ a) b = rs a b

/-- Reader-oriented translation: preserves resonance TO the idea.
    "Moving the author to the reader." -/
def readerOriented (φ : I → I) : Prop :=
  ∀ a b, rs a (φ b) = rs a b

/-- Identity is both author- and reader-oriented. -/
theorem id_authorOriented : authorOriented (id : I → I) := fun _ _ => rfl
theorem id_readerOriented : readerOriented (id : I → I) := fun _ _ => rfl

/-- Author-oriented translations compose. -/
theorem authorOriented_comp (φ ψ : I → I) (hφ : authorOriented φ)
    (hψ : authorOriented ψ) : authorOriented (ψ ∘ φ) := by
  intro a b; simp [Function.comp]; rw [hψ (φ a) b, hφ a b]

/-- Reader-oriented translations compose. -/
theorem readerOriented_comp (φ ψ : I → I) (hφ : readerOriented φ)
    (hψ : readerOriented ψ) : readerOriented (ψ ∘ φ) := by
  intro a b; simp [Function.comp]; rw [hψ a (φ b), hφ a b]

/-- An author-oriented translation is c-relevant for ALL c. -/
theorem authorOriented_relevant (φ : I → I) (hφ : authorOriented φ) (c : I) :
    relevant φ c :=
  fun a => hφ a c

/-- If a translation is both author- and reader-oriented, it is faithful.
    The only "perfect" Schleiermacher translation is the identity-like one. -/
theorem author_reader_faithful (φ : I → I)
    (ha : authorOriented φ) (hr : readerOriented φ) : faithful φ := by
  intro a b
  have h1 := ha a (φ b)
  have h2 := hr a b
  linarith

end Schleiermacher

/-! ## §27. Semantic Fields and Translation Coverage

A semantic field is a cluster of ideas that mutually resonate.
Translation between semantic fields is the core of lexical translation.
We define field-faithful translations and study coverage. -/

section SemanticFields
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A translation is field-faithful for a pair (a, b) if it preserves
    their mutual resonance. -/
def fieldFaithful (φ : I → I) (a b : I) : Prop :=
  rs (φ a) (φ b) = rs a b

/-- Faithful translations are field-faithful for all pairs. -/
theorem faithful_fieldFaithful (φ : I → I) (h : faithful φ) (a b : I) :
    fieldFaithful φ a b := h a b

/-- Identity is field-faithful for all pairs. -/
theorem id_fieldFaithful (a b : I) :
    fieldFaithful (id : I → I) a b := rfl

/-- Field-faithfulness composes: if φ is field-faithful for (a,b)
    and ψ is field-faithful for (φ a, φ b), then ψ ∘ φ is. -/
theorem fieldFaithful_comp (φ ψ : I → I) (a b : I)
    (hφ : fieldFaithful φ a b) (hψ : fieldFaithful ψ (φ a) (φ b)) :
    fieldFaithful (ψ ∘ φ) a b := by
  unfold fieldFaithful at *; simp [Function.comp]; linarith

/-- Field-faithfulness is symmetric: if φ preserves rs(a,b) = rs(φa,φb)
    then it also preserves the value at (b,a) iff it preserves at (a,b). -/
theorem fieldFaithful_of_faithful (φ : I → I) (h : faithful φ) (a b : I) :
    fieldFaithful φ a b ∧ fieldFaithful φ b a :=
  ⟨h a b, h b a⟩

end SemanticFields

/-! ## §28. Abductive Translation and Pragmatic Inference

In pragmatics (Grice, Sperber & Wilson), hearers abductively infer
the speaker's intention. Translation involves double abduction:
the translator infers the source author's intent, then re-encodes
for the target audience. We model this as a two-step composition. -/

section AbductiveTranslation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Abductive interpretation: the translator's understanding of source a,
    mediated by their own background knowledge t (translator's mind). -/
noncomputable def abductiveReading (translator source : I) : I :=
  compose translator source

/-- Re-encoding: the translator produces output by composing their
    interpretation with the target-language frame. -/
noncomputable def reencode (frame interpretation : I) : I :=
  compose frame interpretation

/-- Full abductive translation: read through translator, re-encode through frame. -/
noncomputable def abductiveTranslation (translator frame source : I) : I :=
  reencode frame (abductiveReading translator source)

/-- Abductive translation is triple composition. -/
theorem abductive_is_compose (translator frame source : I) :
    abductiveTranslation translator frame source =
    compose frame (compose translator source) := rfl

/-- Void translator: abductive reading without background = source itself. -/
theorem abductive_void_translator (frame source : I) :
    abductiveTranslation (void : I) frame source = compose frame source := by
  unfold abductiveTranslation abductiveReading reencode; simp

/-- Void frame: re-encoding without framing = translator's interpretation. -/
theorem abductive_void_frame (translator source : I) :
    abductiveTranslation translator (void : I) source =
    compose translator source := by
  unfold abductiveTranslation abductiveReading reencode; simp

/-- Void source: translating silence = frame ∘ translator. -/
theorem abductive_void_source (translator frame : I) :
    abductiveTranslation translator frame (void : I) =
    compose frame translator := by
  unfold abductiveTranslation abductiveReading reencode; simp

/-- All void: abductive translation of nothing through nothing = nothing. -/
theorem abductive_all_void :
    abductiveTranslation (void : I) (void : I) (void : I) = (void : I) := by
  unfold abductiveTranslation abductiveReading reencode; simp

end AbductiveTranslation

/-! ## §29. Translation Entropy and Information-Theoretic Bounds

Each translation either compresses or expands the resonance profile.
We define a "resonance weight" measure and study how translation
changes it, connecting to information-theoretic notions of loss. -/

section TranslationEntropy
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The weight change under translation: how much "resonance mass"
    the idea gains or loses. Always non-negative change for enriching
    translations. -/
noncomputable def weightChange (φ : I → I) (a : I) : ℝ :=
  rs (φ a) (φ a) - rs a a

/-- Identity has zero weight change. -/
theorem id_zero_weightChange (a : I) :
    weightChange (id : I → I) a = 0 := by
  unfold weightChange; simp

/-- Faithful translations have zero weight change (they preserve self-resonance). -/
theorem faithful_zero_weightChange (φ : I → I) (h : faithful φ) (a : I) :
    weightChange φ a = 0 := by
  unfold weightChange; rw [h a a]; ring

/-- Weight change equals self-distortion (by definition). -/
theorem weightChange_eq_selfDistortion (φ : I → I) (a : I) :
    weightChange φ a = selfDistortion φ a := by
  unfold weightChange selfDistortion; rfl

/-- Weight change of a chain decomposes. -/
theorem weightChange_chain (φ ψ : I → I) (a : I) :
    weightChange (ψ ∘ φ) a =
    weightChange ψ (φ a) + weightChange φ a := by
  unfold weightChange
  simp only [Function.comp]
  ring

/-- Weight change of void is zero for void-preserving translations. -/
theorem weightChange_void (φ : I → I) (hφ : voidPreserving φ) :
    weightChange φ (void : I) = 0 := by
  unfold weightChange; rw [hφ]; ring

end TranslationEntropy

/-! ## §30. Multi-Target Translation

In practice, a text is often translated into many languages simultaneously.
The collective behavior of multiple translations reveals the text's
"translational affordances." -/

section MultiTarget
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Agreement between two translations: how much they agree on a pair. -/
noncomputable def translationAgreement (φ ψ : I → I) (a : I) : ℝ :=
  rs (φ a) (ψ a)

/-- Self-agreement: a translation agrees with itself = self-resonance
    of the output. -/
theorem selfAgreement (φ : I → I) (a : I) :
    translationAgreement φ φ a = rs (φ a) (φ a) := rfl

/-- Agreement with identity: how much the translation output resonates
    with the original. -/
theorem agreement_with_id (φ : I → I) (a : I) :
    translationAgreement φ id a = rs (φ a) a := rfl

/-- Agreement of two void-preserving translations on void = 0. -/
theorem agreement_void (φ ψ : I → I)
    (hφ : voidPreserving φ) (hψ : voidPreserving ψ) :
    translationAgreement φ ψ (void : I) = 0 := by
  unfold translationAgreement; rw [hφ, hψ]; exact rs_void_void

/-- The disagreement between two translations. -/
noncomputable def translationDisagreement (φ ψ : I → I) (a : I) : ℝ :=
  rs (φ a) (φ a) + rs (ψ a) (ψ a) - 2 * translationAgreement φ ψ a

/-- Self-disagreement is zero. -/
theorem selfDisagreement (φ : I → I) (a : I) :
    translationDisagreement φ φ a = 0 := by
  unfold translationDisagreement translationAgreement; ring

end MultiTarget

/-! ## §31. Jakobson's Three Types of Translation

Roman Jakobson (1959) identified three fundamental types of translation:
1. **Intralingual** — rewording within the same language
2. **Interlingual** — translation between languages
3. **Intersemiotic** — transmutation between sign systems

In IDT, all three are endofunctions on the ideatic space, but they
differ in what they preserve. Intralingual preserves self-resonance,
interlingual preserves compositional structure, and intersemiotic
may change both. -/

section JakobsonTypes
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Jakobson's intralingual translation: rewording preserves self-resonance.
    "Saying the same thing in different words within one language." -/
def intralingual (φ : I → I) : Prop :=
  ∀ a, rs (φ a) (φ a) = rs a a

/-- Jakobson's interlingual translation: preserves resonance structure.
    This is simply faithfulness — the standard notion. -/
def interlingual (φ : I → I) : Prop := faithful φ

/-- Jakobson's intersemiotic translation: transmutation between sign
    systems. Only preserves void and compositional structure, but
    may change resonance values entirely. -/
def intersemiotic (φ : I → I) : Prop :=
  voidPreserving φ ∧ compositional φ

/-- Every interlingual translation is intralingual: preserving all
    resonances entails preserving self-resonance. -/
theorem interlingual_is_intralingual (φ : I → I) (h : interlingual φ) :
    intralingual φ :=
  fun a => h a a

/-- Intersemiotic translation is literally "literal" (in our sense). -/
theorem intersemiotic_is_literal (φ : I → I) (h : intersemiotic φ) :
    literal φ := h

/-- Identity is intralingual. -/
theorem id_intralingual : intralingual (id : I → I) := fun _ => rfl

/-- Identity is interlingual. -/
theorem id_interlingual : interlingual (id : I → I) := id_faithful

/-- Identity is intersemiotic. -/
theorem id_intersemiotic : intersemiotic (id : I → I) :=
  ⟨id_voidPreserving, id_compositional⟩

/-- Intralingual translations have zero weight change. -/
theorem intralingual_zero_weightChange (φ : I → I) (h : intralingual φ)
    (a : I) : weightChange φ a = 0 := by
  unfold weightChange; rw [h a]; ring

/-- Composition of intralingual translations is intralingual. -/
theorem intralingual_comp (φ ψ : I → I) (hφ : intralingual φ)
    (hψ : intralingual ψ) : intralingual (ψ ∘ φ) := by
  intro a; simp [Function.comp]; rw [hψ (φ a), hφ a]

/-- Composition of interlingual translations is interlingual. -/
theorem interlingual_comp (φ ψ : I → I) (hφ : interlingual φ)
    (hψ : interlingual ψ) : interlingual (ψ ∘ φ) :=
  faithful_comp ψ φ hψ hφ

/-- Composition of intersemiotic translations is intersemiotic. -/
theorem intersemiotic_comp (φ ψ : I → I) (hφ : intersemiotic φ)
    (hψ : intersemiotic ψ) : intersemiotic (ψ ∘ φ) :=
  literal_comp ψ φ hψ hφ

/-- An intersemiotic translation has zero emergence gap.
    Jakobson: transmutation preserves compositional structure. -/
theorem intersemiotic_zero_emergence (φ : I → I) (h : intersemiotic φ)
    (a b c : I) : translationEmergence φ a b c = 0 :=
  compositional_zero_emergence φ h.2 a b c

/-- An interlingual + compositional translation is always domesticating.
    Jakobson: a fully structure-preserving interlingual translation is domesticating. -/
theorem interlingual_compositional_domesticating (φ : I → I)
    (_h : interlingual φ) (hc : compositional φ)
    (a b c : I) : domesticating φ a b c := by
  exact compositional_domesticating φ hc a b c

end JakobsonTypes

/-! ## §32. Steiner's Hermeneutic Motion

George Steiner (After Babel, 1975) described translation as a
fourfold hermeneutic motion:
1. **Trust** — the translator trusts the source has meaning
2. **Aggression** — the translator extracts meaning
3. **Incorporation** — the translator absorbs meaning into the target
4. **Restitution** — the translator compensates for what was taken

We formalize each phase as a property of the translation map. -/

section SteinerMotion
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Steiner's trust: the translator believes the source has
    non-trivial resonance structure. A non-void source. -/
def steinerTrust (a : I) : Prop := a ≠ void

/-- Steiner's aggression: the translator's operation extracts
    resonance — self-resonance of the result is at least the source's.
    The translation "takes" from the source. -/
def steinerAggression (φ : I → I) (a : I) : Prop :=
  rs (φ a) (φ a) ≥ rs a a

/-- Steiner's incorporation: the translated idea resonates with the
    target culture c. The extraction is "absorbed" into the target. -/
def steinerIncorporation (φ : I → I) (a c : I) : Prop :=
  rs (φ a) c ≥ rs a c

/-- Steiner's restitution: the translator compensates — the total
    "weight" doesn't increase beyond what can be justified.
    Formalized: weight change is non-negative but bounded by emergence. -/
def steinerRestitution (φ : I → I) (a : I) : Prop :=
  weightChange φ a ≥ 0

/-- A non-void idea satisfies Steiner's trust. -/
theorem steiner_trust_of_ne_void (a : I) (h : a ≠ void) :
    steinerTrust a := h

/-- Faithful translations satisfy aggression (with equality). -/
theorem faithful_aggression (φ : I → I) (h : faithful φ) (a : I) :
    steinerAggression φ a := by
  unfold steinerAggression; rw [h a a]

/-- Identity satisfies aggression. -/
theorem id_aggression (a : I) :
    steinerAggression (id : I → I) a := le_refl _

/-- Identity satisfies restitution. -/
theorem id_restitution (a : I) :
    steinerRestitution (id : I → I) a := by
  unfold steinerRestitution weightChange; simp

/-- Faithful translations satisfy restitution (weight change = 0). -/
theorem faithful_restitution (φ : I → I) (h : faithful φ) (a : I) :
    steinerRestitution φ a := by
  unfold steinerRestitution; rw [faithful_zero_weightChange φ h a]

/-- The hermeneutic motion is complete when trust, aggression, and
    restitution all hold. -/
def completeHermeneuticMotion (φ : I → I) (a : I) : Prop :=
  steinerTrust a ∧ steinerAggression φ a ∧ steinerRestitution φ a

/-- Identity performs a complete hermeneutic motion on any non-void idea. -/
theorem id_complete_motion (a : I) (h : a ≠ void) :
    completeHermeneuticMotion (id : I → I) a :=
  ⟨h, id_aggression a, id_restitution a⟩

/-- Faithful translations perform complete hermeneutic motion on non-void ideas. -/
theorem faithful_complete_motion (φ : I → I) (hf : faithful φ) (a : I)
    (h : a ≠ void) : completeHermeneuticMotion φ a :=
  ⟨h, faithful_aggression φ hf a, faithful_restitution φ hf a⟩

end SteinerMotion

/-! ## §33. Berman's Twelve Deforming Tendencies

Antoine Berman (1985) identified twelve "deforming tendencies" in
translation — systematic ways translations distort the source text.
We formalize several key tendencies as measurable properties of
translation maps. -/

section BermanTendencies
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Berman's rationalization: the translation imposes more compositional
    order than the source. Measured by reduction in emergence magnitude. -/
noncomputable def rationalizationDegree (φ : I → I) (a b c : I) : ℝ :=
  |emergence a b c| - |emergence (φ a) (φ b) c|

/-- Berman's clarification: the translation makes explicit what was
    implicit. Measured by increase in resonance with observer c. -/
noncomputable def clarificationDegree (φ : I → I) (a c : I) : ℝ :=
  rs (φ a) c - rs a c

/-- Berman's expansion: the translation is "wordier" — higher
    self-resonance (more "weight"). -/
noncomputable def expansionDegree (φ : I → I) (a : I) : ℝ :=
  rs (φ a) (φ a) - rs a a

/-- Expansion degree equals weight change. -/
theorem expansion_eq_weight (φ : I → I) (a : I) :
    expansionDegree φ a = weightChange φ a := rfl

/-- Berman's ennoblement: the translation "elevates" style —
    increases resonance with a cultural ideal c.
    Same as clarification but for a prestige observer. -/
noncomputable def ennoblementDegree (φ : I → I) (a prestige : I) : ℝ :=
  clarificationDegree φ a prestige

/-- Berman's destruction of rhythms: the translation changes the
    self-resonance pattern of repeated composition. -/
noncomputable def rhythmDestruction (φ : I → I) (a : I) : ℝ :=
  rs (compose (φ a) (φ a)) (compose (φ a) (φ a)) -
  rs (compose a a) (compose a a)

/-- Identity has zero rationalization. -/
theorem id_zero_rationalization (a b c : I) :
    rationalizationDegree (id : I → I) a b c = 0 := by
  unfold rationalizationDegree; simp

/-- Identity has zero clarification. -/
theorem id_zero_clarification (a c : I) :
    clarificationDegree (id : I → I) a c = 0 := by
  unfold clarificationDegree; simp

/-- Identity has zero expansion. -/
theorem id_zero_expansion (a : I) :
    expansionDegree (id : I → I) a = 0 := by
  unfold expansionDegree; simp

/-- Faithful translations have zero expansion. -/
theorem faithful_zero_expansion (φ : I → I) (h : faithful φ) (a : I) :
    expansionDegree φ a = 0 := by
  unfold expansionDegree; rw [h a a]; ring

/-- Berman's qualitative impoverishment: the loss of texture,
    measured by decrease in self-resonance. -/
noncomputable def qualitativeImpoverishment (φ : I → I) (a : I) : ℝ :=
  rs a a - rs (φ a) (φ a)

/-- Qualitative impoverishment is the negation of expansion. -/
theorem impoverishment_neg_expansion (φ : I → I) (a : I) :
    qualitativeImpoverishment φ a = -expansionDegree φ a := by
  unfold qualitativeImpoverishment expansionDegree; ring

/-- Identity has zero impoverishment. -/
theorem id_zero_impoverishment (a : I) :
    qualitativeImpoverishment (id : I → I) a = 0 := by
  unfold qualitativeImpoverishment; simp

/-- Berman's quantitative impoverishment: the destruction of
    compositional patterns. Measured by how much compositionality fails. -/
noncomputable def quantitativeImpoverishment (φ : I → I) (a b c : I) : ℝ :=
  |translationEmergence φ a b c|

/-- Compositional translations have zero quantitative impoverishment. -/
theorem compositional_zero_quant_impoverishment (φ : I → I) (h : compositional φ)
    (a b c : I) : quantitativeImpoverishment φ a b c = 0 := by
  unfold quantitativeImpoverishment
  rw [compositional_zero_emergence φ h a b c]; simp

/-- Berman's effacement of superimposition: the destruction of
    layered meaning, measured by change in emergence between translated pairs. -/
noncomputable def superimpositionEffacement (φ : I → I) (a b c : I) : ℝ :=
  emergence a b c - emergence (φ a) (φ b) c

/-- Author-oriented + compositional translations have zero superimposition effacement.
    When φ preserves resonance FROM its output (author-oriented), and preserves
    compositional structure, the layered meaning is preserved. -/
theorem authorOriented_zero_effacement (φ : I → I) (ha : authorOriented φ)
    (hc : compositional φ) (a b c : I) :
    superimpositionEffacement φ a b c = 0 := by
  unfold superimpositionEffacement emergence
  -- Goal involves compose(φ a)(φ b). Rewrite using compositionality.
  have h1 : rs (compose (φ a) (φ b)) c = rs (φ (compose a b)) c := by
    congr 1; exact (hc a b).symm
  rw [h1, ha (compose a b) c, ha a c, ha b c]; ring

/-- Identity has zero superimposition effacement. -/
theorem id_zero_effacement (a b c : I) :
    superimpositionEffacement (id : I → I) a b c = 0 := by
  unfold superimpositionEffacement; simp

end BermanTendencies

/-! ## §34. Toury's Descriptive Translation Studies — Norms

Gideon Toury's (1995) descriptive translation studies centers on
"norms" — the regularities that govern translation behavior in a
culture. We formalize:
- **Initial norm**: source vs. target orientation
- **Preliminary norms**: what gets translated
- **Operational norms**: how translation decisions are made -/

section TouryNorms
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Toury's adequacy: a translation is adequate (source-oriented) to
    the degree it preserves source resonance structure. Faithful
    translations are maximally adequate. -/
noncomputable def touryAdequacy (φ : I → I) (a b : I) : ℝ :=
  -(|translationFidelity φ a b|)

/-- Faithful translations have maximum adequacy (zero loss). -/
theorem faithful_max_adequacy (φ : I → I) (h : faithful φ) (a b : I) :
    touryAdequacy φ a b = 0 := by
  unfold touryAdequacy; rw [faithful_zero_fidelity φ h a b]; simp

/-- Toury's acceptability: a translation is acceptable (target-oriented)
    to the degree it achieves resonance with a target-culture norm c. -/
noncomputable def touryAcceptability (φ : I → I) (a norm : I) : ℝ :=
  rs (φ a) norm

/-- Identity acceptability = source's resonance with the norm. -/
theorem id_acceptability (a norm : I) :
    touryAcceptability (id : I → I) a norm = rs a norm := rfl

/-- Toury's initial norm tension: the trade-off between adequacy
    and acceptability. The sum measures the translator's position. -/
noncomputable def initialNormTension (φ : I → I) (a b norm : I) : ℝ :=
  touryAdequacy φ a b + touryAcceptability φ a norm

/-- Toury's operational norm: compositionality constraint.
    Operational norms govern segmentation — we model as the degree
    to which translation respects compositional boundaries. -/
noncomputable def operationalNormViolation (φ : I → I) (a b c : I) : ℝ :=
  |translationEmergence φ a b c|

/-- Compositional translations satisfy operational norms perfectly. -/
theorem compositional_operational (φ : I → I) (h : compositional φ)
    (a b c : I) : operationalNormViolation φ a b c = 0 := by
  unfold operationalNormViolation
  rw [compositional_zero_emergence φ h a b c]; simp

/-- Toury's law of growing standardization: repeated translation
    chains tend toward the "standard" (identity).
    Faithful chains have zero deviation from standard. -/
theorem standardization_faithful (φ ψ : I → I) (hφ : faithful φ)
    (hψ : faithful ψ) (a b : I) :
    touryAdequacy (ψ ∘ φ) a b = 0 := by
  unfold touryAdequacy
  rw [faithful_zero_fidelity (ψ ∘ φ) (faithful_comp ψ φ hψ hφ) a b]; simp

end TouryNorms

/-! ## §35. Lefevere's Refraction and Patronage

André Lefevere (1992) argued that translation is "refraction" —
ideas are bent through the lens of ideology, poetics, and patronage.
Translation is never transparent; it is always mediated by power
structures. -/

section LefevereRefraction
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Lefevere's refraction: translation through an ideological lens.
    The lens L "bends" the resonance of a. -/
noncomputable def refraction (lens a : I) : I :=
  compose lens a

/-- Refraction through void = no refraction. -/
theorem refraction_void_lens (a : I) :
    refraction (void : I) a = a := by
  unfold refraction; simp

/-- Refraction of void = the lens itself.
    Lefevere: even silence is ideologically charged. -/
theorem refraction_void_source (lens : I) :
    refraction lens (void : I) = lens := by
  unfold refraction; simp

/-- The refraction gap: how much the lens changes resonance with c. -/
noncomputable def refractionGap (lens a c : I) : ℝ :=
  rs (refraction lens a) c - rs a c

/-- Void lens has zero refraction gap. -/
theorem void_refraction_gap (a c : I) :
    refractionGap (void : I) a c = 0 := by
  unfold refractionGap refraction; simp

/-- Refraction gap decomposes into emergence + lens contribution.
    Lefevere: the ideological distortion is emergence + direct influence. -/
theorem refraction_gap_eq (lens a c : I) :
    refractionGap lens a c = emergence lens a c + rs lens c := by
  unfold refractionGap refraction emergence; ring

/-- Lefevere's patronage: the patron P determines which translations
    are produced. A patron-approved translation achieves high resonance
    with the patron's interests. -/
noncomputable def patronageAlignment (φ : I → I) (a patron : I) : ℝ :=
  rs (φ a) patron

/-- Identity patronage = source's own alignment with the patron. -/
theorem id_patronage (a patron : I) :
    patronageAlignment (id : I → I) a patron = rs a patron := rfl

/-- Double refraction: two ideological lenses composed.
    Lefevere: power structures are layered. -/
noncomputable def doubleRefraction (lens1 lens2 a : I) : I :=
  refraction lens1 (refraction lens2 a)

/-- Double refraction is triple composition. -/
theorem double_refraction_eq (lens1 lens2 a : I) :
    doubleRefraction lens1 lens2 a = compose lens1 (compose lens2 a) := rfl

/-- Refraction is associative: composing lenses then refracting = sequential refraction. -/
theorem refraction_assoc (lens1 lens2 a : I) :
    refraction (compose lens1 lens2) a = doubleRefraction lens1 lens2 a := by
  simp [refraction, doubleRefraction, compose_assoc']

end LefevereRefraction

/-! ## §36. Bassnett and Lefevere's Cultural Turn

Susan Bassnett and André Lefevere (1990) proposed the "cultural turn"
in translation studies: translation is not merely linguistic transfer
but a form of cultural negotiation. The target culture's norms shape
what is translatable. -/

section CulturalTurn
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Cultural distance: how much resonance changes when both ideas
    are embedded in a cultural context C. -/
noncomputable def culturalDistance (C a b : I) : ℝ :=
  rs (compose C a) (compose C b) - rs a b

/-- Void culture imposes zero cultural distance. -/
theorem void_cultural_distance (a b : I) :
    culturalDistance (void : I) a b = 0 := by
  unfold culturalDistance; simp

/-- Cultural distance with void pair: embedding void in culture C
    vs. resonance of void with b. -/
theorem cultural_distance_void_left (C b : I) :
    culturalDistance C (void : I) b = rs C (compose C b) - rs (void : I) b := by
  unfold culturalDistance; simp

/-- Cultural embedding: how translation operates within a culture.
    The "cultural translation" of a through culture C toward audience d. -/
noncomputable def culturalEmbedding (C a d : I) : ℝ :=
  rs (compose C a) d

/-- Void culture embedding is just resonance. -/
theorem void_cultural_embedding (a d : I) :
    culturalEmbedding (void : I) a d = rs a d := by
  unfold culturalEmbedding; simp

/-- Cultural embedding of void: only the culture resonates. -/
theorem cultural_embedding_void (C d : I) :
    culturalEmbedding C (void : I) d = rs C d := by
  unfold culturalEmbedding; simp

/-- The cultural negotiation gap: how much a differs from b when
    both are embedded in the same culture. -/
noncomputable def culturalNegotiationGap (C a b d : I) : ℝ :=
  culturalEmbedding C a d - culturalEmbedding C b d

/-- Cultural negotiation gap is antisymmetric. -/
theorem cultural_negotiation_antisymm (C a b d : I) :
    culturalNegotiationGap C a b d = -culturalNegotiationGap C b a d := by
  unfold culturalNegotiationGap; ring

/-- Negotiation gap vanishes for identical ideas. -/
theorem cultural_negotiation_self (C a d : I) :
    culturalNegotiationGap C a a d = 0 := by
  unfold culturalNegotiationGap; ring

end CulturalTurn

/-! ## §37. Post-Colonial Translation Theory

Tejaswini Niranjana (Siting Translation, 1992) and Gayatri Spivak
argue that translation is never neutral — it is always embedded in
power relations. Colonial translation "domesticates" the Other;
post-colonial translation resists this by preserving alterity. -/

section PostColonialTranslation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Colonial translation: the colonizer's lens L forces the source
    into the colonizer's framework. This is refraction through
    the colonial gaze. -/
noncomputable def colonialTranslation (colonialLens source : I) : I :=
  compose colonialLens source

/-- Niranjana's asymmetry of colonial translation: the colonial lens
    adds its own resonance on top of the source. The gap measures
    epistemic violence. -/
noncomputable def epistemicViolence (colonialLens source observer : I) : ℝ :=
  rs (colonialTranslation colonialLens source) observer - rs source observer

/-- Epistemic violence is zero when the colonial lens is void
    (i.e., transparent, non-colonial). -/
theorem epistemic_violence_void (source observer : I) :
    epistemicViolence (void : I) source observer = 0 := by
  unfold epistemicViolence colonialTranslation; simp

/-- Epistemic violence decomposes into emergence + direct lens effect.
    Spivak: the violence is both structural (emergence) and direct. -/
theorem epistemic_violence_decompose (L source observer : I) :
    epistemicViolence L source observer = emergence L source observer + rs L observer := by
  unfold epistemicViolence colonialTranslation emergence; ring

/-- Post-colonial resistance: a translation that counteracts the colonial
    lens by minimizing resonance with the colonial norm. -/
noncomputable def resistanceDegree (φ : I → I) (a colonialNorm : I) : ℝ :=
  rs a colonialNorm - rs (φ a) colonialNorm

/-- Identity has zero resistance (it doesn't change anything). -/
theorem id_zero_resistance (a colonialNorm : I) :
    resistanceDegree (id : I → I) a colonialNorm = 0 := by
  unfold resistanceDegree; simp

/-- Spivak's "strategic essentialism": using the colonizer's own
    categories to resist. Modeled as composing source WITH the colonial
    lens, then measuring how it reshapes the lens's own resonance. -/
noncomputable def strategicEssentialism (source colonialLens : I) : ℝ :=
  rs (compose source colonialLens) colonialLens - rs colonialLens colonialLens

/-- Strategic essentialism with void source: silence doesn't resist. -/
theorem strategic_essentialism_void (colonialLens : I) :
    strategicEssentialism (void : I) colonialLens = 0 := by
  unfold strategicEssentialism; simp

/-- Niranjana's double bind: the translator is caught between
    preserving source authenticity and making it intelligible.
    The measure is the gap between fidelity to source and to target. -/
noncomputable def doubleBind (φ : I → I) (a source target : I) : ℝ :=
  |rs (φ a) source - rs a source| + |rs (φ a) target - rs a target|

/-- Identity has zero double bind. -/
theorem id_zero_doubleBind (a source target : I) :
    doubleBind (id : I → I) a source target = 0 := by
  unfold doubleBind; simp

end PostColonialTranslation

/-! ## §38. Machine Translation — Formal Limits

Formalizing the inherent limitations of machine translation:
optimizing for one criterion creates blind spots for others.
This extends §22 with deeper structural results. -/

section MachineTranslationLimits
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An MT system is loss-minimizing for a pair (a,b) under observer c
    if the absolute relevance gap is zero. -/
def mtLossMinimal (φ : I → I) (a c : I) : Prop :=
  rs (φ a) c = rs a c

/-- Loss-minimal for void observer is trivially true. -/
theorem mt_loss_void (φ : I → I) (a : I) :
    mtLossMinimal φ a (void : I) := by
  unfold mtLossMinimal; simp [rs_void_right']

/-- Loss-minimality for c is exactly dynamic equivalence at c. -/
theorem mt_loss_eq_dynamic (φ : I → I) (c : I) :
    (∀ a, mtLossMinimal φ a c) ↔ dynamicEquivalence φ c :=
  Iff.rfl

/-- Composition preserves loss-minimality. -/
theorem mt_loss_comp (φ ψ : I → I) (a c : I)
    (hφ : mtLossMinimal φ a c) (hψ : mtLossMinimal ψ (φ a) c) :
    mtLossMinimal (ψ ∘ φ) a c := by
  unfold mtLossMinimal at *; simp [Function.comp]; linarith

/-- The MT emergence gap: how much emergence is missed by the MT system.
    Measures what no loss function can capture about compositional meaning. -/
noncomputable def mtEmergenceGap (φ : I → I) (a b c : I) : ℝ :=
  emergence a b c - emergence (φ a) (φ b) c

/-- Author-oriented + compositional MT has zero emergence gap. -/
theorem faithful_mt_zero_gap (φ : I → I) (ha : authorOriented φ) (hc : compositional φ)
    (a b c : I) : mtEmergenceGap φ a b c = 0 :=
  authorOriented_zero_effacement φ ha hc a b c

/-- The MT fidelity-fluency trade-off: faithful translation may not
    be compositional, and vice versa. We formalize: if both hold, identity. -/
theorem mt_fidelity_fluency_id (φ : I → I)
    (hf : faithful φ) (hc : compositional φ) (hv : voidPreserving φ) :
    formalEquivalence φ :=
  ⟨hf, hc⟩

end MachineTranslationLimits

/-! ## §39. Multimodal Translation

Translation between modalities: text → image, speech → writing,
music → dance. Each modality is a different "section" of the ideatic
space with its own resonance patterns. We model modalities as
projection maps. -/

section MultimodalTranslation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A modality is a projection: applying it twice is the same as once.
    "Once you're in visual mode, re-visualizing doesn't change anything." -/
def isModality (π : I → I) : Prop := ∀ a, π (π a) = π a

/-- Identity is trivially a modality. -/
theorem id_isModality : isModality (id : I → I) := fun _ => rfl

/-- The cross-modal gap: how much resonance changes when one idea
    is projected to a different modality. -/
noncomputable def crossModalGap (π : I → I) (a b : I) : ℝ :=
  rs (π a) b - rs a b

/-- Identity has zero cross-modal gap. -/
theorem id_zero_crossModalGap (a b : I) :
    crossModalGap (id : I → I) a b = 0 := by
  unfold crossModalGap; simp

/-- Modal self-distortion: how much a modality changes self-resonance. -/
noncomputable def modalSelfDistortion (π : I → I) (a : I) : ℝ :=
  rs (π a) (π a) - rs a a

/-- Intralingual modalities have zero self-distortion. -/
theorem intralingual_modal_distortion (π : I → I) (h : intralingual π)
    (a : I) : modalSelfDistortion π a = 0 := by
  unfold modalSelfDistortion; rw [h a]; ring

/-- Cross-modal emergence: the emergence that arises from composing
    ideas from different modalities. -/
noncomputable def crossModalEmergence (π₁ π₂ : I → I) (a b c : I) : ℝ :=
  emergence (π₁ a) (π₂ b) c

/-- Same-modality emergence reduces to standard emergence on projected ideas. -/
theorem same_modal_emergence (π : I → I) (a b c : I) :
    crossModalEmergence π π a b c = emergence (π a) (π b) c := rfl

/-- Void modality produces zero cross-modal emergence with void observer. -/
theorem void_crossModalEmergence (π : I → I) (hv : voidPreserving π)
    (b c : I) :
    crossModalEmergence π id (void : I) b c = emergence (void : I) b c := by
  unfold crossModalEmergence; rw [hv]; rfl

/-- Multimodal composition: composing across modalities. -/
noncomputable def multimodalCompose (π₁ π₂ : I → I) (a b : I) : I :=
  compose (π₁ a) (π₂ b)

/-- Multimodal composition with identities is standard composition. -/
theorem multimodal_id (a b : I) :
    multimodalCompose (id : I → I) (id : I → I) a b = compose a b := rfl

/-- Multimodal composition with void left. -/
theorem multimodal_void_left (π₁ π₂ : I → I) (hv : voidPreserving π₁)
    (b : I) : multimodalCompose π₁ π₂ (void : I) b = π₂ b := by
  unfold multimodalCompose; rw [hv]; simp

end MultimodalTranslation

/-! ## §40. Translation Universals

Baker (1993) and Laviosa-Braithwaite (1998) proposed "translation
universals" — features that are common to ALL translations regardless
of language pair:
1. **Simplification**: translations are simpler than originals
2. **Explicitation**: translations make implicit information explicit
3. **Normalization**: translations gravitate toward conventional patterns
4. **Leveling-out**: translations are more homogeneous than originals -/

section TranslationUniversals
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Simplification: the translation reduces self-resonance (weight).
    Simpler ideas have less "resonance mass." -/
def simplifying (φ : I → I) (a : I) : Prop :=
  rs (φ a) (φ a) ≤ rs a a

/-- Identity is not simplifying (unless trivial). More precisely,
    identity is exactly weight-preserving, hence weakly simplifying. -/
theorem id_weakly_simplifying (a : I) :
    simplifying (id : I → I) a := le_refl _

/-- Explicitation: the translation increases resonance with a specific
    "explicit meaning" observer e. -/
def explicitating (φ : I → I) (a e : I) : Prop :=
  rs (φ a) e ≥ rs a e

/-- Identity is weakly explicitating. -/
theorem id_weakly_explicitating (a e : I) :
    explicitating (id : I → I) a e := le_refl _

/-- Normalization: the translation makes the idea more "standard" —
    closer to a norm n in resonance. -/
def normalizing (φ : I → I) (a n : I) : Prop :=
  |rs (φ a) n - rs n n| ≤ |rs a n - rs n n|

/-- Identity is trivially normalizing. -/
theorem id_normalizing (a n : I) :
    normalizing (id : I → I) a n := le_refl _

/-- Leveling out: two different ideas become more alike under translation.
    Measured by their resonance getting closer to each other. -/
def levelingOut (φ : I → I) (a b c : I) : Prop :=
  |rs (φ a) c - rs (φ b) c| ≤ |rs a c - rs b c|

/-- Identity trivially levels out. -/
theorem id_levelingOut (a b c : I) :
    levelingOut (id : I → I) a b c := le_refl _

/-- A faithful translation levels out trivially (exact preservation). -/
theorem faithful_levelingOut (φ : I → I) (h : faithful φ) (a b c : I)
    (hc : φ c = c) : levelingOut φ a b c := by
  unfold levelingOut
  have h1 := h a c; rw [hc] at h1
  have h2 := h b c; rw [hc] at h2
  rw [h1, h2]

/-- A simplifying, explicitating translation is a "typical" translation
    in Baker's sense. -/
def bakerTypical (φ : I → I) (a e : I) : Prop :=
  simplifying φ a ∧ explicitating φ a e

/-- Identity is Baker-typical (weakly). -/
theorem id_bakerTypical (a e : I) :
    bakerTypical (id : I → I) a e :=
  ⟨id_weakly_simplifying a, id_weakly_explicitating a e⟩

end TranslationUniversals

/-! ## §41. Translation Group Structure

The set of faithful translations forms a group under composition
(with identity as unit). More generally, we study the algebraic
structure of translation maps. -/

section TranslationGroup
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The composition of two faithful maps is faithful. (Closure) -/
theorem faithful_group_closure (φ ψ : I → I) (hφ : faithful φ)
    (hψ : faithful ψ) : faithful (ψ ∘ φ) :=
  faithful_comp ψ φ hψ hφ

/-- Identity is faithful. (Identity element) -/
theorem faithful_group_id : faithful (id : I → I) := id_faithful

/-- Faithful translations associate under composition. -/
theorem faithful_group_assoc (φ ψ χ : I → I) :
    (χ ∘ ψ) ∘ φ = χ ∘ (ψ ∘ φ) := by
  ext x; simp [Function.comp]

/-- The compositional translations also form a monoid. -/
theorem compositional_monoid_closure (φ ψ : I → I) (hφ : compositional φ)
    (hψ : compositional ψ) : compositional (ψ ∘ φ) :=
  compositional_comp ψ φ hψ hφ

/-- Compositional monoid identity. -/
theorem compositional_monoid_id : compositional (id : I → I) :=
  id_compositional

/-- The void-preserving translations form a monoid. -/
theorem voidPres_monoid_closure (φ ψ : I → I) (hφ : voidPreserving φ)
    (hψ : voidPreserving ψ) : voidPreserving (ψ ∘ φ) := by
  show (ψ ∘ φ) void = void
  change ψ (φ void) = void
  rw [hφ, hψ]

/-- Void-preserving monoid identity. -/
theorem voidPres_monoid_id : voidPreserving (id : I → I) :=
  id_voidPreserving

end TranslationGroup

/-! ## §42. Translation Invariants

A translation invariant is a quantity that remains unchanged under
all faithful translations. We study which resonance-derived quantities
are invariants. -/

section TranslationInvariants
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Self-resonance is a translation invariant under faithful maps. -/
theorem selfRS_invariant (φ : I → I) (h : faithful φ) (a : I) :
    rs (φ a) (φ a) = rs a a := h a a

/-- Pairwise resonance is a translation invariant under faithful maps. -/
theorem pairRS_invariant (φ : I → I) (h : faithful φ) (a b : I) :
    rs (φ a) (φ b) = rs a b := h a b

/-- Emergence between pairs is invariant under faithful translation
    (when the observer is also in the image). -/
theorem emergence_invariant_faithful (φ : I → I) (h : faithful φ)
    (hc : compositional φ) (a b c : I) :
    emergence (φ a) (φ b) (φ c) = emergence a b c := by
  unfold emergence
  rw [← hc a b, h (compose a b) c, h a c, h b c]

/-- The resonance gap (asymmetry) is preserved by faithful translation. -/
theorem asymmetry_invariant (φ : I → I) (h : faithful φ) (a b : I) :
    rs (φ a) (φ b) - rs (φ b) (φ a) = rs a b - rs b a := by
  rw [h a b, h b a]

/-- Translation fidelity composition: the triangle inequality of distortion.
    For chains φ → ψ, total distortion = sum of distortions. -/
theorem fidelity_triangle (φ ψ : I → I) (a b : I) :
    translationFidelity (ψ ∘ φ) a b =
    translationFidelity ψ (φ a) (φ b) + translationFidelity φ a b := by
  unfold translationFidelity; simp only [Function.comp]; ring

/-- The semantic charge is preserved by faithful + compositional translations. -/
theorem charge_invariant (φ : I → I) (hf : faithful φ) (hc : compositional φ)
    (a : I) : semanticCharge (φ a) = semanticCharge a := by
  unfold semanticCharge
  exact emergence_invariant_faithful φ hf hc a a a

end TranslationInvariants

/-! ## §43. Translation Kernel

The kernel of a translation φ is the set of ideas that become void
under φ. This measures what the translation "annihilates." -/

section TranslationKernel
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An idea is in the kernel of φ if it maps to void. -/
def inKernel (φ : I → I) (a : I) : Prop := φ a = void

/-- Void is always in the kernel of a void-preserving translation. -/
theorem void_in_kernel (φ : I → I) (hφ : voidPreserving φ) :
    inKernel φ (void : I) := hφ

/-- Kernel elements have zero self-resonance after translation. -/
theorem kernel_zero_selfRS (φ : I → I) (a : I) (h : inKernel φ a) :
    rs (φ a) (φ a) = 0 := by
  rw [h]; exact rs_void_void

/-- Kernel elements are "invisible" after translation: they have
    zero resonance with everything. -/
theorem kernel_invisible_left (φ : I → I) (a b : I) (h : inKernel φ a) :
    rs (φ a) b = 0 := by
  rw [h]; exact rs_void_left' b

/-- Kernel elements are invisible from the right too. -/
theorem kernel_invisible_right (φ : I → I) (a b : I) (h : inKernel φ a) :
    rs b (φ a) = 0 := by
  rw [h]; exact rs_void_right' b

/-- The kernel of a faithful translation is trivial: only void maps to void.
    A faithful translation annihilates nothing. -/
theorem faithful_trivial_kernel (φ : I → I) (h : faithful φ) (a : I)
    (hk : inKernel φ a) : a = void := by
  apply rs_nondegen'
  have h1 := h a a
  rw [hk] at h1
  rw [rs_void_void] at h1
  linarith

/-- If a is in the kernel, composing a with anything maps to void
    under a compositional φ: the kernel is an ideal. -/
theorem kernel_compose_left (φ : I → I) (hc : compositional φ) (a b : I)
    (h : inKernel φ a) : φ (compose a b) = compose void (φ b) := by
  rw [hc a b, h]

/-- Kernel is closed under left-composition for compositional maps. -/
theorem kernel_left_absorb (φ : I → I) (hc : compositional φ) (a b : I)
    (h : inKernel φ a) : φ (compose a b) = φ b := by
  rw [kernel_compose_left φ hc a b h]; simp

/-- Two kernel elements compose to a kernel element (for compositional,
    void-preserving translations). -/
theorem kernel_compose_closed (φ : I → I) (hc : compositional φ)
    (hv : voidPreserving φ) (a b : I)
    (ha : inKernel φ a) (hb : inKernel φ b) :
    inKernel φ (compose a b) := by
  unfold inKernel at *
  rw [hc a b, ha, hb]; simp

end TranslationKernel

/-! ## §44. Translation Orbit and Stabilizer

For a fixed idea a, the orbit of a under a family of translations
reveals the "space of possible translations." The stabilizer is the
set of translations that leave a unchanged. -/

section OrbitStabilizer
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The orbit resonance: how the translated versions of a resonate with b. -/
noncomputable def orbitResonance (φ : I → I) (a b : I) : ℝ :=
  rs (φ a) b

/-- Orbit resonance of identity is just resonance. -/
theorem orbit_id (a b : I) :
    orbitResonance (id : I → I) a b = rs a b := rfl

/-- A stabilizer element fixes a. -/
def isStabilizer (φ : I → I) (a : I) : Prop := φ a = a

/-- Identity is in every stabilizer. -/
theorem id_in_stabilizer (a : I) :
    isStabilizer (id : I → I) a := rfl

/-- Stabilizer elements compose: if φ and ψ fix a, so does ψ ∘ φ. -/
theorem stabilizer_comp (φ ψ : I → I) (a : I)
    (hφ : isStabilizer φ a) (hψ : isStabilizer ψ a) :
    isStabilizer (ψ ∘ φ) a := by
  unfold isStabilizer at *; simp [Function.comp, hφ, hψ]

/-- Stabilizer elements preserve self-resonance of the fixed idea. -/
theorem stabilizer_selfRS (φ : I → I) (a : I) (h : isStabilizer φ a) :
    rs (φ a) (φ a) = rs a a := by rw [h]

/-- Stabilizer elements have zero fidelity on the fixed idea. -/
theorem stabilizer_zero_fidelity (φ : I → I) (a : I) (h : isStabilizer φ a) :
    translationFidelity φ a a = 0 := by
  unfold translationFidelity; rw [h]; ring

/-- The orbit distance: how far the translation moves a in resonance space. -/
noncomputable def orbitDistance (φ : I → I) (a : I) : ℝ :=
  rs a a + rs (φ a) (φ a) - 2 * rs a (φ a)

/-- Stabilizer elements have zero orbit distance. -/
theorem stabilizer_zero_distance (φ : I → I) (a : I) (h : isStabilizer φ a) :
    orbitDistance φ a = 0 := by
  unfold orbitDistance; rw [h]; ring

/-- Identity has zero orbit distance. -/
theorem id_zero_orbit (a : I) :
    orbitDistance (id : I → I) a = 0 := by
  unfold orbitDistance; simp; ring

end OrbitStabilizer

/-! ## §45. Schleiermacher Revisited — The Translator's Invisibility

Venuti (1995) extended Schleiermacher: the translator is "invisible"
when domesticating (the translation reads as if originally in the
target language) and "visible" when foreignizing. We formalize
translator visibility via resonance. -/

section TranslatorVisibility
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Translator visibility: how much the translator's presence is
    detectable. Measured by the gap between translated and original
    self-resonance. -/
noncomputable def translatorVisibility (φ : I → I) (a : I) : ℝ :=
  |rs (φ a) (φ a) - rs a a|

/-- Identity translator is invisible. -/
theorem id_invisible (a : I) :
    translatorVisibility (id : I → I) a = 0 := by
  unfold translatorVisibility; simp

/-- Faithful translators are invisible. -/
theorem faithful_invisible (φ : I → I) (h : faithful φ) (a : I) :
    translatorVisibility φ a = 0 := by
  unfold translatorVisibility; rw [h a a]; simp

/-- Intralingual translations are invisible (they preserve self-resonance). -/
theorem intralingual_invisible (φ : I → I) (h : intralingual φ) (a : I) :
    translatorVisibility φ a = 0 := by
  unfold translatorVisibility; rw [h a]; simp

/-- The visibility-fidelity connection: visibility equals |expansion degree|. -/
theorem visibility_eq_expansion (φ : I → I) (a : I) :
    translatorVisibility φ a = |expansionDegree φ a| := rfl

end TranslatorVisibility

/-! ## §46. Abductive Inference Chains

Extending §28: chains of abductive interpretation model how a text
passes through multiple translators, each adding their own
interpretive layer. -/

section AbductiveChains
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Sequential abduction: two translators read the same source. -/
noncomputable def dualAbduction (t₁ t₂ source : I) : I :=
  compose (abductiveReading t₁ source) (abductiveReading t₂ source)

/-- Dual abduction with void first translator. -/
theorem dual_abduction_void_first (t₂ source : I) :
    dualAbduction (void : I) t₂ source =
    compose source (compose t₂ source) := by
  unfold dualAbduction abductiveReading; simp

/-- Dual abduction with void second translator. -/
theorem dual_abduction_void_second (t₁ source : I) :
    dualAbduction t₁ (void : I) source =
    compose (compose t₁ source) source := by
  unfold dualAbduction abductiveReading; simp

/-- Cascaded translation: translator 2 reads what translator 1 produced. -/
noncomputable def cascadedTranslation (t₁ t₂ f₁ f₂ source : I) : I :=
  abductiveTranslation t₂ f₂ (abductiveTranslation t₁ f₁ source)

/-- Cascaded translation with all-void is identity. -/
theorem cascaded_all_void :
    cascadedTranslation (void : I) (void : I) (void : I) (void : I) (void : I) = (void : I) := by
  unfold cascadedTranslation abductiveTranslation abductiveReading reencode; simp

end AbductiveChains

/-! ## §47. Translation Distance and Metric-Like Properties

We study the "distance" between two translations — how much they
differ on average. This gives a pseudo-metric on the space of
translations. -/

section TranslationDistance
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Pointwise translation distance: how far apart φ and ψ move
    an idea a, as measured by an observer c. -/
noncomputable def translationPointDist (φ ψ : I → I) (a c : I) : ℝ :=
  rs (φ a) c - rs (ψ a) c

/-- Translation distance is antisymmetric. -/
theorem translationPointDist_antisymm (φ ψ : I → I) (a c : I) :
    translationPointDist φ ψ a c = -translationPointDist ψ φ a c := by
  unfold translationPointDist; ring

/-- Translation distance of a map with itself is zero. -/
theorem translationPointDist_self (φ : I → I) (a c : I) :
    translationPointDist φ φ a c = 0 := by
  unfold translationPointDist; ring

/-- Translation distance triangle decomposition: φ→χ = φ→ψ + ψ→χ. -/
theorem translationPointDist_triangle (φ ψ χ : I → I) (a c : I) :
    translationPointDist φ χ a c =
    translationPointDist φ ψ a c + translationPointDist ψ χ a c := by
  unfold translationPointDist; ring

/-- Distance from identity measures "how much translation moves a." -/
theorem dist_from_id (φ : I → I) (a c : I) :
    translationPointDist φ id a c = rs (φ a) c - rs a c := rfl

/-- Translation distance with void observer is always zero. -/
theorem translationPointDist_void_observer (φ ψ : I → I) (a : I) :
    translationPointDist φ ψ a (void : I) = 0 := by
  unfold translationPointDist; simp [rs_void_right']

end TranslationDistance

/-! ## §48. Translation and Emergence Preservation

Deep structural results on how translation interacts with the
fundamental emergence structure of the ideatic space. -/

section EmergencePreservation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Emergence preservation degree: how much of the original emergence
    is retained under translation. -/
noncomputable def emergencePreservation (φ : I → I) (a b c : I) : ℝ :=
  emergence (φ a) (φ b) (φ c) - emergence a b c

/-- Identity perfectly preserves emergence. -/
theorem id_emergence_preservation (a b c : I) :
    emergencePreservation (id : I → I) a b c = 0 := by
  unfold emergencePreservation; simp

/-- Faithful + compositional translations preserve emergence. -/
theorem faithful_comp_emergence (φ : I → I) (hf : faithful φ)
    (hc : compositional φ) (a b c : I) :
    emergencePreservation φ a b c = 0 := by
  unfold emergencePreservation
  rw [emergence_invariant_faithful φ hf hc a b c]; ring

/-- The emergence cocycle is preserved by faithful + compositional maps. -/
theorem cocycle_preserved (φ : I → I) (hf : faithful φ) (hc : compositional φ)
    (a b c d : I) :
    emergence (φ a) (φ b) (φ d) + emergence (compose (φ a) (φ b)) (φ c) (φ d) =
    emergence (φ b) (φ c) (φ d) + emergence (φ a) (compose (φ b) (φ c)) (φ d) := by
  have h1 := cocycle_condition (φ a) (φ b) (φ c) (φ d)
  exact h1

/-- Void-preservation ensures emergence with void is maintained. -/
theorem void_emergence_preserved (φ : I → I) (hv : voidPreserving φ)
    (b c : I) : emergence (φ (void : I)) (φ b) c = emergence (void : I) (φ b) c := by
  rw [hv]

end EmergencePreservation

/-! ## §49. Translation Equivalence Classes

Two translations are "resonance-equivalent" if they produce ideas
with the same resonance profile. This is weaker than pointwise
equality. -/

section TranslationEquivClasses
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Pointwise resonance equivalence: φ and ψ produce ideas that
    resonate identically with everything. -/
def pointwiseEquiv (φ ψ : I → I) (a : I) : Prop :=
  ∀ c, rs (φ a) c = rs (ψ a) c

/-- Pointwise equivalence at void is trivial for void-preserving maps. -/
theorem pointwiseEquiv_void (φ ψ : I → I) (hφ : voidPreserving φ)
    (hψ : voidPreserving ψ) : pointwiseEquiv φ ψ (void : I) := by
  intro c; rw [hφ, hψ]

/-- Identity is pointwise equivalent to itself. -/
theorem pointwiseEquiv_refl (φ : I → I) (a : I) :
    pointwiseEquiv φ φ a := fun _ => rfl

/-- Pointwise equivalence is symmetric. -/
theorem pointwiseEquiv_symm (φ ψ : I → I) (a : I) (h : pointwiseEquiv φ ψ a) :
    pointwiseEquiv ψ φ a :=
  fun c => (h c).symm

/-- Pointwise equivalence is transitive. -/
theorem pointwiseEquiv_trans (φ ψ χ : I → I) (a : I)
    (h1 : pointwiseEquiv φ ψ a) (h2 : pointwiseEquiv ψ χ a) :
    pointwiseEquiv φ χ a :=
  fun c => (h1 c).trans (h2 c)

/-- Pointwise equivalent translations have the same relevance gap. -/
theorem pointwiseEquiv_relevanceGap (φ ψ : I → I) (a c : I)
    (h : pointwiseEquiv φ ψ a) : relevanceGap φ a c = relevanceGap ψ a c := by
  unfold relevanceGap; rw [h c]

end TranslationEquivClasses

/-! ## §50. Translation and Order Sensitivity

How does translation interact with the order sensitivity of ideas?
Order sensitivity measures non-commutativity; translation can
increase or decrease it. -/

section TranslationOrder
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The order sensitivity shift: how much translation changes the
    non-commutativity of a pair. -/
noncomputable def orderSensitivityShift (φ : I → I) (a b c : I) : ℝ :=
  orderSensitivity (φ a) (φ b) c - orderSensitivity a b c

/-- Identity has zero order sensitivity shift. -/
theorem id_zero_orderShift (a b c : I) :
    orderSensitivityShift (id : I → I) a b c = 0 := by
  unfold orderSensitivityShift; simp

/-- Order sensitivity shift is antisymmetric in a, b. -/
theorem orderShift_swap (φ : I → I) (a b c : I) :
    orderSensitivityShift φ a b c = -orderSensitivityShift φ b a c := by
  unfold orderSensitivityShift orderSensitivity; ring

/-- Author-oriented + compositional translations preserve order sensitivity. -/
theorem authorOriented_comp_orderSensitivity (φ : I → I) (ha : authorOriented φ)
    (hc : compositional φ) (a b c : I) :
    orderSensitivityShift φ a b c = 0 := by
  unfold orderSensitivityShift orderSensitivity
  have h1 : rs (compose (φ a) (φ b)) c = rs (compose a b) c := by
    have := (hc a b).symm
    rw [show compose (φ a) (φ b) = φ (compose a b) from this.symm ▸ rfl]
    exact ha (compose a b) c
  have h2 : rs (compose (φ b) (φ a)) c = rs (compose b a) c := by
    have := (hc b a).symm
    rw [show compose (φ b) (φ a) = φ (compose b a) from this.symm ▸ rfl]
    exact ha (compose b a) c
  linarith

/-- The meaning curvature shift under translation. -/
noncomputable def curvatureShift (φ : I → I) (a b c : I) : ℝ :=
  meaningCurvature (φ a) (φ b) c - meaningCurvature a b c

/-- Identity has zero curvature shift. -/
theorem id_zero_curvatureShift (a b c : I) :
    curvatureShift (id : I → I) a b c = 0 := by
  unfold curvatureShift; simp

/-- Curvature shift equals order sensitivity shift (by definition). -/
theorem curvatureShift_eq_orderShift (φ : I → I) (a b c : I) :
    curvatureShift φ a b c = orderSensitivityShift φ a b c := by
  unfold curvatureShift orderSensitivityShift meaningCurvature orderSensitivity emergence
  ring

end TranslationOrder

/-! ## §51. Deep Mathematics: Translation as Homomorphism

A translation that is both faithful and compositional is a
homomorphism of ideatic spaces. We derive consequences. -/

section TranslationHomomorphism
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A translation homomorphism preserves all algebraic and
    resonance structure. -/
def isHomomorphism (φ : I → I) : Prop :=
  faithful φ ∧ compositional φ ∧ voidPreserving φ

/-- Identity is a homomorphism. -/
theorem id_isHomomorphism : isHomomorphism (id : I → I) :=
  ⟨id_faithful, id_compositional, id_voidPreserving⟩

/-- Homomorphisms compose. -/
theorem homomorphism_comp (φ ψ : I → I) (hφ : isHomomorphism φ)
    (hψ : isHomomorphism ψ) : isHomomorphism (ψ ∘ φ) :=
  ⟨faithful_comp ψ φ hψ.1 hφ.1,
   compositional_comp ψ φ hψ.2.1 hφ.2.1,
   voidPres_monoid_closure φ ψ hφ.2.2 hψ.2.2⟩

/-- Homomorphisms preserve emergence exactly. -/
theorem homomorphism_emergence (φ : I → I) (h : isHomomorphism φ)
    (a b c : I) : emergence (φ a) (φ b) (φ c) = emergence a b c :=
  emergence_invariant_faithful φ h.1 h.2.1 a b c

/-- Homomorphisms preserve the cocycle condition. -/
theorem homomorphism_cocycle (φ : I → I) (h : isHomomorphism φ)
    (a b c d : I) :
    emergence (φ a) (φ b) (φ d) + emergence (compose (φ a) (φ b)) (φ c) (φ d) =
    emergence (φ b) (φ c) (φ d) + emergence (φ a) (compose (φ b) (φ c)) (φ d) :=
  cocycle_preserved φ h.1 h.2.1 a b c d

/-- Homomorphisms preserve semantic charge. -/
theorem homomorphism_charge (φ : I → I) (h : isHomomorphism φ) (a : I) :
    semanticCharge (φ a) = semanticCharge a :=
  charge_invariant φ h.1 h.2.1 a

/-- Homomorphisms preserve iterated composition. -/
theorem homomorphism_composeN (φ : I → I) (h : isHomomorphism φ) (a : I) :
    ∀ n, φ (composeN a n) = composeN (φ a) n :=
  calque_composeN φ h.2.1 h.2.2 a

/-- Homomorphisms preserve non-voidness. -/
theorem homomorphism_ne_void (φ : I → I) (h : isHomomorphism φ) (a : I)
    (ha : a ≠ void) : φ a ≠ void := by
  intro heq
  have := faithful_trivial_kernel φ h.1 a heq
  exact ha this

/-- Homomorphisms preserve self-resonance positivity. -/
theorem homomorphism_selfRS_pos (φ : I → I) (h : isHomomorphism φ)
    (a : I) (ha : a ≠ void) : rs (φ a) (φ a) > 0 := by
  rw [h.1 a a]; exact rs_self_pos a ha

end TranslationHomomorphism

/-! ## §52. Translation Quotient — What's Left After Translation

The "quotient" of translation: what remains of the source after
the translation has done its work. Connects to Benjamin's "afterlife"
of the text. -/

section TranslationQuotient
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The afterlife of an idea under translation: the composition of
    the original with its translation. Benjamin: the original lives
    on THROUGH its translations. -/
noncomputable def afterlife (φ : I → I) (a : I) : I :=
  compose a (φ a)

/-- Afterlife of void is void (for void-preserving translations). -/
theorem afterlife_void (φ : I → I) (hv : voidPreserving φ) :
    afterlife φ (void : I) = (void : I) := by
  unfold afterlife; rw [hv]; simp

/-- The afterlife self-resonance is at least the original's.
    Benjamin: translation enriches, never diminishes. -/
theorem afterlife_enriches (φ : I → I) (a : I) :
    rs (afterlife φ a) (afterlife φ a) ≥ rs a a := by
  unfold afterlife; exact compose_enriches' a (φ a)

/-- The afterlife under identity is just repetition. -/
theorem afterlife_id (a : I) :
    afterlife (id : I → I) a = compose a a := rfl

/-- The translation surplus: how much the afterlife exceeds the original. -/
noncomputable def translationSurplus (φ : I → I) (a : I) : ℝ :=
  rs (afterlife φ a) (afterlife φ a) - rs a a

/-- Translation surplus is non-negative. -/
theorem surplus_nonneg (φ : I → I) (a : I) :
    translationSurplus φ a ≥ 0 := by
  unfold translationSurplus
  linarith [afterlife_enriches φ a]

/-- Void has zero surplus. -/
theorem surplus_void (φ : I → I) (hv : voidPreserving φ) :
    translationSurplus φ (void : I) = 0 := by
  unfold translationSurplus afterlife; rw [hv]; simp

end TranslationQuotient

/-! ## §53. Dialectical Translation — Thesis/Antithesis/Synthesis

Hegelian dialectical translation: the source (thesis) meets the
target language (antithesis) and produces a new text (synthesis)
that transcends both. -/

section DialecticalTranslation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The dialectical product of translation: composing source with
    its translation. The "synthesis" of original and translation. -/
noncomputable def dialecticalProduct (φ : I → I) (a : I) : I :=
  compose a (φ a)

/-- The dialectical tension in translation: how much the synthesis
    exceeds the sum of thesis (a) and antithesis (φ a). -/
noncomputable def dialecticalTranslationTension (φ : I → I) (a c : I) : ℝ :=
  emergence a (φ a) c

/-- Identity dialectical tension is self-emergence. -/
theorem id_dialectical_tension (a c : I) :
    dialecticalTranslationTension (id : I → I) a c = emergence a a c := rfl

/-- Dialectical tension with void source is zero. -/
theorem dialectical_void_source (φ : I → I) (hv : voidPreserving φ) (c : I) :
    dialecticalTranslationTension φ (void : I) c = 0 := by
  unfold dialecticalTranslationTension; rw [hv]
  exact emergence_void_left (void : I) c

/-- Dialectical tension against void observer is zero. -/
theorem dialectical_void_observer (φ : I → I) (a : I) :
    dialecticalTranslationTension φ a (void : I) = 0 := by
  unfold dialecticalTranslationTension; exact emergence_against_void a (φ a)

/-- The aufhebung measure: total dialectical enrichment.
    How much the synthesis exceeds the thesis in self-resonance. -/
noncomputable def aufhebung (φ : I → I) (a : I) : ℝ :=
  rs (dialecticalProduct φ a) (dialecticalProduct φ a) - rs a a

/-- The aufhebung is non-negative: the synthesis is always at least
    as "present" as the thesis. Hegel's sublation enriches. -/
theorem aufhebung_nonneg (φ : I → I) (a : I) :
    aufhebung φ a ≥ 0 := by
  unfold aufhebung dialecticalProduct
  linarith [compose_enriches' a (φ a)]

end DialecticalTranslation

/-! ## §54. Translation and Polysemy

Polysemous ideas (those with multiple resonance patterns) pose
special challenges for translation. We study how translation
interacts with polysemy. -/

section TranslationPolysemy
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The polysemy gap: how much translation changes the polysemous
    nature of an idea. Measured by change in resonance asymmetry
    between two observers. -/
noncomputable def polysemyGap (φ : I → I) (a c d : I) : ℝ :=
  (rs (φ a) c - rs (φ a) d) - (rs a c - rs a d)

/-- Identity has zero polysemy gap. -/
theorem id_zero_polysemyGap (a c d : I) :
    polysemyGap (id : I → I) a c d = 0 := by
  unfold polysemyGap; simp

/-- Polysemy gap is antisymmetric in the observers. -/
theorem polysemyGap_antisymm (φ : I → I) (a c d : I) :
    polysemyGap φ a c d = -polysemyGap φ a d c := by
  unfold polysemyGap; ring

/-- The sense disambiguation measure: how much translation reduces
    polysemous ambiguity relative to two observers. -/
noncomputable def senseDisambiguation (φ : I → I) (a c d : I) : ℝ :=
  |rs a c - rs a d| - |rs (φ a) c - rs (φ a) d|

/-- Identity has zero disambiguation. -/
theorem id_zero_disambiguation (a c d : I) :
    senseDisambiguation (id : I → I) a c d = 0 := by
  unfold senseDisambiguation; simp

end TranslationPolysemy

/-! ## §55. Translation Networks and Relay Translation

In practice, translation often proceeds through relay languages:
A → B → C where B is an intermediary. We study the properties
of relay networks. -/

section RelayTranslation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The relay error: how much additional distortion the intermediary
    step introduces beyond what direct translation would give. -/
noncomputable def relayError (φ_AB φ_BC φ_AC : I → I) (a b : I) : ℝ :=
  translationFidelity (φ_BC ∘ φ_AB) a b - translationFidelity φ_AC a b

/-- If the relay goes through faithful intermediary, relay error
    equals the difference of the two translations' fidelities. -/
theorem relay_faithful_mid (φ_AB φ_BC φ_AC : I → I)
    (hAB : faithful φ_AB) (a b : I) :
    relayError φ_AB φ_BC φ_AC a b =
    translationFidelity φ_BC (φ_AB a) (φ_AB b) - translationFidelity φ_AC a b := by
  unfold relayError
  rw [fidelity_triangle φ_AB φ_BC a b, faithful_zero_fidelity φ_AB hAB a b]
  ring

/-- If all legs are faithful, relay error is zero. -/
theorem relay_faithful_zero (φ_AB φ_BC φ_AC : I → I)
    (hAB : faithful φ_AB) (hBC : faithful φ_BC) (hAC : faithful φ_AC)
    (a b : I) : relayError φ_AB φ_BC φ_AC a b = 0 := by
  unfold relayError
  have h1 : translationFidelity (φ_BC ∘ φ_AB) a b = 0 :=
    faithful_zero_fidelity _ (faithful_comp φ_BC φ_AB hBC hAB) a b
  have h2 : translationFidelity φ_AC a b = 0 :=
    faithful_zero_fidelity _ hAC a b
  linarith

/-- Relay self-composition: using the same translation as relay.
    The error measures how much φ² deviates from φ. -/
noncomputable def selfRelayError (φ : I → I) (a b : I) : ℝ :=
  translationFidelity (φ ∘ φ) a b - translationFidelity φ a b

/-- Faithful translations have zero self-relay error. -/
theorem faithful_selfRelay (φ : I → I) (h : faithful φ) (a b : I) :
    selfRelayError φ a b = 0 := by
  unfold selfRelayError
  have h1 : translationFidelity (φ ∘ φ) a b = 0 :=
    faithful_zero_fidelity _ (faithful_comp φ φ h h) a b
  have h2 : translationFidelity φ a b = 0 :=
    faithful_zero_fidelity _ h a b
  linarith

end RelayTranslation

/-! ## §56. Translation Entropy Bounds

Information-theoretic bounds on translation quality. The emergence
bounded axiom gives us Cauchy-Schwarz-like bounds on translation
distortion. -/

section TranslationBounds
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The translation emergence is bounded: its square is non-negative,
    giving us a trivial but foundational bound. -/
theorem translation_emergence_sq_nonneg (φ : I → I) (a b c : I) :
    (translationEmergence φ a b c) ^ 2 ≥ 0 :=
  sq_nonneg _

/-- Self-distortion is bounded for void (it's zero). -/
theorem selfDistortion_void (φ : I → I) (hv : voidPreserving φ) :
    selfDistortion φ (void : I) = 0 := by
  unfold selfDistortion; rw [hv]; ring

/-- Weight change is bounded below by the negative of the original weight.
    You can't lose more weight than you have. -/
theorem weightChange_lower_bound (φ : I → I) (a : I) :
    weightChange φ a ≥ -(rs a a) := by
  unfold weightChange
  linarith [rs_self_nonneg' (φ a)]

end TranslationBounds

/-! ## §57. Translation Conjugation

Two translations are conjugate if one can be obtained from the other
by pre- and post-composition with a third. This captures the idea that
"essentially the same translation" can look different in different
coordinates. -/

section TranslationConjugation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- φ and ψ are conjugate via χ: ψ = χ ∘ φ ∘ χ⁻¹ (informally).
    Since we don't have inverses in general, we use a weaker form:
    ψ is obtained from φ by sandwiching with χ and ρ. -/
def isConjugate (φ ψ χ ρ : I → I) : Prop :=
  ∀ a, ψ a = χ (φ (ρ a))

/-- Conjugation is reflexive (φ is conjugate to itself via id). -/
theorem conjugate_refl (φ : I → I) :
    isConjugate φ φ id id := fun _ => rfl

/-- Conjugation of faithful maps via faithful maps is faithful. -/
theorem conjugate_faithful (φ ψ χ ρ : I → I)
    (hconj : isConjugate φ ψ χ ρ) (hφ : faithful φ)
    (hχ : faithful χ) (hρ : faithful ρ) : faithful ψ := by
  intro a b
  rw [hconj a, hconj b]
  rw [hχ (φ (ρ a)) (φ (ρ b))]
  rw [hφ (ρ a) (ρ b)]
  rw [hρ a b]

end TranslationConjugation

/-! ## §58. Translation and Semantic Charge Dynamics

How does translation affect the "self-amplification" properties of ideas?
Semantic charge measures whether an idea grows or decays under repetition;
translation can change this dynamics. -/

section ChargeTranslation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The charge shift: how much translation changes semantic charge. -/
noncomputable def chargeShift (φ : I → I) (a : I) : ℝ :=
  semanticCharge (φ a) - semanticCharge a

/-- Identity has zero charge shift. -/
theorem id_zero_chargeShift (a : I) :
    chargeShift (id : I → I) a = 0 := by
  unfold chargeShift; simp

/-- Homomorphisms have zero charge shift. -/
theorem homomorphism_zero_chargeShift (φ : I → I) (h : isHomomorphism φ)
    (a : I) : chargeShift φ a = 0 := by
  unfold chargeShift; rw [homomorphism_charge φ h a]; ring

/-- The dialectical tension shift: how translation changes the
    dialectical potential of an idea. -/
noncomputable def dialecticalShift (φ : I → I) (a c : I) : ℝ :=
  dialecticalTension (φ a) (φ a) - dialecticalTension a a

/-- Identity has zero dialectical shift. -/
theorem id_zero_dialecticalShift (a c : I) :
    dialecticalShift (id : I → I) a c = 0 := by
  unfold dialecticalShift; simp

end ChargeTranslation

/-! ## §59. Eco's "Saying Almost the Same Thing"

Umberto Eco (2003) argued that translation is always "saying almost
the same thing" — perfect translation is impossible, but good
translation is possible through negotiation. We formalize the
"almost" as bounded distortion. -/

section EcoNegotiation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An ε-faithful translation: resonance distortion bounded by ε.
    Eco's "almost the same thing" formalized. -/
def epsilonFaithful (φ : I → I) (a b : I) (ε : ℝ) : Prop :=
  |translationFidelity φ a b| ≤ ε

/-- A faithful translation is 0-faithful. -/
theorem faithful_epsilon_zero (φ : I → I) (h : faithful φ) (a b : I) :
    epsilonFaithful φ a b 0 := by
  unfold epsilonFaithful; rw [faithful_zero_fidelity φ h a b]; simp

/-- Identity is 0-faithful. -/
theorem id_epsilon_zero (a b : I) :
    epsilonFaithful (id : I → I) a b 0 := by
  unfold epsilonFaithful translationFidelity; simp

/-- ε-faithfulness is monotone in ε. -/
theorem epsilon_mono (φ : I → I) (a b : I) (ε₁ ε₂ : ℝ) (h : ε₁ ≤ ε₂)
    (hf : epsilonFaithful φ a b ε₁) : epsilonFaithful φ a b ε₂ := by
  unfold epsilonFaithful at *; linarith

/-- The negotiation margin: how much room the translator has.
    Eco: every translation is a negotiation between fidelity and readability. -/
noncomputable def negotiationMargin (φ : I → I) (a b : I) (budget : ℝ) : ℝ :=
  budget - |translationFidelity φ a b|

/-- Faithful translations use zero budget. -/
theorem faithful_full_margin (φ : I → I) (h : faithful φ) (a b : I)
    (budget : ℝ) : negotiationMargin φ a b budget = budget := by
  unfold negotiationMargin; rw [faithful_zero_fidelity φ h a b]; simp

end EcoNegotiation

/-! ## §60. Catford's Translation Shifts

J. C. Catford (1965) categorized translation shifts:
level shifts (between phonology, grammar, lexis) and category shifts.
We model these as different "projections" of the resonance structure. -/

section CatfordShifts
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A level shift: the translation operates at a different level of
    linguistic structure. Modeled as translating then embedding in a level. -/
noncomputable def levelShift (φ : I → I) (level : I → I) (a : I) : I :=
  level (φ a)

/-- Level shift with identity level is just translation. -/
theorem levelShift_id_level (φ : I → I) (a : I) :
    levelShift φ id a = φ a := rfl

/-- Level shift with identity translation is just level projection. -/
theorem levelShift_id_trans (level : I → I) (a : I) :
    levelShift id level a = level a := rfl

/-- A category shift: the translation changes the grammatical category.
    Modeled as the gap between translation at two different levels. -/
noncomputable def categoryShift (φ : I → I) (l₁ l₂ : I → I) (a c : I) : ℝ :=
  rs (levelShift φ l₁ a) c - rs (levelShift φ l₂ a) c

/-- Category shift with identical levels is zero. -/
theorem categoryShift_same (φ : I → I) (l : I → I) (a c : I) :
    categoryShift φ l l a c = 0 := by
  unfold categoryShift; ring

/-- Category shift is antisymmetric in levels. -/
theorem categoryShift_antisymm (φ : I → I) (l₁ l₂ : I → I) (a c : I) :
    categoryShift φ l₁ l₂ a c = -categoryShift φ l₂ l₁ a c := by
  unfold categoryShift; ring

end CatfordShifts

end IDT3
