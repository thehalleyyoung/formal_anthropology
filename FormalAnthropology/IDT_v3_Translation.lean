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

end IDT3
