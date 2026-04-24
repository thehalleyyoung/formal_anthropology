import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Hermeneutics — The Theory of Interpretation

Gadamer's key insight: interpretation is a **fusion of horizons**. The reader
brings their own horizon (repertoire of ideas) and the text brings its horizon.
Reading = composing text with the reader's existing ideas.

In the quantitative resonance framework of IDT v2:

- **Reading changes the reader**: after reading text `t`, reader `r` becomes
  `compose r t` — a strictly richer idea with higher self-resonance.
- **Understanding** = positive resonance between reader and text.
- **Hermeneutic gain** = the increase in the reader's self-resonance from reading.
  This is always non-negative (Gadamer's optimism: genuine reading always enriches).
- **The hermeneutic circle**: iterated reading of the same text deepens understanding
  monotonically — each re-reading grows the reader's self-resonance.
- **Shared reading**: two readers who read the same text resonate at least as strongly
  with each other as they did before (a formalization of community through shared texts).

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Interpretation

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Core Definitions -/

/-- Reading: the reader composes the text with their existing horizon.
    After reading text `t`, reader `r` becomes `compose r t`. -/
def reading (text reader : I) : I := compose reader text

/-- The hermeneutic gain: the increase in the reader's self-resonance from reading.
    Measures how much richer the reader becomes after engaging with the text. -/
noncomputable def hermeneuticGain (text reader : I) : ℝ :=
  resonanceStrength (reading text reader) (reading text reader) -
  resonanceStrength reader reader

/-- Understanding: the reader positively resonates with the text.
    This is a stronger condition than mere non-negative resonance. -/
def understands (reader text : I) : Prop :=
  resonanceStrength reader text > 0

/-- The comprehension gap: how much less the reader resonates with
    the text compared to their own self-resonance. -/
noncomputable def comprehensionGap (reader text : I) : ℝ :=
  resonanceStrength reader reader - resonanceStrength reader text

/-- The fusion of horizons (Horizontverschmelzung): the composed idea
    resulting from the reader engaging with the text. -/
def fusionOfHorizons (reader text : I) : I := compose reader text

/-- Iterated reading: reading the same text `n` times.
    Models the hermeneutic circle — re-reading deepens understanding. -/
def iteratedReading (text : I) : ℕ → I → I
  | 0, reader => reader
  | n + 1, reader => reading text (iteratedReading text n reader)

/-! ## §2. Basic Reading Theorems -/

/-- Reading nothing doesn't change the reader (void text = no text). -/
@[simp] theorem reading_void_text (reader : I) :
    reading (void : I) reader = reader := by
  unfold reading; exact IdeaticSpace2.void_right reader

/-- A blank slate simply becomes the text (void reader absorbs text). -/
@[simp] theorem reading_void_reader (text : I) :
    reading text (void : I) = text := by
  unfold reading; exact IdeaticSpace2.void_left text

/-- Sequential reading is reading the composition: reading `t₂` after `t₁`
    equals reading `compose t₁ t₂` at once. This is Gadamer's insight
    that prior readings shape subsequent ones. -/
theorem reading_assoc (t₁ t₂ reader : I) :
    reading t₂ (reading t₁ reader) = reading (compose t₁ t₂) reader := by
  unfold reading; exact IDT2.compose_assoc reader t₁ t₂

/-- The depth of a reading is bounded by the sum of depths. -/
theorem reading_depth_bound (text reader : I) :
    depth (reading text reader) ≤ depth reader + depth text := by
  unfold reading; exact IdeaticSpace2.depth_subadditive reader text

/-- The fusion of horizons IS the reading — just different terminology. -/
theorem fusion_is_reading (reader text : I) :
    fusionOfHorizons reader text = reading text reader := rfl

/-- Double reading: reading a text twice = reading its double. -/
theorem double_reading (text reader : I) :
    reading text (reading text reader) = reading (compose text text) reader := by
  exact reading_assoc text text reader

/-- Reading a text twice is the same as reading its square. -/
theorem double_reading_eq_composeN (text reader : I) :
    reading text (reading text reader) =
    compose reader (composeN text 2) := by
  unfold reading
  rw [IDT2.compose_assoc, composeN_two]

/-- Reading grows self-resonance: the reader becomes "weightier" after reading.
    This is Gadamer's optimism: genuine engagement always enriches. -/
theorem reading_self_resonance_grows (text reader : I) :
    resonanceStrength (reading text reader) (reading text reader) ≥
    resonanceStrength reader reader := by
  unfold reading; exact rs_compose_self_right reader text

/-- Reading absorbs the text's weight: the fusion resonates at least as
    strongly as the text alone. -/
theorem reading_absorbs_text_weight (text reader : I) :
    resonanceStrength (reading text reader) (reading text reader) ≥
    resonanceStrength text text := by
  unfold reading; exact rs_compose_self_left text reader

/-! ## §3. Hermeneutic Gain -/

/-- The hermeneutic gain is always non-negative.
    Reading can never diminish the reader — a key Gadamerian insight. -/
theorem hermeneutic_gain_nonneg (text reader : I) :
    hermeneuticGain text reader ≥ 0 := by
  unfold hermeneuticGain
  linarith [reading_self_resonance_grows (I := I) text reader]

/-- Reading nothing yields zero gain. -/
theorem hermeneutic_gain_void_text (reader : I) :
    hermeneuticGain (void : I) reader = 0 := by
  unfold hermeneuticGain
  simp [reading_void_text]

/-- A blank slate gains the text's self-resonance minus the unit resonance. -/
theorem hermeneutic_gain_void_reader (text : I) :
    hermeneuticGain text (void : I) =
    resonanceStrength text text - 1 := by
  unfold hermeneuticGain
  simp [reading_void_reader, IdeaticSpace2.rs_void_self]

/-- The gain of a blank slate reading is non-negative (since rs ≥ 1). -/
theorem hermeneutic_gain_void_reader_nonneg (text : I) :
    hermeneuticGain text (void : I) ≥ 0 := by
  rw [hermeneutic_gain_void_reader]
  linarith [rs_self_ge_one (I := I) text]

/-- The hermeneutic gain equals the resonance excess from the foundations. -/
theorem hermeneutic_gain_eq_excess (text reader : I) :
    hermeneuticGain text reader = resonanceExcess reader text := by
  simp only [hermeneuticGain, resonanceExcess, reading]

/-- Sequential reading: the total gain of reading t₁ then t₂ is at least
    the gain of reading t₁ alone. -/
theorem hermeneutic_gain_sequential_mono (t₁ t₂ reader : I) :
    hermeneuticGain (compose t₁ t₂) reader ≥
    hermeneuticGain t₁ reader := by
  unfold hermeneuticGain reading
  have h := rs_compose_self_right (compose reader t₁) t₂
  rw [IDT2.compose_assoc] at h
  linarith

/-! ## §4. Understanding -/

/-- Self-understanding: every idea positively resonates with itself.
    "To be is to understand oneself." -/
theorem self_understanding (a : I) : understands a a :=
  rs_self_pos' a

/-- Understanding is symmetric: if the reader understands the text,
    the text "understands" the reader. A formalization of the
    dialogical nature of interpretation. -/
theorem understanding_symm {reader text : I} :
    understands reader text → understands text reader := by
  unfold understands; rw [IdeaticSpace2.rs_symm]; exact id

/-- Understanding is reflexive: everything understands itself. -/
theorem understanding_refl (a : I) : understands a a :=
  self_understanding a

/-- Void understands itself (void has unit self-resonance = 1 > 0). -/
theorem void_self_understanding :
    understands (void : I) (void : I) := by
  unfold understands; rw [IdeaticSpace2.rs_void_self]; linarith

/-- Shared reading preserves mutual resonance: if two readers both read the same
    text, they resonate at least as strongly as before. Reading shared texts
    builds community. -/
theorem shared_reading_preserves_resonance (r₁ r₂ text : I) :
    resonanceStrength (reading text r₁) (reading text r₂) ≥
    resonanceStrength r₁ r₂ := by
  unfold reading; exact rs_compose_both_mono r₁ r₂ text

/-- If two readers understand each other, they still understand each other
    after reading the same text. Shared reading preserves understanding. -/
theorem shared_reading_preserves_understanding (r₁ r₂ text : I)
    (h : understands r₁ r₂) :
    understands (reading text r₁) (reading text r₂) := by
  unfold understands at *
  have hmono := shared_reading_preserves_resonance (I := I) r₁ r₂ text
  linarith

/-- If a reader understands an idea, the reader after absorbing ANY text
    via common context still resonates positively.
    More precisely: composing a common prefix preserves understanding. -/
theorem understanding_left_context (r t ctx : I) :
    resonanceStrength (compose ctx r) (compose ctx t) ≥
    resonanceStrength r t := by
  exact IdeaticSpace2.rs_compose_left_mono r t ctx

/-- After composing a common context, understanding is preserved. -/
theorem understanding_left_context_preserves (r t ctx : I) (h : understands r t) :
    understands (compose ctx r) (compose ctx t) := by
  unfold understands at *
  linarith [understanding_left_context (I := I) r t ctx]

/-- Understanding of self after reading: after reading, the reader's fusion
    resonates with itself at least as strongly as before. -/
theorem reading_self_resonance_ge_one (text reader : I) :
    resonanceStrength (reading text reader) (reading text reader) ≥ 1 := by
  unfold reading; exact rs_compose_ge_one reader text

/-! ## §5. The Comprehension Gap -/

/-- The comprehension gap with yourself is zero: you perfectly understand yourself. -/
theorem comprehensionGap_self (a : I) :
    comprehensionGap a a = 0 := by
  unfold comprehensionGap; linarith

/-- When the text's self-resonance doesn't exceed the reader's,
    the comprehension gap is non-negative. The reader resonates more
    with themselves than with any "simpler" text. -/
theorem comprehensionGap_nonneg_when (reader text : I)
    (h : resonanceStrength text text ≤ resonanceStrength reader reader) :
    comprehensionGap reader text ≥ 0 := by
  unfold comprehensionGap
  linarith [rs_le_self_when (I := I) reader text h]

/-- The comprehension gap is bounded by the self-resonance. -/
theorem comprehensionGap_le_self (reader text : I) :
    comprehensionGap reader text ≤ resonanceStrength reader reader := by
  unfold comprehensionGap
  linarith [IdeaticSpace2.rs_nonneg reader text]

/-! ## §6. The Hermeneutic Circle — Iterated Reading -/

/-- Zero iterations: no reading means no change. -/
@[simp] theorem iteratedReading_zero (text : I) (reader : I) :
    iteratedReading text 0 reader = reader := rfl

/-- The successor step: one more reading. -/
theorem iteratedReading_succ (text : I) (n : ℕ) (reader : I) :
    iteratedReading text (n + 1) reader =
    reading text (iteratedReading text n reader) := rfl

/-- Iterated reading equals composing with n copies of the text.
    This connects the hermeneutic circle to the algebraic structure. -/
theorem iteratedReading_eq_composeN (text : I) :
    ∀ (n : ℕ) (reader : I),
    iteratedReading text n reader = compose reader (composeN text n)
  | 0, reader => by simp [iteratedReading, composeN]
  | n + 1, reader => by
    simp only [iteratedReading, reading, composeN]
    rw [iteratedReading_eq_composeN text n reader]
    exact IDT2.compose_assoc reader (composeN text n) text

/-- Self-resonance grows monotonically with each re-reading.
    The hermeneutic circle deepens understanding at every turn. -/
theorem iteratedReading_self_resonance_mono (text : I) (n : ℕ) (reader : I) :
    resonanceStrength (iteratedReading text (n + 1) reader)
                      (iteratedReading text (n + 1) reader) ≥
    resonanceStrength (iteratedReading text n reader)
                      (iteratedReading text n reader) := by
  simp only [iteratedReading_succ]
  exact reading_self_resonance_grows (I := I) text (iteratedReading text n reader)

/-- After n readings, self-resonance is at least the original reader's. -/
theorem iteratedReading_self_resonance_ge_base (text : I) :
    ∀ (n : ℕ) (reader : I),
    resonanceStrength (iteratedReading text n reader)
                      (iteratedReading text n reader) ≥
    resonanceStrength reader reader
  | 0, reader => by simp [iteratedReading]
  | n + 1, reader => by
    have ih := iteratedReading_self_resonance_ge_base text n reader
    have step := iteratedReading_self_resonance_mono (I := I) text n reader
    linarith

/-- Depth of iterated reading is bounded. -/
theorem iteratedReading_depth_bound (text : I) :
    ∀ (n : ℕ) (reader : I),
    depth (iteratedReading text n reader) ≤ depth reader + n * depth text
  | 0, reader => by simp [iteratedReading]
  | n + 1, reader => by
    rw [iteratedReading_eq_composeN]
    have h1 := IdeaticSpace2.depth_subadditive reader (composeN text (n + 1))
    have h2 := depth_composeN_le (I := I) text (n + 1)
    omega

/-- Iterating void text is the identity: re-reading nothing changes nothing. -/
@[simp] theorem iteratedReading_void_text :
    ∀ (n : ℕ) (reader : I),
    iteratedReading (void : I) n reader = reader
  | 0, reader => rfl
  | n + 1, reader => by
    simp only [iteratedReading, reading]
    rw [iteratedReading_void_text n reader]
    exact IdeaticSpace2.void_right reader

/-- Iterated reading from void reader produces n copies of the text. -/
theorem iteratedReading_void_reader (text : I) (n : ℕ) :
    iteratedReading text n (void : I) = composeN text n := by
  rw [iteratedReading_eq_composeN]; simp

/-- The self-resonance after n readings is always ≥ 1. -/
theorem iteratedReading_self_resonance_ge_one (text : I) (n : ℕ) (reader : I) :
    resonanceStrength (iteratedReading text n reader)
                      (iteratedReading text n reader) ≥ 1 := by
  have h := iteratedReading_self_resonance_ge_base (I := I) text n reader
  linarith [rs_self_ge_one (I := I) reader]

/-! ## §7. Hermeneutic Community -/

/-- A reading community: a collection of readers who all read the same text. -/
structure ReadingCommunity (I : Type*) [IdeaticSpace2 I] where
  text : I
  members : List I

/-- After shared reading, every pair of members resonates at least as
    strongly as before. This is the mathematical foundation of how
    shared texts build intellectual communities. -/
theorem community_resonance_grows (r₁ r₂ text : I) :
    resonanceStrength (reading text r₁) (reading text r₂) ≥
    resonanceStrength r₁ r₂ :=
  shared_reading_preserves_resonance r₁ r₂ text

/-- Hermeneutic gain is non-negative for all community members. -/
theorem community_all_gain (text : I) (reader : I) :
    hermeneuticGain text reader ≥ 0 :=
  hermeneutic_gain_nonneg text reader

/-- In a community of shared reading, the "weight" of each member
    grows: self-resonance is monotonically non-decreasing. -/
theorem community_weight_grows (text : I) (reader : I) :
    resonanceStrength (reading text reader) (reading text reader) ≥
    resonanceStrength reader reader :=
  reading_self_resonance_grows text reader

end IDT2.Interpretation
