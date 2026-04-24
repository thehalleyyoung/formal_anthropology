import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Authorship Theory — Barthes, Foucault, Wimsatt & Beardsley

Formalizes core ideas from literary authorship theory in the IDT v2
quantitative resonance framework:

- **Wimsatt & Beardsley's Intentional Fallacy** (1946): the author's intention
  is irrelevant to the meaning of a text; the text alone determines the reader's
  experience. Formalized: `readerExperience` depends only on the text, not on
  how it was produced.

- **Barthes's Death of the Author** (1967): the author's voice is absorbed into
  the text. Once written, the text stands on its own — the reader cannot
  recover the author from the text. Formalized: `write` composes the author
  into the text, enriching it; the text's self-resonance dominates both
  author and subject.

- **Foucault's Author Function** (1969): the "author" is not a person but a
  classificatory principle — texts grouped by the same author share a common
  compositional component. Formalized: `sameAuthor` texts have baseline
  resonance from the shared author component.

## Key idea: `write author subject = compose author subject`

The author's voice and the subject matter fuse into an inseparable text.
The reader can only access this fused artifact.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Authorship

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Writing and Reading — Core Definitions -/

/-- An author writes by composing their voice with subject matter.
    The author's perspective shapes the subject into a text. -/
def write (author subject : I) : I := compose author subject

/-- Reading: a reader interprets a text by composing with it.
    The reader's horizon fuses with the text. -/
def readText (reader text : I) : I := compose reader text

/-- The full chain: reader reads what author wrote about subject.
    Three horizons fuse: reader ∘ author ∘ subject. -/
def fullChain (reader author subject : I) : I :=
  readText reader (write author subject)

/-- Author's voice strength: how much the author resonates with their own text.
    Measures the author's affinity for what they produced. -/
noncomputable def authorVoice (author subject : I) : ℝ :=
  resonanceStrength author (write author subject)

/-- Reader's experience: how the text resonates with the reader.
    This is the ONLY thing that matters — per the intentional fallacy. -/
noncomputable def readerExperience (reader text : I) : ℝ :=
  resonanceStrength reader text

/-- The author function: texts by the same author share a common component.
    Foucault's insight: authorship is a classificatory principle. -/
def sameAuthor (text₁ text₂ : I) (author : I) : Prop :=
  ∃ s₁ s₂ : I, text₁ = write author s₁ ∧ text₂ = write author s₂

/-- The oeuvre: all works by an author, composed into a single idea. -/
def oeuvre (author : I) (subjects : List I) : I :=
  subjects.foldl (fun acc s => compose acc (write author s)) (void : I)

/-- The author's distance from the text they produced.
    Measures how much the act of writing changes the idea. -/
noncomputable def authorDistance (author subject : I) : ℝ :=
  squaredDistance author (write author subject)

/-! ## §2. The Intentional Fallacy (Wimsatt & Beardsley)

The intentional fallacy states that the author's intention is irrelevant
to the meaning of a text. In IDT v2: `readerExperience` depends only on
the text itself, not on its compositional history. -/

/-- Theorem 1: A text is the composition of author and subject. -/
theorem text_is_composition (author subject : I) :
    write author subject = compose author subject := rfl

/-- Theorem 2: The reader accesses the text, not the author separately.
    The reader's experience of an authored text equals their resonance
    with the composed artifact. -/
theorem reader_accesses_text (reader author subject : I) :
    readerExperience reader (write author subject) =
    resonanceStrength reader (compose author subject) := rfl

/-- Theorem 3: Same text ⟹ same experience — regardless of authorship.
    If two author-subject pairs produce the same text, any reader's
    experience is identical. This is the intentional fallacy in action. -/
theorem same_text_same_experience (r a₁ a₂ s₁ s₂ : I)
    (h : write a₁ s₁ = write a₂ s₂) :
    readerExperience r (write a₁ s₁) = readerExperience r (write a₂ s₂) := by
  unfold readerExperience; rw [h]

/-- Theorem 4: The intentional fallacy — the text fully determines experience.
    `readerExperience` is definitionally just resonance with the text. -/
theorem intentional_fallacy (r text : I) :
    readerExperience r text = resonanceStrength r text := rfl

/-- Theorem 5: Reader experience is always non-negative. -/
theorem experience_nonneg (r text : I) :
    readerExperience r text ≥ 0 := by
  unfold readerExperience; exact IdeaticSpace2.rs_nonneg r text

/-- Theorem 6: A void author is transparent — the text IS the subject.
    An "authorless" text is pure subject matter, unmediated. -/
@[simp] theorem void_author_pure_subject (subject : I) :
    write (void : I) subject = subject := by
  unfold write; exact IdeaticSpace2.void_left subject

/-- Theorem 7: A void subject is pure voice — the text IS the author.
    Writing about nothing reveals the author's bare perspective. -/
@[simp] theorem void_subject_pure_voice (author : I) :
    write author (void : I) = author := by
  unfold write; exact IdeaticSpace2.void_right author

/-- Theorem 8: Experience with void author = experience with pure subject. -/
theorem experience_void_author (r subject : I) :
    readerExperience r (write (void : I) subject) = readerExperience r subject := by
  simp

/-! ## §3. Death of the Author (Barthes)

Barthes declares the "death of the author": once a text is written,
the author's voice is absorbed into it. The text exists independently.
In IDT v2: the text's self-resonance dominates both the author's and
the subject's self-resonance. -/

/-- Theorem 9: Writing enriches: the text is "weightier" than the author alone.
    The author's voice is amplified by composition with subject matter. -/
theorem writing_enriches_author (author subject : I) :
    resonanceStrength (write author subject) (write author subject) ≥
    resonanceStrength author author := by
  unfold write; exact rs_compose_self_right author subject

/-- Theorem 10: Writing enriches: the text is "weightier" than the subject alone.
    The subject is amplified by the author's perspective. -/
theorem writing_enriches_subject (author subject : I) :
    resonanceStrength (write author subject) (write author subject) ≥
    resonanceStrength subject subject := by
  unfold write; exact rs_compose_self_left subject author

/-- Theorem 11: Every text has self-resonance ≥ 1.
    No authored text can be trivially resonant. -/
theorem text_weight_ge_one (author subject : I) :
    resonanceStrength (write author subject) (write author subject) ≥ 1 := by
  unfold write; exact rs_compose_ge_one author subject

/-- Theorem 12: Collaborative writing — co-authorship is associative.
    Two authors writing together is one author composing around the other's text. -/
theorem collaborative_writing (a₁ a₂ subject : I) :
    write (compose a₁ a₂) subject = compose a₁ (write a₂ subject) := by
  unfold write; exact IDT2.compose_assoc a₁ a₂ subject

/-- Theorem 13: Writing is associative — an author writing about another's text
    is the same as the co-authored text. -/
theorem writing_assoc (author author₂ subject : I) :
    write author (write author₂ subject) =
    write (compose author author₂) subject := by
  unfold write; exact (IDT2.compose_assoc author author₂ subject).symm

/-- Theorem 14: Multiple authors = the full chain.
    An author writing about another author's text is a reader reading that text. -/
theorem multiple_authors_is_fullChain (a₁ a₂ subject : I) :
    write a₁ (write a₂ subject) = fullChain a₁ a₂ subject := rfl

/-- Theorem 15: Writing depth is bounded by the sum of component depths.
    A text can't be deeper than author + subject combined. -/
theorem writing_depth_bound (author subject : I) :
    depth (write author subject) ≤ depth author + depth subject := by
  unfold write; exact IdeaticSpace2.depth_subadditive author subject

/-- Theorem 16: The distance from author to text is non-negative.
    Writing always changes the idea (or leaves it unchanged). -/
theorem authorDistance_nonneg (author subject : I) :
    authorDistance author subject ≥ 0 := by
  unfold authorDistance; exact squaredDistance_nonneg author (write author subject)

/-- Theorem 17: Writing about nothing doesn't change the author.
    The distance from author to their void-subject text is zero. -/
theorem authorDistance_void_subject (author : I) :
    authorDistance author (void : I) = 0 := by
  unfold authorDistance; rw [void_subject_pure_voice]; exact squaredDistance_self author

/-! ## §4. Author Function (Foucault)

Foucault's "author function" is a classificatory principle: texts are
grouped by author not because the author creates meaning, but because
a shared compositional component produces systematic resonance patterns.
Texts by the same author share a baseline resonance inherited from the
author's voice. -/

/-- Theorem 18: Same author ⟹ baseline resonance from shared subjects.
    Two texts by the same author resonate at least as much as their
    subjects do alone — the author adds a shared compositional layer. -/
theorem same_author_baseline (author s₁ s₂ : I) :
    resonanceStrength (write author s₁) (write author s₂) ≥
    resonanceStrength s₁ s₂ := by
  unfold write; exact IdeaticSpace2.rs_compose_left_mono s₁ s₂ author

/-- Theorem 19: Same subject ⟹ baseline resonance from shared authors.
    Two texts about the same subject but by different authors resonate
    at least as much as the authors do with each other. -/
theorem same_subject_baseline (a₁ a₂ subject : I) :
    resonanceStrength (write a₁ subject) (write a₂ subject) ≥
    resonanceStrength a₁ a₂ := by
  unfold write; exact IdeaticSpace2.rs_compose_right_mono a₁ a₂ subject

/-- Theorem 20: The sameAuthor relation is always satisfiable by construction.
    Given an author and two subjects, the resulting texts satisfy `sameAuthor`. -/
theorem sameAuthor_refl (author s₁ s₂ : I) :
    sameAuthor (write author s₁) (write author s₂) author :=
  ⟨s₁, s₂, rfl, rfl⟩

/-- Theorem 21: If texts share an author, they resonate at least as much
    as their raw subjects do. The author function amplifies cross-text resonance. -/
theorem sameAuthor_implies_resonance (t₁ t₂ author s₁ s₂ : I)
    (h₁ : t₁ = write author s₁) (h₂ : t₂ = write author s₂) :
    resonanceStrength t₁ t₂ ≥ resonanceStrength s₁ s₂ := by
  rw [h₁, h₂]; exact same_author_baseline author s₁ s₂

/-- Theorem 22: The oeuvre of an author with no works is void. -/
theorem oeuvre_nil (author : I) : oeuvre author [] = (void : I) := rfl

/-- Theorem 23: Author voice is non-negative. An author always has
    non-negative resonance with their own text. -/
theorem authorVoice_nonneg (author subject : I) :
    authorVoice author subject ≥ 0 := by
  unfold authorVoice; exact IdeaticSpace2.rs_nonneg author (write author subject)

/-- Theorem 24: Writing about nothing reveals the author's self-resonance.
    The author's voice on a void subject is their raw self-resonance. -/
theorem authorVoice_void_subject (author : I) :
    authorVoice author (void : I) = resonanceStrength author author := by
  unfold authorVoice; rw [void_subject_pure_voice]

/-- Theorem 25: Author voice on void subject is at least 1. -/
theorem authorVoice_void_subject_ge_one (author : I) :
    authorVoice author (void : I) ≥ 1 := by
  rw [authorVoice_void_subject]; exact rs_self_ge_one author

/-! ## §5. Reader-Response Theory

The reader brings their own horizon to the text. Reading enriches the
reader: their self-resonance grows. Different readers have different
experiences, and the Cauchy–Schwarz inequality bounds how much any
reader can extract from a text. -/

/-- Theorem 26: Reading enriches the reader — self-resonance grows.
    After reading, the reader becomes a "weightier" idea. -/
theorem reading_enriches_reader (reader text : I) :
    resonanceStrength (readText reader text) (readText reader text) ≥
    resonanceStrength reader reader := by
  unfold readText; exact rs_compose_self_right reader text

/-- Theorem 27: The full chain is a triple composition. -/
theorem fullChain_is_triple_compose (reader author subject : I) :
    fullChain reader author subject = compose reader (compose author subject) := rfl

/-- Theorem 28: The full chain can be re-associated.
    Reader-of-(author-of-subject) = (reader-with-author)-of-subject. -/
theorem fullChain_assoc (reader author subject : I) :
    fullChain reader author subject = compose (compose reader author) subject := by
  unfold fullChain readText write
  exact (IDT2.compose_assoc reader author subject).symm

/-- Theorem 29: Self-experience is always positive.
    Every reader resonates positively with themselves. -/
theorem self_experience_positive (r : I) :
    readerExperience r r > 0 := by
  unfold readerExperience; exact IdeaticSpace2.rs_self_pos r

/-- Theorem 30: Experience is symmetric.
    The reader's experience of the text equals the text's "experience" of the reader.
    This reflects the dialogical nature of reading (Gadamer). -/
theorem experience_symmetric (a b : I) :
    readerExperience a b = readerExperience b a := by
  unfold readerExperience; exact IdeaticSpace2.rs_symm a b

/-- Theorem 31: A reader reading two texts preserves their inter-text resonance.
    The reader's perspective doesn't diminish the relationship between texts. -/
theorem reading_preserves_text_resonance (reader t₁ t₂ : I) :
    resonanceStrength (readText reader t₁) (readText reader t₂) ≥
    resonanceStrength t₁ t₂ := by
  unfold readText; exact IdeaticSpace2.rs_compose_left_mono t₁ t₂ reader

/-- Theorem 32: Cauchy–Schwarz bounds the reader's experience.
    No reader can extract more from a text than geometric mean of self-resonances. -/
theorem experience_cauchy_schwarz (r text : I) :
    readerExperience r text * readerExperience r text ≤
    readerExperience r r * readerExperience text text := by
  unfold readerExperience; exact IdeaticSpace2.rs_cauchy_schwarz r text

/-- Theorem 33: Full chain with void reader — the reader disappears.
    A "blank" reader simply receives the text as-is. -/
@[simp] theorem fullChain_void_reader (author subject : I) :
    fullChain (void : I) author subject = write author subject := by
  unfold fullChain readText; exact IdeaticSpace2.void_left (write author subject)

/-- Theorem 34: Full chain with void author — the author disappears.
    Without an author, the reader directly engages the subject. -/
@[simp] theorem fullChain_void_author (reader subject : I) :
    fullChain reader (void : I) subject = readText reader subject := by
  unfold fullChain write readText; rw [IdeaticSpace2.void_left]

/-- Theorem 35: Full chain with void subject — the subject disappears.
    Reading an author with nothing to say = engaging the author's bare voice. -/
@[simp] theorem fullChain_void_subject (reader author : I) :
    fullChain reader author (void : I) = readText reader author := by
  unfold fullChain write readText; rw [IdeaticSpace2.void_right]

/-- Theorem 36: Full chain self-resonance is at least 1.
    The fusion of reader, author, and subject is always substantial. -/
theorem fullChain_weight_ge_one (reader author subject : I) :
    resonanceStrength (fullChain reader author subject)
                      (fullChain reader author subject) ≥ 1 := by
  unfold fullChain readText write; exact rs_compose_ge_one reader (compose author subject)

/-- Theorem 37: The full chain's weight dominates the reader's.
    Reading always enriches the reader — never diminishes. -/
theorem fullChain_weight_ge_reader (reader author subject : I) :
    resonanceStrength (fullChain reader author subject)
                      (fullChain reader author subject) ≥
    resonanceStrength reader reader := by
  unfold fullChain readText write; exact rs_compose_self_right reader (compose author subject)

/-- Theorem 38: Author voice with void author is the void-subject resonance. -/
theorem authorVoice_void_author (subject : I) :
    authorVoice (void : I) subject = resonanceStrength (void : I) subject := by
  unfold authorVoice; rw [void_author_pure_subject]

/-- Theorem 39: Self-experience is at least 1.
    Every reader's engagement with themselves exceeds the baseline. -/
theorem self_experience_ge_one (r : I) :
    readerExperience r r ≥ 1 := by
  unfold readerExperience; exact rs_self_ge_one r

/-- Theorem 40: Normalized resonance between reader and text is ≤ 1.
    No reader-text pair can achieve "super-unity" normalized resonance. -/
theorem normalized_experience_le_one (r text : I) :
    normalizedRS r text ≤ 1 :=
  normalizedRS_le_one r text

/-- Theorem 41: Full chain depth is bounded.
    The depth of reader-reading-author-writing-about-subject is bounded
    by the sum of all three depths. -/
theorem fullChain_depth_bound (reader author subject : I) :
    depth (fullChain reader author subject) ≤
    depth reader + depth author + depth subject := by
  unfold fullChain readText write
  have h1 := IdeaticSpace2.depth_subadditive reader (compose author subject)
  have h2 := IdeaticSpace2.depth_subadditive author subject
  omega

end IDT2.Authorship
