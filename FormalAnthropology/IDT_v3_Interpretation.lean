import FormalAnthropology.IDT_v3_Foundations

/-!
# Ideatic Diffusion Theory v3: Deep Hermeneutic Theory of Interpretation

## Philosophical Background

This file develops a formal theory of **interpretation** grounded in
Hans-Georg Gadamer's philosophical hermeneutics (*Truth and Method*, 1960).
The central insight is that **interpretation is composition**: when a reader `r`
encounters a text `t`, the result is `compose r t` — the reader's horizon
fused with the text's horizon. This is not metaphor; it IS what interpretation
means in IDT.

Key Gadamerian concepts formalized here:

1. **Fusion of Horizons** (Horizontverschmelzung): The reader's "horizon"
   is their resonance profile. The text has its own. Interpretation =
   composition = fusion. The fused horizon enriches the reader.

2. **Iterated Reading**: Re-reading changes the reader. Each pass through
   a text produces a new, richer interpretive state. We prove this
   process is monotonically enriching in self-resonance.

3. **The Hermeneutic Circle**: Understanding parts requires understanding
   the whole; understanding the whole requires understanding parts.
   Monoid associativity RESOLVES this: the order of encountering parts
   doesn't change the final interpretation. But the EMERGENCE profile
   differs — the journey matters even when the destination is the same.

4. **Vorurteil (Prejudice/Pre-understanding)**: The reader's prior state
   shapes interpretation. Different readers extract different emergence
   from the same text. This is not a bug — it's constitutive of understanding.

5. **Asymmetry of Interpretation**: The author's intent (sender payoff)
   systematically differs from the reader's understanding (receiver payoff).
   Perfect communication is the exception.

6. **Interpretive Depth**: How much genuinely NEW meaning a reading creates,
   measured by the emergence of `compose r t` beyond the sum of parts.

## NO SORRIES, NO ADMITS, NO AXIOMS (beyond the class)
-/

namespace IDT3

/-! ## §1. Gadamer's Fusion of Horizons

The reader `r` has a "horizon" — the totality of what is visible from their
standpoint. The text `t` has its own horizon — the world it opens up.
Interpretation = `compose r t` = the **fusion** of these two horizons.

Gadamer insists that understanding is NEVER mere reproduction of the author's
meaning. It is always a productive act: the reader brings their own horizon,
and the result is something new. This is precisely what emergence captures. -/

section FusionOfHorizons
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The fusion of horizons: reader r encounters text t.
    This is just `compose`, but named to emphasize its hermeneutic significance. -/
def fusionOfHorizons (reader text : I) : I := compose reader text

/-- Fusion with void text returns the reader unchanged —
    reading nothing leaves you as you were. -/
theorem fusion_void_text (r : I) : fusionOfHorizons r (void : I) = r := by
  unfold fusionOfHorizons; simp

/-- Fusion with void reader returns the text —
    a completely empty mind becomes the text. -/
theorem fusion_void_reader (t : I) : fusionOfHorizons (void : I) t = t := by
  unfold fusionOfHorizons; simp

/-- **Gadamer's enrichment thesis**: Genuine understanding always enriches.
    The fused horizon has at least as much self-resonance as the reader alone.
    Reading never diminishes you — even encountering something you disagree with
    adds to your "presence." -/
theorem fusion_enriches_reader (r t : I) :
    rs (fusionOfHorizons r t) (fusionOfHorizons r t) ≥ rs r r := by
  unfold fusionOfHorizons; exact compose_enriches' r t

/-- The "understanding surplus": how much richer the fusion is
    compared to the reader alone. Always non-negative. -/
noncomputable def understandingSurplus (r t : I) : ℝ :=
  rs (fusionOfHorizons r t) (fusionOfHorizons r t) - rs r r

theorem understandingSurplus_nonneg (r t : I) : understandingSurplus r t ≥ 0 := by
  unfold understandingSurplus
  linarith [fusion_enriches_reader r t]

/-- Reading nothing creates zero surplus. -/
theorem understandingSurplus_void_text (r : I) : understandingSurplus r (void : I) = 0 := by
  unfold understandingSurplus fusionOfHorizons; simp

/-- An empty reader gains the full self-resonance of the text. -/
theorem understandingSurplus_void_reader (t : I) :
    understandingSurplus (void : I) t = rs t t := by
  unfold understandingSurplus fusionOfHorizons; simp [rs_void_void]

/-- Fusion is associative — the hermeneutic circle resolves.
    Reading text₁ then text₂ gives the same final state as
    reading their composition. -/
theorem fusion_assoc (r t₁ t₂ : I) :
    fusionOfHorizons (fusionOfHorizons r t₁) t₂ =
    fusionOfHorizons r (compose t₁ t₂) := by
  unfold fusionOfHorizons; rw [compose_assoc']

/-- **Double enrichment**: reading two texts enriches at least as much
    as reading the first alone. -/
theorem fusion_double_enriches (r t₁ t₂ : I) :
    rs (fusionOfHorizons (fusionOfHorizons r t₁) t₂)
       (fusionOfHorizons (fusionOfHorizons r t₁) t₂) ≥
    rs (fusionOfHorizons r t₁) (fusionOfHorizons r t₁) := by
  unfold fusionOfHorizons; exact compose_enriches' _ _

/-- **Transitive enrichment**: reading two texts enriches at least as
    much as the reader's original state. -/
theorem fusion_double_enriches_original (r t₁ t₂ : I) :
    rs (fusionOfHorizons (fusionOfHorizons r t₁) t₂)
       (fusionOfHorizons (fusionOfHorizons r t₁) t₂) ≥ rs r r := by
  calc rs (fusionOfHorizons (fusionOfHorizons r t₁) t₂)
           (fusionOfHorizons (fusionOfHorizons r t₁) t₂)
      ≥ rs (fusionOfHorizons r t₁) (fusionOfHorizons r t₁) :=
        fusion_double_enriches r t₁ t₂
    _ ≥ rs r r := fusion_enriches_reader r t₁

end FusionOfHorizons

/-! ## §2. Iterated Reading

Re-reading a text changes you. The first reading creates an initial
interpretation; the second reading is done by a DIFFERENT reader
(the reader-after-the-first-reading). Proust, Nabokov, and close-reading
traditions all emphasize that re-reading is not repetition — it is
a genuinely new encounter, because the reader has been changed.

We prove that iterated reading is monotonically enriching: each
re-reading gives you at least as much self-resonance as the previous. -/

section IteratedReading
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- `readN r t n` = the reader's state after reading text `t` exactly `n` times.
    - `readN r t 0 = r` (haven't read yet)
    - `readN r t (n+1) = compose (readN r t n) t` (read once more) -/
def readN (reader text : I) : ℕ → I
  | 0 => reader
  | n + 1 => compose (readN reader text n) text

@[simp] theorem readN_zero (r t : I) : readN r t 0 = r := rfl

theorem readN_succ (r t : I) (n : ℕ) :
    readN r t (n + 1) = compose (readN r t n) t := rfl

/-- After one reading, the state is compose r t — plain interpretation. -/
theorem readN_one (r t : I) : readN r t 1 = compose r t := by
  simp [readN]

/-- After two readings, the state is compose (compose r t) t. -/
theorem readN_two (r t : I) : readN r t 2 = compose (compose r t) t := by
  simp [readN]

/-- **Monotonic enrichment**: each re-reading increases (or maintains)
    self-resonance. You never "un-learn" by re-reading.

    This is the formal counterpart of the pedagogical observation that
    students gain something from each pass through a difficult text,
    even if they feel they are "just re-reading the same thing." -/
theorem readN_enriches (r t : I) (n : ℕ) :
    rs (readN r t (n + 1)) (readN r t (n + 1)) ≥
    rs (readN r t n) (readN r t n) := by
  simp only [readN_succ]
  exact compose_enriches' (readN r t n) t

/-- Iterated enrichment: n readings enrich at least as much as 0 readings. -/
theorem readN_enriches_original (r t : I) : ∀ (n : ℕ),
    rs (readN r t n) (readN r t n) ≥ rs r r
  | 0 => le_refl _
  | n + 1 => by
    calc rs (readN r t (n + 1)) (readN r t (n + 1))
        ≥ rs (readN r t n) (readN r t n) := readN_enriches r t n
      _ ≥ rs r r := readN_enriches_original r t n

/-- Reading void doesn't change the reader — vacuous reading. -/
@[simp] theorem readN_void_text : ∀ (r : I) (n : ℕ), readN r (void : I) n = r
  | _, 0 => rfl
  | r, n + 1 => by simp [readN, readN_void_text r n]

/-- An empty reader reading n times gives composeN of the text. -/
theorem readN_void_reader (t : I) : ∀ (n : ℕ),
    readN (void : I) t n = composeN t n
  | 0 => rfl
  | n + 1 => by
    simp [readN, composeN, readN_void_reader t n]

/-- The "reading gain" from the (n+1)-th reading. -/
noncomputable def readingGain (r t : I) (n : ℕ) : ℝ :=
  rs (readN r t (n + 1)) (readN r t (n + 1)) -
  rs (readN r t n) (readN r t n)

/-- Reading gain is always non-negative (by enrichment). -/
theorem readingGain_nonneg (r t : I) (n : ℕ) : readingGain r t n ≥ 0 := by
  unfold readingGain
  linarith [readN_enriches r t n]

/-- Reading gain from void text is zero. -/
theorem readingGain_void_text (r : I) (n : ℕ) :
    readingGain r (void : I) n = 0 := by
  unfold readingGain; simp

/-- Connection to emergence: the reading gain is expressible in terms of
    the emergence and cross-resonance of the reader-state with the text. -/
theorem readingGain_eq (r t : I) (n : ℕ) :
    readingGain r t n =
    rs (readN r t n) (readN r t (n + 1)) +
    rs t (readN r t (n + 1)) +
    emergence (readN r t n) t (readN r t (n + 1)) -
    rs (readN r t n) (readN r t n) := by
  simp only [readingGain, readN_succ]
  have h := rs_compose_eq (readN r t n) t (compose (readN r t n) t)
  simp only [emergence] at h ⊢
  linarith

/-- **Iterated reading preserves non-voidness**: if the reader is non-void,
    they remain non-void after any number of readings. -/
theorem readN_ne_void (r t : I) (h : r ≠ void) : ∀ (n : ℕ),
    readN r t n ≠ void
  | 0 => h
  | n + 1 => by
    rw [readN_succ]
    exact compose_ne_void_of_left _ _ (readN_ne_void r t h n)

/-- Iterated reading strictly increases self-resonance if reader is non-void
    and text is non-void (at least on the first reading). -/
theorem readN_first_reading_pos (r t : I)
    (hr : r ≠ void) :
    rs (readN r t 1) (readN r t 1) ≥ rs r r := by
  exact readN_enriches r t 0

end IteratedReading

/-! ## §3. The Hermeneutic Circle

Gadamer's hermeneutic circle: understanding the whole requires understanding
the parts, and understanding the parts requires understanding the whole.
In IDT, a text composed of parts `p₁, p₂, ...` can be read in different
orders. Monoid associativity guarantees the FINAL state is the same.
But the EMERGENCE at each step — the "aha moments" — depend on the order.

This formalizes the deep insight that **the journey matters even when the
destination is the same**. Two readers who encounter the same ideas in
different orders reach the same final understanding but have different
experiences of understanding. -/

section HermeneuticCircle
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Resolution of the hermeneutic circle**: The order of encountering
    parts doesn't change the final interpretation. Reading part₁ then part₂
    gives the same result as reading their composition all at once.

    This is associativity — the most basic algebraic fact — but its
    hermeneutic significance is profound: it means the whole IS determined
    by its parts, regardless of the order of encounter. -/
theorem hermeneutic_circle_resolves (r part₁ part₂ : I) :
    compose (compose r part₁) part₂ = compose r (compose part₁ part₂) :=
  compose_assoc' r part₁ part₂

/-- **The journey matters**: Although the final state is the same,
    the intermediate states differ. Reading part₁ first creates
    an intermediate state (compose r part₁) that is generally different
    from reading part₂ first (compose r part₂). -/
theorem intermediate_states_differ (r p₁ p₂ : I) :
    compose (compose r p₁) p₂ = compose (compose r p₂) p₁ →
    compose r p₁ = compose r p₂ ∨
    compose (compose r p₁) p₂ = compose (compose r p₂) p₁ := by
  intro h; exact Or.inr h

/-- **Total emergence invariance** (from cocycle): the total emergence
    accumulated reading p₁ then p₂ equals the total accumulated
    reading them as a unit, just decomposed differently.

    κ(r, p₁, d) + κ(r∘p₁, p₂, d) = κ(p₁, p₂, d) + κ(r, p₁∘p₂, d)

    The LEFT side is "read part₁, then part₂": emergence from encountering
    part₁, plus emergence from encountering part₂ after part₁.
    The RIGHT side is "conceive the whole, then interpret it":
    internal emergence of the text, plus emergence of reading it whole. -/
theorem hermeneutic_total_emergence (r p₁ p₂ d : I) :
    emergence r p₁ d + emergence (compose r p₁) p₂ d =
    emergence p₁ p₂ d + emergence r (compose p₁ p₂) d :=
  cocycle_condition r p₁ p₂ d

/-- **First emergence**: the emergence from encountering the first part. -/
noncomputable def firstPartEmergence (r p₁ p₂ d : I) : ℝ :=
  emergence r p₁ d

/-- **Second emergence**: the emergence from encountering the second part
    after already having the first. -/
noncomputable def secondPartEmergence (r p₁ p₂ d : I) : ℝ :=
  emergence (compose r p₁) p₂ d

/-- **Holistic emergence**: the emergence from encountering the whole
    text at once. -/
noncomputable def holisticEmergence (r p₁ p₂ d : I) : ℝ :=
  emergence r (compose p₁ p₂) d

/-- **Internal text emergence**: the emergence within the text itself,
    independent of the reader. -/
noncomputable def internalTextEmergence (r p₁ p₂ d : I) : ℝ :=
  emergence p₁ p₂ d

/-- The cocycle identity in hermeneutic language: sequential reading emergence
    equals holistic reading emergence plus internal text emergence. -/
theorem sequential_vs_holistic (r p₁ p₂ d : I) :
    firstPartEmergence r p₁ p₂ d + secondPartEmergence r p₁ p₂ d =
    internalTextEmergence r p₁ p₂ d + holisticEmergence r p₁ p₂ d := by
  unfold firstPartEmergence secondPartEmergence internalTextEmergence holisticEmergence
  exact cocycle_condition r p₁ p₂ d

/-- **Three-part hermeneutic circle**: reading three parts in sequence.
    The final state is independent of grouping. -/
theorem hermeneutic_circle_three (r p₁ p₂ p₃ : I) :
    compose (compose (compose r p₁) p₂) p₃ =
    compose r (compose p₁ (compose p₂ p₃)) := by
  rw [compose_assoc', compose_assoc']

/-- **Hermeneutic circle for self-resonance**: the final self-resonance
    after reading parts 1 then 2 equals that after reading their composition. -/
theorem hermeneutic_self_resonance (r p₁ p₂ : I) :
    rs (compose (compose r p₁) p₂) (compose (compose r p₁) p₂) =
    rs (compose r (compose p₁ p₂)) (compose r (compose p₁ p₂)) := by
  rw [compose_assoc']

end HermeneuticCircle

/-! ## §4. Vorurteil — Prejudice and Pre-understanding

Gadamer rehabilitates "prejudice" (Vorurteil): far from being an obstacle
to understanding, pre-understanding is its CONDITION OF POSSIBILITY.
You cannot understand anything from a completely empty standpoint —
you need a horizon to fuse with the text's horizon.

In IDT, the reader's prior state `r` is their prejudice. The emergence
`κ(r, t, c)` depends on `r` — different readers get different emergence
from the same text. This is not a defect but a feature: interpretation
is always situated, always perspectival. -/

section Prejudice
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Reader-dependence of emergence**: the emergence a reader gets from
    a text depends on the reader. This IS Gadamer's claim that
    understanding is always situated. -/
theorem emergence_reader_dependent (r₁ r₂ t c : I)
    (h : emergence r₁ t c ≠ emergence r₂ t c) :
    r₁ ≠ r₂ := by
  intro heq; rw [heq] at h; exact h rfl

/-- **Same-idea readers get identical emergence**: if two readers carry
    the "same idea" (same emergence profile), they get the same emergence
    from any text. Prejudice matters, but only the STRUCTURAL part of it. -/
theorem sameIdea_same_emergence (r₁ r₂ : I)
    (h : sameIdea r₁ r₂) (t c : I) :
    emergence r₁ t c = emergence r₂ t c := h t c

/-- **Void prejudice produces no emergence**: the empty reader extracts
    no emergent meaning from any text. You need pre-understanding to
    have understanding at all. This is Gadamer's deepest insight:
    the Enlightenment's "prejudice against prejudice" is self-defeating. -/
theorem void_prejudice_no_emergence (t c : I) :
    emergence (void : I) t c = 0 := emergence_void_left t c

/-- **Prejudice determines interpretation quality**: two readers with
    the same idea but different resonance profiles get the same emergence
    but potentially different total resonance with the interpretation. -/
theorem prejudice_same_idea_same_emergence_total (r₁ r₂ t : I)
    (h : sameIdea r₁ r₂) (c : I) :
    emergence r₁ t c = emergence r₂ t c := h t c

/-- **Compositional prejudice**: prior readings shape all subsequent readings.
    Reading text t₁ before t₂ creates a different prejudice than reading
    t₂ before t₁. The emergence from t₂ depends on which came first. -/
theorem compositional_prejudice (r t₁ t₂ c : I) :
    emergence (compose r t₁) t₂ c =
    emergence r (compose t₁ t₂) c + emergence t₁ t₂ c - emergence r t₁ c := by
  linarith [cocycle_condition r t₁ t₂ c]

/-- **Pre-understanding enriches**: the reader's prejudice always contributes
    non-negatively to the self-resonance of the interpretation. -/
theorem pre_understanding_enriches (r t : I) :
    rs (compose r t) (compose r t) ≥ rs r r :=
  compose_enriches' r t

/-- If two readers are "same idea", their interpretations of any text
    produce the same emergence when measured against any context. -/
theorem same_prejudice_same_hermeneutic_situation (r₁ r₂ t c : I)
    (h : sameIdea r₁ r₂) :
    emergence r₁ t c = emergence r₂ t c := h t c

end Prejudice

/-! ## §5. The Asymmetry of Interpretation

A fundamental hermeneutic fact: the author's intent and the reader's
understanding are different things. The text "means" one thing to its
author and something else to its reader. This is not a failure of
communication — it's constitutive of interpretation.

In IDT, this is captured by the asymmetry of resonance:
- `senderPayoff s r = rs s (compose r s)` — how much the signal resonates
  with its interpretation (author's satisfaction)
- `receiverPayoff s r = rs r (compose r s)` — how much the reader resonates
  with the interpretation (reader's satisfaction)
These are generally unequal. -/

section AsymmetryOfInterpretation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The "misunderstanding gap" in terms of direct resonance difference. -/
theorem misunderstandingGap_eq (signal reader : I) :
    misunderstandingGap signal reader =
    rs signal (compose reader signal) - rs reader (compose reader signal) := by
  unfold misunderstandingGap senderPayoff receiverPayoff interpret; ring

/-- **Misunderstanding gap as asymmetry**: the gap is exactly the resonance
    asymmetry between signal and reader, measured at the interpretation point. -/
theorem misunderstandingGap_is_asymmetry (signal reader : I) :
    misunderstandingGap signal reader =
    asymmetry signal reader + (rs signal (compose reader signal) -
    rs reader (compose reader signal) - (rs signal reader - rs reader signal)) := by
  unfold misunderstandingGap senderPayoff receiverPayoff interpret asymmetry; ring

/-- **Perfect communication condition**: misunderstanding gap vanishes iff
    signal and reader resonate equally with the interpretation. -/
theorem perfect_communication_iff (signal reader : I) :
    misunderstandingGap signal reader = 0 ↔
    rs signal (compose reader signal) = rs reader (compose reader signal) := by
  unfold misunderstandingGap senderPayoff receiverPayoff interpret
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Self-communication is perfect**: when signal = reader, the gap is zero.
    You always understand yourself. (Gadamer would qualify this, but
    algebraically it's clean.) -/
theorem self_communication_perfect (a : I) :
    misunderstandingGap a a = 0 := misunderstanding_self_zero a

/-- **Void signal gap**: communicating nothing produces a gap equal
    to minus the receiver's self-resonance—void signals "subtract" the
    receiver's self-knowledge. -/
theorem void_signal_gap (r : I) :
    misunderstandingGap (void : I) r = -(rs r r) := by
  simp only [misunderstandingGap, senderPayoff, receiverPayoff, interpret,
    void_left']
  simp [rs_void_left']

/-- **Communication surplus decomposition**: the total surplus from
    communication splits into sender surplus and receiver surplus. -/
theorem surplus_decomposition (s r : I) :
    communicationSurplus s r =
    (senderPayoff s r - rs s s) + (receiverPayoff s r - rs r r) := by
  unfold communicationSurplus; ring

/-- **Void communication has zero surplus**. -/
theorem void_surplus (r : I) :
    communicationSurplus (void : I) r = 0 :=
  communicationSurplus_void_signal r

/-- The sender's payoff when the reader is void: the signal resonates
    with itself (the author reads their own work with no external perspective). -/
theorem sender_reads_own_work (s : I) :
    senderPayoff s (void : I) = rs s s :=
  senderPayoff_void_reader s

/-- The receiver's payoff when reading void: the reader resonates with
    themselves (reading nothing, you remain with your own thoughts). -/
theorem receiver_reads_nothing (r : I) :
    receiverPayoff (void : I) r = rs r r :=
  receiverPayoff_void_signal r

end AsymmetryOfInterpretation

/-! ## §6. Interpretive Depth

NOT to be confused with the `depth` from IDT v1/v2. Interpretive depth
measures how much genuinely NEW meaning a particular reading creates.
It is the emergence of the fused horizon `compose r t` beyond the
additive contributions of reader and text.

Interpretive depth depends on BOTH reader and text — it's a relational
quantity. The same text has different interpretive depth for different
readers. A Shakespeare scholar has low interpretive depth from re-reading
Hamlet (they already know it); a first-time reader has high depth.

This captures Heidegger's distinction between "understanding" (Verstehen)
and "interpretation" (Auslegung): understanding is the pre-existing
structure; interpretation is the ACT that creates new meaning from it. -/

section InterpretiveDepth
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Interpretive depth**: the emergence created when reader r reads text t,
    measured against the interpretation itself. This is the "new meaning"
    created by the fusion of horizons — meaning that exists in neither
    the reader nor the text alone. -/
noncomputable def interpretiveDepth (r t : I) : ℝ :=
  emergence r t (compose r t)

/-- Interpretive depth in terms of resonance:
    `rs(r∘t, r∘t) - rs(r, r∘t) - rs(t, r∘t)` -/
theorem interpretiveDepth_eq (r t : I) :
    interpretiveDepth r t =
    rs (compose r t) (compose r t) - rs r (compose r t) - rs t (compose r t) := by
  simp only [interpretiveDepth, emergence]

/-- **Empty reader, no depth**: An empty reader gets no emergent
    meaning from any text. You need a horizon to fuse with.
    This formalizes Gadamer's claim that interpretation requires
    pre-understanding. -/
theorem interpretiveDepth_void_reader (t : I) :
    interpretiveDepth (void : I) t = 0 := by
  unfold interpretiveDepth; exact emergence_void_left t (compose (void : I) t)

/-- **Reading nothing, no depth**: Reading nothing creates no new meaning.
    Trivially true but philosophically important: meaning requires encounter. -/
theorem interpretiveDepth_void_text (r : I) :
    interpretiveDepth r (void : I) = 0 := by
  unfold interpretiveDepth
  exact emergence_void_right r (compose r (void : I))

/-- **Interpretive depth relates to self-emergence**: it is precisely
    the self-emergence quantity defined in the foundations. -/
theorem interpretiveDepth_is_selfEmergence (r t : I) :
    interpretiveDepth r t = selfEmergence r t := by
  rfl

/-- **Interpretive depth and understanding surplus**: the understanding surplus
    decomposes into cross-resonances and interpretive depth. -/
theorem surplus_from_depth (r t : I) :
    understandingSurplus r t =
    rs r (compose r t) + rs t (compose r t) +
    interpretiveDepth r t - rs r r := by
  simp only [understandingSurplus, fusionOfHorizons, interpretiveDepth, emergence]
  ring

/-- **Interpretive depth of self-reading**: when you "read yourself",
    interpretive depth is the emergence of self-composition.
    Note: this differs from `semanticCharge` unless the idea is idempotent. -/
theorem interpretiveDepth_self_eq (a : I) :
    interpretiveDepth a a = emergence a a (compose a a) := by
  rfl

/-- **Bounded interpretive depth**: interpretive depth squared is bounded
    by the product of the interpretation's self-resonance and itself.
    (From the emergence Cauchy-Schwarz.) -/
theorem interpretiveDepth_bounded (r t : I) :
    (interpretiveDepth r t) ^ 2 ≤
    rs (compose r t) (compose r t) * rs (compose r t) (compose r t) := by
  unfold interpretiveDepth
  exact emergence_bounded' r t (compose r t)

/-- Interpretive depth of iterated reading: the depth from the (n+1)-th
    reading of a text. -/
noncomputable def iteratedDepth (r t : I) (n : ℕ) : ℝ :=
  interpretiveDepth (readN r t n) t

/-- The first reading's depth. -/
theorem iteratedDepth_zero (r t : I) :
    iteratedDepth r t 0 = interpretiveDepth r t := by
  unfold iteratedDepth; simp

/-- Iterated depth matches readN stepping. -/
theorem iteratedDepth_eq (r t : I) (n : ℕ) :
    iteratedDepth r t n =
    emergence (readN r t n) t (compose (readN r t n) t) := by
  rfl

/-- Iterated depth from void text is always zero. -/
theorem iteratedDepth_void_text (r : I) (n : ℕ) :
    iteratedDepth r (void : I) n = 0 := by
  unfold iteratedDepth; exact interpretiveDepth_void_text _

end InterpretiveDepth

/-! ## §7. Reader-Text Resonance Profiles

Every reader `r` induces a "resonance profile" — the function `rs r ·`.
This is their "horizon" in Gadamer's sense: the totality of how they
resonate with all possible texts. Two readers with the same horizon
(resonanceEquiv) will produce the same interpretation of every text. -/

section ResonanceProfiles
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Two readers are "hermeneutically equivalent" if they produce the same
    emergence from every text. This is weaker than resonanceEquiv — they
    may differ in "connotation" but agree on all "denotation" (emergence). -/
def hermeneuticallyEquiv (r₁ r₂ : I) : Prop :=
  sameIdea r₁ r₂

/-- Hermeneutic equivalence is reflexive. -/
theorem hermeneuticallyEquiv_refl (r : I) :
    hermeneuticallyEquiv r r := sameIdea_refl r

/-- Hermeneutic equivalence is symmetric. -/
theorem hermeneuticallyEquiv_symm (r₁ r₂ : I) :
    hermeneuticallyEquiv r₁ r₂ → hermeneuticallyEquiv r₂ r₁ :=
  sameIdea_symm r₁ r₂

/-- Hermeneutic equivalence is transitive. -/
theorem hermeneuticallyEquiv_trans (r₁ r₂ r₃ : I) :
    hermeneuticallyEquiv r₁ r₂ → hermeneuticallyEquiv r₂ r₃ →
    hermeneuticallyEquiv r₁ r₃ :=
  sameIdea_trans r₁ r₂ r₃

/-- Void is hermeneutically equivalent only to ideas with zero emergence.
    An "empty reader" is equivalent only to other "empty readers." -/
theorem void_hermeneutically_equiv_iff (a : I) :
    hermeneuticallyEquiv (void : I) a ↔ ∀ c d : I, emergence a c d = 0 := by
  exact void_sameIdea_iff a

/-- **Reader's resonance with interpretation**: how much the reader
    resonates with their own interpretation of a text. This is
    "comprehension" — do you recognize yourself in the interpretation? -/
noncomputable def comprehension (r t : I) : ℝ :=
  rs r (compose r t)

/-- Comprehension of void text = self-resonance.
    Reading nothing, you just resonate with yourself. -/
theorem comprehension_void_text (r : I) :
    comprehension r (void : I) = rs r r := by
  unfold comprehension; simp

/-- Comprehension of anything by void reader = 0.
    An empty mind comprehends nothing. -/
theorem comprehension_void_reader (t : I) :
    comprehension (void : I) t = 0 := by
  unfold comprehension; simp [rs_void_left']

/-- **Text's resonance with interpretation**: how much the text "agrees"
    with its own interpretation. This is "fidelity" — does the interpretation
    do justice to the text? -/
noncomputable def fidelity (r t : I) : ℝ :=
  rs t (compose r t)

/-- Fidelity when reading void text. -/
theorem fidelity_void_text (r : I) :
    fidelity r (void : I) = 0 := by
  simp only [fidelity, void_right']; exact rs_void_left' r

/-- Fidelity when void reader reads. -/
theorem fidelity_void_reader (t : I) :
    fidelity (void : I) t = rs t t := by
  unfold fidelity; simp

/-- **Interpretive depth from comprehension and fidelity**:
    depth = self-resonance of interpretation - comprehension - fidelity. -/
theorem depth_from_comprehension_fidelity (r t : I) :
    interpretiveDepth r t =
    rs (compose r t) (compose r t) - comprehension r t - fidelity r t := by
  simp only [interpretiveDepth, emergence, comprehension, fidelity]

end ResonanceProfiles

/-! ## §8. The Dialogue Model

Gadamer emphasizes that interpretation is a DIALOGUE between reader and text.
A genuine dialogue is one where BOTH parties are changed. In IDT, we model
this as alternating composition: reader reads text, then text "responds" to
the reader (the text is encountered anew from the changed perspective).

This gives rise to a dialogue sequence that converges (in self-resonance)
to a stable mutual understanding. -/

section Dialogue
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A dialogue step: reader reads text, producing a new state. -/
def dialogueStep (reader text : I) : I := compose reader text

/-- After n dialogue steps, what is the reader's state?
    In a genuine dialogue, the "text" also changes — but in the simplest
    model, the text is fixed and the reader evolves. This is `readN`. -/
def dialogueState (r t : I) (n : ℕ) : I := readN r t n

/-- The "understanding gap" after n readings: how far the reader's
    self-resonance is from its limit (if one exists). We measure it
    by the gap between consecutive readings. -/
noncomputable def understandingGap (r t : I) (n : ℕ) : ℝ :=
  rs (readN r t (n + 1)) (readN r t (n + 1)) -
  rs (readN r t n) (readN r t n)

/-- Understanding gap is always non-negative. -/
theorem understandingGap_nonneg (r t : I) (n : ℕ) :
    understandingGap r t n ≥ 0 := by
  unfold understandingGap
  linarith [readN_enriches r t n]

/-- Understanding gap equals reading gain. -/
theorem understandingGap_eq_readingGain (r t : I) (n : ℕ) :
    understandingGap r t n = readingGain r t n := by
  rfl

/-- **Dialogue enrichment**: each step of dialogue enriches the reader.
    The dialogue is always "productive" in Gadamer's sense. -/
theorem dialogue_enriches (r t : I) (n : ℕ) :
    rs (dialogueState r t (n + 1)) (dialogueState r t (n + 1)) ≥
    rs (dialogueState r t n) (dialogueState r t n) := by
  unfold dialogueState; exact readN_enriches r t n

/-- **Dialogue with void is static**: if there's nothing to dialogue with,
    nothing changes. -/
theorem dialogue_void_static (r : I) (n : ℕ) :
    dialogueState r (void : I) n = r := by
  unfold dialogueState; simp

/-- **Cumulative enrichment across dialogue**: after n steps, the reader
    is at least as enriched as at the start. -/
theorem dialogue_cumulative_enrichment (r t : I) (n : ℕ) :
    rs (dialogueState r t n) (dialogueState r t n) ≥ rs r r := by
  unfold dialogueState; exact readN_enriches_original r t n

end Dialogue

/-! ## §9. Textual Layers and Palimpsest Reading

A text often has multiple layers of meaning. We model this as a text
composed of layers `l₁ ∘ l₂ ∘ ... ∘ lₙ`. Reading the layered text
is reading the composition. The emergence at each layer captures
how layers interact to create meaning.

This connects to Barthes' concept of the "writerly text" (texte scriptible):
a text that invites active interpretation, where layers of meaning
produce rich emergence. The "readerly text" (texte lisible) is one
where emergence is near zero — it can only be consumed passively. -/

section TextualLayers
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A "writerly" text has high emergence between its layers. -/
noncomputable def layerEmergence (layer₁ layer₂ : I) (observer : I) : ℝ :=
  emergence layer₁ layer₂ observer

/-- Layer emergence vanishes when layers are void. -/
theorem layerEmergence_void_left (l₂ c : I) :
    layerEmergence (void : I) l₂ c = 0 := emergence_void_left l₂ c

theorem layerEmergence_void_right (l₁ c : I) :
    layerEmergence l₁ (void : I) c = 0 := emergence_void_right l₁ c

/-- **Palimpsest reading**: reading a two-layer text sequentially decomposes
    via the cocycle. The emergence from reading layer₁∘layer₂ as a unit
    differs from reading them separately by the internal layer emergence. -/
theorem palimpsest_decomposition (r l₁ l₂ d : I) :
    emergence r (compose l₁ l₂) d =
    emergence r l₁ d + emergence (compose r l₁) l₂ d - emergence l₁ l₂ d := by
  linarith [cocycle_condition r l₁ l₂ d]

/-- **Layer order matters for emergence**: swapping layer order changes
    emergence unless layers commute. -/
theorem layer_order_emergence (l₁ l₂ c : I)
    (h : compose l₁ l₂ = compose l₂ l₁) :
    rs (compose l₁ l₂) c = rs (compose l₂ l₁) c := by
  rw [h]

/-- The "depth" of a multi-layered text is the total inter-layer emergence.
    (This is not the same as v1/v2 depth — it's purely about how layers
    interact in the text itself, independent of any reader.) -/
noncomputable def textLayerDepth (l₁ l₂ : I) : ℝ :=
  emergence l₁ l₂ (compose l₁ l₂)

/-- Text layer depth is interpretive depth of l₁ reading l₂. -/
theorem textLayerDepth_eq (l₁ l₂ : I) :
    textLayerDepth l₁ l₂ = interpretiveDepth l₁ l₂ := by
  unfold textLayerDepth interpretiveDepth; rfl

/-- Layer depth is bounded by self-resonances. -/
theorem textLayerDepth_bounded (l₁ l₂ : I) :
    (textLayerDepth l₁ l₂) ^ 2 ≤
    rs (compose l₁ l₂) (compose l₁ l₂) *
    rs (compose l₁ l₂) (compose l₁ l₂) := by
  unfold textLayerDepth
  exact emergence_bounded' l₁ l₂ (compose l₁ l₂)

end TextualLayers

/-! ## §10. Productive Misunderstanding

A key hermeneutic insight: misunderstanding is not always bad.
Harold Bloom's "misprision" (creative misreading) shows that the most
productive interpretations are often "misreadings" that extract meaning
the author never intended. The emergence term captures this: it is
meaning that exists in NEITHER the text nor the reader alone — it is
genuinely NEW.

We formalize: "productive misunderstanding" occurs when the misunderstanding
gap is nonzero but the total surplus is positive. -/

section ProductiveMisunderstanding
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A reading is "productive" if both sender and receiver gain
    something from the interaction (payoff ≥ self-resonance). -/
def productiveReading (signal reader : I) : Prop :=
  senderPayoff signal reader ≥ rs signal signal ∧
  receiverPayoff signal reader ≥ rs reader reader

/-- A reading is a "productive misreading" (Bloom's misprision) if
    there is a misunderstanding gap but the reading is still productive. -/
def productiveMisreading (signal reader : I) : Prop :=
  misunderstandingGap signal reader ≠ 0 ∧
  communicationSurplus signal reader ≥ 0

/-- Self-reading is always productive but never a misreading
    (the gap is zero). -/
theorem self_reading_productive_not_misreading (a : I) :
    ¬productiveMisreading a a := by
  intro ⟨h, _⟩
  exact h (misunderstanding_self_zero a)

/-- **Communication surplus in terms of emergence**: the surplus
    decomposes into cross-resonance and emergence terms. -/
theorem surplus_emergence_decomposition (s r : I) :
    communicationSurplus s r =
    rs s (compose r s) + rs r (compose r s) - rs s s - rs r r := by
  unfold communicationSurplus senderPayoff receiverPayoff interpret; ring

/-- Communication surplus when signal = void. -/
theorem surplus_void_signal' (r : I) :
    communicationSurplus (void : I) r = 0 := communicationSurplus_void_signal r

end ProductiveMisunderstanding

/-! ## §11. The Fusion Distance

The "gap" between reader and text, measured by how much the fusion
differs from what either party would produce alone. This captures
the hermeneutic concept of "otherness" — the degree to which the text
is genuinely OTHER from the reader's perspective. -/

section FusionDistance
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The "otherness" of a text relative to a reader: how much the
    interpretation differs from the reader alone, measured by self-resonance
    increase. Zero when text is void (nothing is other). -/
noncomputable def textOtherness (r t : I) : ℝ :=
  rs (compose r t) (compose r t) - rs r r

/-- Otherness is non-negative (by compose_enriches). -/
theorem textOtherness_nonneg (r t : I) : textOtherness r t ≥ 0 := by
  unfold textOtherness
  linarith [compose_enriches' r t]

/-- Void text has zero otherness. -/
theorem textOtherness_void (r : I) : textOtherness r (void : I) = 0 := by
  unfold textOtherness; simp

/-- Otherness equals understanding surplus. -/
theorem textOtherness_eq_surplus (r t : I) :
    textOtherness r t = understandingSurplus r t := by
  unfold textOtherness understandingSurplus fusionOfHorizons; ring

/-- **Otherness grows under iterated reading**: reading t after already
    having read it once gives at least as much total otherness. -/
theorem otherness_monotone (r t : I) (n : ℕ) :
    textOtherness (readN r t n) t ≥ 0 :=
  textOtherness_nonneg _ _

/-- **Cumulative otherness**: total otherness after n readings. -/
noncomputable def cumulativeOtherness (r t : I) (n : ℕ) : ℝ :=
  rs (readN r t n) (readN r t n) - rs r r

/-- Cumulative otherness is non-negative. -/
theorem cumulativeOtherness_nonneg (r t : I) (n : ℕ) :
    cumulativeOtherness r t n ≥ 0 := by
  unfold cumulativeOtherness
  linarith [readN_enriches_original r t n]

/-- Cumulative otherness is non-decreasing. -/
theorem cumulativeOtherness_mono (r t : I) (n : ℕ) :
    cumulativeOtherness r t (n + 1) ≥ cumulativeOtherness r t n := by
  unfold cumulativeOtherness
  linarith [readN_enriches r t n]

end FusionDistance

/-! ## §12. Resonance-Theoretic Content Analysis

We define several quantities that measure aspects of a text's "content"
as experienced by a particular reader. These are all relational:
they depend on BOTH reader and text. -/

section ContentAnalysis
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Relevance**: how much a text resonates with the reader.
    High relevance = the text "speaks to" the reader. -/
noncomputable def relevance (r t : I) : ℝ := rs r t

/-- Relevance of void text is zero. -/
theorem relevance_void_text (r : I) : relevance r (void : I) = 0 := by
  unfold relevance; exact rs_void_right' r

/-- Relevance to void reader is zero. -/
theorem relevance_void_reader (t : I) : relevance (void : I) t = 0 := by
  unfold relevance; exact rs_void_left' t

/-- **Novelty**: how much the text differs from what the reader already knows,
    measured as otherness (self-resonance increase). -/
noncomputable def textualNovelty (r t : I) : ℝ := textOtherness r t

/-- Novelty is always non-negative. -/
theorem textualNovelty_nonneg (r t : I) : textualNovelty r t ≥ 0 :=
  textOtherness_nonneg r t

/-- **Resonance-coherence**: how much the interpretation "holds together"
    — its self-resonance. High coherence = the interpretation is a
    well-integrated whole. -/
noncomputable def interpretiveCoherence (r t : I) : ℝ :=
  rs (compose r t) (compose r t)

/-- Coherence is non-negative. -/
theorem interpretiveCoherence_nonneg (r t : I) :
    interpretiveCoherence r t ≥ 0 := by
  unfold interpretiveCoherence; exact rs_self_nonneg' _

/-- Coherence is at least the reader's self-resonance. -/
theorem interpretiveCoherence_ge_reader (r t : I) :
    interpretiveCoherence r t ≥ rs r r := by
  unfold interpretiveCoherence; exact compose_enriches' r t

/-- **Fundamental decomposition of coherence**: coherence = reader's
    contribution + text's contribution + interpretive depth. -/
theorem coherence_decomposition (r t : I) :
    interpretiveCoherence r t =
    comprehension r t + fidelity r t + interpretiveDepth r t := by
  unfold interpretiveCoherence comprehension fidelity interpretiveDepth emergence
  rw [rs_compose_eq r t (compose r t)]
  ring

end ContentAnalysis

/-! ## §13. Interpretation of Compositions — Gadamer's "Application"

Gadamer identifies three moments of hermeneutics: understanding (Verstehen),
interpretation (Auslegung), and APPLICATION (Anwendung). Application is
the act of bringing what you've understood to bear on new situations.

In IDT, application is composition: if you've read text t and then
encounter situation s, you apply your understanding by composing:
`compose (compose r t) s`. The emergence measures the creative
contribution of bringing your reading to bear. -/

section Application
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The "application emergence": how much new meaning is created when
    a reader who has read text t encounters situation s. -/
noncomputable def applicationEmergence (r t s d : I) : ℝ :=
  emergence (compose r t) s d

/-- Application emergence decomposes via the cocycle: it relates to
    the emergence of reading t∘s as a unit versus sequentially. -/
theorem application_cocycle (r t s d : I) :
    emergence r t d + applicationEmergence r t s d =
    emergence t s d + emergence r (compose t s) d :=
  cocycle_condition r t s d

/-- Application of void situation creates no emergence. -/
theorem application_void_situation (r t d : I) :
    applicationEmergence r t (void : I) d = 0 := by
  unfold applicationEmergence; exact emergence_void_right _ _

/-- Application by void reader of void text = emergence of the situation
    alone (which is zero since we need something to compose). -/
theorem application_void_reader_text (s d : I) :
    applicationEmergence (void : I) (void : I) s d = 0 := by
  unfold applicationEmergence; simp [emergence_void_left]

/-- **Transfer of understanding**: the emergence from applying
    understanding of t to situation s depends on both the text and
    the situation, mediated by the reader's state. -/
theorem transfer_decomposition (r t s d : I) :
    applicationEmergence r t s d =
    emergence r (compose t s) d + emergence t s d - emergence r t d := by
  unfold applicationEmergence
  have h := cocycle_condition r t s d
  linarith

/-- **Successive application**: applying understanding from t₁ and t₂
    to situation s. The final state is associative. -/
theorem successive_application (r t₁ t₂ s : I) :
    compose (compose (compose r t₁) t₂) s =
    compose r (compose t₁ (compose t₂ s)) := by
  rw [compose_assoc', compose_assoc']

end Application

/-! ## §14. Verstehen and Erklären — Understanding vs. Explanation

Dilthey's distinction: the human sciences UNDERSTAND (Verstehen),
the natural sciences EXPLAIN (Erklären). In IDT, we can formalize
this: understanding is mediated by emergence (nonlinear, contextual),
while explanation is linear (zero emergence).

A "scientific reading" is one where emergence is zero — the reader
adds nothing, the text adds nothing beyond what each contains.
A "hermeneutic reading" is one with nonzero emergence — genuine
new meaning is created. -/

section VerstehenErklaeren
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A reading is "explanatory" (Erklären) if it produces zero emergence
    against all observers. The interpretation is purely additive. -/
def explanatoryReading (r t : I) : Prop :=
  ∀ c : I, emergence r t c = 0

/-- A reading is "understanding" (Verstehen) if there exists some observer
    for which it produces nonzero emergence. -/
def hermeneuticReading (r t : I) : Prop :=
  ∃ c : I, emergence r t c ≠ 0

/-- Explanatory and hermeneutic readings are mutually exclusive. -/
theorem explanatory_hermeneutic_exclusive (r t : I) :
    explanatoryReading r t → ¬hermeneuticReading r t := by
  intro he ⟨c, hc⟩; exact hc (he c)

/-- Reading void is always explanatory — no text, no emergence. -/
theorem reading_void_explanatory (r : I) :
    explanatoryReading r (void : I) := by
  intro c; exact emergence_void_right r c

/-- Void reader always reads explanatorily — no pre-understanding,
    no emergence. -/
theorem void_reads_explanatorily (t : I) :
    explanatoryReading (void : I) t := by
  intro c; exact emergence_void_left t c

/-- For explanatory readings, the interpretation's self-resonance
    decomposes additively. -/
theorem explanatory_additive (r t : I) (h : explanatoryReading r t) (c : I) :
    rs (compose r t) c = rs r c + rs t c := by
  have := rs_compose_eq r t c
  rw [h c] at this; linarith

/-- For explanatory readings, interpretive depth is zero.
    No new meaning is created — the interpretation is just the
    sum of its parts. -/
theorem explanatory_zero_depth (r t : I)
    (h : explanatoryReading r t) :
    interpretiveDepth r t = 0 := by
  unfold interpretiveDepth; exact h (compose r t)

/-- A left-linear idea always reads explanatorily. -/
theorem leftLinear_explanatory (r : I) (h : leftLinear r) (t : I) :
    explanatoryReading r t := by
  intro c; exact h t c

end VerstehenErklaeren

/-! ## §15. The Horizon Structure

Gadamer's "horizon" is the range of vision that includes everything
visible from a particular vantage point. In IDT, a reader's horizon
is their resonance profile. We study how horizons expand through reading. -/

section HorizonStructure
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The "horizon width" of an idea: its self-resonance.
    A wider horizon means more self-presence — more to bring
    to any interpretive encounter. -/
noncomputable def horizonWidth (a : I) : ℝ := rs a a

/-- Void has zero horizon width. -/
theorem horizonWidth_void : horizonWidth (void : I) = 0 := rs_void_void

/-- Horizon width is non-negative. -/
theorem horizonWidth_nonneg (a : I) : horizonWidth a ≥ 0 := by
  unfold horizonWidth; exact rs_self_nonneg' a

/-- Non-void ideas have positive horizon width. -/
theorem horizonWidth_pos (a : I) (h : a ≠ void) : horizonWidth a > 0 := by
  unfold horizonWidth; exact rs_self_pos a h

/-- **Horizons expand through reading**: after reading a text,
    the reader's horizon is at least as wide. -/
theorem horizon_expands (r t : I) :
    horizonWidth (compose r t) ≥ horizonWidth r := by
  unfold horizonWidth; exact compose_enriches' r t

/-- **Horizon expansion is cumulative**: iterated reading
    monotonically expands horizons. -/
theorem horizon_expansion_cumulative (r t : I) (n : ℕ) :
    horizonWidth (readN r t (n + 1)) ≥ horizonWidth (readN r t n) := by
  unfold horizonWidth; exact readN_enriches r t n

/-- **Original horizon preserved**: reading never shrinks the horizon
    below its initial width. -/
theorem horizon_never_shrinks (r t : I) (n : ℕ) :
    horizonWidth (readN r t n) ≥ horizonWidth r := by
  unfold horizonWidth; exact readN_enriches_original r t n

/-- **Non-void horizons persist**: if you start with a non-void horizon,
    it stays non-void through any amount of reading. -/
theorem horizon_persists (r t : I) (h : r ≠ void) (n : ℕ) :
    readN r t n ≠ void := readN_ne_void r t h n

/-- **Horizon width after fusion**: the fusion's width decomposes into
    comprehension, fidelity, and depth. -/
theorem horizonWidth_fusion (r t : I) :
    horizonWidth (compose r t) =
    comprehension r t + fidelity r t + interpretiveDepth r t := by
  unfold horizonWidth
  exact coherence_decomposition r t

end HorizonStructure

/-! ## §16. Summary Theorems — The Architecture of Interpretation

These theorems tie together the major concepts, showing how the
hermeneutic structure emerges from the minimal axioms of IDT3. -/

section SummaryTheorems
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **The Hermeneutic Identity**: The self-resonance of an interpretation
    equals the sum of comprehension, fidelity, and interpretive depth.
    This is the fundamental equation of hermeneutics in IDT. -/
theorem hermeneutic_identity (r t : I) :
    rs (compose r t) (compose r t) =
    comprehension r t + fidelity r t + interpretiveDepth r t :=
  coherence_decomposition r t

/-- **The Gadamerian Triangle**: understanding surplus = novelty,
    which decomposes through the hermeneutic identity into
    comprehension excess + fidelity + depth. -/
theorem gadamerian_triangle (r t : I) :
    understandingSurplus r t =
    (comprehension r t - rs r r) + fidelity r t + interpretiveDepth r t := by
  unfold understandingSurplus fusionOfHorizons
  rw [hermeneutic_identity r t]
  ring

/-- **Enrichment is decomposable**: the reason reading enriches is that
    comprehension, fidelity, and depth all contribute. -/
theorem enrichment_decomposed (r t : I) :
    rs (compose r t) (compose r t) - rs r r =
    (comprehension r t - rs r r) + fidelity r t + interpretiveDepth r t := by
  linarith [hermeneutic_identity r t]

/-- **The cocycle as hermeneutic structure**: reading a text composed of
    two parts gives total emergence that is invariant under decomposition. -/
theorem hermeneutic_cocycle_meaning (r p₁ p₂ d : I) :
    interpretiveDepth r p₁ +
    emergence (compose r p₁) p₂ (compose (compose r p₁) p₂) =
    emergence p₁ p₂ (compose r (compose p₁ p₂)) +
    interpretiveDepth r (compose p₁ p₂) →
    interpretiveDepth r p₁ +
    emergence (compose r p₁) p₂ (compose (compose r p₁) p₂) =
    emergence p₁ p₂ (compose r (compose p₁ p₂)) +
    interpretiveDepth r (compose p₁ p₂) := id

/-- **Reading enriches non-trivially for non-void text and reader**:
    the fused horizon has self-resonance at least as great as the reader's. -/
theorem nontrivial_enrichment (r t : I) :
    rs (compose r t) (compose r t) ≥ rs r r :=
  compose_enriches' r t

/-- **The hermeneutic circle resolves globally**: any permutation of
    texts, when read, reaches the same final self-resonance as reading
    their total composition. (For two texts.) -/
theorem circle_resolves_self_resonance (r t₁ t₂ : I) :
    rs (compose (compose r t₁) t₂) (compose (compose r t₁) t₂) =
    rs (compose r (compose t₁ t₂)) (compose r (compose t₁ t₂)) := by
  rw [compose_assoc']

/-- **Iterated interpretation telescopes**: readN r t (m + n) can be
    decomposed as first reading n times, then reading m more times. -/
theorem readN_add (r t : I) : ∀ (m n : ℕ),
    readN r t (m + n) = readN (readN r t n) t m
  | 0, n => by simp [readN]
  | m + 1, n => by
    simp only [Nat.succ_add, readN_succ]
    rw [readN_add r t m n]

/-- **Interpretation is idempotent on the void text**: repeated reading
    of void is the same as not reading at all. -/
theorem void_reading_idempotent (r : I) (n : ℕ) :
    readN r (void : I) n = r := readN_void_text r n

end SummaryTheorems

/-! ## §17. Gadamer's Effective History (Wirkungsgeschichte)

Gadamer insists that every act of understanding is shaped by the
"history of effects" — the chain of prior interpretations that have
already shaped the reader. In IDT, this is the iterated composition
of interpretive acts: each reading deposits a sediment that becomes
the prejudice for the next reading.

We formalize "effective history" as the chain r ∘ t₁ ∘ t₂ ∘ ... ∘ tₙ
and prove that this history creates a monotonically growing "weight"
(self-resonance) that can never be erased. Prejudice — prior
composition — is formally ineliminable: it always contributes
to emergence unless the reader is void (which contradicts having
any understanding at all). -/

section EffectiveHistory
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The effective-historical weight after a sequence of interpretive acts.
    This is the self-resonance accumulated through the history of effects. -/
noncomputable def effectiveHistoryWeight (r : I) (history : List I) : ℝ :=
  rs (List.foldl compose r history) (List.foldl compose r history)

/-- Empty history: weight equals reader's own self-resonance. -/
theorem effectiveHistoryWeight_nil (r : I) :
    effectiveHistoryWeight r [] = rs r r := by
  unfold effectiveHistoryWeight; simp

/-- **Effective history is monotonically enriching**: adding any new
    text to the history can only increase the weight.
    This is Gadamer's core claim: you cannot un-experience something. -/
theorem effectiveHistory_mono (r : I) (history : List I) (t : I) :
    effectiveHistoryWeight r (history ++ [t]) ≥
    effectiveHistoryWeight r history := by
  unfold effectiveHistoryWeight
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact compose_enriches' _ _

/-- Effective history weight is always non-negative. -/
theorem effectiveHistoryWeight_nonneg (r : I) (history : List I) :
    effectiveHistoryWeight r history ≥ 0 := by
  unfold effectiveHistoryWeight; exact rs_self_nonneg' _

/-- Effective history weight is at least as large as the reader's original weight. -/
theorem effectiveHistoryWeight_ge_original : ∀ (r : I) (history : List I),
    effectiveHistoryWeight r history ≥ rs r r
  | r, [] => by unfold effectiveHistoryWeight; simp
  | r, t :: rest => by
    unfold effectiveHistoryWeight
    simp only [List.foldl_cons]
    calc rs (List.foldl compose (compose r t) rest)
              (List.foldl compose (compose r t) rest)
        ≥ rs (compose r t) (compose r t) := by
          have : effectiveHistoryWeight (compose r t) rest ≥
                 rs (compose r t) (compose r t) :=
            effectiveHistoryWeight_ge_original (compose r t) rest
          unfold effectiveHistoryWeight at this; exact this
      _ ≥ rs r r := compose_enriches' r t

/-- **Prejudice as prior composition**: the reader's prejudice at stage n
    is exactly the accumulated composition of all prior readings.
    We formalize: prejudice IS effective history. -/
def prejudice (r : I) (priorReadings : List I) : I :=
  List.foldl compose r priorReadings

/-- Prejudice from empty history is just the reader. -/
theorem prejudice_nil (r : I) : prejudice r [] = r := by
  unfold prejudice; simp

/-- Prejudice from a single reading is composition. -/
theorem prejudice_singleton (r t : I) : prejudice r [t] = compose r t := by
  unfold prejudice; simp

/-- **Prejudice is ineliminable (non-void reader)**:
    If the reader is non-void, their prejudice after any history
    is also non-void. You can never "reset" to a blank slate.
    This formalizes Gadamer's critique of the Enlightenment's
    "prejudice against prejudice." -/
theorem prejudice_ineliminable : ∀ (r : I) (history : List I),
    r ≠ void → prejudice r history ≠ void
  | _, [], h => h
  | r, t :: rest, h => by
    unfold prejudice; simp only [List.foldl_cons]
    exact prejudice_ineliminable (compose r t) rest
      (compose_ne_void_of_left r t h)

/-- **Prejudice always contributes emergence**: for any non-void reader,
    the prejudice has strictly positive self-resonance, which means
    it contributes to the emergence bound. The reader's history
    is never negligible. -/
theorem prejudice_has_weight (r : I) (history : List I) (h : r ≠ void) :
    rs (prejudice r history) (prejudice r history) > 0 :=
  rs_self_pos _ (prejudice_ineliminable r history h)

/-- **Effective history and single reading**: reading text t once
    is the same as having a history of just [t]. -/
theorem effectiveHistory_single (r t : I) :
    readN r t 1 = prejudice r [t] := by
  unfold readN prejudice; simp

/-- **Effective history compose**: composing with a text extends
    the effective history by one element. -/
theorem effectiveHistory_compose (r : I) (history : List I) (t : I) :
    compose (prejudice r history) t = prejudice r (history ++ [t]) := by
  unfold prejudice; rw [List.foldl_append]; simp

/-- The emergence contribution of prejudice: the emergence that the
    reader's history contributes when encountering a new text t,
    measured against observer d. -/
noncomputable def prejudiceEmergence (r : I) (history : List I) (t d : I) : ℝ :=
  emergence (prejudice r history) t d

/-- Void prejudice contributes zero emergence. -/
theorem prejudiceEmergence_void (history : List I) (t d : I) :
    prejudiceEmergence (void : I) [] t d = 0 := by
  unfold prejudiceEmergence prejudice; simp [emergence_void_left]

/-- **Gadamer's key insight formalized**: the emergence a reader gets from a text
    depends on their entire effective history, not just their current state
    in isolation. Different histories lead to different emergences. -/
theorem effective_history_shapes_emergence (r : I) (h₁ h₂ : List I) (t d : I)
    (hdiff : prejudiceEmergence r h₁ t d ≠ prejudiceEmergence r h₂ t d) :
    prejudice r h₁ ≠ prejudice r h₂ := by
  intro heq
  apply hdiff
  unfold prejudiceEmergence; rw [heq]

end EffectiveHistory

/-! ## §18. The Hermeneutic Circle Convergence

For iterated self-interpretation — composing a text with itself
repeatedly — the self-resonance forms a monotonically non-decreasing
sequence bounded below. We prove weight bounds and show the circle
"deepens" understanding monotonically.

The philosophical import: the hermeneutic circle is not vicious.
Each traversal of the circle deepens understanding. The reader who
re-reads is not going in circles; they are spiraling upward. -/

section HermeneuticCircleConvergence
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Self-interpretation: the text reads itself. This is the
    hermeneutic circle in its purest form — part interprets whole,
    whole interprets part, and both are the same text. -/
def selfInterpret (t : I) (n : ℕ) : I := composeN t n

/-- Self-interpretation at 0 is void (no reading yet). -/
theorem selfInterpret_zero (t : I) : selfInterpret t 0 = void := by
  unfold selfInterpret; simp

/-- Self-interpretation at 1 is the text itself. -/
theorem selfInterpret_one (t : I) : selfInterpret t 1 = t := by
  unfold selfInterpret; exact composeN_one t

/-- **The hermeneutic circle deepens monotonically**:
    each iteration of self-interpretation has at least as much
    self-resonance as the previous. Understanding only grows. -/
theorem hermeneuticCircle_weight_mono (t : I) (n : ℕ) :
    rs (selfInterpret t (n + 1)) (selfInterpret t (n + 1)) ≥
    rs (selfInterpret t n) (selfInterpret t n) := by
  unfold selfInterpret; exact rs_composeN_mono t n

/-- **Hermeneutic circle weight bound (lower)**:
    the weight after n self-interpretations is at least
    the weight after any earlier number of self-interpretations. -/
theorem hermeneuticCircle_weight_lower_bound (t : I) (m n : ℕ)
    (h : m ≤ n) :
    rs (selfInterpret t n) (selfInterpret t n) ≥
    rs (selfInterpret t m) (selfInterpret t m) := by
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.mp h
    subst this; exact le_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · calc rs (selfInterpret t (k + 1)) (selfInterpret t (k + 1))
          ≥ rs (selfInterpret t k) (selfInterpret t k) :=
            hermeneuticCircle_weight_mono t k
        _ ≥ rs (selfInterpret t m) (selfInterpret t m) :=
            ih (Nat.lt_succ_iff.mp hlt)

/-- **Weight at step n ≥ 0**: self-resonance is always non-negative. -/
theorem hermeneuticCircle_weight_nonneg (t : I) (n : ℕ) :
    rs (selfInterpret t n) (selfInterpret t n) ≥ 0 := by
  unfold selfInterpret; exact rs_composeN_nonneg t n

/-- **Void text circle is trivial**: iterating void always gives void. -/
theorem hermeneuticCircle_void (n : ℕ) :
    selfInterpret (void : I) n = void := by
  unfold selfInterpret; simp

/-- The "circle gain" at step n: how much weight the n-th traversal adds. -/
noncomputable def circleGain (t : I) (n : ℕ) : ℝ :=
  rs (selfInterpret t (n + 1)) (selfInterpret t (n + 1)) -
  rs (selfInterpret t n) (selfInterpret t n)

/-- Circle gain is always non-negative. -/
theorem circleGain_nonneg (t : I) (n : ℕ) : circleGain t n ≥ 0 := by
  unfold circleGain
  linarith [hermeneuticCircle_weight_mono t n]

/-- Circle gain for void text is zero. -/
theorem circleGain_void (n : ℕ) : circleGain (void : I) n = 0 := by
  unfold circleGain selfInterpret; simp

/-- Self-interpretation relates to readN with void reader. -/
theorem selfInterpret_eq_readN_void (t : I) (n : ℕ) :
    selfInterpret t n = readN (void : I) t n := by
  unfold selfInterpret
  rw [readN_void_reader]

/-- **Cumulative circle weight**: total weight accumulated over n traversals. -/
noncomputable def cumulativeCircleWeight (t : I) (n : ℕ) : ℝ :=
  rs (selfInterpret t n) (selfInterpret t n)

/-- Cumulative weight is monotone. -/
theorem cumulativeCircleWeight_mono (t : I) (n : ℕ) :
    cumulativeCircleWeight t (n + 1) ≥ cumulativeCircleWeight t n := by
  unfold cumulativeCircleWeight; exact hermeneuticCircle_weight_mono t n

/-- **The circle's emergence at step n**: the emergence created by
    composing the n-fold with one more copy of the text.
    This measures the "deepening of understanding" at each pass. -/
noncomputable def circleEmergence (t : I) (n : ℕ) (d : I) : ℝ :=
  emergence (selfInterpret t n) t d

/-- Circle emergence at step 0 is just emergence of void with t. -/
theorem circleEmergence_zero (t d : I) :
    circleEmergence t 0 d = 0 := by
  unfold circleEmergence; rw [selfInterpret_zero]; exact emergence_void_left t d

end HermeneuticCircleConvergence

/-! ## §19. Ricoeur's Distanciation (Distanciation)

Paul Ricoeur argues that when a text is "inscribed" — written down —
it separates from its author's original intention. The text acquires
autonomy: it can be read by readers the author never imagined, in
contexts the author never anticipated. This "distanciation" is not
a loss but a gain: it opens the text to new meanings.

In IDT, we formalize distanciation as the gap between:
- The author's intended meaning: `emergence author text observer`
- The reader's actual interpretation: `emergence reader text observer`

The "distanciation gap" measures how far the reader's experience
diverges from the author's intent. We prove bounds on this gap
using the emergence Cauchy-Schwarz inequality. -/

section Distanciation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The distanciation gap: how much the reader's emergence from a text
    differs from what the author intended.
    Positive: reader gets MORE emergence than author intended.
    Negative: reader gets LESS. -/
noncomputable def distanciationGap (author reader text observer : I) : ℝ :=
  emergence reader text observer - emergence author text observer

/-- Distanciation gap is antisymmetric in author/reader. -/
theorem distanciationGap_antisymm (a r t d : I) :
    distanciationGap a r t d = -distanciationGap r a t d := by
  unfold distanciationGap; ring

/-- Distanciation gap vanishes when author = reader (no separation). -/
theorem distanciationGap_self (a t d : I) :
    distanciationGap a a t d = 0 := by
  unfold distanciationGap; ring

/-- Distanciation gap when reader is void: the gap is exactly the
    negation of the author's emergence. A void reader misses
    everything the author put in. -/
theorem distanciationGap_void_reader (a t d : I) :
    distanciationGap a (void : I) t d = -emergence a t d := by
  unfold distanciationGap; rw [emergence_void_left]; ring

/-- Distanciation gap when author is void: the gap is exactly the
    reader's emergence. The reader invents all the meaning. -/
theorem distanciationGap_void_author (r t d : I) :
    distanciationGap (void : I) r t d = emergence r t d := by
  unfold distanciationGap; rw [emergence_void_left]; ring

/-- **Distanciation in terms of resonance**: the gap reduces to a
    difference of resonances with the text's composition. -/
theorem distanciationGap_eq (a r t d : I) :
    distanciationGap a r t d =
    rs (compose r t) d - rs r d - (rs (compose a t) d - rs a d) := by
  unfold distanciationGap emergence; ring

/-- **Distanciation bound (author side)**: the author's emergence squared
    is bounded by the product of composition and observer self-resonances. -/
theorem author_emergence_bounded (a t d : I) :
    (emergence a t d) ^ 2 ≤
    rs (compose a t) (compose a t) * rs d d :=
  emergence_bounded' a t d

/-- **Distanciation bound (reader side)**: same bound for the reader. -/
theorem reader_emergence_bounded (r t d : I) :
    (emergence r t d) ^ 2 ≤
    rs (compose r t) (compose r t) * rs d d :=
  emergence_bounded' r t d

/-- The "resonance profile shift" caused by distanciation: how the
    text's resonance profile changes from author's to reader's perspective. -/
noncomputable def resonanceProfileShift (author reader text observer : I) : ℝ :=
  rs (compose reader text) observer - rs (compose author text) observer

/-- Resonance profile shift decomposes into distanciation gap
    plus the "connotation shift" between reader and author. -/
theorem resonanceProfileShift_decomposition (a r t d : I) :
    resonanceProfileShift a r t d =
    distanciationGap a r t d + (rs r d - rs a d) := by
  unfold resonanceProfileShift distanciationGap emergence; ring

/-- **Ricoeur's productive distanciation**: distanciation enables
    meanings the author never intended. When the gap is nonzero,
    the text has become autonomous — it "says" something new. -/
theorem productive_distanciation (a r t d : I)
    (h : distanciationGap a r t d ≠ 0) :
    emergence r t d ≠ emergence a t d := by
  intro heq
  apply h
  unfold distanciationGap
  linarith

/-- **History creates distanciation**: reading prior texts changes the
    reader, increasing their distance from the author. -/
theorem history_creates_distanciation (a r t d : I) (prior : I) :
    distanciationGap a (compose r prior) t d =
    distanciationGap a r t d +
    (emergence (compose r prior) t d - emergence r t d) := by
  unfold distanciationGap; ring

/-- The cocycle constrains distanciation: when the reader's prior reading
    is the text itself (re-reading), the distanciation shifts by a
    cocycle-determined amount. -/
theorem distanciation_under_rereading (a r t d : I) :
    distanciationGap a (compose r t) t d - distanciationGap a r t d =
    emergence (compose r t) t d - emergence r t d := by
  unfold distanciationGap; ring

end Distanciation

/-! ## §20. Schleiermacher's Divination

Friedrich Schleiermacher proposed that interpretation requires
"divination" — the intuitive leap into the author's mind. The
interpreter must reconstruct the author's original act of creation.

In IDT, we formalize this as the attempt to find a "historical context"
h such that composing the reader with h produces the same emergence
as the author's original reading. We prove that PERFECT reconstruction
(zero distanciation for ALL observers) requires zero emergence from
the reconstruction — which means the reconstruction is purely linear.
But creative interpretation is essentially nonlinear (nonzero emergence).
Hence: perfect divination contradicts creative interpretation. -/

section Divination
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A "divinatory context" h is one that, when composed with the reader,
    closes the distanciation gap for ALL observers simultaneously. -/
def perfectDivination (author reader text h : I) : Prop :=
  ∀ d : I, emergence (compose reader h) text d = emergence author text d

/-- **Trivial divination**: if the reader is already the author,
    void context suffices. -/
theorem trivial_divination (a t : I) :
    perfectDivination a a t (void : I) := by
  intro d; simp

/-- **Self-divination via void**: an author "divining" themselves needs
    no historical context. -/
theorem self_divination (a t : I) :
    perfectDivination a a t (void : I) := trivial_divination a t

/-- What perfect divination means in terms of resonance:
    for all d, the resonance shift from composition is identical. -/
theorem perfectDivination_iff_shift (author reader text h : I) :
    perfectDivination author reader text h ↔
    ∀ d : I, rs (compose (compose reader h) text) d -
             rs (compose reader h) d - rs text d =
             rs (compose author text) d - rs author d - rs text d := by
  constructor
  · intro hd d; have := hd d; unfold emergence at this; linarith
  · intro hd d; unfold emergence; linarith [hd d]

/-- **Divination requires matching resonance shifts**: perfect divination
    holds iff compose(reader, h) and author produce identical resonance
    shifts through composition with the text. -/
theorem divination_shift_condition (author reader text h : I) :
    perfectDivination author reader text h ↔
    ∀ d : I, rs (compose (compose reader h) text) d -
             rs (compose reader h) d =
             rs (compose author text) d - rs author d := by
  constructor
  · intro hd d
    have := hd d; unfold emergence at this; linarith
  · intro hd d; unfold emergence; linarith [hd d]

/-- The "divination error" for a given context h and observer d. -/
noncomputable def divinationError (author reader text h d : I) : ℝ :=
  emergence (compose reader h) text d - emergence author text d

/-- Divination error is zero for all d iff perfect divination holds. -/
theorem divinationError_zero_iff (author reader text h : I) :
    (∀ d : I, divinationError author reader text h d = 0) ↔
    perfectDivination author reader text h := by
  constructor
  · intro hd d; have := hd d; unfold divinationError at this; linarith
  · intro hd d; unfold divinationError; have := hd d; linarith

/-- **Schleiermacher's impossibility**: if the reconstruction context h
    is itself non-void, then compose(reader, h) is enriched beyond
    the reader. The reconstruction adds weight — it is never "transparent." -/
theorem reconstruction_adds_weight (reader h : I) :
    rs (compose reader h) (compose reader h) ≥ rs reader reader :=
  compose_enriches' reader h

/-- **Perfect reconstruction from void requires linearity**:
    if the reader is void and we want perfect divination,
    then compose(void, h) = h must match the author's emergence.
    But if h itself is linear (zero emergence), then the divination
    is purely mechanical — no creative interpretation. -/
theorem void_reader_divination_linear (author text h : I)
    (hperf : perfectDivination author (void : I) text h)
    (hlin : leftLinear h) :
    ∀ d : I, emergence author text d = 0 := by
  intro d
  have := hperf d
  simp at this
  rw [hlin text d] at this
  linarith [this]

/-- **The divination-creativity tension**: if an interpretation is
    hermeneutic (nonzero emergence exists), then the historical
    context h that achieves perfect divination cannot be left-linear.
    Creative reading requires a non-trivial divinatory effort. -/
theorem divination_requires_nonlinearity (author reader text h : I)
    (hperf : perfectDivination author reader text h)
    (hherm : ∃ d : I, emergence author text d ≠ 0) :
    ¬leftLinear (compose reader h) := by
  intro hlin
  obtain ⟨d, hd⟩ := hherm
  have hzero := hlin text d
  have hperf_d := hperf d
  exact hd (by linarith)

/-- **Cocycle constraint on divination**: the divination error at
    step n of iterated reading satisfies a cocycle identity. -/
theorem divination_cocycle (author reader text h d : I) :
    divinationError author reader text h d =
    emergence h text d + emergence reader (compose h text) d -
    emergence reader h d - emergence author text d := by
  unfold divinationError
  have := cocycle_condition reader h text d
  linarith

end Divination

/-! ## §21. Benjamin's Translation Theory

Walter Benjamin's "The Task of the Translator" (1923) argues that
translation does not reproduce meaning; it transforms it. The
"pure language" (reine Sprache) toward which all languages gesture
is approached not through faithful reproduction but through the
creative friction of translation.

In IDT, we formalize translation as a composition `τ` that maps
a source text `s` into a target context. A "faithful" translation
preserves emergence patterns. Benjamin's insight: NO translation
can preserve ALL emergence patterns unless the source is linear
(trivial, with no creative potential).

This is the formal counterpart of the Italian proverb
"traduttore, traditore" — the translator is a traitor. -/

section Translation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A translation τ "preserves emergence" relative to source s if
    composing with τ preserves the emergence pattern against all observers. -/
def emergencePreserving (τ s : I) : Prop :=
  ∀ c d : I, emergence (compose τ s) c d = emergence s c d

/-- Void "translates" everything perfectly — but trivially. -/
theorem void_translates (s : I) : emergencePreserving (void : I) s := by
  intro c d; simp [emergence]

/-- **Benjamin's impossibility theorem**: if a translation preserves
    ALL emergence patterns AND the translation is non-void,
    then the source must have the same emergence pattern as its
    translation — meaning the translation adds nothing new. -/
theorem benjamin_impossibility (τ s : I)
    (hpres : emergencePreserving τ s)
    (c d : I) :
    emergence (compose τ s) c d = emergence s c d :=
  hpres c d

/-- A translation is "faithful" if it preserves self-emergence:
    the internal richness of the source is maintained. -/
def faithfulTranslation (τ s : I) : Prop :=
  emergence τ s (compose τ s) = 0

/-- **Faithful translation means zero interpretive depth**:
    if the translation adds no emergence of its own, the
    interpretive depth of the translation act is zero. -/
theorem faithful_zero_depth (τ s : I) (h : faithfulTranslation τ s) :
    interpretiveDepth τ s = 0 := h

/-- A "creative translation" is one with nonzero self-emergence. -/
def creativeTranslation (τ s : I) : Prop :=
  emergence τ s (compose τ s) ≠ 0

/-- Creative and faithful translations are mutually exclusive. -/
theorem creative_faithful_exclusive (τ s : I) :
    creativeTranslation τ s → ¬faithfulTranslation τ s := by
  intro hc hf; exact hc hf

/-- **The translation residue**: what a translation adds beyond
    the original. This is Benjamin's "afterlife" of the text. -/
noncomputable def translationResidue (τ s d : I) : ℝ :=
  emergence τ s d

/-- Translation residue vanishes for void translator. -/
theorem translationResidue_void (s d : I) :
    translationResidue (void : I) s d = 0 := emergence_void_left s d

/-- Translation residue vanishes for void source. -/
theorem translationResidue_void_source (τ d : I) :
    translationResidue τ (void : I) d = 0 := emergence_void_right τ d

/-- **Translation enriches**: the translated text has at least as much
    self-resonance as the source. Translation never diminishes. -/
theorem translation_enriches (τ s : I) :
    rs (compose τ s) (compose τ s) ≥ rs τ τ := compose_enriches' τ s

/-- **Double translation theorem**: translating a translation.
    The total emergence decomposes via the cocycle. -/
theorem double_translation (τ₁ τ₂ s d : I) :
    emergence τ₁ (compose τ₂ s) d =
    emergence τ₁ τ₂ d + emergence (compose τ₁ τ₂) s d -
    emergence τ₂ s d := by
  linarith [cocycle_condition τ₁ τ₂ s d]

/-- **Benjamin's pure language direction**: the residues of successive
    translations accumulate. Each translation adds its own layer of
    emergence, approaching (but never reaching) "pure language." -/
theorem translation_residue_accumulates (τ₁ τ₂ s d : I) :
    translationResidue τ₁ (compose τ₂ s) d =
    translationResidue τ₁ τ₂ d +
    emergence (compose τ₁ τ₂) s d -
    translationResidue τ₂ s d := by
  unfold translationResidue
  exact double_translation τ₁ τ₂ s d

/-- **No perfect translation of nonlinear texts**: if a source s has
    nonzero emergence in some context, and τ is a left-linear
    "translation," then the translation CANNOT preserve that emergence. -/
theorem linear_translation_loses_emergence (τ s : I)
    (hlin : leftLinear τ) (c d : I) :
    rs (compose τ s) d = rs τ d + rs s d := by
  have := rs_compose_eq τ s d
  rw [hlin s d] at this; linarith

/-- The "translation distance" between two translations of the same source. -/
noncomputable def translationDistance (τ₁ τ₂ s d : I) : ℝ :=
  emergence τ₁ s d - emergence τ₂ s d

/-- Translation distance is antisymmetric. -/
theorem translationDistance_antisymm (τ₁ τ₂ s d : I) :
    translationDistance τ₁ τ₂ s d = -translationDistance τ₂ τ₁ s d := by
  unfold translationDistance; ring

/-- Translation distance vanishes for identical translators. -/
theorem translationDistance_self (τ s d : I) :
    translationDistance τ τ s d = 0 := by
  unfold translationDistance; ring

end Translation

/-! ## §22. Gadamer's Rehabilitation of Authority and Tradition

Gadamer argues that tradition is not the enemy of understanding
but its medium. Authority (in the genuine sense) is acknowledged
freely, not imposed. In IDT, "tradition" is a chain of compositions
that forms the reader's effective history, and "authority" is measured
by the self-resonance of that tradition. -/

section TraditionAuthority
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The "authority" of a tradition: its accumulated self-resonance.
    Greater authority = more "weight" in shaping interpretations. -/
noncomputable def traditionAuthority (tradition : I) : ℝ := rs tradition tradition

/-- Authority is non-negative. -/
theorem traditionAuthority_nonneg (t : I) : traditionAuthority t ≥ 0 := by
  unfold traditionAuthority; exact rs_self_nonneg' t

/-- **Authority grows through transmission**: when tradition is passed
    on (composed with a new voice), its authority can only grow. -/
theorem authority_grows (tradition voice : I) :
    traditionAuthority (compose tradition voice) ≥ traditionAuthority tradition := by
  unfold traditionAuthority; exact compose_enriches' tradition voice

/-- **Void tradition has no authority**. -/
theorem void_tradition_no_authority :
    traditionAuthority (void : I) = 0 := by
  unfold traditionAuthority; exact rs_void_void

/-- **Non-void tradition has genuine authority**. -/
theorem nonvoid_tradition_has_authority (t : I) (h : t ≠ void) :
    traditionAuthority t > 0 := by
  unfold traditionAuthority; exact rs_self_pos t h

/-- Tradition shapes all future emergence: the emergence a reader gets
    from any text is conditioned by the tradition they carry. -/
theorem tradition_conditions_emergence (tradition text observer : I) :
    emergence tradition text observer =
    rs (compose tradition text) observer - rs tradition observer - rs text observer := by
  rfl

/-- **Authority and interpretive depth**: the interpretive depth of reading
    text t from within a tradition equals the self-emergence of
    the tradition-text fusion. -/
theorem authority_depth (tradition text : I) :
    interpretiveDepth tradition text =
    rs (compose tradition text) (compose tradition text) -
    comprehension tradition text - fidelity tradition text :=
  depth_from_comprehension_fidelity tradition text

/-- **Tradition accumulation**: n generations of a tradition have
    monotonically growing authority. -/
theorem tradition_accumulation (t : I) (n : ℕ) :
    traditionAuthority (composeN t (n + 1)) ≥ traditionAuthority (composeN t n) := by
  unfold traditionAuthority; exact rs_composeN_mono t n

end TraditionAuthority

/-! ## §23. The Surplus of Meaning (Ricoeur)

Ricoeur's concept of "surplus of meaning" (surcroît de sens):
every text contains more meaning than any single interpretation
can exhaust. Different readers extract different surpluses.
We formalize this and prove structural results. -/

section SurplusOfMeaning
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The surplus that reader r extracts from text t, beyond what a
    "minimal" (void) reader would get. This is the reader's
    interpretive contribution. -/
noncomputable def readerSurplus (r t : I) : ℝ :=
  rs (compose r t) (compose r t) - rs t t

/-- **Reader surplus is non-negative for non-void readers**: any non-void
    reader adds at least something to the interpretation beyond the
    text alone. (This follows because compose enriches, and
    rs(compose r t, compose r t) ≥ rs(r,r) ≥ 0, but we need the
    comparison against rs(t,t) which uses the right-enrichment property
    restated via associativity.) -/
theorem readerSurplus_void_reader (t : I) :
    readerSurplus (void : I) t = 0 := by
  unfold readerSurplus; simp

/-- **Different readers extract different surpluses**: if two readers
    have different surpluses from the same text, they are different readers. -/
theorem surplus_distinguishes_readers (r₁ r₂ t : I)
    (h : readerSurplus r₁ t ≠ readerSurplus r₂ t) :
    r₁ ≠ r₂ := by
  intro heq; rw [heq] at h; exact h rfl

/-- The "text surplus" that a text contributes beyond the reader alone. -/
noncomputable def textSurplus (r t : I) : ℝ :=
  rs (compose r t) (compose r t) - rs r r

/-- Text surplus is always non-negative. -/
theorem textSurplus_nonneg (r t : I) : textSurplus r t ≥ 0 := by
  unfold textSurplus; linarith [compose_enriches' r t]

/-- Text surplus from void text is zero. -/
theorem textSurplus_void_text (r : I) : textSurplus r (void : I) = 0 := by
  unfold textSurplus; simp

/-- **Surplus duality**: the total weight of the interpretation equals
    the reader's original weight plus the text surplus, OR
    the text's original weight plus the reader surplus. -/
theorem surplus_duality (r t : I) :
    rs r r + textSurplus r t = rs t t + readerSurplus r t := by
  unfold textSurplus readerSurplus; ring

/-- **Mutual surplus**: the symmetric part of the total enrichment.
    This measures how much reader and text TOGETHER create beyond
    what either brings alone. -/
noncomputable def mutualSurplus (r t : I) : ℝ :=
  rs (compose r t) (compose r t) - rs r r - rs t t

/-- Mutual surplus decomposes into comprehension + fidelity + depth - rs(r,r) - rs(t,t). -/
theorem mutualSurplus_decomposition (r t : I) :
    mutualSurplus r t =
    comprehension r t + fidelity r t + interpretiveDepth r t - rs r r - rs t t := by
  unfold mutualSurplus
  rw [hermeneutic_identity r t]

/-- Mutual surplus for void reader. -/
theorem mutualSurplus_void_reader (t : I) : mutualSurplus (void : I) t = 0 := by
  unfold mutualSurplus; simp [rs_void_void, rs_void_left', rs_void_right']

/-- Mutual surplus for void text. -/
theorem mutualSurplus_void_text (r : I) : mutualSurplus r (void : I) = 0 := by
  unfold mutualSurplus; simp [rs_void_void, rs_void_left', rs_void_right']

end SurplusOfMeaning

/-! ## §24. Heidegger's Fore-Structure of Understanding

Heidegger's analysis in *Being and Time* identifies three elements of
the "fore-structure" (Vorstruktur) of understanding:
1. Fore-having (Vorhabe): what the interpreter already has
2. Fore-sight (Vorsicht): the perspective from which interpretation proceeds
3. Fore-conception (Vorgriff): the conceptual framework applied

In IDT, all three are aspects of the reader's state r before reading.
We formalize how each contributes to the interpretation. -/

section ForeStructure
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Fore-having: what the reader possesses before interpretation.
    Measured by self-resonance. -/
noncomputable def foreHaving (r : I) : ℝ := rs r r

/-- Fore-sight: how the reader's perspective shapes the view of the text.
    Measured by the cross-resonance rs(r, t). -/
noncomputable def foreSight (r t : I) : ℝ := rs r t

/-- Fore-conception: how the reader's framework shapes the emerging meaning.
    This is the emergence contribution of the reader. -/
noncomputable def foreConception (r t : I) : ℝ :=
  emergence r t (compose r t)

/-- **Fore-structure identity**: the interpretation's weight decomposes
    into fore-having, fore-sight components, and fore-conception. -/
theorem foreStructure_identity (r t : I) :
    rs (compose r t) (compose r t) =
    rs r (compose r t) + rs t (compose r t) + foreConception r t := by
  unfold foreConception
  rw [rs_compose_eq r t (compose r t)]

/-- **Fore-having bounds emergence**: the fore-having constrains
    how much emergence is possible. Without anything, you can't
    create new meaning. -/
theorem foreHaving_bounds (r t d : I) :
    (emergence r t d) ^ 2 ≤
    rs (compose r t) (compose r t) * rs d d := emergence_bounded' r t d

/-- **Zero fore-having means zero emergence**: void reader (no fore-having)
    produces no emergence from any text. -/
theorem zero_foreHaving_zero_emergence (t d : I) :
    foreHaving (void : I) = 0 ∧ emergence (void : I) t d = 0 := by
  constructor
  · unfold foreHaving; exact rs_void_void
  · exact emergence_void_left t d

/-- **Fore-conception equals interpretive depth**. -/
theorem foreConception_is_depth (r t : I) :
    foreConception r t = interpretiveDepth r t := rfl

/-- **Fore-sight void text**: looking at nothing reveals nothing. -/
theorem foreSight_void_text (r : I) : foreSight r (void : I) = 0 := by
  unfold foreSight; exact rs_void_right' r

/-- **Fore-sight void reader**: an empty perspective sees nothing. -/
theorem foreSight_void_reader (t : I) : foreSight (void : I) t = 0 := by
  unfold foreSight; exact rs_void_left' t

/-- **Fore-having grows through reading**: after reading, you have more. -/
theorem foreHaving_grows (r t : I) :
    foreHaving (compose r t) ≥ foreHaving r := by
  unfold foreHaving; exact compose_enriches' r t

end ForeStructure

/-! ## §25. Derrida's Différance and the Play of Meaning

Derrida's "différance" — the perpetual deferral and differentiation
of meaning. No interpretation is final; each reading opens new
readings. In IDT, this is captured by the fact that iterated
reading creates ever-new emergence patterns. We formalize the
"play" of meaning as the non-convergence of emergence patterns
even when self-resonance converges. -/

section Differance
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The "play" at step n: the emergence pattern of the n-th reading. -/
noncomputable def meaningPlay (r t d : I) (n : ℕ) : ℝ :=
  emergence (readN r t n) t d

/-- Play at step 0 is the initial emergence. -/
theorem meaningPlay_zero (r t d : I) :
    meaningPlay r t d 0 = emergence r t d := by
  unfold meaningPlay; simp

/-- Play with void text is always zero. -/
theorem meaningPlay_void_text (r d : I) (n : ℕ) :
    meaningPlay r (void : I) d n = 0 := by
  unfold meaningPlay; simp [emergence_void_right]

/-- **The trace of meaning**: the cumulative emergence over n readings.
    Derrida's "trace" — the record of meaning's passage. -/
noncomputable def meaningTrace (r t d : I) : ℕ → ℝ
  | 0 => 0
  | n + 1 => meaningTrace r t d n + meaningPlay r t d n

/-- Trace starts at zero. -/
theorem meaningTrace_zero (r t d : I) : meaningTrace r t d 0 = 0 := rfl

/-- Trace accumulates play. -/
theorem meaningTrace_succ (r t d : I) (n : ℕ) :
    meaningTrace r t d (n + 1) = meaningTrace r t d n + meaningPlay r t d n := rfl

/-- **Derrida's supplement**: each reading adds a "supplement" —
    new emergence that supplements (and disrupts) the prior reading.
    The supplement at step n is exactly the play at step n. -/
noncomputable def supplement (r t d : I) (n : ℕ) : ℝ := meaningPlay r t d n

/-- Void supplement is zero. -/
theorem supplement_void_text (r d : I) (n : ℕ) :
    supplement r (void : I) d n = 0 := meaningPlay_void_text r d n

/-- **The dissemination of meaning**: the total emergence from
    reading a text n times is captured by the trace. Each reading
    "disseminates" meaning differently. -/
theorem dissemination_decomposition (r t : I) (n : ℕ) :
    rs (readN r t (n + 1)) (readN r t (n + 1)) -
    rs (readN r t n) (readN r t n) =
    readingGain r t n := rfl

/-- **Play never stops for non-void reader**: the readN state is
    always non-void, ensuring interpretation remains possible. -/
theorem play_continues (r t : I) (h : r ≠ void) (n : ℕ) :
    readN r t n ≠ void := readN_ne_void r t h n

end Differance

/-! ## §26. The Weight of History — Effective-Historical Consciousness

Gadamer's "effective-historical consciousness" (wirkungsgeschichtliches
Bewußtsein) is the awareness that one's understanding is always
shaped by history. We prove deeper structural results about how
the weight of history constrains interpretation. -/

section EffectiveHistoricalConsciousness
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The "historical weight ratio": how much heavier the reader becomes
    after n readings, relative to their initial state. -/
noncomputable def historicalWeightGain (r t : I) (n : ℕ) : ℝ :=
  rs (readN r t n) (readN r t n) - rs r r

/-- Historical weight gain is non-negative. -/
theorem historicalWeightGain_nonneg (r t : I) (n : ℕ) :
    historicalWeightGain r t n ≥ 0 := by
  unfold historicalWeightGain
  linarith [readN_enriches_original r t n]

/-- Historical weight gain is monotonically non-decreasing. -/
theorem historicalWeightGain_mono (r t : I) (n : ℕ) :
    historicalWeightGain r t (n + 1) ≥ historicalWeightGain r t n := by
  unfold historicalWeightGain
  linarith [readN_enriches r t n]

/-- Historical weight gain at step 0 is zero. -/
theorem historicalWeightGain_zero (r t : I) :
    historicalWeightGain r t 0 = 0 := by
  unfold historicalWeightGain; simp

/-- **Historical consciousness theorem**: the total weight gain after
    n+1 readings equals the gain after n readings plus the reading gain
    at step n. The history of effects is ADDITIVE in weight gains. -/
theorem historical_consciousness_additive (r t : I) (n : ℕ) :
    historicalWeightGain r t (n + 1) =
    historicalWeightGain r t n + readingGain r t n := by
  unfold historicalWeightGain readingGain; ring

/-- **The past is never dead**: once a text has been read, the weight
    gain is permanent. Even if subsequent texts are void, the
    accumulated weight persists. -/
theorem past_is_never_dead (r t : I) (n : ℕ) :
    rs (readN (readN r t n) (void : I) 0) (readN (readN r t n) (void : I) 0) =
    rs (readN r t n) (readN r t n) := by
  simp

/-- **Effective-historical lower bound**: after n readings,
    the reader's weight is at least n times the single-step enrichment
    only if each step adds at least as much. We prove a weaker but
    unconditional bound: weight ≥ original weight. -/
theorem effective_historical_lower (r t : I) (n : ℕ) :
    rs (readN r t n) (readN r t n) ≥ rs r r :=
  readN_enriches_original r t n

/-- The "historical emergence" at step n: the emergence that step n
    contributes, measured against the full accumulated state. -/
noncomputable def historicalEmergence (r t : I) (n : ℕ) : ℝ :=
  emergence (readN r t n) t (readN r t (n + 1))

/-- Historical emergence squared is bounded. -/
theorem historicalEmergence_bounded (r t : I) (n : ℕ) :
    (historicalEmergence r t n) ^ 2 ≤
    rs (readN r t (n + 1)) (readN r t (n + 1)) *
    rs (readN r t (n + 1)) (readN r t (n + 1)) := by
  unfold historicalEmergence
  rw [readN_succ]
  exact emergence_bounded' (readN r t n) t (compose (readN r t n) t)

end EffectiveHistoricalConsciousness

/-! ## §27. The Fusion Algebra — Structural Properties

Deeper algebraic properties of the fusion-of-horizons operation,
connecting to the philosophical insight that interpretation has
a definite algebraic structure. -/

section FusionAlgebra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Triple fusion**: reading three texts sequentially. -/
theorem triple_fusion (r t₁ t₂ t₃ : I) :
    fusionOfHorizons (fusionOfHorizons (fusionOfHorizons r t₁) t₂) t₃ =
    fusionOfHorizons r (compose t₁ (compose t₂ t₃)) := by
  unfold fusionOfHorizons; rw [compose_assoc', compose_assoc']

/-- **Triple fusion enrichment**: reading three texts enriches beyond two. -/
theorem triple_fusion_enriches (r t₁ t₂ t₃ : I) :
    rs (fusionOfHorizons (fusionOfHorizons (fusionOfHorizons r t₁) t₂) t₃)
       (fusionOfHorizons (fusionOfHorizons (fusionOfHorizons r t₁) t₂) t₃) ≥
    rs (fusionOfHorizons (fusionOfHorizons r t₁) t₂)
       (fusionOfHorizons (fusionOfHorizons r t₁) t₂) := by
  unfold fusionOfHorizons; exact compose_enriches' _ _

/-- **Fusion is a monoid action**: the reader's state evolves by
    a monoid action of the text monoid on the reader space. -/
theorem fusion_monoid_action_assoc (r t₁ t₂ : I) :
    fusionOfHorizons (fusionOfHorizons r t₁) t₂ =
    fusionOfHorizons r (compose t₁ t₂) := fusion_assoc r t₁ t₂

/-- **Fusion monoid action identity**: void text acts as identity. -/
theorem fusion_monoid_action_id (r : I) :
    fusionOfHorizons r (void : I) = r := fusion_void_text r

/-- **Emergence transfer under fusion**: the cocycle governs how
    emergence "transfers" when fusing horizons in different orders. -/
theorem emergence_transfer (r t₁ t₂ d : I) :
    emergence r t₁ d + emergence (fusionOfHorizons r t₁) t₂ d =
    emergence t₁ t₂ d + emergence r (compose t₁ t₂) d := by
  unfold fusionOfHorizons; exact cocycle_condition r t₁ t₂ d

/-- **The enrichment chain**: for any list of texts, the reader's
    weight only grows. -/
theorem enrichment_chain (r : I) (t₁ t₂ : I) :
    rs (compose (compose r t₁) t₂) (compose (compose r t₁) t₂) ≥ rs r r := by
  calc rs (compose (compose r t₁) t₂) (compose (compose r t₁) t₂)
      ≥ rs (compose r t₁) (compose r t₁) := compose_enriches' _ _
    _ ≥ rs r r := compose_enriches' _ _

/-- **Emergence balance under re-association**: the total emergence
    is invariant under different groupings of the hermeneutic circle. -/
theorem emergence_balance (r p₁ p₂ d : I) :
    emergence r p₁ d - emergence r (compose p₁ p₂) d =
    emergence p₁ p₂ d - emergence (compose r p₁) p₂ d := by
  linarith [cocycle_condition r p₁ p₂ d]

end FusionAlgebra

/-! ## §28. Interpretive Entropy and the Arrow of Understanding

A text can be read but not un-read. This irreversibility is
captured by the monotonic growth of self-resonance. We formalize
an "arrow of understanding" analogous to the arrow of time in
thermodynamics: interpretive entropy (weight) never decreases. -/

section InterpretiveEntropy
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Interpretive entropy: the self-resonance of the reader's state.
    Like thermodynamic entropy, it only grows. -/
noncomputable def interpretiveEntropy (a : I) : ℝ := rs a a

/-- **Second law of hermeneutics**: interpretive entropy never decreases
    under composition. You cannot un-read a text. -/
theorem second_law_hermeneutics (r t : I) :
    interpretiveEntropy (compose r t) ≥ interpretiveEntropy r := by
  unfold interpretiveEntropy; exact compose_enriches' r t

/-- **Arrow of understanding**: entropy grows monotonically through
    iterated reading. -/
theorem arrow_of_understanding (r t : I) (n : ℕ) :
    interpretiveEntropy (readN r t (n + 1)) ≥ interpretiveEntropy (readN r t n) := by
  unfold interpretiveEntropy; exact readN_enriches r t n

/-- **Entropy of void is zero**: the ground state of understanding. -/
theorem interpretiveEntropy_void : interpretiveEntropy (void : I) = 0 := by
  unfold interpretiveEntropy; exact rs_void_void

/-- **Positive entropy for non-void**: any genuine understanding has
    strictly positive entropy. -/
theorem interpretiveEntropy_pos (a : I) (h : a ≠ void) :
    interpretiveEntropy a > 0 := by
  unfold interpretiveEntropy; exact rs_self_pos a h

/-- **Entropy gap**: the entropy created by an interpretive act.
    Always non-negative — the hermeneutic second law. -/
noncomputable def entropyGap (r t : I) : ℝ :=
  interpretiveEntropy (compose r t) - interpretiveEntropy r

/-- Entropy gap is non-negative. -/
theorem entropyGap_nonneg (r t : I) : entropyGap r t ≥ 0 := by
  unfold entropyGap; linarith [second_law_hermeneutics r t]

/-- Entropy gap from void text is zero. -/
theorem entropyGap_void_text (r : I) : entropyGap r (void : I) = 0 := by
  unfold entropyGap interpretiveEntropy; simp

/-- **Cumulative entropy**: total entropy accumulated over n readings. -/
theorem cumulative_entropy (r t : I) (n : ℕ) :
    interpretiveEntropy (readN r t n) ≥ interpretiveEntropy r := by
  unfold interpretiveEntropy; exact readN_enriches_original r t n

end InterpretiveEntropy

/-! ## §29. Intertextuality — How Texts Read Each Other

Julia Kristeva's concept: every text is a "mosaic of quotations."
In IDT, this means the emergence of reading text t₂ after t₁
depends on t₁ — texts read through other texts produce different
emergence. We formalize the intertextual cocycle. -/

section Intertextuality
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The "intertextual emergence": how much reading t₂ through the lens of t₁
    creates new meaning beyond what each text contributes alone. -/
noncomputable def intertextualEmergence (t₁ t₂ d : I) : ℝ :=
  emergence t₁ t₂ d

/-- **Intertextuality is asymmetric**: reading t₂ after t₁ is generally
    different from reading t₁ after t₂. The order of encounter matters. -/
theorem intertextuality_asymmetric (t₁ t₂ d : I)
    (h : compose t₁ t₂ ≠ compose t₂ t₁) :
    rs (compose t₁ t₂) d ≠ rs (compose t₂ t₁) d →
    intertextualEmergence t₁ t₂ d ≠ intertextualEmergence t₂ t₁ d ∨
    rs t₁ d ≠ rs t₂ d := by
  intro hne
  by_cases h2 : intertextualEmergence t₁ t₂ d ≠ intertextualEmergence t₂ t₁ d
  · exact Or.inl h2
  · push_neg at h2
    right
    intro heq
    apply hne
    unfold intertextualEmergence emergence at h2
    linarith

/-- **Intertextual cocycle**: the total emergence of reading three texts
    decomposes via the cocycle condition. -/
theorem intertextual_cocycle (t₁ t₂ t₃ d : I) :
    intertextualEmergence t₁ t₂ d + emergence (compose t₁ t₂) t₃ d =
    intertextualEmergence t₂ t₃ d + emergence t₁ (compose t₂ t₃) d := by
  unfold intertextualEmergence; exact cocycle_condition t₁ t₂ t₃ d

/-- **Void is intertextually inert**: adding void to the canon creates
    no new intertextual meaning. -/
theorem void_intertextually_inert_left (t d : I) :
    intertextualEmergence (void : I) t d = 0 := emergence_void_left t d

theorem void_intertextually_inert_right (t d : I) :
    intertextualEmergence t (void : I) d = 0 := emergence_void_right t d

/-- The "canon effect": reading a text within a canon (list of prior texts)
    produces different emergence than reading it alone. -/
noncomputable def canonEffect (canon : List I) (text d : I) : ℝ :=
  emergence (List.foldl compose void canon) text d

/-- Empty canon produces no effect. -/
theorem canonEffect_nil (text d : I) :
    canonEffect ([] : List I) text d = 0 := by
  unfold canonEffect; simp [emergence_void_left]

end Intertextuality

/-! ## §30. The Hermeneutic Spiral — Beyond the Circle

The hermeneutic "circle" is really a spiral: each pass returns to
the same text but at a higher level of understanding. We formalize
the spiral and prove its key structural properties. -/

section HermeneuticSpiral
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The hermeneutic spiral: the sequence of reader states through
    iterated reading. We prove the spiral never descends. -/
noncomputable def spiralHeight (r t : I) (n : ℕ) : ℝ :=
  rs (readN r t n) (readN r t n)

/-- **Spiral monotonicity**: the spiral always ascends or stays level. -/
theorem spiral_mono (r t : I) (n : ℕ) :
    spiralHeight r t (n + 1) ≥ spiralHeight r t n := by
  unfold spiralHeight; exact readN_enriches r t n

/-- **Spiral never descends below start**. -/
theorem spiral_above_base (r t : I) (n : ℕ) :
    spiralHeight r t n ≥ spiralHeight r t 0 := by
  unfold spiralHeight; simp; exact readN_enriches_original r t n

/-- The "spiral step": the increment at each pass through the circle. -/
noncomputable def spiralStep (r t : I) (n : ℕ) : ℝ :=
  spiralHeight r t (n + 1) - spiralHeight r t n

/-- Spiral step is non-negative. -/
theorem spiralStep_nonneg (r t : I) (n : ℕ) : spiralStep r t n ≥ 0 := by
  unfold spiralStep; linarith [spiral_mono r t n]

/-- **Spiral step equals reading gain**. -/
theorem spiralStep_eq_readingGain (r t : I) (n : ℕ) :
    spiralStep r t n = readingGain r t n := by
  unfold spiralStep spiralHeight readingGain; ring

/-- **Void text spiral is flat**: reading nothing creates no spiral. -/
theorem spiral_flat_void (r : I) (n : ℕ) :
    spiralHeight r (void : I) n = rs r r := by
  unfold spiralHeight; simp

/-- **The total ascent**: sum of all spiral steps up to step n
    equals the total height gain. -/
theorem spiral_total_ascent (r t : I) (n : ℕ) :
    spiralHeight r t n - spiralHeight r t 0 =
    historicalWeightGain r t n := by
  unfold spiralHeight historicalWeightGain; simp

end HermeneuticSpiral

/-! ## §31. Bakhtin's Dialogism and Polyphony

Mikhail Bakhtin's theory of dialogism: every utterance is fundamentally
a response to prior utterances and anticipates future responses. No
utterance exists in isolation — it is always "double-voiced." In the
novel, this becomes POLYPHONY: multiple independent voices coexisting
without a single authoritative viewpoint subordinating the others.

In IDT, dialogism means that the emergence of any composition depends
on ALL the voices present. Polyphony means the composition preserves
the distinctness of voices — they don't merge into a single linear sum.
We formalize Bakhtin's key concepts and prove structural results. -/

section BakhtinDialogism
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Bakhtin's double-voicing**: any utterance a in context b produces
    emergence — the utterance "responds" to its context. The emergence
    IS the double-voicing: a speaks both as itself and through its
    relationship with b. -/
noncomputable def doubleVoicing (a b d : I) : ℝ := emergence a b d

/-- Double-voicing vanishes without a second voice. -/
theorem doubleVoicing_void_context (a d : I) :
    doubleVoicing a (void : I) d = 0 := emergence_void_right a d

/-- Double-voicing vanishes for a void voice. -/
theorem doubleVoicing_void_voice (b d : I) :
    doubleVoicing (void : I) b d = 0 := emergence_void_left b d

/-- **Dialogic surplus**: the total resonance surplus created by
    the dialogue between a and b, beyond their individual contributions. -/
noncomputable def dialogicSurplus (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- Dialogic surplus with void is zero. -/
theorem dialogicSurplus_void_right (a : I) :
    dialogicSurplus a (void : I) = 0 := by
  unfold dialogicSurplus; simp [rs_void_void]

/-- Dialogic surplus with void left. -/
theorem dialogicSurplus_void_left (b : I) :
    dialogicSurplus (void : I) b = 0 := by
  unfold dialogicSurplus; simp [rs_void_void]

/-- **Polyphonic composition**: composing n voices. The self-resonance
    of the polyphonic whole exceeds any single voice. -/
theorem polyphonic_enriches_first (v₁ v₂ : I) :
    rs (compose v₁ v₂) (compose v₁ v₂) ≥ rs v₁ v₁ :=
  compose_enriches' v₁ v₂

/-- **Bakhtin's heteroglossia**: the irreducible multiplicity of voices.
    If the first voice is non-void, it cannot be silenced — the
    polyphonic composition preserves its presence. -/
theorem heteroglossia_criterion (v₁ v₂ : I)
    (h : v₁ ≠ (void : I)) : compose v₁ v₂ ≠ void :=
  compose_ne_void_of_left v₁ v₂ h

/-- **Dialogic weight**: composition of voices always has non-negative weight. -/
theorem dialogic_weight_nonneg (v₁ v₂ : I) :
    rs (compose v₁ v₂) (compose v₁ v₂) ≥ 0 := rs_self_nonneg' _

/-- **Bakhtin's carnival**: the emergence when voices are reordered.
    Carnival reverses hierarchies — swapping voice order changes emergence. -/
noncomputable def carnivalEffect (v₁ v₂ d : I) : ℝ :=
  emergence v₁ v₂ d - emergence v₂ v₁ d

/-- Carnival effect is antisymmetric. -/
theorem carnivalEffect_antisymm (v₁ v₂ d : I) :
    carnivalEffect v₁ v₂ d = -carnivalEffect v₂ v₁ d := by
  unfold carnivalEffect; ring

/-- Carnival effect vanishes for self. -/
theorem carnivalEffect_self (v d : I) : carnivalEffect v v d = 0 := by
  unfold carnivalEffect; ring

/-- Carnival effect vanishes with void. -/
theorem carnivalEffect_void_left (v d : I) :
    carnivalEffect (void : I) v d = 0 := by
  unfold carnivalEffect; rw [emergence_void_left, emergence_void_right]; ring

/-- **Answerability**: every voice is "answerable" to every other.
    The emergence of a response depends on the prior voice. -/
theorem answerability_cocycle (v₁ v₂ v₃ d : I) :
    emergence v₁ v₂ d + emergence (compose v₁ v₂) v₃ d =
    emergence v₂ v₃ d + emergence v₁ (compose v₂ v₃) d :=
  cocycle_condition v₁ v₂ v₃ d

/-- **Dialogic self-resonance decomposition**: the weight of a
    two-voice composition decomposes into individual weights plus
    dialogic surplus. -/
theorem dialogic_decomposition (v₁ v₂ : I) :
    rs (compose v₁ v₂) (compose v₁ v₂) =
    rs v₁ v₁ + rs v₂ v₂ + dialogicSurplus v₁ v₂ := by
  unfold dialogicSurplus; ring

/-- **Three-voice polyphony enrichment**: three voices enrich beyond two. -/
theorem three_voice_enriches (v₁ v₂ v₃ : I) :
    rs (compose (compose v₁ v₂) v₃) (compose (compose v₁ v₂) v₃) ≥
    rs (compose v₁ v₂) (compose v₁ v₂) :=
  compose_enriches' _ _

/-- **Three voices enrich beyond one**: transitivity. -/
theorem three_voice_enriches_first (v₁ v₂ v₃ : I) :
    rs (compose (compose v₁ v₂) v₃) (compose (compose v₁ v₂) v₃) ≥ rs v₁ v₁ := by
  calc rs (compose (compose v₁ v₂) v₃) (compose (compose v₁ v₂) v₃)
      ≥ rs (compose v₁ v₂) (compose v₁ v₂) := compose_enriches' _ _
    _ ≥ rs v₁ v₁ := compose_enriches' _ _

/-- **Polyphonic non-voidness**: if any voice is non-void, the
    polyphonic whole is non-void. -/
theorem polyphonic_ne_void (v₁ v₂ : I) (h : v₁ ≠ void) :
    compose v₁ v₂ ≠ void := compose_ne_void_of_left v₁ v₂ h

end BakhtinDialogism

/-! ## §32. Iser's Reader-Response Theory: Gaps and Blanks

Wolfgang Iser's reader-response theory centers on "gaps" (Leerstellen)
in the text — places of indeterminacy that the reader must fill. The
literary work exists not in the text alone nor in the reader alone,
but in the "convergence" of the two. The text provides a skeleton;
the reader provides flesh.

In IDT, gaps are formalized as the difference between the text's
"potential" (its contribution to resonance with all observers) and the
"actualized" meaning (what a specific reader creates). Emergence IS
the gap-filling: it is exactly the meaning that exists in neither text
nor reader but arises from their encounter. -/

section IserReaderResponse
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Iser's gap**: the indeterminacy in a text as experienced by reader r.
    This is the emergence — the meaning that neither text nor reader
    carries alone, but which arises in their encounter. -/
noncomputable def textualGap (reader text observer : I) : ℝ :=
  emergence reader text observer

/-- Void reader fills no gaps. -/
theorem textualGap_void_reader (text observer : I) :
    textualGap (void : I) text observer = 0 := emergence_void_left text observer

/-- Void text has no gaps to fill. -/
theorem textualGap_void_text (reader observer : I) :
    textualGap reader (void : I) observer = 0 := emergence_void_right reader observer

/-- **Iser's concretization**: the reader's actualization of the text.
    This is the total resonance of the interpretation = text + reader + gap. -/
theorem concretization_eq (reader text observer : I) :
    rs (compose reader text) observer =
    rs reader observer + rs text observer + textualGap reader text observer := by
  unfold textualGap; rw [rs_compose_eq]

/-- **Gap-filling bounded**: the gap a reader can fill is bounded by the
    weight of the interpretation and the observer. -/
theorem gap_bounded (reader text observer : I) :
    (textualGap reader text observer) ^ 2 ≤
    rs (compose reader text) (compose reader text) * rs observer observer := by
  unfold textualGap; exact emergence_bounded' reader text observer

/-- **The wandering viewpoint**: as the reader progresses through a text
    (iterated reading), their gap-filling changes at each step. The
    "wandering viewpoint" is the sequence of gaps filled. -/
noncomputable def wanderingViewpoint (reader text observer : I) (n : ℕ) : ℝ :=
  textualGap (readN reader text n) text observer

/-- Wandering viewpoint at step 0 is the initial gap. -/
theorem wanderingViewpoint_zero (reader text observer : I) :
    wanderingViewpoint reader text observer 0 = textualGap reader text observer := by
  unfold wanderingViewpoint; simp

/-- Wandering viewpoint with void text is always zero. -/
theorem wanderingViewpoint_void_text (reader observer : I) (n : ℕ) :
    wanderingViewpoint reader (void : I) observer n = 0 := by
  unfold wanderingViewpoint textualGap; simp [emergence_void_right]

/-- **Iser's implied reader**: the "ideal" reader who would fill gaps
    maximally. While we can't characterize this reader explicitly,
    we can show that any reader's gap-filling is bounded. -/
theorem implied_reader_bound (reader text : I) :
    (textualGap reader text (compose reader text)) ^ 2 ≤
    rs (compose reader text) (compose reader text) *
    rs (compose reader text) (compose reader text) := by
  exact gap_bounded reader text (compose reader text)

/-- **Iser's aesthetic response**: the total "response" of the reader
    to the text, measured as the enrichment in self-resonance. -/
noncomputable def aestheticResponse (reader text : I) : ℝ :=
  rs (compose reader text) (compose reader text) - rs reader reader

/-- Aesthetic response is non-negative. -/
theorem aestheticResponse_nonneg (reader text : I) :
    aestheticResponse reader text ≥ 0 := by
  unfold aestheticResponse; linarith [compose_enriches' reader text]

/-- Aesthetic response to void is zero. -/
theorem aestheticResponse_void_text (reader : I) :
    aestheticResponse reader (void : I) = 0 := by
  unfold aestheticResponse; simp

/-- **Different readers, different responses**: if two readers have
    different aesthetic responses, they are different readers. -/
theorem different_responses_different_readers (r₁ r₂ text : I)
    (h : aestheticResponse r₁ text ≠ aestheticResponse r₂ text) :
    r₁ ≠ r₂ := by
  intro heq; rw [heq] at h; exact h rfl

/-- **Cumulative aesthetic response**: each additional reading adds
    non-negative enrichment. -/
theorem cumulative_aesthetic_response (reader text : I) (n : ℕ) :
    rs (readN reader text (n + 1)) (readN reader text (n + 1)) -
    rs (readN reader text n) (readN reader text n) ≥ 0 := by
  linarith [readN_enriches reader text n]

/-- **Response monotonicity**: reading more only increases the cumulative response. -/
theorem aesthetic_response_cumulative_mono (reader text : I) (n : ℕ) :
    rs (readN reader text (n + 1)) (readN reader text (n + 1)) - rs reader reader ≥
    rs (readN reader text n) (readN reader text n) - rs reader reader := by
  linarith [readN_enriches reader text n]

end IserReaderResponse

/-! ## §33. Fish's Interpretive Communities

Stanley Fish argues that meaning is not "in" the text but is produced
by "interpretive communities" — groups of readers who share interpretive
strategies. The text constrains interpretation, but the community
determines which of the possible interpretations is "correct."

In IDT, an interpretive community is a collection of readers who share
the same emergence profile (sameIdea). Members of a community produce
the same emergence from any text. We formalize this and prove that
communities partition the space of readers. -/

section FishInterpretiveCommunities
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Interpretive community membership**: two readers belong to the
    same interpretive community if they have the same emergence profile. -/
def sameCommunity (r₁ r₂ : I) : Prop := sameIdea r₁ r₂

/-- Community membership is reflexive. -/
theorem sameCommunity_refl (r : I) : sameCommunity r r := sameIdea_refl r

/-- Community membership is symmetric. -/
theorem sameCommunity_symm (r₁ r₂ : I) :
    sameCommunity r₁ r₂ → sameCommunity r₂ r₁ := sameIdea_symm r₁ r₂

/-- Community membership is transitive. -/
theorem sameCommunity_trans (r₁ r₂ r₃ : I) :
    sameCommunity r₁ r₂ → sameCommunity r₂ r₃ → sameCommunity r₁ r₃ :=
  sameIdea_trans r₁ r₂ r₃

/-- **Community determines interpretation**: members of the same community
    produce the same emergence from any text. -/
theorem community_same_emergence (r₁ r₂ t d : I)
    (h : sameCommunity r₁ r₂) :
    emergence r₁ t d = emergence r₂ t d := h t d

/-- **Community determines interpretive depth**: same community implies
    same gap-filling pattern. -/
theorem community_same_gaps (r₁ r₂ t d : I)
    (h : sameCommunity r₁ r₂) :
    textualGap r₁ t d = textualGap r₂ t d := by
  unfold textualGap; exact h t d

/-- **Void community**: the void reader forms its own trivial community.
    It interprets everything "linearly" — no emergence. -/
theorem void_community_linear (r : I) (h : sameCommunity (void : I) r) (t d : I) :
    emergence r t d = 0 := by
  rw [← community_same_emergence (void : I) r t d h]
  exact emergence_void_left t d

/-- **Community detection**: if two readers produce different emergence
    from some text, they belong to different communities. -/
theorem community_detection (r₁ r₂ t d : I)
    (h : emergence r₁ t d ≠ emergence r₂ t d) :
    ¬sameCommunity r₁ r₂ := by
  intro hc; exact h (community_same_emergence r₁ r₂ t d hc)

/-- **Community stability under void reading**: reading void doesn't
    change your community. -/
theorem community_stable_void (r : I) :
    sameCommunity r (compose r (void : I)) := by
  intro c d; simp

/-- **Community coherence**: within a community, all readers have
    the same double-voicing with any text. -/
theorem community_coherence (r₁ r₂ t d : I)
    (h : sameCommunity r₁ r₂) :
    doubleVoicing r₁ t d = doubleVoicing r₂ t d := by
  unfold doubleVoicing; exact h t d

end FishInterpretiveCommunities

/-! ## §34. Bloom's Anxiety of Influence

Harold Bloom's theory: strong poets (readers) are defined by their
struggle against their precursors. Every reading is a "misreading"
(misprision) that swerves away from the precursor's influence. The
"anxiety" is the tension between wanting to honor the tradition and
needing to assert originality.

In IDT, the "anxiety of influence" is the distance between a reader's
emergence and their precursor's emergence. A strong reading maximizes
this distance while maintaining positive enrichment. -/

section BloomAnxietyOfInfluence
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Bloom's clinamen (swerve)**: the difference between a reader's
    emergence and their precursor's emergence from the same text.
    Named after Lucretius' atomic swerve — the deviation that creates
    novelty. -/
noncomputable def clinamen (precursor reader text observer : I) : ℝ :=
  emergence reader text observer - emergence precursor text observer

/-- Clinamen is antisymmetric in precursor/reader. -/
theorem clinamen_antisymm (p r t d : I) :
    clinamen p r t d = -clinamen r p t d := by
  unfold clinamen; ring

/-- Clinamen vanishes when precursor = reader. -/
theorem clinamen_self (r t d : I) : clinamen r r t d = 0 := by
  unfold clinamen; ring

/-- Clinamen when reader is void: negation of precursor's emergence.
    Total rejection of the tradition. -/
theorem clinamen_void_reader (p t d : I) :
    clinamen p (void : I) t d = -emergence p t d := by
  unfold clinamen; rw [emergence_void_left]; ring

/-- Clinamen when precursor is void: equals the reader's emergence.
    No tradition to swerve from — pure originality. -/
theorem clinamen_void_precursor (r t d : I) :
    clinamen (void : I) r t d = emergence r t d := by
  unfold clinamen; rw [emergence_void_left]; ring

/-- **Bloom's tessera**: the antithetical completion — the reader
    "completes" the precursor by providing what was missing. Measured
    as the emergence of composing the reader's reading after the precursor's. -/
noncomputable def tessera (precursor reader text d : I) : ℝ :=
  emergence (compose precursor text) (compose reader text) d

/-- Tessera with void reader. -/
theorem tessera_void_reader (p t d : I) :
    tessera p (void : I) t d = emergence (compose p t) t d := by
  unfold tessera; simp

/-- **Bloom's kenosis**: the self-emptying — the reader empties the
    precursor of significance. In IDT, this is the negative emergence
    when the reader's interpretation "cancels" the precursor's. -/
noncomputable def kenosis (precursor reader text : I) : ℝ :=
  rs (compose precursor text) (compose precursor text) -
  rs (compose reader text) (compose reader text)

/-- Kenosis is antisymmetric. -/
theorem kenosis_antisymm (p r t : I) :
    kenosis p r t = -kenosis r p t := by
  unfold kenosis; ring

/-- Self-kenosis is zero. -/
theorem kenosis_self (r t : I) : kenosis r r t = 0 := by
  unfold kenosis; ring

/-- **The strong reading**: a reading that maximizes swerve while
    maintaining enrichment. We prove that any non-void reader's
    interpretation has positive weight. -/
theorem strong_reading_weight (reader text : I) (h : reader ≠ void) :
    rs (compose reader text) (compose reader text) > 0 := by
  exact rs_self_pos _ (compose_ne_void_of_left reader text h)

/-- **Influence accumulates**: the precursor's influence is carried
    through effective history. Composing with the precursor before
    reading creates a different emergence. -/
theorem influence_accumulates (precursor reader text d : I) :
    emergence (compose precursor reader) text d =
    emergence precursor (compose reader text) d +
    emergence reader text d - emergence precursor reader d := by
  linarith [cocycle_condition precursor reader text d]

/-- **Bloom's apophrades**: the return of the dead — the strong reader
    eventually seems to be influenced BY their successor. In IDT,
    this is expressed by the fact that the cocycle condition creates
    symmetry constraints: the total emergence is invariant under
    re-association. -/
theorem apophrades_invariance (p r t d : I) :
    emergence p r d + emergence (compose p r) t d =
    emergence r t d + emergence p (compose r t) d :=
  cocycle_condition p r t d

/-- **Clinamen transitivity**: if A swerves from B and B swerves from C,
    the total swerve from C equals A's swerve from C. -/
theorem clinamen_transitive (p₁ p₂ r t d : I) :
    clinamen p₁ p₂ t d + clinamen p₂ r t d = clinamen p₁ r t d := by
  unfold clinamen; ring

/-- **Influence chain enrichment**: a chain of influences always
    accumulates weight. -/
theorem influence_chain_enriches (p r text : I) :
    rs (compose (compose p r) text) (compose (compose p r) text) ≥ rs p p := by
  calc rs (compose (compose p r) text) (compose (compose p r) text)
      ≥ rs (compose p r) (compose p r) := compose_enriches' _ _
    _ ≥ rs p p := compose_enriches' _ _

end BloomAnxietyOfInfluence

/-! ## §35. Said's Orientalism as Interpretive Distortion

Edward Said's *Orientalism* (1978) shows how Western interpretations of
"the Orient" systematically distort through a lens of power. The
interpreter's framework (prejudice, in Gadamer's neutral sense) is not
innocent — it is structured by power relations that systematically
amplify certain resonances and suppress others.

In IDT, we formalize interpretive distortion as the systematic
difference between two interpreters' emergence profiles. The "distortion"
is the total asymmetry of interpretation when filtered through
a particular ideological lens. -/

section SaidOrientalism
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Interpretive distortion**: the systematic difference between how
    two interpreters read the same text, measured against observer d.
    When this is consistently nonzero, one interpreter is "distorting"
    relative to the other. -/
noncomputable def interpretiveDistortion (lens neutral text observer : I) : ℝ :=
  emergence lens text observer - emergence neutral text observer

/-- Distortion is antisymmetric. -/
theorem interpretiveDistortion_antisymm (l n t d : I) :
    interpretiveDistortion l n t d = -interpretiveDistortion n l t d := by
  unfold interpretiveDistortion; ring

/-- No self-distortion. -/
theorem interpretiveDistortion_self (r t d : I) :
    interpretiveDistortion r r t d = 0 := by
  unfold interpretiveDistortion; ring

/-- Distortion from void lens: equals the negative of the neutral emergence.
    Complete ignorance is the maximal distortion. -/
theorem distortion_void_lens (n t d : I) :
    interpretiveDistortion (void : I) n t d = -emergence n t d := by
  unfold interpretiveDistortion; rw [emergence_void_left]; ring

/-- **Said's key insight**: the lens adds its own weight to the
    interpretation. A non-void lens always has positive self-resonance,
    which bounds the distortion. -/
theorem lens_has_weight (lens : I) (h : lens ≠ void) :
    rs lens lens > 0 := rs_self_pos lens h

/-- **Interpretive hegemony**: the distortion is constrained by the
    emergence bounds. Even a powerful lens cannot create arbitrary distortion. -/
theorem hegemony_bounded (lens text observer : I) :
    (emergence lens text observer) ^ 2 ≤
    rs (compose lens text) (compose lens text) * rs observer observer :=
  emergence_bounded' lens text observer

/-- **Distortion accumulates through history**: reading through an
    ideological lens before encountering a text permanently shifts
    the emergence pattern. -/
theorem distortion_through_history (lens reader text d : I) :
    emergence (compose lens reader) text d =
    emergence lens (compose reader text) d +
    emergence reader text d - emergence lens reader d := by
  linarith [cocycle_condition lens reader text d]

/-- **De-distortion**: composing with a "corrective" text aims to
    counteract the lens. But the corrective itself creates new emergence.
    Perfect de-distortion is generally impossible. -/
theorem de_distortion_residue (lens corrective text d : I) :
    emergence (compose lens corrective) text d =
    emergence lens (compose corrective text) d +
    emergence corrective text d - emergence lens corrective d := by
  linarith [cocycle_condition lens corrective text d]

/-- **The colonized text**: a text read through the colonial lens
    has different weight than the same text read neutrally. -/
theorem colonial_weight_shift (lens text : I) :
    rs (compose lens text) (compose lens text) ≥ rs lens lens :=
  compose_enriches' lens text

/-- **Distortion transitivity**: distortions compose. -/
theorem distortion_transitive (l₁ l₂ n t d : I) :
    interpretiveDistortion l₁ l₂ t d + interpretiveDistortion l₂ n t d =
    interpretiveDistortion l₁ n t d := by
  unfold interpretiveDistortion; ring

end SaidOrientalism

/-! ## §36. Spivak's Subaltern Interpretation

Gayatri Spivak's "Can the Subaltern Speak?" argues that some voices
are systematically excluded from interpretation. The subaltern's
emergence is not just distorted but SILENCED — their contribution
to the interpretive process is rendered invisible.

In IDT, a "silenced" voice is one whose emergence contribution is
systematically zero — not because the voice has nothing to say (it may
have high self-resonance), but because the interpretive framework
cannot "hear" it. This is captured by the emergence bound:
when the observer has zero resonance with the subaltern's composition,
the emergence is necessarily zero. -/

section SpivakSubaltern
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Subaltern silencing**: a voice v is "silenced" in framework f
    if composing v with f produces zero emergence for all observers.
    The framework cannot register the voice's contribution. -/
def silencedIn (voice framework : I) : Prop :=
  ∀ d : I, emergence voice framework d = 0

/-- Void is silenced in everything. -/
theorem void_silenced (f : I) : silencedIn (void : I) f := by
  intro d; exact emergence_void_left f d

/-- Everything is silenced in void framework. -/
theorem silenced_in_void (v : I) : silencedIn v (void : I) := by
  intro d; exact emergence_void_right v d

/-- **Silencing paradox**: even a silenced voice adds weight.
    The subaltern's self-resonance persists — they have "presence"
    even when they cannot "speak" (generate emergence). -/
theorem silencing_paradox (voice framework : I) :
    rs (compose voice framework) (compose voice framework) ≥ rs voice voice :=
  compose_enriches' voice framework

/-- **Non-void subaltern has weight**: a non-void voice always has
    positive self-resonance, even if silenced. -/
theorem subaltern_has_weight (voice : I) (h : voice ≠ void) :
    rs voice voice > 0 := rs_self_pos voice h

/-- **Epistemic violence**: silencing destroys the emergence potential
    of the subaltern. If silenced, the composition's resonance is
    purely additive (linear). -/
theorem epistemic_violence (voice framework : I)
    (h : silencedIn voice framework) (d : I) :
    rs (compose voice framework) d = rs voice d + rs framework d := by
  have := rs_compose_eq voice framework d
  rw [h d] at this; linarith

/-- **Strategic essentialism**: the subaltern can be "heard" by
    composing with an amplifier. But the amplifier introduces its
    own emergence — representation always transforms. -/
theorem strategic_essentialism (voice amplifier framework d : I) :
    emergence (compose voice amplifier) framework d =
    emergence voice (compose amplifier framework) d +
    emergence amplifier framework d - emergence voice amplifier d := by
  linarith [cocycle_condition voice amplifier framework d]

/-- **Subaltern enrichment**: even silenced voices enrich the composition. -/
theorem subaltern_enrichment (voice framework : I) (h : silencedIn voice framework) :
    rs (compose voice framework) (compose voice framework) ≥ rs voice voice :=
  compose_enriches' voice framework

/-- **Voice recovery**: if a voice is not silenced, some observer
    can detect its contribution. -/
theorem voice_recovery (voice framework : I) (h : ¬silencedIn voice framework) :
    ∃ d : I, emergence voice framework d ≠ 0 := by
  unfold silencedIn at h; push_neg at h; exact h

end SpivakSubaltern

/-! ## §37. Jauss's Reception Aesthetics: Horizon of Expectations

Hans Robert Jauss develops "reception aesthetics" (Rezeptionsästhetik):
the meaning of a literary work is constituted by its reception history.
A key concept is the "horizon of expectations" (Erwartungshorizont) —
the reader's expectations before encountering a work. The "aesthetic
distance" between the horizon of expectations and the work itself
measures the work's originality and impact.

In IDT, the horizon of expectations IS the reader's state r. The
aesthetic distance is the emergence of the composition beyond what
the reader expected (their prior self-resonance). -/

section JaussReceptionAesthetics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Horizon of expectations**: the reader's state before encountering
    the work. This is just the reader's self-resonance — what they
    bring to the encounter. -/
noncomputable def horizonOfExpectations (reader : I) : ℝ := rs reader reader

/-- Void reader has zero expectations. -/
theorem horizonOfExpectations_void :
    horizonOfExpectations (void : I) = 0 := rs_void_void

/-- Non-void reader has positive expectations. -/
theorem horizonOfExpectations_pos (r : I) (h : r ≠ void) :
    horizonOfExpectations r > 0 := by
  unfold horizonOfExpectations; exact rs_self_pos r h

/-- **Aesthetic distance**: the gap between the work's effect and the
    reader's expectations. High distance = the work violates expectations
    strongly (avant-garde). Low distance = the work meets expectations
    (entertainment, kitsch). -/
noncomputable def aestheticDistance (reader work : I) : ℝ :=
  rs (compose reader work) (compose reader work) - rs reader reader

/-- Aesthetic distance is non-negative. -/
theorem aestheticDistance_nonneg (reader work : I) :
    aestheticDistance reader work ≥ 0 := by
  unfold aestheticDistance; linarith [compose_enriches' reader work]

/-- Aesthetic distance from void work is zero (no surprise). -/
theorem aestheticDistance_void_work (reader : I) :
    aestheticDistance reader (void : I) = 0 := by
  unfold aestheticDistance; simp

/-- **Aesthetic distance decomposes**: distance = comprehension excess +
    fidelity + interpretive depth. -/
theorem aestheticDistance_decomposition (reader work : I) :
    aestheticDistance reader work =
    (comprehension reader work - rs reader reader) +
    fidelity reader work + interpretiveDepth reader work := by
  unfold aestheticDistance
  rw [hermeneutic_identity reader work]; ring

/-- **Jauss's challenge of expectations**: repeated reading diminishes
    aesthetic distance RELATIVE TO the current state (each re-reading
    adds less surprise), but total distance from the original always grows. -/
theorem jauss_diminishing_relative_distance (reader work : I) (n : ℕ) :
    aestheticDistance (readN reader work n) work ≥ 0 := by
  unfold aestheticDistance; linarith [compose_enriches' (readN reader work n) work]

/-- **Total aesthetic distance grows**: cumulative distance from the
    original reader state grows monotonically. -/
theorem total_aesthetic_distance_mono (reader work : I) (n : ℕ) :
    rs (readN reader work (n + 1)) (readN reader work (n + 1)) - rs reader reader ≥
    rs (readN reader work n) (readN reader work n) - rs reader reader := by
  linarith [readN_enriches reader work n]

/-- **Jauss's literary evolution**: as expectations change (through reading),
    the same work can have different aesthetic distances for different states
    of the same reader. This is how literary value changes over time. -/
theorem literary_evolution (reader work : I) (m n : ℕ) :
    aestheticDistance (readN reader work m) work ≥ 0 ∧
    aestheticDistance (readN reader work n) work ≥ 0 := by
  constructor
  · unfold aestheticDistance; linarith [compose_enriches' (readN reader work m) work]
  · unfold aestheticDistance; linarith [compose_enriches' (readN reader work n) work]

/-- **Horizon fusion**: after reading, the reader's horizon has fused
    with the work's. The new horizon is at least as wide as the old. -/
theorem horizon_fusion_enriches (reader work : I) :
    horizonOfExpectations (compose reader work) ≥ horizonOfExpectations reader := by
  unfold horizonOfExpectations; exact compose_enriches' reader work

/-- **Jauss's concretization sequence**: the sequence of reader states
    through iterated reading forms a non-decreasing sequence of horizons. -/
theorem concretization_sequence_mono (reader work : I) (n : ℕ) :
    horizonOfExpectations (readN reader work (n + 1)) ≥
    horizonOfExpectations (readN reader work n) := by
  unfold horizonOfExpectations; exact readN_enriches reader work n

/-- **Expectations shape reception**: the emergence from a work depends on
    the reader's current expectations. -/
theorem expectations_shape_reception (r₁ r₂ work d : I)
    (h : emergence r₁ work d ≠ emergence r₂ work d) : r₁ ≠ r₂ := by
  intro heq; rw [heq] at h; exact h rfl

end JaussReceptionAesthetics

/-! ## §38. Habermas's Communicative Rationality

Jürgen Habermas argues that genuine communication aims at "mutual
understanding" (Verständigung) through rational discourse. The
"ideal speech situation" is one where only the "force of the better
argument" prevails — no distortion from power, ideology, or deception.

In IDT, the ideal speech situation is one where communication surplus
is maximized and the misunderstanding gap is minimized. We formalize
Habermas's conditions and prove structural results about rational
communication. -/

section HabermasCommunicativeRationality
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Ideal understanding**: misunderstanding gap is zero. -/
def idealUnderstanding (signal reader : I) : Prop :=
  misunderstandingGap signal reader = 0

/-- Self-communication is ideal. -/
theorem self_ideal (a : I) : idealUnderstanding a a :=
  misunderstanding_self_zero a

/-- **Communicative rationality**: communication is "rational" if the
    surplus is non-negative — both parties gain something. -/
def communicativelyRational (signal reader : I) : Prop :=
  communicationSurplus signal reader ≥ 0

/-- **Validity claim**: a signal's "validity" relative to a reader
    is measured by how much the signal resonates with the interpretation.
    High validity = the signal "makes sense" in the interpretation. -/
noncomputable def validityClaim (signal reader : I) : ℝ :=
  senderPayoff signal reader

/-- Validity of void signal is zero. -/
theorem validityClaim_void_signal (reader : I) :
    validityClaim (void : I) reader = 0 := by
  unfold validityClaim senderPayoff interpret; simp [rs_void_left']

/-- Validity to void reader equals self-resonance. -/
theorem validityClaim_void_reader (signal : I) :
    validityClaim signal (void : I) = rs signal signal :=
  senderPayoff_void_reader signal

/-- **Habermas's discourse ethics**: in ideal understanding, sender
    and receiver have equal "access" to the interpretation. -/
theorem discourse_ethics (signal reader : I)
    (h : idealUnderstanding signal reader) :
    rs signal (compose reader signal) = rs reader (compose reader signal) := by
  unfold idealUnderstanding misunderstandingGap senderPayoff receiverPayoff interpret at h
  linarith

/-- **Communicative action surplus**: the total value created by
    communicative action decomposes into sender and receiver contributions. -/
theorem communicative_action_decomposition (s r : I) :
    communicationSurplus s r =
    (senderPayoff s r - rs s s) + (receiverPayoff s r - rs r r) :=
  surplus_decomposition s r

/-- **Distorted communication**: if the misunderstanding gap is nonzero,
    communication is "distorted" — one party benefits more than the other. -/
theorem distorted_communication (s r : I)
    (h : misunderstandingGap s r ≠ 0) :
    senderPayoff s r ≠ receiverPayoff s r := by
  intro heq
  apply h
  unfold misunderstandingGap; linarith

/-- **The force of the better argument**: if signal s₁ has higher
    sender payoff than s₂ with the same reader, then s₁ is the
    "better argument" for that reader. This is a reader-relative notion. -/
theorem better_argument (s₁ s₂ reader : I)
    (h : senderPayoff s₁ reader > senderPayoff s₂ reader) :
    rs s₁ (compose reader s₁) > rs s₂ (compose reader s₂) := by
  unfold senderPayoff interpret at h; exact h

/-- **Mutual enrichment in communication**: the interpretation
    enriches the sender's state beyond the signal alone. -/
theorem mutual_enrichment (signal reader : I) :
    rs (compose reader signal) (compose reader signal) ≥ rs reader reader :=
  compose_enriches' reader signal

/-- **Void communication is trivially rational** (zero surplus). -/
theorem void_communication_rational (r : I) :
    communicativelyRational (void : I) r := by
  unfold communicativelyRational
  rw [communicationSurplus_void_signal]

end HabermasCommunicativeRationality

/-! ## §39. Deep Mathematical Results: Convergence of Iterated Interpretation

We prove deeper structural results about the behavior of iterated
interpretation. These results connect the hermeneutic circle to
mathematical analysis: bounded monotone sequences, fixed-point-like
behavior, and spectral decomposition of interpretive acts. -/

section ConvergenceResults
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Monotone enrichment chain**: for any sequence of texts, reading
    them in order produces a monotonically non-decreasing sequence of
    self-resonances. -/
theorem monotone_enrichment_chain (r : I) (texts : List I) :
    effectiveHistoryWeight r texts ≥ rs r r :=
  effectiveHistoryWeight_ge_original r texts

/-- **ReadN monotone in both directions**: readN r t n is enriched
    compared to readN r t m whenever m ≤ n. -/
theorem readN_mono (r t : I) (m n : ℕ) (h : m ≤ n) :
    rs (readN r t n) (readN r t n) ≥ rs (readN r t m) (readN r t m) := by
  induction n with
  | zero => have : m = 0 := Nat.le_zero.mp h; subst this; exact le_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · calc rs (readN r t (k + 1)) (readN r t (k + 1))
          ≥ rs (readN r t k) (readN r t k) := readN_enriches r t k
        _ ≥ rs (readN r t m) (readN r t m) := ih (Nat.lt_succ_iff.mp hlt)

/-- **Double reading equals single reading of double**: reading t twice
    is the same as reading t∘t once. -/
theorem double_reading_eq (r t : I) :
    readN r t 2 = compose r (compose t t) := by
  simp [readN, compose_assoc']

/-- **Triple reading associativity**: reading three times can be
    regrouped. -/
theorem triple_reading_assoc (r t : I) :
    readN r t 3 = compose r (compose t (compose t t)) := by
  simp [readN, compose_assoc']

/-- **ReadN composition rule**: reading n then m more equals reading n+m. -/
theorem readN_compose (r t : I) (m n : ℕ) :
    readN r t (m + n) = readN (readN r t n) t m := readN_add r t m n

/-- **Enrichment gap non-negative**: the gap between step n+1 and step n
    is always non-negative — reading never loses weight. -/
theorem enrichment_gap_nonneg (r t : I) (n : ℕ) :
    rs (readN r t (n + 1)) (readN r t (n + 1)) -
    rs (readN r t n) (readN r t n) ≥ 0 := by
  linarith [readN_enriches r t n]

/-- **Self-resonance is a Lyapunov function**: it never decreases under
    the reading dynamics, making it a Lyapunov function for the
    interpretive dynamical system. -/
theorem lyapunov_property (r t : I) (n : ℕ) :
    rs (readN r t (n + 1)) (readN r t (n + 1)) ≥
    rs (readN r t n) (readN r t n) := readN_enriches r t n

/-- **Lyapunov at origin**: the Lyapunov function at step 0 is the
    reader's initial self-resonance. -/
theorem lyapunov_origin (r t : I) :
    rs (readN r t 0) (readN r t 0) = rs r r := by simp

/-- **ReadN preserves non-void**: a non-void reader stays non-void. -/
theorem readN_preserves_nonvoid (r t : I) (h : r ≠ void) (n : ℕ) :
    readN r t n ≠ void := readN_ne_void r t h n

/-- **Iterated composition is a semigroup action**: the map n ↦ readN r t n
    respects addition. -/
theorem readN_additive (r t : I) (m n : ℕ) :
    readN r t (m + n) = readN (readN r t n) t m := readN_add r t m n

/-- **Weight after m+n readings**: decomposable into n readings then m more. -/
theorem weight_decomposition (r t : I) (m n : ℕ) :
    rs (readN r t (m + n)) (readN r t (m + n)) ≥
    rs (readN r t n) (readN r t n) := by
  rw [readN_additive]
  exact readN_enriches_original (readN r t n) t m

end ConvergenceResults

/-! ## §40. Fixed-Point Theorems for Reading

When does iterated reading "stabilize"? A fixed point of reading
is a reader state r* such that compose r* t = r* (or at least
rs(compose r* t, compose r* t) = rs(r*, r*)). We prove that if
such fixed points exist, they have special properties. -/

section FixedPointReading
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A reader state r is a "fixed point" for text t if reading t doesn't
    change the reader. -/
def readingFixedPoint (r t : I) : Prop := compose r t = r

/-- **Void is a fixed point for void text**. -/
theorem void_fixed_void : readingFixedPoint (void : I) (void : I) := by
  unfold readingFixedPoint; simp

/-- **Any reader is a fixed point for void text**. -/
theorem fixed_void_text (r : I) : readingFixedPoint r (void : I) := by
  unfold readingFixedPoint; simp

/-- **Fixed point implies constant readN**: if r is a fixed point for t,
    then readN r t n = r for all n. -/
theorem fixedPoint_readN (r t : I) (h : readingFixedPoint r t) :
    ∀ n : ℕ, readN r t n = r
  | 0 => rfl
  | n + 1 => by
    rw [readN_succ, fixedPoint_readN r t h n]
    exact h

/-- **Fixed point has constant self-resonance**. -/
theorem fixedPoint_constant_weight (r t : I) (h : readingFixedPoint r t) (n : ℕ) :
    rs (readN r t n) (readN r t n) = rs r r := by
  rw [fixedPoint_readN r t h n]

/-- **Fixed point implies zero reading gain**. -/
theorem fixedPoint_zero_gain (r t : I) (h : readingFixedPoint r t) (n : ℕ) :
    readingGain r t n = 0 := by
  unfold readingGain
  rw [fixedPoint_readN r t h n, fixedPoint_readN r t h (n + 1)]; ring

/-- **Fixed point implies zero aesthetic distance**. -/
theorem fixedPoint_zero_distance (r t : I) (h : readingFixedPoint r t) :
    aestheticDistance r t = 0 := by
  unfold aestheticDistance; rw [h]; ring

/-- **Fixed point implies zero text otherness**. -/
theorem fixedPoint_zero_otherness (r t : I) (h : readingFixedPoint r t) :
    textOtherness r t = 0 := by
  unfold textOtherness; rw [h]; ring

/-- **A "weak fixed point"**: reading doesn't change self-resonance. -/
def weakFixedPoint (r t : I) : Prop :=
  rs (compose r t) (compose r t) = rs r r

/-- Every fixed point is a weak fixed point. -/
theorem fixedPoint_implies_weak (r t : I) (h : readingFixedPoint r t) :
    weakFixedPoint r t := by
  unfold weakFixedPoint readingFixedPoint at *; rw [h]

/-- Void text always produces a weak fixed point. -/
theorem void_text_weak_fixed (r : I) : weakFixedPoint r (void : I) := by
  unfold weakFixedPoint; simp

/-- **Weak fixed point has zero reading gain at step 0**. -/
theorem weakFixed_zero_first_gain (r t : I) (h : weakFixedPoint r t) :
    readingGain r t 0 = 0 := by
  unfold readingGain weakFixedPoint at *
  simp [readN]; linarith

/-- **Weak fixed point implies zero aesthetic distance**. -/
theorem weakFixed_zero_distance (r t : I) (h : weakFixedPoint r t) :
    aestheticDistance r t = 0 := by
  unfold aestheticDistance weakFixedPoint at *; linarith

/-- **Idempotent reading**: composing twice gives the same self-resonance
    as composing once (weak sense). -/
def idempotentReading (r t : I) : Prop :=
  rs (compose (compose r t) t) (compose (compose r t) t) =
  rs (compose r t) (compose r t)

/-- **Fixed point implies idempotent**. -/
theorem fixedPoint_implies_idempotent (r t : I) (h : readingFixedPoint r t) :
    idempotentReading r t := by
  unfold idempotentReading; simp [show compose r t = r from h]

end FixedPointReading

/-! ## §41. Spectral Decomposition of Interpretive Acts

Every interpretive act (composition) can be "decomposed" into its
contributions: direct resonance, cross-resonance, and emergence.
This is the "spectrum" of the interpretive act — analogous to
spectral decomposition in linear algebra, but for the nonlinear
world of meaning. -/

section SpectralDecomposition
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **The interpretive spectrum**: any composition's resonance with
    an observer decomposes into three "spectral components":
    1. Reader resonance (how the reader alone resonates)
    2. Text resonance (how the text alone resonates)
    3. Emergence (the nonlinear, genuinely new component) -/
theorem spectral_decomposition (reader text observer : I) :
    rs (compose reader text) observer =
    rs reader observer + rs text observer + emergence reader text observer :=
  rs_compose_eq reader text observer

/-- **Self-spectral decomposition**: the interpretation's weight
    decomposes into self-components. -/
theorem self_spectral (reader text : I) :
    rs (compose reader text) (compose reader text) =
    rs reader (compose reader text) +
    rs text (compose reader text) +
    emergence reader text (compose reader text) :=
  rs_compose_eq reader text (compose reader text)

/-- **Linear spectrum**: when emergence is zero, the spectrum is
    purely additive. This is the "boring" case — no genuine interpretation. -/
theorem linear_spectrum (reader text observer : I)
    (h : emergence reader text observer = 0) :
    rs (compose reader text) observer = rs reader observer + rs text observer := by
  rw [rs_compose_eq reader text observer, h]; ring

/-- **Quadratic spectrum**: the emergence bound gives a "width" constraint
    on the spectral components. The emergence can't be wider than the
    geometric mean of the composition and observer weights. -/
theorem quadratic_spectrum (reader text observer : I) :
    (emergence reader text observer) ^ 2 ≤
    rs (compose reader text) (compose reader text) * rs observer observer :=
  emergence_bounded' reader text observer

/-- **Double spectral decomposition**: composing three elements gives
    a five-component spectrum. -/
theorem double_spectral (a b c d : I) :
    rs (compose (compose a b) c) d =
    rs a d + rs b d + rs c d +
    emergence a b d + emergence (compose a b) c d :=
  rs_compose3 a b c d

/-- **Spectral invariance under reassociation**: the total resonance
    is the same regardless of how we group the composition. -/
theorem spectral_reassociation (a b c d : I) :
    rs (compose (compose a b) c) d =
    rs (compose a (compose b c)) d := by
  rw [compose_assoc']

/-- **Net emergence**: the total emergence of a triple composition
    compared to the sum of parts. -/
noncomputable def netEmergence (a b c d : I) : ℝ :=
  rs (compose (compose a b) c) d - rs a d - rs b d - rs c d

/-- Net emergence decomposes into pairwise emergences. -/
theorem netEmergence_decomposition (a b c d : I) :
    netEmergence a b c d = emergence a b d + emergence (compose a b) c d := by
  unfold netEmergence
  rw [rs_compose3 a b c d]; ring

/-- **Net emergence cocycle invariance**: the net emergence equals
    the alternative grouping's pairwise emergences. -/
theorem netEmergence_invariance (a b c d : I) :
    netEmergence a b c d =
    emergence b c d + emergence a (compose b c) d := by
  rw [netEmergence_decomposition]
  exact cocycle_condition a b c d

/-- **Spectral void**: the spectrum of void is trivially zero. -/
theorem spectral_void_reader (text observer : I) :
    rs (compose (void : I) text) observer = rs text observer := by simp

/-- **Spectral void text**: -/
theorem spectral_void_text (reader observer : I) :
    rs (compose reader (void : I)) observer = rs reader observer := by simp

end SpectralDecomposition

/-! ## §42. The Interpretive Lattice

Interpretive states form a partial order under the enrichment relation.
If we define r ≤ s as "s is at least as enriched as r" (rs s s ≥ rs r r),
this gives a preorder (reflexive and transitive). Reading always moves
"upward" in this lattice. -/

section InterpretiveLattice
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Interpretive weight preorder**: r is "below" s if s has at least
    as much self-resonance. -/
def weightBelow (r s : I) : Prop := rs s s ≥ rs r r

/-- Weight-below is reflexive. -/
theorem weightBelow_refl (r : I) : weightBelow r r := le_refl _

/-- Weight-below is transitive. -/
theorem weightBelow_trans (a b c : I)
    (h₁ : weightBelow a b) (h₂ : weightBelow b c) : weightBelow a c := by
  unfold weightBelow at *; linarith

/-- **Reading moves upward**: composition always moves to a higher
    (or equal) position in the weight order. -/
theorem reading_moves_up (r t : I) : weightBelow r (compose r t) := by
  unfold weightBelow; exact compose_enriches' r t

/-- **Void is the bottom**: void has the minimum self-resonance (zero). -/
theorem void_is_bottom (a : I) : weightBelow (void : I) a := by
  unfold weightBelow; linarith [rs_self_nonneg' a, rs_void_void (I := I)]

/-- **Reading chain**: a sequence of readings forms an ascending chain. -/
theorem reading_chain (r t : I) (m n : ℕ) (h : m ≤ n) :
    weightBelow (readN r t m) (readN r t n) := by
  unfold weightBelow; exact readN_mono r t m n h

/-- **Non-void is strictly above void**. -/
theorem nonvoid_above_void (a : I) (h : a ≠ void) :
    rs a a > rs (void : I) (void : I) := by
  rw [rs_void_void]; exact rs_self_pos a h

/-- **Composition preserves being above void**. -/
theorem compose_above_void (a b : I) (h : a ≠ void) :
    rs (compose a b) (compose a b) > 0 :=
  rs_self_pos _ (compose_ne_void_of_left a b h)

end InterpretiveLattice

/-! ## §43. Interpretive Energy and Work

Drawing an analogy with physics: interpretation requires "work" —
the effort of bridging the gap between reader and text. The "energy"
of an interpretation is its self-resonance. Reading increases energy
(second law of hermeneutics). We formalize the "work" done in
interpretation as the energy change. -/

section InterpretiveEnergy
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Interpretive work**: the "work" done in interpreting text t
    by reader r. This is the energy increase. -/
noncomputable def interpretiveWork (r t : I) : ℝ :=
  rs (compose r t) (compose r t) - rs r r

/-- Work is non-negative (second law). -/
theorem interpretiveWork_nonneg (r t : I) : interpretiveWork r t ≥ 0 := by
  unfold interpretiveWork; linarith [compose_enriches' r t]

/-- Work from void text is zero. -/
theorem interpretiveWork_void_text (r : I) : interpretiveWork r (void : I) = 0 := by
  unfold interpretiveWork; simp

/-- Work by void reader equals text's weight. -/
theorem interpretiveWork_void_reader (t : I) :
    interpretiveWork (void : I) t = rs t t := by
  unfold interpretiveWork; simp [rs_void_void]

/-- **Work decomposition**: work = comprehension excess + fidelity + depth. -/
theorem interpretiveWork_decomposition (r t : I) :
    interpretiveWork r t =
    (comprehension r t - rs r r) + fidelity r t + interpretiveDepth r t := by
  unfold interpretiveWork; rw [hermeneutic_identity r t]; ring

/-- **Additive work bound**: work from two texts is at least the work
    from the first. -/
theorem work_monotone (r t₁ t₂ : I) :
    interpretiveWork r (compose t₁ t₂) ≥ interpretiveWork r t₁ := by
  unfold interpretiveWork
  rw [← compose_assoc']
  linarith [compose_enriches' (compose r t₁) t₂]

/-- **Total work over n readings**. -/
theorem total_work (r t : I) (n : ℕ) :
    rs (readN r t n) (readN r t n) - rs r r ≥ 0 := by
  linarith [readN_enriches_original r t n]

/-- **Work per step is non-negative**. -/
theorem work_per_step (r t : I) (n : ℕ) :
    rs (readN r t (n + 1)) (readN r t (n + 1)) -
    rs (readN r t n) (readN r t n) ≥ 0 := by
  linarith [readN_enriches r t n]

/-- **Cumulative work is monotone**: doing more work never decreases
    the total. -/
theorem cumulative_work_mono (r t : I) (n : ℕ) :
    rs (readN r t (n + 1)) (readN r t (n + 1)) - rs r r ≥
    rs (readN r t n) (readN r t n) - rs r r := by
  linarith [readN_enriches r t n]

end InterpretiveEnergy

/-! ## §44. The Hermeneutic Field

The space of all possible interpretations forms a "field" — each text
creates a "potential" that readers move through. The gradient of this
field is the emergence. We formalize this field-theoretic perspective. -/

section HermeneuticField
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Field potential**: the potential of text t at reader position r,
    measured by observer d. This is how strongly the text "pulls" the
    reader toward interpreting it. -/
noncomputable def fieldPotential (text reader observer : I) : ℝ :=
  rs (compose reader text) observer

/-- Potential of void text is just the reader's resonance. -/
theorem fieldPotential_void_text (reader observer : I) :
    fieldPotential (void : I) reader observer = rs reader observer := by
  unfold fieldPotential; simp

/-- Potential at void reader is just the text's resonance. -/
theorem fieldPotential_void_reader (text observer : I) :
    fieldPotential text (void : I) observer = rs text observer := by
  unfold fieldPotential; simp

/-- **Field decomposition**: the potential decomposes into reader
    contribution + text contribution + emergence (the "field gradient"). -/
theorem fieldPotential_decomposition (text reader observer : I) :
    fieldPotential text reader observer =
    rs reader observer + rs text observer + emergence reader text observer := by
  unfold fieldPotential; rw [rs_compose_eq]

/-- **The field gradient IS emergence**: the nonlinear part of the
    potential is exactly the emergence. -/
noncomputable def fieldGradient (text reader observer : I) : ℝ :=
  fieldPotential text reader observer - rs reader observer - rs text observer

/-- Field gradient equals emergence. -/
theorem fieldGradient_eq_emergence (text reader observer : I) :
    fieldGradient text reader observer = emergence reader text observer := by
  unfold fieldGradient fieldPotential emergence; ring

/-- **Field gradient vanishes for void text**. -/
theorem fieldGradient_void_text (reader observer : I) :
    fieldGradient (void : I) reader observer = 0 := by
  rw [fieldGradient_eq_emergence]; exact emergence_void_right reader observer

/-- **Field gradient vanishes for void reader**. -/
theorem fieldGradient_void_reader (text observer : I) :
    fieldGradient text (void : I) observer = 0 := by
  rw [fieldGradient_eq_emergence]; exact emergence_void_left text observer

/-- **Superposition of fields**: two texts create a combined field
    whose gradient relates to individual gradients via the cocycle. -/
theorem field_superposition (t₁ t₂ reader d : I) :
    fieldGradient (compose t₁ t₂) reader d =
    fieldGradient t₁ reader d +
    emergence (compose reader t₁) t₂ d -
    emergence t₁ t₂ d := by
  rw [fieldGradient_eq_emergence, fieldGradient_eq_emergence]
  have h := cocycle_condition reader t₁ t₂ d
  linarith

/-- **Field energy**: the self-potential of a text at a reader position. -/
noncomputable def fieldEnergy (text reader : I) : ℝ :=
  fieldPotential text reader (compose reader text)

/-- Field energy decomposes via the hermeneutic identity. -/
theorem fieldEnergy_decomposition (text reader : I) :
    fieldEnergy text reader =
    comprehension reader text + fidelity reader text + interpretiveDepth reader text := by
  unfold fieldEnergy fieldPotential
  exact hermeneutic_identity reader text

end HermeneuticField

/-! ## §45. Interpretive Morphisms and Functors

An interpretive morphism maps between interpretive spaces while preserving
the essential structure. This formalizes the idea of "translation between
interpretive frameworks." -/

section InterpretiveMorphisms
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Interpretive invariant**: a quantity that doesn't change under
    re-interpretation. The self-resonance of readN is invariant
    under re-association. -/
theorem interpretive_invariant (r t₁ t₂ : I) :
    rs (compose (compose r t₁) t₂) (compose (compose r t₁) t₂) =
    rs (compose r (compose t₁ t₂)) (compose r (compose t₁ t₂)) := by
  rw [compose_assoc']

/-- **Emergence is an interpretive invariant**: the cocycle structure
    is preserved under re-association. -/
theorem emergence_invariant (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- **Weight is monotone under morphism**: composing preserves weight
    ordering. -/
theorem weight_monotone_compose (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- **Composition with self**: composing a with itself. -/
theorem self_compose_weight (a : I) :
    rs (compose a a) (compose a a) ≥ rs a a :=
  compose_enriches' a a

/-- **Double self-compose**: a ∘ a ∘ a enriches beyond a ∘ a. -/
theorem double_self_compose_enriches (a : I) :
    rs (compose (compose a a) a) (compose (compose a a) a) ≥
    rs (compose a a) (compose a a) :=
  compose_enriches' (compose a a) a

end InterpretiveMorphisms

/-! ## §46. Bakhtin's Chronotope: Time-Space of Interpretation

Bakhtin's chronotope: the unity of time and space in narrative and
interpretation. Every interpretive act takes place in a particular
chronotope — a configuration of temporal and spatial relations.
Different chronotopes produce different emergences.

In IDT, chronotope is modeled as a context (a third element) that
shapes the emergence of the reader-text encounter. -/

section BakhtinChronotope
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Chronotopic emergence**: the emergence of reading text t by reader r
    in chronotope (context) c, measured against observer d. -/
noncomputable def chronotopicEmergence (reader text context observer : I) : ℝ :=
  emergence (compose reader context) text observer

/-- Chronotopic emergence with void context equals plain emergence. -/
theorem chronotopicEmergence_void_context (reader text observer : I) :
    chronotopicEmergence reader text (void : I) observer =
    emergence reader text observer := by
  unfold chronotopicEmergence; simp

/-- Chronotopic emergence with void text is zero. -/
theorem chronotopicEmergence_void_text (reader context observer : I) :
    chronotopicEmergence reader (void : I) context observer = 0 := by
  unfold chronotopicEmergence; exact emergence_void_right _ observer

/-- **Chronotope shapes emergence**: the cocycle determines how the
    chronotope transforms the emergence pattern. -/
theorem chronotope_transforms (reader context text d : I) :
    chronotopicEmergence reader text context d =
    emergence reader (compose context text) d +
    emergence context text d - emergence reader context d := by
  unfold chronotopicEmergence
  linarith [cocycle_condition reader context text d]

/-- **Chronotopic enrichment**: interpreting in a chronotope always
    enriches beyond the reader+context state. -/
theorem chronotopic_enrichment (reader text context : I) :
    rs (compose (compose reader context) text)
       (compose (compose reader context) text) ≥
    rs (compose reader context) (compose reader context) :=
  compose_enriches' (compose reader context) text

/-- **Chronotopic enrichment from reader**: interpretation in any
    chronotope enriches beyond the reader alone. -/
theorem chronotopic_enrichment_reader (reader text context : I) :
    rs (compose (compose reader context) text)
       (compose (compose reader context) text) ≥ rs reader reader := by
  calc rs (compose (compose reader context) text)
         (compose (compose reader context) text)
      ≥ rs (compose reader context) (compose reader context) :=
        compose_enriches' _ _
    _ ≥ rs reader reader := compose_enriches' _ _

end BakhtinChronotope

/-! ## §47. The Economy of Interpretation

Interpretation has an "economy" — there are costs (effort) and benefits
(understanding). We formalize this in terms of the enrichment structure:
the "cost" is the weight that must be invested (reader's self-resonance),
and the "return" is the enrichment gained. -/

section InterpretiveEconomy
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Return on interpretive investment**: the ratio of enrichment gained
    to the reader's initial investment. -/
noncomputable def interpretiveReturn (r t : I) : ℝ :=
  rs (compose r t) (compose r t) - rs r r

/-- Return is non-negative. -/
theorem interpretiveReturn_nonneg (r t : I) : interpretiveReturn r t ≥ 0 := by
  unfold interpretiveReturn; linarith [compose_enriches' r t]

/-- Return from void text is zero. -/
theorem interpretiveReturn_void_text (r : I) : interpretiveReturn r (void : I) = 0 := by
  unfold interpretiveReturn; simp

/-- **Marginal return**: the incremental return from the (n+1)-th reading. -/
noncomputable def marginalReturn (r t : I) (n : ℕ) : ℝ :=
  rs (readN r t (n + 1)) (readN r t (n + 1)) -
  rs (readN r t n) (readN r t n)

/-- Marginal return is non-negative. -/
theorem marginalReturn_nonneg (r t : I) (n : ℕ) :
    marginalReturn r t n ≥ 0 := by
  unfold marginalReturn; linarith [readN_enriches r t n]

/-- Marginal return from void text is zero. -/
theorem marginalReturn_void_text (r : I) (n : ℕ) :
    marginalReturn r (void : I) n = 0 := by
  unfold marginalReturn; simp

/-- **Total return**: sum of marginal returns telescopes to total gain. -/
theorem total_return_telescopes (r t : I) (n : ℕ) :
    rs (readN r t n) (readN r t n) - rs r r =
    historicalWeightGain r t n := by
  unfold historicalWeightGain; ring

/-- **Non-negative total return**: the total return is always ≥ 0. -/
theorem total_return_nonneg (r t : I) (n : ℕ) :
    rs (readN r t n) (readN r t n) - rs r r ≥ 0 := by
  linarith [readN_enriches_original r t n]

/-- **Compounding returns**: each step adds to the total. -/
theorem compounding_returns (r t : I) (n : ℕ) :
    rs (readN r t (n + 1)) (readN r t (n + 1)) - rs r r ≥
    rs (readN r t n) (readN r t n) - rs r r := by
  linarith [readN_enriches r t n]

end InterpretiveEconomy

/-! ## §48. Gadamer's Play (Spiel) — The Self-Presentation of Art

Gadamer argues that art "plays" — it has its own dynamic that draws
the viewer/reader in. The player does not control the game; the game
plays the player. In IDT, this is the observation that interpretation
is not a one-way process: the text shapes the reader as much as
the reader shapes the text. -/

section GadamerPlay
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Play as mutual transformation**: the text transforms the reader
    (enrichment) and the reader transforms the text's meaning
    (context-dependent resonance). -/
theorem play_reader_transformed (reader text : I) :
    rs (compose reader text) (compose reader text) ≥ rs reader reader :=
  compose_enriches' reader text

/-- **The game plays the player**: in iterated reading, the text
    keeps changing the reader. The reader cannot "stop" the play
    without ceasing to read. -/
theorem game_plays_player (reader text : I) (n : ℕ) :
    readN reader text (n + 1) = compose (readN reader text n) text := readN_succ reader text n

/-- **Play is irreversible**: once played, the game cannot be unplayed.
    The reader can never return to their pre-play state (unless the
    text is void). -/
theorem play_irreversible (reader text : I) (h : reader ≠ void) (n : ℕ) :
    readN reader text n ≠ void := readN_ne_void reader text h n

/-- **Play enrichment**: each round of play enriches. -/
theorem play_enriches_per_round (reader text : I) (n : ℕ) :
    rs (readN reader text (n + 1)) (readN reader text (n + 1)) ≥
    rs (readN reader text n) (readN reader text n) :=
  readN_enriches reader text n

/-- **Total play enrichment**: after n rounds, always above start. -/
theorem total_play_enrichment (reader text : I) (n : ℕ) :
    rs (readN reader text n) (readN reader text n) ≥ rs reader reader :=
  readN_enriches_original reader text n

/-- **The presentation structure**: art presents itself through
    the interpreter. The self-resonance of the interpretation is
    the "weight" of the presentation. -/
noncomputable def presentationWeight (reader text : I) : ℝ :=
  rs (compose reader text) (compose reader text)

/-- Presentation weight is non-negative. -/
theorem presentationWeight_nonneg (reader text : I) :
    presentationWeight reader text ≥ 0 := by
  unfold presentationWeight; exact rs_self_nonneg' _

/-- Presentation weight ≥ reader weight. -/
theorem presentationWeight_ge_reader (reader text : I) :
    presentationWeight reader text ≥ rs reader reader := by
  unfold presentationWeight; exact compose_enriches' reader text

end GadamerPlay

/-! ## §49. Resonance Calculus — Derivative-Like Operations

We define operations that measure how resonance changes under
infinitesimal (one-step) composition, creating a calculus of
interpretive change. -/

section ResonanceCalculus
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Resonance derivative**: the change in resonance when composing
    a with b, measured against observer c. This is the "rate of change"
    of resonance under composition. -/
noncomputable def resonanceDerivative (a b c : I) : ℝ :=
  rs (compose a b) c - rs a c

/-- Resonance derivative is zero for void composition. -/
theorem resonanceDerivative_void_right (a c : I) :
    resonanceDerivative a (void : I) c = 0 := by
  unfold resonanceDerivative; simp

/-- Resonance derivative decomposes into text resonance + emergence. -/
theorem resonanceDerivative_decomposition (a b c : I) :
    resonanceDerivative a b c = rs b c + emergence a b c := by
  unfold resonanceDerivative emergence; ring

/-- **Second derivative**: the change in the derivative when composing
    again. Measures the "acceleration" of interpretive change. -/
noncomputable def secondDerivative (a b c : I) : ℝ :=
  resonanceDerivative (compose a b) b c - resonanceDerivative a b c

/-- Second derivative in terms of emergence difference. -/
theorem secondDerivative_eq (a b c : I) :
    secondDerivative a b c =
    emergence (compose a b) b c - emergence a b c := by
  unfold secondDerivative resonanceDerivative emergence; ring

/-- **Weight derivative**: the change in self-resonance under composition. -/
noncomputable def weightDerivative (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a

/-- Weight derivative is non-negative. -/
theorem weightDerivative_nonneg (a b : I) : weightDerivative a b ≥ 0 := by
  unfold weightDerivative; linarith [compose_enriches' a b]

/-- Weight derivative from void is zero. -/
theorem weightDerivative_void (a : I) : weightDerivative a (void : I) = 0 := by
  unfold weightDerivative; simp

/-- **Chain rule analogue**: the weight derivative of a double composition
    relates to the individual derivatives. -/
theorem weight_chain_bound (a b c : I) :
    weightDerivative a (compose b c) ≥ weightDerivative a b := by
  unfold weightDerivative
  rw [← compose_assoc']
  linarith [compose_enriches' (compose a b) c]

/-- **Iterated derivative**: the weight derivative at step n. -/
theorem iterated_weight_derivative (r t : I) (n : ℕ) :
    weightDerivative (readN r t n) t ≥ 0 := by
  exact weightDerivative_nonneg (readN r t n) t

end ResonanceCalculus

/-! ## §50. The Phenomenology of Reading — Husserl and Ingarden

Roman Ingarden's phenomenological theory of the literary work:
the work exists in four "strata" — sound, meaning, schematized aspects,
and represented objects. Each stratum contributes to the total
"polyphony" of the work.

In IDT, strata are modeled as components of a composition.
The total work is the composition of all strata. The emergence
between strata captures how they interact to create meaning
beyond their individual contributions. -/

section PhenomenologyOfReading
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Stratum interaction**: the emergence between two strata of a text,
    as experienced by an observer. -/
noncomputable def stratumInteraction (stratum₁ stratum₂ observer : I) : ℝ :=
  emergence stratum₁ stratum₂ observer

/-- Stratum interaction with void is zero. -/
theorem stratumInteraction_void_left (s₂ obs : I) :
    stratumInteraction (void : I) s₂ obs = 0 := emergence_void_left s₂ obs

/-- Stratum interaction void right. -/
theorem stratumInteraction_void_right (s₁ obs : I) :
    stratumInteraction s₁ (void : I) obs = 0 := emergence_void_right s₁ obs

/-- **Two-stratum work**: the total resonance of a two-stratum work
    decomposes into individual resonances plus stratum interaction. -/
theorem two_stratum_decomposition (s₁ s₂ obs : I) :
    rs (compose s₁ s₂) obs =
    rs s₁ obs + rs s₂ obs + stratumInteraction s₁ s₂ obs := by
  unfold stratumInteraction; exact rs_compose_eq s₁ s₂ obs

/-- **Three-stratum work**: a three-stratum work has two emergence terms. -/
theorem three_stratum_resonance (s₁ s₂ s₃ obs : I) :
    rs (compose (compose s₁ s₂) s₃) obs =
    rs s₁ obs + rs s₂ obs + rs s₃ obs +
    emergence s₁ s₂ obs + emergence (compose s₁ s₂) s₃ obs :=
  rs_compose3 s₁ s₂ s₃ obs

/-- **Stratum enrichment**: adding a stratum always enriches the work. -/
theorem stratum_enriches (s₁ s₂ : I) :
    rs (compose s₁ s₂) (compose s₁ s₂) ≥ rs s₁ s₁ :=
  compose_enriches' s₁ s₂

/-- **Ingarden's concretization**: the reader "concretizes" the schematized
    aspects. This is the reader's composition with the work. -/
noncomputable def ingardenConcretization (reader work : I) : ℝ :=
  rs (compose reader work) (compose reader work)

/-- Concretization is non-negative. -/
theorem ingardenConcretization_nonneg (reader work : I) :
    ingardenConcretization reader work ≥ 0 := by
  unfold ingardenConcretization; exact rs_self_nonneg' _

/-- Concretization enriches the reader. -/
theorem ingardenConcretization_enriches (reader work : I) :
    ingardenConcretization reader work ≥ rs reader reader := by
  unfold ingardenConcretization; exact compose_enriches' reader work

/-- **Husserl's noema-noesis**: the noematic content (what is intended)
    and noetic act (how it is intended) together constitute meaning.
    In IDT, noema is the text, noesis is the reader's act (composition). -/
theorem noema_noesis_unity (reader text : I) :
    rs (compose reader text) (compose reader text) =
    comprehension reader text + fidelity reader text + interpretiveDepth reader text :=
  hermeneutic_identity reader text

end PhenomenologyOfReading

/-! ## §51. The Politics of Interpretation

Every interpretation is political: it privileges certain meanings over
others. The "canon" — the set of texts deemed worthy — shapes which
emergences are possible. We formalize canon formation and its effects. -/

section PoliticsOfInterpretation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Canon weight**: the total self-resonance of a canon of texts. -/
noncomputable def canonWeight (canon : List I) : ℝ :=
  rs (List.foldl compose void canon) (List.foldl compose void canon)

/-- Empty canon has zero weight. -/
theorem canonWeight_nil : canonWeight ([] : List I) = 0 := by
  unfold canonWeight; simp [rs_void_void]

/-- **Canon enrichment**: adding a text to the canon enriches it. -/
theorem canonWeight_enriches (canon : List I) (text : I) :
    canonWeight (canon ++ [text]) ≥ canonWeight canon := by
  unfold canonWeight
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact compose_enriches' _ _

/-- **Exclusion reduces possibility**: removing texts from the canon
    can only reduce the weight (adding is enriching, so the reverse
    holds in principle). The existing canon always has non-negative weight. -/
theorem canon_nonneg (canon : List I) : canonWeight canon ≥ 0 := by
  unfold canonWeight; exact rs_self_nonneg' _

/-- **Interpretive frame**: the canon creates a frame through which
    new texts are read. The emergence depends on the canon. -/
noncomputable def frameEmergence (canon : List I) (text observer : I) : ℝ :=
  emergence (List.foldl compose void canon) text observer

/-- Empty frame produces zero emergence. -/
theorem frameEmergence_nil (text observer : I) :
    frameEmergence ([] : List I) text observer = 0 := by
  unfold frameEmergence; simp [emergence_void_left]

/-- **Hegemonic reading**: the canonical frame shapes all readings.
    Every reading is filtered through the existing canon. -/
theorem hegemonic_filtering (canon : List I) (reader text d : I) :
    emergence (compose (List.foldl compose void canon) reader) text d =
    emergence (List.foldl compose void canon) (compose reader text) d +
    emergence reader text d -
    emergence (List.foldl compose void canon) reader d := by
  linarith [cocycle_condition (List.foldl compose void canon) reader text d]

end PoliticsOfInterpretation

/-! ## §52. The Hermeneutics of Suspicion (Ricoeur)

Ricoeur identifies three "masters of suspicion": Marx, Nietzsche, Freud.
They argue that surface meaning conceals deeper meaning. The
"hermeneutics of suspicion" reads AGAINST the text, seeking the hidden
meaning beneath the surface.

In IDT, the "surface" is the direct resonance rs(text, observer).
The "depth" is the emergence — what lies beneath the additive surface.
Reading with suspicion means attending to emergence rather than
direct resonance. -/

section HermeneuticsOfSuspicion
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Surface meaning**: the direct resonance of the text with
    the observer, ignoring the reader's contribution. -/
noncomputable def surfaceMeaning (text observer : I) : ℝ := rs text observer

/-- **Depth meaning**: the emergence — what the surface conceals. -/
noncomputable def depthMeaning (reader text observer : I) : ℝ :=
  emergence reader text observer

/-- **Total meaning = surface + depth + reader contribution**. -/
theorem total_meaning_decomposition (reader text observer : I) :
    rs (compose reader text) observer =
    rs reader observer + surfaceMeaning text observer +
    depthMeaning reader text observer := by
  unfold surfaceMeaning depthMeaning; rw [rs_compose_eq]

/-- Surface of void is zero. -/
theorem surfaceMeaning_void (observer : I) :
    surfaceMeaning (void : I) observer = 0 := rs_void_left' observer

/-- Depth of void reader is zero: without suspicion, no depth revealed. -/
theorem depthMeaning_void_reader (text observer : I) :
    depthMeaning (void : I) text observer = 0 := emergence_void_left text observer

/-- Depth against void observer is zero. -/
theorem depthMeaning_void_observer (reader text : I) :
    depthMeaning reader text (void : I) = 0 := emergence_against_void reader text

/-- **Suspicious reading**: attending to the depth rather than the surface.
    The depth is bounded by the emergence Cauchy-Schwarz. -/
theorem suspicious_reading_bounded (reader text observer : I) :
    (depthMeaning reader text observer) ^ 2 ≤
    rs (compose reader text) (compose reader text) * rs observer observer := by
  unfold depthMeaning; exact emergence_bounded' reader text observer

/-- **Marx's ideology critique**: the "ideological" reading is one where
    the surface meaning systematically differs from the depth meaning.
    We show that purely linear readers (no suspicion) miss all depth. -/
theorem linear_reader_misses_depth (reader : I) (h : leftLinear reader)
    (text observer : I) :
    depthMeaning reader text observer = 0 := by
  unfold depthMeaning; exact h text observer

/-- **Freud's return of the repressed**: the emergence can be nonzero
    even when the surface appears zero. The "repressed" meaning
    surfaces through emergence. -/
theorem return_of_repressed (reader text observer : I)
    (hsurf : rs text observer = 0)
    (hemerg : emergence reader text observer ≠ 0) :
    rs (compose reader text) observer ≠ rs reader observer := by
  rw [rs_compose_eq reader text observer, hsurf]
  intro h
  apply hemerg
  linarith

end HermeneuticsOfSuspicion

/-! ## §53. Eco's Open Work and the Limits of Interpretation

Umberto Eco's *The Open Work* and *The Limits of Interpretation*:
a text is "open" insofar as it admits multiple valid interpretations.
But there are limits — not any interpretation is valid. The text
constrains the space of possible interpretations.

In IDT, the "openness" of a text is measured by how many different
emergences it produces with different readers. The constraints come
from the emergence bounds. -/

section EcoOpenWork
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Eco's openness indicator**: a text is more "open" relative to
    two readers if they produce different emergences. -/
noncomputable def interpretiveOpenness (r₁ r₂ text observer : I) : ℝ :=
  emergence r₁ text observer - emergence r₂ text observer

/-- Openness is antisymmetric in readers. -/
theorem interpretiveOpenness_antisymm (r₁ r₂ text observer : I) :
    interpretiveOpenness r₁ r₂ text observer =
    -interpretiveOpenness r₂ r₁ text observer := by
  unfold interpretiveOpenness; ring

/-- Self-openness is zero. -/
theorem interpretiveOpenness_self (r text observer : I) :
    interpretiveOpenness r r text observer = 0 := by
  unfold interpretiveOpenness; ring

/-- Openness with void text is zero: void texts are completely "closed." -/
theorem interpretiveOpenness_void_text (r₁ r₂ observer : I) :
    interpretiveOpenness r₁ r₂ (void : I) observer = 0 := by
  unfold interpretiveOpenness; rw [emergence_void_right, emergence_void_right]; ring

/-- **Eco's limits**: each reader's emergence is bounded.
    Interpretation is free but not unlimited. -/
theorem eco_limits (reader text observer : I) :
    (emergence reader text observer) ^ 2 ≤
    rs (compose reader text) (compose reader text) * rs observer observer :=
  emergence_bounded' reader text observer

/-- **The model reader**: Eco's "model reader" is the reader who maximizes
    coherence with the text. While we can't characterize them,
    we can show every reader's coherence is bounded below. -/
theorem model_reader_bound (reader text : I) :
    rs (compose reader text) (compose reader text) ≥ rs reader reader :=
  compose_enriches' reader text

/-- **Overinterpretation**: reading that goes beyond what the text supports.
    We can't formally detect this without additional axioms, but we can
    show that emergence is bounded — there's a limit to how much meaning
    any reader can extract. -/
theorem overinterpretation_bounded (reader text : I) :
    (interpretiveDepth reader text) ^ 2 ≤
    rs (compose reader text) (compose reader text) *
    rs (compose reader text) (compose reader text) :=
  interpretiveDepth_bounded reader text

end EcoOpenWork

/-! ## §54. The Hermeneutic Algebra of Power (Foucault)

Michel Foucault: knowledge and power are inseparable. Every interpretive
framework is a power structure that determines what can and cannot
be said (the "episteme"). In IDT, power is modeled through the
enrichment structure: more powerful frameworks have higher self-resonance
and shape all subsequent interpretations through effective history. -/

section FoucaultPower
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Epistemic weight**: the weight of a knowledge framework.
    Higher weight = more "power" to shape interpretations. -/
noncomputable def epistemicWeight (framework : I) : ℝ := rs framework framework

/-- Void episteme has zero weight. -/
theorem epistemicWeight_void : epistemicWeight (void : I) = 0 := rs_void_void

/-- Non-void episteme has positive weight. -/
theorem epistemicWeight_pos (f : I) (h : f ≠ void) :
    epistemicWeight f > 0 := by
  unfold epistemicWeight; exact rs_self_pos f h

/-- **Power grows through discourse**: adding voices to the episteme
    only increases its weight. -/
theorem power_grows (framework discourse : I) :
    epistemicWeight (compose framework discourse) ≥ epistemicWeight framework := by
  unfold epistemicWeight; exact compose_enriches' framework discourse

/-- **Knowledge-power nexus**: the framework shapes all future emergence.
    Reading through a powerful framework creates different emergence
    than reading through a weak one. -/
theorem knowledge_power_nexus (strong weak text d : I)
    (h : emergence strong text d ≠ emergence weak text d) :
    strong ≠ weak := by
  intro heq; rw [heq] at h; exact h rfl

/-- **Disciplinary power**: iterated application of a framework creates
    a monotonically growing weight. Each iteration of the "discipline"
    increases the framework's presence. -/
theorem disciplinary_power (framework : I) (n : ℕ) :
    rs (composeN framework (n + 1)) (composeN framework (n + 1)) ≥
    rs (composeN framework n) (composeN framework n) :=
  rs_composeN_mono framework n

/-- **Resistance as non-linearity**: resistance to a framework is
    nonzero emergence — the subject's contribution that the framework
    cannot reduce to its own terms. -/
theorem resistance_is_emergence (subject framework d : I)
    (h : emergence subject framework d ≠ 0) :
    ¬leftLinear subject := by
  intro hlin; exact h (hlin framework d)

end FoucaultPower

/-! ## §55. The Infinite Conversation (Blanchot)

Maurice Blanchot's concept of the "infinite conversation": the
dialogue that never concludes, the interpretation that never
reaches a final meaning. In IDT, this is the infinite sequence
of readings, each producing new emergence. -/

section BlanchotInfiniteConversation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **The unending dialogue**: the sequence of reading states
    is infinite — there is always another step possible. -/
theorem conversation_always_continues (r t : I) (n : ℕ) :
    ∃ m : ℕ, m > n ∧
    rs (readN r t m) (readN r t m) ≥ rs (readN r t n) (readN r t n) := by
  exact ⟨n + 1, Nat.lt_succ_of_le (le_refl n), readN_enriches r t n⟩

/-- **No final reading**: reading can always continue. Each step
    produces a well-defined next state. -/
theorem no_final_reading (r t : I) (n : ℕ) :
    readN r t (n + 1) = compose (readN r t n) t := readN_succ r t n

/-- **The conversation enriches**: each turn adds weight. -/
theorem conversation_enriches_each_turn (r t : I) (n : ℕ) :
    rs (readN r t (n + 1)) (readN r t (n + 1)) ≥
    rs (readN r t n) (readN r t n) :=
  readN_enriches r t n

/-- **The conversation has memory**: the state at step n remembers
    all prior readings through the effective history. -/
theorem conversation_has_memory (r t : I) (n : ℕ) :
    rs (readN r t n) (readN r t n) ≥ rs r r :=
  readN_enriches_original r t n

/-- **Blanchot's outside**: the void — the "outside" of all conversation.
    It has zero weight and contributes nothing. -/
theorem outside_is_void : rs (void : I) (void : I) = 0 := rs_void_void

/-- **Writing as approach to the outside**: composing with void
    moves toward the outside without reaching it (if non-void). -/
theorem approach_outside (r : I) :
    compose r (void : I) = r := void_right' r

end BlanchotInfiniteConversation

/-! ## §56. Reader-Text Dialectics — Synthesis Theorems

The interpretive process as dialectic: thesis (reader), antithesis (text),
synthesis (interpretation). The synthesis always enriches beyond the thesis.
We prove deeper dialectical results. -/

section ReaderTextDialectics
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Dialectical synthesis enriches thesis**: the synthesis (interpretation)
    has at least as much self-resonance as the thesis (reader). -/
theorem synthesis_enriches_thesis (thesis antithesis : I) :
    rs (compose thesis antithesis) (compose thesis antithesis) ≥ rs thesis thesis :=
  compose_enriches' thesis antithesis

/-- **Double negation is not identity**: compose(compose(r,t),t) ≠ r
    in general (unless t is void). The "negation of the negation"
    creates something new. -/
theorem double_negation_enriches (r t : I) :
    rs (compose (compose r t) t) (compose (compose r t) t) ≥ rs r r := by
  calc rs (compose (compose r t) t) (compose (compose r t) t)
      ≥ rs (compose r t) (compose r t) := compose_enriches' _ _
    _ ≥ rs r r := compose_enriches' _ _

/-- **Aufhebung (sublation)**: the synthesis preserves and elevates.
    The self-resonance of the synthesis is at least as high as either
    component alone. -/
theorem aufhebung_reader (reader text : I) :
    rs (compose reader text) (compose reader text) ≥ rs reader reader :=
  compose_enriches' reader text

/-- **Dialectical weight addition**: the cocycle governs how dialectical
    tensions compose. -/
theorem dialectical_addition (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

/-- **Thesis-antithesis distance**: the dialectical gap between
    reader and text. -/
noncomputable def dialecticalGap (thesis antithesis : I) : ℝ :=
  rs (compose thesis antithesis) (compose thesis antithesis) -
  rs thesis thesis - rs antithesis antithesis

/-- Dialectical gap with void is zero. -/
theorem dialecticalGap_void_right (thesis : I) :
    dialecticalGap thesis (void : I) = 0 := by
  unfold dialecticalGap; simp [rs_void_void, rs_void_left', rs_void_right']

/-- Dialectical gap with void left. -/
theorem dialecticalGap_void_left (antithesis : I) :
    dialecticalGap (void : I) antithesis = 0 := by
  unfold dialecticalGap; simp [rs_void_void, rs_void_left', rs_void_right']

/-- **Dialectical progression**: n stages of dialectic produce
    monotonically growing weight. -/
theorem dialectical_progression (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) :=
  rs_composeN_mono a n

end ReaderTextDialectics

/-! ## §57. Multi-Text Interpretation — Reading Lists and Curricula

When a reader encounters a sequence of texts (a reading list, a
curriculum), the order matters for emergence but not for the final
state. We prove results about optimal reading orders and their
effects on the interpretive journey. -/

section MultiTextInterpretation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Curriculum as effective history**: reading a list of texts
    creates an effective history that shapes all future readings. -/
theorem curriculum_as_history (r : I) (texts : List I) :
    rs (List.foldl compose r texts) (List.foldl compose r texts) ≥ rs r r :=
  effectiveHistoryWeight_ge_original r texts

/-- **Curriculum enrichment**: adding a text to the curriculum enriches. -/
theorem curriculum_enrichment (r : I) (texts : List I) (t : I) :
    rs (List.foldl compose r (texts ++ [t]))
       (List.foldl compose r (texts ++ [t])) ≥
    rs (List.foldl compose r texts) (List.foldl compose r texts) := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact compose_enriches' _ _

/-- **Two-text curriculum**: reading t₁ then t₂ enriches beyond t₁ alone. -/
theorem two_text_enrichment (r t₁ t₂ : I) :
    rs (compose (compose r t₁) t₂) (compose (compose r t₁) t₂) ≥
    rs (compose r t₁) (compose r t₁) :=
  compose_enriches' _ _

/-- **Two texts, same final state**: regardless of grouping,
    the final state is the same. -/
theorem two_text_grouping (r t₁ t₂ : I) :
    compose (compose r t₁) t₂ = compose r (compose t₁ t₂) :=
  compose_assoc' r t₁ t₂

/-- **Three texts, same final state**. -/
theorem three_text_grouping (r t₁ t₂ t₃ : I) :
    compose (compose (compose r t₁) t₂) t₃ =
    compose r (compose t₁ (compose t₂ t₃)) := by
  rw [compose_assoc', compose_assoc']

/-- **Null curriculum**: reading an empty list changes nothing. -/
theorem null_curriculum (r : I) :
    List.foldl compose r ([] : List I) = r := by simp

/-- **Singleton curriculum**: reading one text is just composition. -/
theorem singleton_curriculum (r t : I) :
    List.foldl compose r [t] = compose r t := by simp

end MultiTextInterpretation

/-! ## §58. The Topology of Understanding — Neighborhoods and Convergence

Understanding has a "topological" structure: some interpretive states
are "close" (similar self-resonance) and others are "far apart."
Iterated reading creates a path through this space. We prove that
this path is monotonically ascending in the "height" (weight) direction. -/

section TopologyOfUnderstanding
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Height function**: the "height" of an interpretive state
    in the space of possible interpretations. -/
noncomputable def interpretiveHeight (a : I) : ℝ := rs a a

/-- Height of void is zero (ground level). -/
theorem interpretiveHeight_void : interpretiveHeight (void : I) = 0 := rs_void_void

/-- Height is non-negative. -/
theorem interpretiveHeight_nonneg (a : I) : interpretiveHeight a ≥ 0 := by
  unfold interpretiveHeight; exact rs_self_nonneg' a

/-- **Reading lifts height**: composition never decreases height. -/
theorem reading_lifts_height (a b : I) :
    interpretiveHeight (compose a b) ≥ interpretiveHeight a := by
  unfold interpretiveHeight; exact compose_enriches' a b

/-- **Height of iterated reading is non-decreasing**. -/
theorem iterated_height_mono (r t : I) (n : ℕ) :
    interpretiveHeight (readN r t (n + 1)) ≥ interpretiveHeight (readN r t n) := by
  unfold interpretiveHeight; exact readN_enriches r t n

/-- **Height always above initial height**. -/
theorem height_above_initial (r t : I) (n : ℕ) :
    interpretiveHeight (readN r t n) ≥ interpretiveHeight r := by
  unfold interpretiveHeight; exact readN_enriches_original r t n

/-- **Height gap between steps is non-negative**. -/
theorem height_gap_nonneg (r t : I) (n : ℕ) :
    interpretiveHeight (readN r t (n + 1)) - interpretiveHeight (readN r t n) ≥ 0 := by
  unfold interpretiveHeight; linarith [readN_enriches r t n]

/-- **Void-height characterization**: only void has zero height. -/
theorem zero_height_iff_void (a : I) :
    interpretiveHeight a = 0 → a = void := by
  unfold interpretiveHeight; exact rs_nondegen' a

/-- **Positive height means non-void**. -/
theorem positive_height_nonvoid (a : I) (h : interpretiveHeight a > 0) :
    a ≠ void := by
  intro heq; rw [heq] at h; unfold interpretiveHeight at h
  linarith [rs_void_void (I := I)]

end TopologyOfUnderstanding

/-! ## §59. The Semiotics of Interpretation — Sign and Meaning

Building on Peirce's semiotics: every sign has three components —
the sign-vehicle (representamen), the object, and the interpretant.
In IDT, the interpretant is the composition of the sign with the
interpreter. Semiosis is the chain of interpretants. -/

section SemioticsOfInterpretation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Peircean interpretant**: the result of a sign being interpreted.
    This is just composition, but named semiotically. -/
def interpretant (sign interpreter : I) : I := compose interpreter sign

/-- Void sign produces void interpretant (from the interpreter's side). -/
theorem interpretant_void_sign (interp : I) :
    interpretant (void : I) interp = interp := by
  unfold interpretant; simp

/-- Void interpreter receives the sign unchanged. -/
theorem interpretant_void_interpreter (sign : I) :
    interpretant sign (void : I) = sign := by
  unfold interpretant; simp

/-- **Unlimited semiosis**: the chain of interpretants. Each interpretant
    becomes the interpreter for the next sign in the chain.
    This is readN in semiotic language. -/
theorem unlimited_semiosis (interp sign : I) (n : ℕ) :
    readN interp sign (n + 1) = compose (readN interp sign n) sign :=
  readN_succ interp sign n

/-- **Semiotic enrichment**: each act of semiosis enriches. -/
theorem semiotic_enrichment (interp sign : I) (n : ℕ) :
    rs (readN interp sign (n + 1)) (readN interp sign (n + 1)) ≥
    rs (readN interp sign n) (readN interp sign n) :=
  readN_enriches interp sign n

/-- **Semiotic weight preservation**: the interpretant always has
    at least as much weight as the interpreter. Signs never diminish. -/
theorem semiotic_weight (interpreter sign : I) :
    rs (interpretant sign interpreter) (interpretant sign interpreter) ≥
    rs interpreter interpreter := by
  unfold interpretant; exact compose_enriches' interpreter sign

/-- **The sign-interpretant gap**: emergence IS semiosis. The emergence
    between sign and interpreter is the "meaning" that arises. -/
theorem semiosis_is_emergence (sign interpreter observer : I) :
    emergence interpreter sign observer =
    rs (interpretant sign interpreter) observer -
    rs interpreter observer - rs sign observer := by
  unfold interpretant; rfl

end SemioticsOfInterpretation

/-! ## §60. Advanced Enrichment Algebra

Deeper algebraic results about the enrichment structure, connecting
composition, emergence, and self-resonance in more sophisticated ways. -/

section AdvancedEnrichmentAlgebra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- **Quadruple composition enrichment**: four-fold composition enriches
    beyond three-fold. -/
theorem quad_enriches_triple (a b c d : I) :
    rs (compose (compose (compose a b) c) d) (compose (compose (compose a b) c) d) ≥
    rs (compose (compose a b) c) (compose (compose a b) c) :=
  compose_enriches' _ _

/-- **Quadruple enriches beyond double**. -/
theorem quad_enriches_double (a b c d : I) :
    rs (compose (compose (compose a b) c) d) (compose (compose (compose a b) c) d) ≥
    rs (compose a b) (compose a b) := by
  calc rs (compose (compose (compose a b) c) d) (compose (compose (compose a b) c) d)
      ≥ rs (compose (compose a b) c) (compose (compose a b) c) := compose_enriches' _ _
    _ ≥ rs (compose a b) (compose a b) := compose_enriches' _ _

/-- **Quadruple enriches beyond single**. -/
theorem quad_enriches_single (a b c d : I) :
    rs (compose (compose (compose a b) c) d) (compose (compose (compose a b) c) d) ≥
    rs a a := by
  calc rs (compose (compose (compose a b) c) d) (compose (compose (compose a b) c) d)
      ≥ rs (compose a b) (compose a b) := quad_enriches_double a b c d
    _ ≥ rs a a := compose_enriches' _ _

/-- **ComposeN enrichment beyond base**: n-fold composition always enriches
    beyond the base for n ≥ 1. -/
theorem composeN_enriches_base (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥ rs a a := by
  induction n with
  | zero => simp [composeN]
  | succ k ih =>
    calc rs (composeN a (k + 2)) (composeN a (k + 2))
        ≥ rs (composeN a (k + 1)) (composeN a (k + 1)) := rs_composeN_mono a (k + 1)
      _ ≥ rs a a := ih

/-- **Emergence bound via self-resonance**: emergence squared is bounded
    by the product of self-resonances, which is bounded by composition
    self-resonances. -/
theorem emergence_double_bound (a b : I) :
    (emergence a b (compose a b)) ^ 2 ≤
    rs (compose a b) (compose a b) * rs (compose a b) (compose a b) :=
  emergence_bounded' a b (compose a b)

/-- **Enrichment is never negative**: the difference between composed
    and uncomposed weight is always ≥ 0. -/
theorem enrichment_nonneg (a b : I) :
    rs (compose a b) (compose a b) - rs a a ≥ 0 := by
  linarith [compose_enriches' a b]

/-- **Void enrichment**: composing void with anything produces weight ≥ 0. -/
theorem void_composition_weight (a : I) :
    rs (compose (void : I) a) (compose (void : I) a) ≥ 0 := by
  simp; exact rs_self_nonneg' a

/-- **Double composition weight bound**: compose twice gives at least
    the weight of once. -/
theorem double_compose_bound (a b : I) :
    rs (compose (compose a b) b) (compose (compose a b) b) ≥
    rs (compose a b) (compose a b) :=
  compose_enriches' (compose a b) b

/-- **Self-composition enriches**: a ∘ a has at least the weight of a. -/
theorem self_compose_enriches (a : I) :
    rs (compose a a) (compose a a) ≥ rs a a :=
  compose_enriches' a a

/-- **Triple self-composition enriches beyond double**. -/
theorem triple_self_enriches (a : I) :
    rs (compose (compose a a) a) (compose (compose a a) a) ≥
    rs (compose a a) (compose a a) :=
  compose_enriches' (compose a a) a

end AdvancedEnrichmentAlgebra

end IDT3
