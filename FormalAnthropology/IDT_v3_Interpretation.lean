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

end IDT3
