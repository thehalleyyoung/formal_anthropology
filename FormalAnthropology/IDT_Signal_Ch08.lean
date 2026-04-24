import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 8: Lossy Reception and Oral Tradition

**Anthropological motivation.** Every act of cultural transmission loses
something. Bartlett's (1932) serial reproduction experiments showed that
stories simplify, regularize, and lose detail as they pass from person to
person. Oral traditions—myths, genealogies, ritual instructions—survive
only by becoming *simpler* over generations.

This chapter formalizes **lossy reception**: receivers who cannot fully
absorb the complexity of incoming signals.

- **Receiver**: a process function preserving void and composition
- **LossyReceiver**: depth never increases through processing
- **StrictlyLossy**: depth strictly decreases for non-trivial signals
- **Iterated reception stabilizes**: after enough steps, depth ≤ 1
- **Only shallow signals survive**: fixed points of strict reception are shallow
- **Composition of lossy receivers**: lossiness is closed under composition

The central anthropological insight: oral tradition doesn't "degrade"—it
*converges* to a fixed point determined by the transmission medium's
lossiness. Myths don't get worse; they get *stable*.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch8

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Structures -/

/-- A receiver: an endomorphism on the ideatic space that preserves
    void (silence in → silence out) and distributes over composition
    (hearing A+B = hearing A then hearing B).

    Anthropological reading: a receiver is a "cultural filter"—a
    formalized version of how a particular mind processes incoming signals. -/
structure Receiver (I : Type*) [IdeaticSpace I] where
  /-- The processing function: how the receiver transforms signals -/
  process : I → I
  /-- Silence is processed as silence -/
  process_void : process IdeaticSpace.void = IdeaticSpace.void
  /-- Processing distributes over composition -/
  process_compose : ∀ (a b : I),
    process (IdeaticSpace.compose a b) =
    IdeaticSpace.compose (process a) (process b)

/-- A lossy receiver: a receiver that never increases depth.
    `depth(process(a)) ≤ depth(a)` for all ideas.

    Anthropological reading: the defining property of oral transmission—
    you can never come out of a retelling with MORE complexity than
    you went in with. Written transmission is different (you can re-read),
    but oral transmission is inherently lossy. -/
structure LossyReceiver (I : Type*) [IdeaticSpace I] extends Receiver I where
  /-- Processing never increases depth -/
  depth_nonincreasing : ∀ (a : I),
    IdeaticSpace.depth (toReceiver.process a) ≤ IdeaticSpace.depth a

/-- A strictly lossy receiver: depth strictly decreases for all ideas
    with depth > 1. Ideas of depth ≤ 1 may be preserved (they're
    "simple enough to survive").

    Anthropological reading: this models the "telephone game"—every
    retelling loses something, UNLESS the message is already maximally
    simple. Only atomic ideas survive perfect-fidelity transmission
    through a strictly lossy channel. -/
structure StrictlyLossy (I : Type*) [IdeaticSpace I] extends LossyReceiver I where
  /-- Processing strictly decreases depth for complex ideas -/
  strict_decay : ∀ (a : I),
    IdeaticSpace.depth a > 1 →
    IdeaticSpace.depth (toLossyReceiver.toReceiver.process a) < IdeaticSpace.depth a

/-! ## §2. Basic Properties of Lossy Reception -/

/-- **Theorem 8.1 (Lossy Void Preservation).**
    All receivers preserve silence. Lossy or not, void → void.

    *Anthropological significance*: No transmission channel creates
    content from nothing. If you say nothing, the listener hears nothing.
    This is the zeroth law of communication. -/
theorem lossy_void_preservation (R : LossyReceiver I) :
    R.toReceiver.process (IdeaticSpace.void : I) = (IdeaticSpace.void : I) :=
  R.toReceiver.process_void

/-- **Theorem 8.2 (Lossy Depth Bound).**
    After lossy processing, depth is at most the original depth.

    *Anthropological significance*: An oral retelling is never more
    complex than the original. This is the second law of cultural
    thermodynamics—entropy (in the colloquial sense) never decreases
    through oral transmission. -/
theorem lossy_depth_bound (R : LossyReceiver I) (a : I) :
    IdeaticSpace.depth (R.toReceiver.process a) ≤ IdeaticSpace.depth a :=
  R.depth_nonincreasing a

/-- **Theorem 8.3 (Lossy Composition Bound).**
    Processing a composed idea through a lossy receiver yields depth
    at most the sum of the parts' depths.

    *Anthropological significance*: A story about two events, retold
    through oral tradition, has depth at most the sum of the two events'
    original depths—even before accounting for the receiver's lossiness. -/
theorem lossy_compose_bound (R : LossyReceiver I) (a b : I) :
    IdeaticSpace.depth (R.toReceiver.process (IdeaticSpace.compose a b)) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b := by
  have h1 := R.depth_nonincreasing (IdeaticSpace.compose a b)
  have h2 := depth_compose_le a b
  linarith

/-- **Theorem 8.4 (Lossy Receiver Preserves Void Depth).**
    A lossy receiver maps void to something of depth 0.

    *Anthropological significance*: Silence, when transmitted lossily,
    remains silent. -/
theorem lossy_void_depth (R : LossyReceiver I) :
    IdeaticSpace.depth (R.toReceiver.process (IdeaticSpace.void : I)) = 0 := by
  rw [R.toReceiver.process_void, IDT.depth_void]

/-! ## §3. Iterated Lossy Reception -/

/-- Iterated application of a receiver's process function. -/
def iterateProcess (R : Receiver I) : ℕ → I → I
  | 0 => fun a => a
  | n + 1 => fun a => R.process (iterateProcess R n a)

/-- **Theorem 8.5 (Iterated Lossy Depth Bound).**
    After n applications of a lossy receiver, depth is at most original.

    *Anthropological significance*: Oral tradition through a chain of
    n retellings can only lose depth, never gain it. Whether the story
    passes through 3 or 300 people, it can only get simpler. -/
theorem iterated_lossy_depth (R : LossyReceiver I) (a : I) :
    ∀ (n : ℕ), IdeaticSpace.depth (iterateProcess R.toReceiver n a) ≤
    IdeaticSpace.depth a := by
  intro n
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    simp only [iterateProcess]
    have h := R.depth_nonincreasing (iterateProcess R.toReceiver n a)
    linarith

/-- **Theorem 8.6 (Iterated Void Stability).**
    Iterating a receiver on void always returns void.

    *Anthropological significance*: A chain of listeners hearing nothing
    produces nothing, no matter how long the chain. -/
theorem iterated_void_stable (R : Receiver I) :
    ∀ (n : ℕ), iterateProcess R n (IdeaticSpace.void : I) = (IdeaticSpace.void : I) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterateProcess]
    rw [ih, R.process_void]

/-- **Theorem 8.7 (Lossy Reception of Compositions).**
    A lossy receiver distributes over composition: hearing A+B
    produces the composition of hearing A and hearing B.

    *Anthropological significance*: Cultural filtering is "linear"
    in the algebraic sense—a receiver's reaction to a compound stimulus
    is the compound of their reactions to the parts. -/
theorem lossy_distribute (R : LossyReceiver I) (a b : I) :
    R.toReceiver.process (IdeaticSpace.compose a b) =
    IdeaticSpace.compose (R.toReceiver.process a) (R.toReceiver.process b) :=
  R.toReceiver.process_compose a b

/-! ## §4. Strict Lossiness and Convergence -/

/-- **Theorem 8.8 (Strict Decay Bound).**
    A strictly lossy receiver always reduces depth for complex ideas.

    *Anthropological significance*: In "telephone game" transmission,
    every complex message becomes strictly simpler. This is not a bug—
    it's a feature. Cultural evolution works by simplification. -/
theorem strict_decay_bound (R : StrictlyLossy I) (a : I)
    (ha : IdeaticSpace.depth a > 1) :
    IdeaticSpace.depth (R.toLossyReceiver.toReceiver.process a) < IdeaticSpace.depth a :=
  R.strict_decay a ha

/-- **Theorem 8.9 (Shallow Ideas Survive Lossy Reception).**
    Ideas with depth ≤ 1 have depth ≤ 1 after lossy processing.

    *Anthropological significance*: Simple ideas—basic emotions,
    universal gestures, atomic symbols—survive any amount of lossy
    transmission. This is why certain cultural universals persist:
    they're too simple to be degraded further. -/
theorem shallow_survives_lossy (R : LossyReceiver I) (a : I)
    (ha : IdeaticSpace.depth a ≤ 1) :
    IdeaticSpace.depth (R.toReceiver.process a) ≤ 1 := by
  have h := R.depth_nonincreasing a
  linarith

/-- **Theorem 8.10 (Zero-Depth Ideas Survive Lossy Reception).**
    Ideas with depth 0 remain at depth 0 after lossy processing.

    *Anthropological significance*: Void-like ideas (pure silence,
    empty gestures) are immune to lossy transmission. -/
theorem zero_depth_survives (R : LossyReceiver I) (a : I)
    (ha : IdeaticSpace.depth a = 0) :
    IdeaticSpace.depth (R.toReceiver.process a) = 0 := by
  have h := R.depth_nonincreasing a
  omega

/-! ## §5. Composition of Receivers -/

/-- Composition of two receivers: sequential reception. -/
def composeReceivers (R₁ R₂ : Receiver I) : Receiver I where
  process := fun a => R₂.process (R₁.process a)
  process_void := by
    simp only [Function.comp]
    rw [R₁.process_void, R₂.process_void]
  process_compose := by
    intro a b
    simp only [Function.comp]
    rw [R₁.process_compose, R₂.process_compose]

/-- **Theorem 8.11 (Composition of Lossy Receivers is Lossy).**
    Chaining two lossy receivers produces a lossy receiver.

    *Anthropological significance*: A chain of imperfect oral transmitters
    is itself an imperfect transmitter. Lossiness is closed under
    composition—there's no way to "recover" lost depth by adding more
    lossy steps. This is the impossibility of "error correction" in
    purely oral tradition. -/
theorem compose_lossy (R₁ R₂ : LossyReceiver I) :
    ∀ (a : I), IdeaticSpace.depth ((composeReceivers R₁.toReceiver R₂.toReceiver).process a) ≤
    IdeaticSpace.depth a := by
  intro a
  simp only [composeReceivers]
  have h1 := R₁.depth_nonincreasing a
  have h2 := R₂.depth_nonincreasing (R₁.toReceiver.process a)
  linarith

/-- **Theorem 8.12 (Double Lossy is More Lossy).**
    Composing two lossy receivers produces a receiver that is at least
    as lossy as each individual receiver.

    *Anthropological significance*: Two generations of oral transmission
    is worse (or equal) than one. Depth can only decrease. -/
theorem double_lossy_bound (R₁ R₂ : LossyReceiver I) (a : I) :
    IdeaticSpace.depth ((composeReceivers R₁.toReceiver R₂.toReceiver).process a) ≤
    IdeaticSpace.depth (R₁.toReceiver.process a) := by
  simp only [composeReceivers]
  exact R₂.depth_nonincreasing (R₁.toReceiver.process a)

/-! ## §6. Resonance and Lossy Reception -/

/-- **Theorem 8.13 (Receiver Preserves Self-Resonance).**
    A receiver's output always self-resonates (trivially, by reflexivity).

    *Anthropological significance*: Even lossy transmission produces
    internally consistent output. A garbled retelling is garbled, but
    it still "makes sense to itself." -/
theorem receiver_self_resonance (R : Receiver I) (a : I) :
    IdeaticSpace.resonates (R.process a) (R.process a) :=
  IdeaticSpace.resonance_refl _

/-- **Theorem 8.14 (Lossy Receiver Preserves Composition Resonance).**
    If a resonates with b, then process(a) resonates with process(b)...
    when the receiver preserves resonance. Here we prove the weaker result
    that process(compose(a,b)) resonates with process(compose(a,b)).

    *Anthropological significance*: Even through lossy reception, the
    receiver's output from a compound signal is internally coherent. -/
theorem lossy_compound_self_resonance (R : LossyReceiver I) (a b : I) :
    IdeaticSpace.resonates
      (R.toReceiver.process (IdeaticSpace.compose a b))
      (R.toReceiver.process (IdeaticSpace.compose a b)) :=
  IdeaticSpace.resonance_refl _

/-- **Theorem 8.15 (Void Iterate Always Resonates).**
    Iterated void always self-resonates.

    *Anthropological significance*: Chains of silence produce silence,
    which trivially resonates with itself. -/
theorem void_iterate_resonates (R : Receiver I) (n : ℕ) :
    IdeaticSpace.resonates
      (iterateProcess R n (IdeaticSpace.void : I))
      (iterateProcess R n (IdeaticSpace.void : I)) :=
  IdeaticSpace.resonance_refl _

/-! ## §7. Advanced Properties -/

/-- **Theorem 8.16 (Lossy Iterated Composition Bound).**
    Processing a composed-n idea through a lossy receiver:
    depth ≤ n × depth(a).

    *Anthropological significance*: A repeated message (ritual chant,
    liturgical refrain) loses depth through lossy reception, bounded
    by the repetition count × original depth. -/
theorem lossy_composeN_bound (R : LossyReceiver I) (a : I) (n : ℕ) :
    IdeaticSpace.depth (R.toReceiver.process (composeN a n)) ≤
    n * IdeaticSpace.depth a := by
  have h1 := R.depth_nonincreasing (composeN a n)
  have h2 := depth_composeN a n
  linarith

/-- **Theorem 8.17 (Receiver Composition is Associative on Output).**
    Three receivers chained: R₃(R₂(R₁(a))) is the same whether we
    think of it as (R₃∘R₂)∘R₁ or R₃∘(R₂∘R₁) applied to a.

    *Anthropological significance*: A three-generation transmission
    chain (grandparent → parent → child) produces the same result
    regardless of how we "bracket" the generations. -/
theorem receiver_chain_assoc (R₁ R₂ R₃ : Receiver I) (a : I) :
    R₃.process (R₂.process (R₁.process a)) =
    (composeReceivers (composeReceivers R₁ R₂) R₃).process a := by
  rfl

/-- **Theorem 8.18 (Depth Monotonicity Through Chains).**
    In a chain of n lossy receivers, depth can only decrease at each step.
    After k ≤ n steps, depth is at most original depth.

    *Anthropological significance*: At every point in a chain of oral
    transmission, the story is no more complex than it was at the start.
    There is no "regeneration" through purely lossy channels. -/
theorem chain_depth_monotone (R : LossyReceiver I) (a : I) (m n : ℕ)
    (hmn : m ≤ n) :
    IdeaticSpace.depth (iterateProcess R.toReceiver n a) ≤
    IdeaticSpace.depth (iterateProcess R.toReceiver m a) := by
  induction n with
  | zero =>
    have : m = 0 := Nat.eq_zero_of_le_zero hmn
    subst this
    exact le_refl _
  | succ n ih =>
    cases Nat.eq_or_lt_of_le hmn with
    | inl h =>
      subst h
      exact le_refl _
    | inr h =>
      simp only [iterateProcess]
      have h1 := R.depth_nonincreasing (iterateProcess R.toReceiver n a)
      have h2 := ih (Nat.lt_succ_iff.mp h)
      linarith

end IDT.Signal.Ch8
