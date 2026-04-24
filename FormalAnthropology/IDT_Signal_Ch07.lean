import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 7: Persuasion Bounds and Propaganda

**Anthropological motivation.** Every propagandist, preacher, and politician
faces the same fundamental constraint: you cannot add more complexity to
someone's worldview than the complexity of your message allows. A simple
slogan cannot produce a sophisticated understanding; a complex treatise
cannot simplify a mind beyond its existing depth.

This chapter formalizes the **limits of persuasion**:

- **Marginal depth**: how much a signal adds to an existing interpretation
- **Persuasion bound**: depth(signal) caps the marginal contribution
- **Subadditivity of propaganda**: chaining messages doesn't multiply impact
- **Void has zero persuasion**: silence cannot persuade
- **Deeper signals have higher persuasion bounds**: complexity enables persuasion

The central anthropological insight: "hearts and minds" campaigns fail not
because of insufficient repetition, but because of the fundamental
*subadditivity* of ideatic composition. You cannot shout your way to depth.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch7

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Marginal depth: how much composing with signal `s` adds to the depth
    of receiver's idea `r`. Uses truncated subtraction (result ≥ 0).

    Anthropological reading: the marginal depth of a sermon to a
    parishioner is how much MORE complex their worldview becomes after
    hearing it, relative to what they had before. -/
def marginalDepth (r s : I) : ℕ :=
  IdeaticSpace.depth (IdeaticSpace.compose r s) - IdeaticSpace.depth r

/-- The persuasion bound of a signal: its own depth. This is the maximum
    marginal depth it can contribute to ANY receiver. -/
def persuasionBound (s : I) : ℕ := IdeaticSpace.depth s

/-! ## §2. The Fundamental Persuasion Bound -/

/-- **Theorem 7.1 (Marginal Depth Bound).**
    The marginal depth of any signal is at most the signal's own depth.
    `marginalDepth(r, s) ≤ depth(s)` for all receivers `r`.

    *Anthropological significance*: No matter how receptive the audience,
    a message cannot add more complexity than it intrinsically contains.
    A bumper sticker cannot produce a PhD-level understanding. This is
    the **fundamental theorem of propaganda theory**. -/
theorem marginal_depth_bound (r s : I) :
    marginalDepth r s ≤ persuasionBound s := by
  unfold marginalDepth persuasionBound
  have h := depth_compose_le r s
  omega

/-- **Theorem 7.2 (Void Has Zero Marginal Depth).**
    Silence adds nothing to any interpretation: `marginalDepth(r, void) = 0`.

    *Anthropological significance*: The formal proof that silence cannot
    persuade. Quaker silence, Buddhist *noble silence*, and the minute
    of silence for the dead change nothing about the listener's depth.
    They are powerful *socially* but informationally null. -/
theorem void_marginal_depth (r : I) :
    marginalDepth r (IdeaticSpace.void : I) = 0 := by
  unfold marginalDepth
  rw [IDT.void_right]
  omega

/-- **Theorem 7.3 (Void Has Zero Persuasion Bound).**
    The persuasion bound of silence is zero.

    *Game-theoretic significance*: In any signalling game, the null
    message has zero persuasive capacity. This is independent of the
    receiver—it's a property of the signal itself. -/
theorem void_persuasion_bound :
    persuasionBound (IdeaticSpace.void : I) = 0 := by
  unfold persuasionBound
  exact IDT.depth_void

/-- **Theorem 7.4 (Persuasion Bound Nonnegativity).**
    The persuasion bound is always ≥ 0 (trivially true for ℕ, but
    conceptually important).

    *Anthropological significance*: Every signal has non-negative
    persuasive potential—there are no "anti-signals" that reduce the
    maximum possible effect below zero. -/
theorem persuasion_bound_nonneg (s : I) :
    0 ≤ persuasionBound s :=
  Nat.zero_le _

/-! ## §3. Deeper Signals Are More Persuasive -/

/-- **Theorem 7.5 (Monotonicity of Persuasion Bound).**
    If `depth(s₁) ≤ depth(s₂)`, then `persuasionBound(s₁) ≤ persuasionBound(s₂)`.
    Deeper signals have higher persuasion ceilings.

    *Anthropological significance*: A complex ritual (high depth) has
    MORE potential to transform a participant's worldview than a simple
    one. This doesn't mean it WILL—marginal depth depends on the receiver—
    but it CAN. Complexity is a necessary (not sufficient) condition for
    deep persuasion. -/
theorem persuasion_bound_mono {s₁ s₂ : I}
    (h : IdeaticSpace.depth s₁ ≤ IdeaticSpace.depth s₂) :
    persuasionBound s₁ ≤ persuasionBound s₂ :=
  h

/-- **Theorem 7.6 (Self-Composition Persuasion Bound).**
    The persuasion bound of `compose(s, s)` is at most twice the bound of `s`.

    *Anthropological significance*: Repeating a message doubles the
    MAXIMUM possible effect—but in practice (Theorem 7.1), the actual
    effect depends on the receiver. Propaganda works by repetition, but
    with diminishing returns. -/
theorem self_compose_persuasion_bound (s : I) :
    persuasionBound (IdeaticSpace.compose s s) ≤ 2 * persuasionBound s := by
  unfold persuasionBound
  have h := depth_compose_le s s
  linarith

/-- **Theorem 7.7 (ComposeN Persuasion Bound).**
    The persuasion bound of n-fold repetition is at most `n × depth(s)`.

    *Anthropological significance*: Even with unlimited repetition,
    persuasive capacity grows at most linearly—never exponentially.
    This is why totalitarian propaganda, despite its volume, has bounded
    effectiveness. The 20th century showed this repeatedly: neither
    Nazi Germany nor the Soviet Union achieved total ideological control
    despite saturation-level messaging. -/
theorem composeN_persuasion_bound (s : I) (n : ℕ) :
    persuasionBound (composeN s n) ≤ n * persuasionBound s := by
  unfold persuasionBound
  exact depth_composeN s n

/-! ## §4. Subadditivity: Chaining Doesn't Multiply -/

/-- **Theorem 7.8 (Persuasion Subadditivity).**
    The persuasion bound of a composed signal is at most the sum of bounds.
    `persuasionBound(compose(s₁, s₂)) ≤ persuasionBound(s₁) + persuasionBound(s₂)`.

    *Anthropological significance*: A two-part message cannot be more
    persuasive than the sum of its parts. This rules out "synergistic
    propaganda"—the idea that combining messages could produce
    super-additive persuasion. The formal foundation of bounded rationality
    in cultural transmission. -/
theorem persuasion_subadditivity (s₁ s₂ : I) :
    persuasionBound (IdeaticSpace.compose s₁ s₂) ≤
    persuasionBound s₁ + persuasionBound s₂ := by
  unfold persuasionBound
  exact depth_compose_le s₁ s₂

/-- **Theorem 7.9 (Three-Message Persuasion Bound).**
    Three composed messages: total persuasion ≤ sum of individual bounds.

    *Anthropological significance*: Multi-act rituals (liturgy with
    readings, sermon, and communion) have bounded total impact ≤ sum of
    individual act complexities. -/
theorem three_message_bound (s₁ s₂ s₃ : I) :
    persuasionBound (IdeaticSpace.compose (IdeaticSpace.compose s₁ s₂) s₃) ≤
    persuasionBound s₁ + persuasionBound s₂ + persuasionBound s₃ := by
  unfold persuasionBound
  have h1 := depth_compose_le (IdeaticSpace.compose s₁ s₂) s₃
  have h2 := depth_compose_le s₁ s₂
  linarith

/-- **Theorem 7.10 (Marginal Depth of Void Receiver).**
    A receiver with no prior ideas absorbs the full signal depth.
    `marginalDepth(void, s) = depth(s)`.

    *Anthropological significance*: The "blank slate" receiver (tabula
    rasa) absorbs every signal fully. This is the formal version of
    John Locke's epistemology—and its anthropological critique: no real
    human is a blank slate, so no real human absorbs a signal fully. -/
theorem marginal_depth_void_receiver (s : I) :
    marginalDepth (IdeaticSpace.void : I) s = IdeaticSpace.depth s := by
  unfold marginalDepth
  rw [IDT.void_left, IDT.depth_void]
  omega

/-! ## §5. Persuasion Through Chains -/

/-- **Theorem 7.11 (Chain Persuasion Bound).**
    If receiver hears signal s through intermediary r₁ (who first composes
    with their own background), total marginal depth is bounded by
    depth(r₁) + depth(s).

    *Anthropological significance*: A teacher cannot transmit more depth
    than their own understanding plus the source material's complexity.
    Great teaching requires both deep knowledge AND rich source texts. -/
theorem chain_persuasion_bound (r r₁ s : I) :
    marginalDepth r (IdeaticSpace.compose r₁ s) ≤
    IdeaticSpace.depth r₁ + IdeaticSpace.depth s := by
  unfold marginalDepth
  have h := depth_compose_le r (IdeaticSpace.compose r₁ s)
  have h2 := depth_compose_le r₁ s
  omega

/-- **Theorem 7.12 (Marginal Depth Self-Composition).**
    The marginal depth of composing with yourself is at most your own depth.

    *Anthropological significance*: Reflecting on your own ideas
    (self-composition) cannot add more than your existing complexity.
    Introspection has bounded returns. -/
theorem marginal_depth_self (r : I) :
    marginalDepth r r ≤ IdeaticSpace.depth r := by
  unfold marginalDepth
  have h := depth_compose_le r r
  omega

/-- **Theorem 7.13 (Marginal Depth Triangle Inequality).**
    `marginalDepth(r, compose(s₁, s₂)) ≤ depth(s₁) + depth(s₂)`.

    *Anthropological significance*: The marginal impact of a compound
    message is bounded by the sum of its parts' complexities. No
    synergy, no multiplication—just addition. -/
theorem marginal_depth_triangle (r s₁ s₂ : I) :
    marginalDepth r (IdeaticSpace.compose s₁ s₂) ≤
    IdeaticSpace.depth s₁ + IdeaticSpace.depth s₂ := by
  unfold marginalDepth
  have h := depth_compose_le r (IdeaticSpace.compose s₁ s₂)
  have h2 := depth_compose_le s₁ s₂
  omega

/-! ## §6. Propaganda Effectiveness Bounds -/

/-- **Theorem 7.14 (Bounded Propaganda Effectiveness).**
    After composing with n repetitions of signal s, the receiver's
    depth is at most their original depth + n × depth(s).

    *Anthropological significance*: Propaganda saturation—hearing
    the same message n times—increases depth at most linearly.
    No amount of repetition can produce exponential radicalization.
    This is why "deprogramming" is possible: the damage is bounded. -/
theorem bounded_propaganda (r s : I) (n : ℕ) :
    IdeaticSpace.depth (IdeaticSpace.compose r (composeN s n)) ≤
    IdeaticSpace.depth r + n * IdeaticSpace.depth s := by
  have h := depth_compose_le r (composeN s n)
  have h2 := depth_composeN s n
  linarith

/-- **Theorem 7.15 (Resonant Signals Have Equal Persuasion Bounds... Not!).**
    Resonance does NOT imply equal depth—but composition with a common
    element preserves resonance. Two resonant propaganda signals produce
    resonant (not identical) interpretations.

    *Anthropological significance*: Competing narratives that "resonate"
    with the same cultural themes produce resonant (structurally similar)
    effects on receivers. Fox News and MSNBC, when they draw on the same
    patriotic imagery, produce resonant (not identical) reactions. -/
theorem resonant_propaganda {s₁ s₂ : I}
    (h : IdeaticSpace.resonates s₁ s₂) (r : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose r s₁) (IdeaticSpace.compose r s₂) :=
  resonance_compose_left r h

/-- **Theorem 7.16 (Double Propagandist Bound).**
    Two propagandists composing their messages: total persuasion bounded
    by sum of individual depths.

    *Anthropological significance*: Allied propaganda campaigns
    (e.g., joint military-religious messaging) cannot exceed the sum
    of their individual complexities. Coalition propaganda doesn't
    synergize—it merely adds. -/
theorem double_propagandist_bound (s₁ s₂ : I) (r : I) :
    marginalDepth r (IdeaticSpace.compose s₁ s₂) ≤
    persuasionBound s₁ + persuasionBound s₂ := by
  unfold marginalDepth persuasionBound
  have h := depth_compose_le r (IdeaticSpace.compose s₁ s₂)
  have h2 := depth_compose_le s₁ s₂
  omega

/-- **Theorem 7.17 (Atomic Signal Minimal Persuasion).**
    An atomic signal has persuasion bound ≤ 1. Simple messages have
    minimal persuasive capacity.

    *Anthropological significance*: Single words, simple gestures,
    basic symbols—all have persuasion bound 1. To deeply transform
    a worldview, you need *structured* complexity, not atomic simplicity.
    A thumbs-up cannot substitute for a treatise. -/
theorem atomic_persuasion_bound {s : I}
    (h : IdeaticSpace.atomic s) :
    persuasionBound s ≤ 1 := by
  unfold persuasionBound
  exact IdeaticSpace.depth_atomic s h

/-- **Theorem 7.18 (Iterated Propaganda Marginal Decay).**
    After k rounds of the same message, the total depth gain is bounded
    by k × depth(s), regardless of how many rounds came before.

    *Anthropological significance*: The k-th repetition of propaganda
    is no more effective than the first—the bound is uniform. This
    formalizes the "diminishing returns" of propaganda: each repetition
    has the same ceiling on marginal depth, but the actual marginal
    depth can only decrease (in many realistic models). -/
theorem iterated_propaganda_bound (r s : I) (n : ℕ) :
    marginalDepth r (composeN s n) ≤ n * persuasionBound s := by
  unfold marginalDepth persuasionBound
  have h := depth_compose_le r (composeN s n)
  have h2 := depth_composeN s n
  omega

end IDT.Signal.Ch7
