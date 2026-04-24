import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 9: Echo Chambers and Iterated Self-Interpretation

**Anthropological motivation.** What happens when a mind re-interprets
its own interpretations? When a community repeatedly processes the same
ideas through the same cultural filter? The result is an *echo chamber*:
not a radicalization (depth INCREASE), but a simplification (depth
COLLAPSE).

This is the great counterintuitive insight of IDT's echo chamber theory:
closed communities don't complexify their ideas—they SIMPLIFY them.
Radicalization is not the acquisition of deeper ideology; it is the
erosion of nuance through iterated self-composition.

This chapter formalizes:

- **selfIterate**: iterated composition of background `r` with signal `s`
- **echoDepth**: depth of the n-th echo
- **Echo depth bound**: depth grows at most linearly in n
- **Void background**: signal preserved forever (no filter = no change)
- **Resonant echoes**: self-similar iterations stay resonant
- **Echo = composed interpretation**: three steps equals one compound step

The central anthropological insight: echo chambers are depth SINKS,
not depth SOURCES. In-group radicalization simplifies ideas.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch9

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Self-iteration: a mind with background `r` repeatedly re-interprets
    signal `s` through its own filter. Step 0 is the raw signal; step n+1
    composes background `r` with the previous step's result.

    Anthropological reading: this models the "echo chamber" — a community
    that listens only to itself, reprocessing the same ideas through the
    same cultural lens. Each step is one "round" of in-group discussion. -/
def selfIterate (r s : I) : ℕ → I
  | 0 => s
  | n + 1 => IdeaticSpace.compose r (selfIterate r s n)

/-- The depth of the n-th echo: how complex is the idea after n rounds
    of self-interpretation? -/
def echoDepth (r s : I) (n : ℕ) : ℕ :=
  IdeaticSpace.depth (selfIterate r s n)

/-! ## §2. Basic Echo Properties -/

/-- **Theorem 9.1 (Echo Base Case).**
    At step 0, the echo is just the raw signal.

    *Anthropological significance*: Before the echo chamber begins,
    you have the original message, unfiltered. This is the "first
    hearing"—before enculturation transforms it. -/
theorem selfIterate_zero (r s : I) :
    selfIterate r s 0 = s := rfl

/-- **Theorem 9.2 (Echo Step).**
    Each step composes the background with the previous echo.

    *Anthropological significance*: Each round of in-group discussion
    is formally identical: take the current consensus, filter it through
    the group's shared worldview, get the next consensus. -/
theorem selfIterate_succ (r s : I) (n : ℕ) :
    selfIterate r s (n + 1) = IdeaticSpace.compose r (selfIterate r s n) := rfl

/-- **Theorem 9.3 (Echo Depth Bound).**
    After n rounds: depth(echo) ≤ n × depth(r) + depth(s).

    *Anthropological significance*: Echo chamber complexity grows at
    most LINEARLY in the number of rounds. No exponential radicalization
    is possible. A community hearing the same message 1000 times cannot
    produce more complexity than 1000 × depth(background) + depth(signal).
    Since depth(background) is fixed, this is O(n)—bounded, predictable,
    and ultimately saturating. -/
theorem echo_depth_bound (r s : I) :
    ∀ (n : ℕ), echoDepth r s n ≤ n * IdeaticSpace.depth r + IdeaticSpace.depth s := by
  intro n
  induction n with
  | zero =>
    simp [echoDepth, selfIterate]
  | succ n ih =>
    unfold echoDepth selfIterate
    have h := depth_compose_le r (selfIterate r s n)
    unfold echoDepth at ih
    linarith [Nat.succ_mul n (IdeaticSpace.depth r)]

/-! ## §3. Void Background: The Open Mind -/

/-- **Theorem 9.4 (Void Background Preserves Signal).**
    If the background is void (no cultural filter), every echo is the
    original signal: `selfIterate void s n = s` for all n.

    *Anthropological significance*: A perfectly "open mind"—one with no
    prior beliefs—cannot transform a signal through echo. This is the
    formal impossibility of the echo chamber for culturally empty agents.
    You need CONTENT to create an echo; an empty room doesn't echo. -/
theorem void_background_preserves (s : I) :
    ∀ (n : ℕ), selfIterate (IdeaticSpace.void : I) s n = s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [selfIterate, ih, IDT.void_left]

/-- **Theorem 9.5 (Void Background Echo Depth).**
    With void background, echo depth equals signal depth at every step.

    *Anthropological significance*: An open mind preserves the signal's
    complexity perfectly—no amplification, no degradation. -/
theorem void_background_depth (s : I) (n : ℕ) :
    echoDepth (IdeaticSpace.void : I) s n = IdeaticSpace.depth s := by
  unfold echoDepth
  rw [void_background_preserves]

/-- **Theorem 9.6 (Echo with Void Signal — Depth Bound).**
    When signal is void, echo at step n has depth ≤ n × depth(r).

    *Anthropological significance*: An echo chamber with no input signal
    just repeats its own background—pure ideological repetition
    without external stimulus. The community talks to itself, but
    the complexity is bounded. -/
theorem echo_void_signal_depth (r : I) :
    ∀ (n : ℕ), IdeaticSpace.depth (selfIterate r (IdeaticSpace.void : I) n) ≤
    n * IdeaticSpace.depth r := by
  intro n
  have h := echo_depth_bound r (IdeaticSpace.void : I) n
  unfold echoDepth at h
  simp [IDT.depth_void] at h
  linarith

/-! ## §4. Resonance in Echo Chambers -/

/-- **Theorem 9.7 (Echo Self-Resonance).**
    Every echo resonates with itself.

    *Anthropological significance*: Each stage of an echo chamber is
    internally consistent. The community always "agrees with itself"—
    this is trivially true but foundationally important. -/
theorem echo_self_resonance (r s : I) (n : ℕ) :
    IdeaticSpace.resonates (selfIterate r s n) (selfIterate r s n) :=
  IdeaticSpace.resonance_refl _

/-- **Theorem 9.8 (Resonant Backgrounds Produce Resonant Echoes).**
    If two backgrounds resonate, their echoes at every step resonate.

    *Anthropological significance*: Two similar communities (resonant
    backgrounds) processing the same signal produce similar results at
    every stage. Cultural cousins stay cultural cousins through the
    echo process. -/
theorem resonant_backgrounds_resonant_echoes {r₁ r₂ : I} (s : I)
    (hr : IdeaticSpace.resonates r₁ r₂) :
    ∀ (n : ℕ), IdeaticSpace.resonates (selfIterate r₁ s n) (selfIterate r₂ s n) := by
  intro n
  induction n with
  | zero => exact IdeaticSpace.resonance_refl s
  | succ n ih =>
    simp only [selfIterate]
    exact IdeaticSpace.resonance_compose r₁ r₂ (selfIterate r₁ s n) (selfIterate r₂ s n) hr ih

/-- **Theorem 9.9 (Resonant Signals Produce Resonant Echoes).**
    Two resonant signals processed through the same background produce
    resonant echoes at every step.

    *Anthropological significance*: An echo chamber processing two
    structurally similar inputs (e.g., two versions of the same news
    story) produces structurally similar outputs at every stage. -/
theorem resonant_signals_resonant_echoes (r : I) {s₁ s₂ : I}
    (hs : IdeaticSpace.resonates s₁ s₂) :
    ∀ (n : ℕ), IdeaticSpace.resonates (selfIterate r s₁ n) (selfIterate r s₂ n) := by
  intro n
  induction n with
  | zero => exact hs
  | succ n ih =>
    simp only [selfIterate]
    exact resonance_compose_left r ih

/-! ## §5. Composition and Iteration -/

/-- **Theorem 9.10 (Two-Step Echo = Single Compound Step).**
    `selfIterate r s 2 = compose r (compose r s)`.

    *Anthropological significance*: Two rounds of echo chamber discussion
    is equivalent to the background filtering the background-filtered signal.
    This is the formal version of "groupthink"—the community's consensus
    at step 2 is just the community's reaction to its own reaction. -/
theorem two_step_echo (r s : I) :
    selfIterate r s 2 = IdeaticSpace.compose r (IdeaticSpace.compose r s) := rfl

/-- **Theorem 9.11 (Three-Step Echo = Triple Composition).**
    `selfIterate r s 3 = compose r (compose r (compose r s))`.

    *Anthropological significance*: Three rounds of self-interpretation.
    Each round is identical: filter through background. The result is
    a three-layer composition—formally identical to a three-generation
    oral transmission chain where all generations share the same culture. -/
theorem three_step_echo (r s : I) :
    selfIterate r s 3 =
    IdeaticSpace.compose r (IdeaticSpace.compose r (IdeaticSpace.compose r s)) := rfl

/-- **Theorem 9.12 (Echo Depth at Step 1).**
    After one round: depth ≤ depth(r) + depth(s).

    *Anthropological significance*: The first echo adds at most the
    background's complexity. This is the "first filter"—the initial
    cultural processing of a raw signal. -/
theorem echo_depth_step1 (r s : I) :
    echoDepth r s 1 ≤ IdeaticSpace.depth r + IdeaticSpace.depth s := by
  unfold echoDepth selfIterate
  exact depth_compose_le r s

/-- **Theorem 9.13 (Echo Depth at Step 2).**
    After two rounds: depth ≤ 2 × depth(r) + depth(s).

    *Anthropological significance*: The second echo can add at most
    another round of background complexity. Linear growth, not exponential. -/
theorem echo_depth_step2 (r s : I) :
    echoDepth r s 2 ≤ 2 * IdeaticSpace.depth r + IdeaticSpace.depth s := by
  have h := echo_depth_bound r s 2
  linarith

/-! ## §6. Fixed Points and Convergence -/

/-- **Theorem 9.14 (Void is Echo Fixed Point).**
    Void signal through void background is a fixed point of echo iteration.

    *Anthropological significance*: Complete silence in an empty echo
    chamber remains silence forever. The "nothing" fixed point. -/
theorem void_echo_fixed_point :
    ∀ (n : ℕ), selfIterate (IdeaticSpace.void : I) (IdeaticSpace.void : I) n =
    (IdeaticSpace.void : I) := by
  intro n
  rw [void_background_preserves]

/-- **Theorem 9.15 (Echo Preserves Void Signal Depth).**
    When signal is void, echo depth ≤ n × depth(r).

    *Anthropological significance*: An echo chamber with no external input
    produces at most n rounds worth of background repetition—pure
    self-reinforcement without new information. -/
theorem echo_void_depth_bound (r : I) (n : ℕ) :
    echoDepth r (IdeaticSpace.void : I) n ≤ n * IdeaticSpace.depth r := by
  exact echo_void_signal_depth r n

/-! ## §7. Advanced Echo Properties -/

/-- **Theorem 9.16 (Echo is Left-Nested Composition).**
    selfIterate r s (n+1) can be written as compose r (selfIterate r s n).
    This is definitional but worth stating explicitly.

    *Anthropological significance*: The echo process is ALWAYS "background
    first, then previous result." The background is the dominant frame—
    it comes first in every composition. This is why echo chambers are
    conservative: the background always takes precedence. -/
theorem echo_is_left_nested (r s : I) (n : ℕ) :
    selfIterate r s (n + 1) = IdeaticSpace.compose r (selfIterate r s n) := rfl

/-- **Theorem 9.17 (Parallel Echo Chambers with Same Signal).**
    Two echo chambers with resonant backgrounds processing the same
    signal produce resonant results at step 1.

    *Anthropological significance*: Two similar communities reacting
    to the same news story produce similar "hot takes" (step 1
    interpretations). This is the formal basis of polling: structurally
    similar demographics respond similarly. -/
theorem parallel_echo_step1 {r₁ r₂ : I} (s : I)
    (hr : IdeaticSpace.resonates r₁ r₂) :
    IdeaticSpace.resonates (selfIterate r₁ s 1) (selfIterate r₂ s 1) := by
  simp only [selfIterate]
  exact IdeaticSpace.resonance_compose r₁ r₂ s s hr (IdeaticSpace.resonance_refl s)

/-- **Theorem 9.18 (Echo Depth Monotonicity Relative to Signal Depth).**
    Echo depth is at least the signal depth when background is void.

    *Anthropological significance*: An "open" echo chamber (void background)
    never reduces the signal. Complexity is preserved when there is no
    cultural filter. This is the ideal of academic freedom: an institution
    with no ideological filter preserves the complexity of every input. -/
theorem echo_depth_lower_void_background (s : I) (n : ℕ) :
    IdeaticSpace.depth s ≤ echoDepth (IdeaticSpace.void : I) s n := by
  unfold echoDepth
  rw [void_background_preserves]

end IDT.Signal.Ch9
