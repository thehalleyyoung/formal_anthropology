import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 1: Repertoires, Interpretation, and the Hermeneutic Bound

**Anthropological motivation.** Every human mind is a repertoire: a stock
of ideas accumulated through enculturation. When a signal arrives—a gesture,
an utterance, a ritual act—the receiver does not passively absorb it.
They *interpret* it by composing it with their existing ideas:
`compose(rᵢ, signal)` for each `rᵢ` in their repertoire.

This chapter builds the foundational structures of the sequel:

- **Repertoire** = `List I` (a mind's stock of ideas)
- **Interpretation** = `map (fun r => compose r signal) repertoire`
- **The Hermeneutic Bound**: interpretation depth ≤ background + signal
- **Silence is Transparent**: void signal leaves the mind unchanged
- **Cultural Consensus**: resonant minds agree on any signal
- **The Telephone Game**: sequential interpretation = composed backgrounds

The payoff in a signalling game is NEVER about the signal itself—it is
always about the interpretations the signal produces in other minds.

## 16 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch1

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- A repertoire: the receiver's stock of ideas, accumulated through
    enculturation. In Bourdieu's terms, this is the *habitus* made formal. -/
abbrev Repertoire (I : Type*) := List I

/-- Interpretation: when a receiver with repertoire `rep` encounters signal `s`,
    they produce `[compose(r₁, s), compose(r₂, s), …]`.
    This is Gadamer's *Horizontverschmelzung* (fusion of horizons). -/
def interpret (rep : Repertoire I) (signal : I) : List I :=
  rep.map (fun r => IdeaticSpace.compose r signal)

/-- Maximum depth across a list of ideas. -/
def maxInterpDepth : List I → ℕ
  | [] => 0
  | a :: rest => max (IdeaticSpace.depth a) (maxInterpDepth rest)

/-! ## §2. The Hermeneutic Bound

"You can only understand what you're prepared to understand." -/

/-- **Theorem 1.1 (Total Hermeneutic Bound).**
    Total depth of all interpretations ≤ total repertoire depth + |rep| × depth(signal).

    *Anthropological significance*: Mass media (one signal, many receivers)
    has bounded total interpretive impact per receiver. A richer repertoire
    absorbs more, but the signal's contribution scales linearly. -/
theorem total_hermeneutic_bound (rep : Repertoire I) (s : I) :
    depthSum (interpret rep s) ≤ depthSum rep + rep.length * IdeaticSpace.depth s := by
  induction rep with
  | nil => simp [interpret, depthSum, List.map, List.sum]
  | cons r rest ih =>
    have hstep : interpret (r :: rest) s =
      IdeaticSpace.compose r s :: interpret rest s := rfl
    rw [hstep, depthSum_cons, depthSum_cons]
    have hcomp := depth_compose_le r s
    have hlen : (r :: rest).length = rest.length + 1 := rfl
    rw [hlen]
    have hmul : (rest.length + 1) * IdeaticSpace.depth s =
                rest.length * IdeaticSpace.depth s + IdeaticSpace.depth s := by ring
    rw [hmul]
    linarith

/-- **Theorem 1.2 (MaxDepth Interpretation Bound).**
    No single interpretation exceeds the deepest background + signal depth.

    *Anthropological significance*: Even the most sophisticated listener
    adds only `depth(s)` to their best existing understanding. -/
theorem max_interp_depth_bound (rep : Repertoire I) (s : I) :
    maxInterpDepth (interpret rep s) ≤ maxInterpDepth rep + IdeaticSpace.depth s := by
  induction rep with
  | nil => simp [interpret, maxInterpDepth]
  | cons r rest ih =>
    have hstep : interpret (r :: rest) s =
      IdeaticSpace.compose r s :: interpret rest s := rfl
    rw [hstep]
    simp only [maxInterpDepth]
    have hcomp := depth_compose_le r s
    apply Nat.max_le.mpr
    constructor
    · have : IdeaticSpace.depth r ≤ max (IdeaticSpace.depth r) (maxInterpDepth rest) :=
        le_max_left _ _
      linarith
    · have : maxInterpDepth rest ≤ max (IdeaticSpace.depth r) (maxInterpDepth rest) :=
        le_max_right _ _
      linarith

/-! ## §3. Silence and the Unsaid -/

/-- **Theorem 1.3 (Silence is Transparent).**
    Void signal leaves the mind unchanged: `interpret rep void = rep`.

    *Anthropological significance*: Ritual silence (Quaker meeting,
    Buddhist *noble silence*, the minute of silence for the dead)
    exploits this: by saying nothing, the receiver's existing framework
    remains undisturbed. The void signal is the formal foundation of taboo. -/
theorem silence_is_transparent (rep : Repertoire I) :
    interpret rep (IdeaticSpace.void : I) = rep := by
  induction rep with
  | nil => rfl
  | cons r rest ih =>
    simp only [interpret, List.map_cons]
    rw [IDT.void_right]
    exact congrArg (List.cons r) ih

/-- **Theorem 1.4 (The Blank Receiver).**
    A receiver whose only idea is void interprets any signal as
    the signal itself, unmediated.

    *Anthropological significance*: The impossible ideal of the
    "objective observer"—true objectivity requires total cultural amnesia. -/
theorem blank_receiver (s : I) :
    interpret [(IdeaticSpace.void : I)] s = [s] := by
  simp [interpret, IDT.void_left]

/-- **Theorem 1.5 (Negative Capability / Keats's Theorem).**
    If void is anywhere in the repertoire, the raw signal appears
    somewhere in the interpretations.

    *Philosophical significance*: A mind retaining a slot of pure
    receptivity—"capable of being in uncertainties" (Keats)—captures
    the signal in its original form alongside culturally mediated versions. -/
theorem negative_capability {rep : Repertoire I} {s : I}
    (h : (IdeaticSpace.void : I) ∈ rep) :
    s ∈ interpret rep s := by
  simp only [interpret, List.mem_map]
  exact ⟨IdeaticSpace.void, h, IDT.void_left s⟩

/-! ## §4. Cultural Consensus -/

/-- **Theorem 1.6 (Durkheimian Consensus).**
    Resonant backgrounds + same signal ⇒ resonant interpretations.

    *Anthropological significance*: Two members of the same culture
    (shared myths, shared categories) ALWAYS produce resonant
    interpretations of the same event. Cultural consensus is a
    structural consequence of shared background—Durkheim's
    *conscience collective*. -/
theorem durkheimian_consensus {r₁ r₂ : I} (s : I)
    (h : IdeaticSpace.resonates r₁ r₂) :
    IdeaticSpace.resonates (IdeaticSpace.compose r₁ s) (IdeaticSpace.compose r₂ s) :=
  resonance_compose_right h s

/-- **Theorem 1.7 (Lévi-Strauss's Mythical Transformation).**
    Same receiver + resonant signals ⇒ resonant interpretations.

    *Anthropological significance*: Ritual repetition-with-variation
    works because the participant's invariant background ensures that
    structurally similar performances produce resonant experiences.
    Lévi-Strauss's mythical "transformations" are perceived as
    "the same story told differently" for this reason. -/
theorem mythical_transformation (r : I) {s₁ s₂ : I}
    (h : IdeaticSpace.resonates s₁ s₂) :
    IdeaticSpace.resonates (IdeaticSpace.compose r s₁) (IdeaticSpace.compose r s₂) :=
  resonance_compose_left r h

/-- **Theorem 1.8 (Intercultural Solidarity / Turner's Communitas).**
    Resonant backgrounds + resonant signals ⇒ resonant interpretations.

    *Anthropological significance*: Members of allied cultures witnessing
    similar rituals produce resonant interpretations—the formal basis
    of what Turner called *communitas*: the spontaneous solidarity that
    arises when structurally similar participants undergo similar experiences. -/
theorem turners_communitas {r₁ r₂ s₁ s₂ : I}
    (hr : IdeaticSpace.resonates r₁ r₂) (hs : IdeaticSpace.resonates s₁ s₂) :
    IdeaticSpace.resonates (IdeaticSpace.compose r₁ s₁) (IdeaticSpace.compose r₂ s₂) :=
  IdeaticSpace.resonance_compose r₁ r₂ s₁ s₂ hr hs

/-! ## §5. The Telephone Game (Cultural Transmission Chains) -/

/-- **Theorem 1.9 (The Telephone Game / Bartlett's Serial Reproduction).**
    Two-stage interpretation through different minds = single-stage
    interpretation through the composed mind.

    *Anthropological significance*: Bartlett's (1932) serial reproduction
    experiments showed that stories change predictably through chains
    of retelling. This theorem shows WHY: the chain of interpreters
    is structurally equivalent to a single composite interpreter.
    Oral tradition scholars can study the "net effect" of a transmission
    chain without tracking each individual retelling. -/
theorem bartletts_serial_reproduction (rA rB s : I) :
    IdeaticSpace.compose rB (IdeaticSpace.compose rA s) =
    IdeaticSpace.compose (IdeaticSpace.compose rB rA) s :=
  (compose_assoc rB rA s).symm

/-- **Theorem 1.10 (Telephone Depth Bound).**
    The depth after two-stage interpretation ≤ sum of all depths.

    *Anthropological significance*: A transmission chain cannot create
    more complexity than the sum of what each participant carries plus
    the original signal. Long chains redistribute complexity but don't
    create it. -/
theorem telephone_depth (rA rB s : I) :
    IdeaticSpace.depth (IdeaticSpace.compose rB (IdeaticSpace.compose rA s)) ≤
    IdeaticSpace.depth rB + IdeaticSpace.depth rA + IdeaticSpace.depth s := by
  rw [← compose_assoc]
  have h1 := depth_compose_le (IdeaticSpace.compose rB rA) s
  have h2 := depth_compose_le rB rA
  omega

/-- **Theorem 1.11 (Resonant Transmission Lines).**
    Parallel chains with pairwise resonant interpreters produce
    resonant final interpretations.

    *Anthropological significance*: Independent lines of ritual
    transmission (e.g., different griots in West Africa, different
    monastic orders) produce resonant outcomes if corresponding
    specialists resonate. Ritual orthodoxy can be maintained across
    geographically separated communities without central authority. -/
theorem resonant_transmission_lines {rA₁ rA₂ rB₁ rB₂ : I} (s : I)
    (hA : IdeaticSpace.resonates rA₁ rA₂) (hB : IdeaticSpace.resonates rB₁ rB₂) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose rB₁ (IdeaticSpace.compose rA₁ s))
      (IdeaticSpace.compose rB₂ (IdeaticSpace.compose rA₂ s)) := by
  rw [← compose_assoc, ← compose_assoc]
  exact IdeaticSpace.resonance_compose (IdeaticSpace.compose rB₁ rA₁) (IdeaticSpace.compose rB₂ rA₂) s s
    (IdeaticSpace.resonance_compose rB₁ rB₂ rA₁ rA₂ hB hA) (IdeaticSpace.resonance_refl s)

/-! ## §6. Structural Invariants of Interpretation -/

/-- **Theorem 1.12 (Void is Unpersuasive).**
    `depth(compose r void) = depth r`. Silence contributes zero marginal depth.

    *Game-theoretic significance*: The null message (babbling) contributes
    zero information. This is WHY babbling equilibria always exist:
    silence costs nothing and changes nothing. -/
theorem void_is_unpersuasive (r : I) :
    IdeaticSpace.depth (IdeaticSpace.compose r (IdeaticSpace.void : I)) = IdeaticSpace.depth r :=
  depth_compose_void r

/-- **Theorem 1.13 (Interpretation Conserves Count).**
    `|interpret rep s| = |rep|`. Signals transform ideas but
    cannot create or destroy them.

    *Anthropological significance*: Cultural contact does not change
    the NUMBER of schemas a society holds—it transforms each one.
    This is the conservation law of interpretation. -/
theorem interpretation_conserves_count (rep : Repertoire I) (s : I) :
    (interpret rep s).length = rep.length := by
  simp [interpret]

/-- **Theorem 1.14 (Interpretation is Additive / Durkheim's Division of Labor).**
    Merging sub-repertoires then interpreting = interpreting each then merging.

    *Anthropological significance*: A polymath's interpretation equals
    the union of specialist interpretations. Interdisciplinary understanding
    is NOT synergistic—it is the disjoint union of specialist understandings.
    This formalizes Durkheim's cognitive division of labor. -/
theorem durkheims_division_of_labor (rep₁ rep₂ : Repertoire I) (s : I) :
    interpret (rep₁ ++ rep₂) s = interpret rep₁ s ++ interpret rep₂ s := by
  simp [interpret, List.map_append]

/-- **Theorem 1.15 (Silence Preserves DepthSum).**
    Total interpretive depth is invariant under silence.

    *Anthropological significance*: Not speaking has exactly zero
    information-theoretic cost. Total complexity is invariant under
    silence—distinct from "forgetting" (mutagenic transmission). -/
theorem silence_preserves_depthSum (rep : Repertoire I) :
    depthSum (interpret rep (IdeaticSpace.void : I)) = depthSum rep := by
  have h := silence_is_transparent rep
  rw [h]

/-- **Theorem 1.16 (Three-Stage Telephone).**
    Three-stage interpretation through rA, rB, rC equals single-stage
    through compose(rC, compose(rB, rA)).

    *Anthropological significance*: Arbitrarily long chains of cultural
    transmission collapse into a single composite interpreter. This is
    why we can meaningfully speak of "the Western tradition" as a single
    interpretive lens, despite it being the product of thousands of
    individual acts of interpretation. -/
theorem three_stage_telephone (rA rB rC s : I) :
    IdeaticSpace.compose rC (IdeaticSpace.compose rB (IdeaticSpace.compose rA s)) =
    IdeaticSpace.compose (IdeaticSpace.compose (IdeaticSpace.compose rC rB) rA) s := by
  have h1 := compose_assoc rB rA s
  have h2 := compose_assoc rC (IdeaticSpace.compose rB rA) s
  have h3 := compose_assoc rC rB rA
  rw [← h1, ← h2, h3]

end IDT.Signal.Ch1
