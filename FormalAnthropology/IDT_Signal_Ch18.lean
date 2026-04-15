import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 18: Network Diffusion and Cultural Epidemiology

**Anthropological motivation.** Dan Sperber's *Explaining Culture* (1996)
proposed that cultural representations spread like epidemics: ideas pass
from mind to mind, transformed at each step. Frederic Bartlett's serial
reproduction experiments (1932) showed that stories mutate systematically
as they pass through chains of retellers.

In IDT, each relay hop is a composition: the relayer composes the incoming
signal with their own interpretive frame. A chain of relayers produces
`compose(rₙ, compose(rₙ₋₁, ... compose(r₁, signal)))`.

This chapter formalizes:

- **relayChain**: signal composed through a chain of relayers
- **chainDepth**: depth of the result after relay
- **NetworkPath**: structure packaging relayers and signal
- Depth bounds on relay chains (subadditivity cascades)
- Void relayers are transparent
- Chain concatenation = sequential relay

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch18

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Relay chain: a signal composed through a sequence of relayers.
    Each relayer composes the signal with their own frame.
    `relayChain [r₁, r₂, r₃] s = compose r₃ (compose r₂ (compose r₁ s))`
    This is `foldl` — left-to-right processing.

    *Sperber*: Each cognitive environment transforms the representation. -/
def relayChain (relayers : List I) (signal : I) : I :=
  relayers.foldl (fun acc r => IdeaticSpace.compose r acc) signal

/-- Depth of the relayed result. -/
def chainDepth (relayers : List I) (signal : I) : ℕ :=
  IdeaticSpace.depth (relayChain relayers signal)

/-- A network path: a signal traveling through a sequence of relayers. -/
structure NetworkPath (I : Type*) [IdeaticSpace I] where
  relayers : List I
  signal : I

/-- The output of a network path. -/
def NetworkPath.output (p : NetworkPath I) : I :=
  relayChain p.relayers p.signal

/-! ## §2. Fundamental Diffusion Theorems -/

/-- **Theorem 18.1 (Empty Chain Preserves Signal).**
    A signal with no relayers arrives unchanged.

    *Communication theory*: Direct transmission without intermediaries
    preserves the original message perfectly. -/
theorem empty_chain_preserves (s : I) :
    relayChain [] s = s := by
  simp [relayChain, List.foldl]

/-- **Theorem 18.2 (Singleton Chain = Single Composition).**
    One relayer simply composes the signal with their frame.

    *Bartlett*: A single retelling = one act of interpretive composition. -/
theorem singleton_chain (r s : I) :
    relayChain [r] s = IdeaticSpace.compose r s := by
  simp [relayChain, List.foldl]

/-- **Theorem 18.3 (Two-Relayer Chain).**
    Two relayers compose sequentially: r₂ ∘ (r₁ ∘ signal).

    *Telephone game*: The second player interprets the first player's
    interpretation, not the original signal. -/
theorem two_relayer_chain (r₁ r₂ s : I) :
    relayChain [r₁, r₂] s = IdeaticSpace.compose r₂ (IdeaticSpace.compose r₁ s) := by
  simp [relayChain, List.foldl]

/-- **Theorem 18.4 (Void Relayer is Transparent).**
    A void relayer doesn't change the signal: silence adds nothing.

    *Sperber*: A cognitively "empty" relay node transmits faithfully.
    This models passive carriers who don't transform the message. -/
theorem void_relayer_transparent (relayers : List I) (s : I) :
    relayChain (relayers ++ [IdeaticSpace.void]) s = relayChain relayers s := by
  simp [relayChain, List.foldl_append, List.foldl]

/-- **Theorem 18.5 (Void Signal Through Chain).**
    Relaying void through a single relayer yields just the relayer.

    *Information theory*: An empty message gets filled with the relayer's
    own content — there is no signal, only interpretation. -/
theorem void_signal_single_relay (r : I) :
    relayChain [r] IdeaticSpace.void = r := by
  simp [relayChain, List.foldl]

/-- **Theorem 18.6 (Chain Depth Bound — Single Relayer).**
    Depth after one relay ≤ depth(relayer) + depth(signal).

    *Bartlett*: A single retelling adds at most the reteller's own
    complexity to the story. -/
theorem single_relay_depth (r s : I) :
    chainDepth [r] s ≤ IdeaticSpace.depth r + IdeaticSpace.depth s := by
  simp [chainDepth, singleton_chain]
  exact depth_compose_le r s

/-- **Theorem 18.7 (Resonant Relayers Produce Resonant Output).**
    If two relayers resonate, their relay outputs resonate.

    *Cultural epidemiology*: Similar cognitive environments produce similar
    transformations of the same input — cultural variants cluster. -/
theorem resonant_relayers_resonant_output {r₁ r₂ : I}
    (hr : IdeaticSpace.resonates r₁ r₂) (s : I) :
    IdeaticSpace.resonates (relayChain [r₁] s) (relayChain [r₂] s) := by
  simp [relayChain, List.foldl]
  exact resonance_compose_right hr s

/-- **Theorem 18.8 (Resonant Signals Through Same Relayer).**
    Resonant signals remain resonant after passing through the same relayer.

    *Meme theory*: Similar memes stay similar even after cultural transmission
    through the same social environment. -/
theorem resonant_signals_same_relay (r : I) {s₁ s₂ : I}
    (hs : IdeaticSpace.resonates s₁ s₂) :
    IdeaticSpace.resonates (relayChain [r] s₁) (relayChain [r] s₂) := by
  simp [relayChain, List.foldl]
  exact IdeaticSpace.resonance_compose r r s₁ s₂ (resonance_refl r) hs

/-- **Theorem 18.9 (Empty Chain Depth Preservation).**
    An empty chain preserves signal depth exactly.

    *Direct communication*: Without intermediaries, complexity is unchanged. -/
theorem empty_chain_depth (s : I) :
    chainDepth [] s = IdeaticSpace.depth s := by
  simp [chainDepth, empty_chain_preserves]

/-- **Theorem 18.10 (Chain Concatenation is Sequential Relay).**
    Concatenating two chains of relayers = sequential relay.

    *Network topology*: Two segments of a communication network compose
    into a single longer path. This is the fundamental composition law
    for information networks. -/
theorem chain_concat (relayers₁ relayers₂ : List I) (s : I) :
    relayChain (relayers₁ ++ relayers₂) s = relayChain relayers₂ (relayChain relayers₁ s) := by
  simp [relayChain, List.foldl_append]

/-- **Theorem 18.11 (Network Path Self-Resonance).**
    Every network path output resonates with itself.

    *Structural coherence*: Any completed transmission, however distorted,
    achieves internal self-consistency. -/
theorem path_self_resonance (p : NetworkPath I) :
    IdeaticSpace.resonates p.output p.output := by
  exact resonance_refl _

/-- **Theorem 18.12 (Void Chain is Identity).**
    A chain of all void relayers preserves the signal.

    *Sperber*: A chain of "empty" cognitive environments transmits perfectly.
    This is the idealized limit of faithful transmission. -/
theorem void_chain_identity : ∀ (n : ℕ) (s : I),
    relayChain (List.replicate n IdeaticSpace.void) s = s
  | 0, s => by simp [relayChain, List.foldl]
  | n + 1, s => by
    simp [relayChain, List.replicate_succ, List.foldl]
    have : List.foldl (fun acc r => IdeaticSpace.compose r acc) s
           (List.replicate n IdeaticSpace.void) = s := by
      have ih := void_chain_identity n s
      simp [relayChain] at ih
      exact ih
    simp [this]

/-- **Theorem 18.13 (Relay Preserves List Length — Relayers Unchanged).**
    The relay chain function doesn't alter the number of relayers.

    *Technical*: The relayer network topology is preserved during diffusion. -/
theorem relay_preserves_relayer_count (relayers : List I) (s : I) :
    (NetworkPath.mk relayers s).relayers.length = relayers.length := rfl

/-- **Theorem 18.14 (Two Chains Resonance).**
    If corresponding relayers resonate and signals resonate, then
    single-relayer chain outputs resonate.

    *Diffusion of innovations*: Similar adopters receiving similar innovations
    produce similar cultural adaptations. -/
theorem two_chains_resonance {r₁ r₂ s₁ s₂ : I}
    (hr : IdeaticSpace.resonates r₁ r₂) (hs : IdeaticSpace.resonates s₁ s₂) :
    IdeaticSpace.resonates (relayChain [r₁] s₁) (relayChain [r₂] s₂) := by
  simp [relayChain, List.foldl]
  exact IdeaticSpace.resonance_compose r₁ r₂ s₁ s₂ hr hs

/-- **Theorem 18.15 (Prepending Void Relayer is No-Op).**
    Starting a chain with a void relayer doesn't change the outcome.

    *Communication theory*: An empty preamble carries no information. -/
theorem void_prepend_chain (relayers : List I) (s : I) :
    relayChain (IdeaticSpace.void :: relayers) s = relayChain relayers s := by
  simp [relayChain, List.foldl]

/-- **Theorem 18.16 (Chain Output Depth Bound — Two Relayers).**
    Two-relayer chain depth ≤ depth(r₁) + depth(r₂) + depth(s).

    *Bartlett*: Two successive retellings add at most the combined
    complexity of both retellers to the original story's depth. -/
theorem two_relay_depth_bound (r₁ r₂ s : I) :
    chainDepth [r₁, r₂] s ≤
    IdeaticSpace.depth r₁ + IdeaticSpace.depth r₂ + IdeaticSpace.depth s := by
  simp [chainDepth, two_relayer_chain]
  have h1 := depth_compose_le r₂ (IdeaticSpace.compose r₁ s)
  have h2 := depth_compose_le r₁ s
  linarith

/-- **Theorem 18.17 (Depth Zero Signal Relay).**
    Relaying a depth-zero signal through a depth-zero relayer gives depth zero.

    *Information theory*: Empty content through an empty channel yields nothing. -/
theorem depth_zero_relay {r s : I}
    (hr : IdeaticSpace.depth r = 0) (hs : IdeaticSpace.depth s = 0) :
    chainDepth [r] s = 0 := by
  simp [chainDepth, singleton_chain]
  exact depth_zero_closed hr hs

/-- **Theorem 18.18 (Chain Append Equivalence).**
    Appending a relayer to a chain = composing the relayer with the chain output.

    *Network theory*: Adding a node at the end of a path is equivalent to
    that node processing the path's accumulated output. -/
theorem chain_append (relayers : List I) (r s : I) :
    relayChain (relayers ++ [r]) s = IdeaticSpace.compose r (relayChain relayers s) := by
  simp [relayChain, List.foldl_append, List.foldl]

end IDT.Signal.Ch18
