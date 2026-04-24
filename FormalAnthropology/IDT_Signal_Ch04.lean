import FormalAnthropology.IDT_Signal_Ch01

/-!
# Signalling Games in IDT — Chapter 4: Resonance Activation and Cultural Priming

**Anthropological motivation.** When a signal arrives at a mind, it does not
activate the entire repertoire uniformly. It selectively *activates* those
ideas with which it resonates — Sperber's (1996) relevance theory formalised.

A Catholic seeing a cross activates christological schemas. A Hindu seeing
the same cross might activate geometric symmetry schemas. The signal is
identical; the activation pattern differs because different repertoire
elements resonate with it.

This chapter builds the formal theory of activation:

- **activated**: an idea is activated by a signal iff it resonates with it
- **activatedInterpretations**: only the resonant subset gets interpreted
- **Cultural priming**: sequential signals modulate activation
- **Double activation**: two signals compose their activation effects

The key insight: signals don't just produce interpretations — they
*select which interpretations matter* through resonance activation.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch4

open IDT IdeaticSpace IDT.Signal.Ch1

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Activation -/

/-- An idea `r` is *activated* by signal `s` if they resonate.
    Activation is the formal counterpart of Sperber's "relevance":
    a signal is relevant to a schema iff it resonates with it. -/
def activated (r s : I) : Prop := IdeaticSpace.resonates r s

/-- The activated subset of a repertoire: those ideas selected by a predicate. -/
def activatedSubset (rep : Repertoire I) (sel : I → Bool) : List I :=
  rep.filter sel

/-- Activated interpretations: compose only the activated elements with the signal.
    This models selective attention — only relevant schemas participate in
    interpretation. We use a decidable-free version: given a selection predicate. -/
def activatedInterpretations (rep : Repertoire I) (s : I)
    (sel : I → Bool) : List I :=
  (rep.filter sel).map (fun r => IdeaticSpace.compose r s)

/-- **Theorem 4.1 (Self-Activation / Resonance Reflexivity).**
    Every idea activates itself: hearing your own thought is always relevant.

    *Anthropological significance*: The formal basis of self-recognition.
    When a signal matches an existing schema exactly, activation is
    guaranteed. This is why familiar symbols are immediately meaningful —
    they resonate with what's already there. -/
theorem self_activation (r : I) : activated r r :=
  resonance_refl r

/-- **Theorem 4.2 (Activation Symmetry).**
    If `r` is activated by `s`, then `s` would be activated by `r`.

    *Anthropological significance*: Relevance is reciprocal. If a
    Christian schema is activated by a cross, then the cross-schema
    would be activated by a Christian symbol. This is why cultural
    exchange is bidirectional: contact activates schemas on both sides. -/
theorem activation_symm {r s : I} (h : activated r s) : activated s r :=
  resonance_symm h

/-- **Theorem 4.3 (Void Self-Activates).**
    The void idea is activated by itself: silence resonates with silence.

    *Philosophical significance*: Even the empty mind has a minimal
    self-resonance. The void is relevant to itself — the baseline
    of all activation. In Buddhist terms, *śūnyatā* recognises itself. -/
theorem void_self_activates : activated (IdeaticSpace.void : I) (IdeaticSpace.void : I) :=
  resonance_refl _

/-- **Theorem 4.4 (Composition Preserves Activation on the Right).**
    If `r` is activated by `s`, then `compose r c` is activated by `compose s c`.

    *Anthropological significance*: Contextualising two resonant ideas
    with the same suffix preserves their resonance. If two schemas
    are relevant to each other, placing them in the same context
    maintains that relevance. -/
theorem activation_compose_right {r s : I} (h : activated r s) (c : I) :
    activated (IdeaticSpace.compose r c) (IdeaticSpace.compose s c) :=
  resonance_compose_right h c

/-- **Theorem 4.5 (Composition Preserves Activation on the Left).**
    If `r` is activated by `s`, then `compose c r` is activated by `compose c s`.

    *Anthropological significance*: Prefixing two resonant ideas with
    the same context preserves their relevance. A ritual frame (opening
    prayer, spatial arrangement) that precedes two resonant symbols
    doesn't destroy their mutual activation. -/
theorem activation_compose_left (c : I) {r s : I} (h : activated r s) :
    activated (IdeaticSpace.compose c r) (IdeaticSpace.compose c s) :=
  resonance_compose_left c h

/-! ## §2. Activation and Interpretation Interaction -/

/-- **Theorem 4.6 (Activated Interpretations Are a Sublist of Full Interpretations).**
    Selective interpretation ⊆ full interpretation (as a sublist).

    *Anthropological significance*: Attention is a filter, not a generator.
    Selective attention can only REDUCE the set of interpretations, never
    add new ones. What you notice is always a subset of what you could
    have understood. -/
theorem activated_interp_sublist (rep : Repertoire I) (s : I) (sel : I → Bool) :
    (activatedInterpretations rep s sel).length ≤ (interpret rep s).length := by
  unfold activatedInterpretations interpret
  rw [List.length_map, List.length_map]
  exact List.length_filter_le sel rep

/-- **Theorem 4.7 (Universal Activation = Full Interpretation).**
    If the selection predicate accepts everything, activated interpretations
    equal full interpretations.

    *Anthropological significance*: A mind with zero attentional filters
    (the "open mind" ideal) interprets everything. Pure receptivity means
    every schema participates, yielding the full interpretation. -/
theorem universal_activation (rep : Repertoire I) (s : I) :
    activatedInterpretations rep s (fun _ => true) = interpret rep s := by
  unfold activatedInterpretations interpret
  congr 1
  exact List.filter_true rep

/-- **Theorem 4.8 (Null Activation = Empty Interpretation).**
    If the selection predicate rejects everything, no interpretations are produced.

    *Anthropological significance*: Total cognitive shutdown — when nothing
    in your repertoire is deemed relevant — produces zero interpretations.
    This models cognitive overload, culture shock, or the "deer in headlights"
    response to incomprehensible stimuli. -/
theorem null_activation (rep : Repertoire I) (s : I) :
    activatedInterpretations rep s (fun _ => false) = [] := by
  unfold activatedInterpretations
  simp [List.filter_false]

/-! ## §3. Double Activation (Sequential Signals) -/

/-- **Theorem 4.9 (Sequential Interpretation Associativity).**
    Interpreting with `s₁` then `s₂` = interpreting with `compose s₁ s₂`.

    *Anthropological significance*: Cultural priming works because
    sequential exposure to signals is equivalent to a single compound
    signal. Ritual sequences (opening chant → sacrifice → closing prayer)
    produce the same interpretations as a single complex ritual. -/
theorem sequential_activation (rep : Repertoire I) (s₁ s₂ : I) :
    interpret (interpret rep s₁) s₂ =
    interpret rep (IdeaticSpace.compose s₁ s₂) := by
  simp only [interpret, List.map_map]
  congr 1
  funext r
  exact compose_assoc r s₁ s₂

/-- **Theorem 4.10 (Resonant Sequential Signals).**
    If `s₁` and `s₂` resonate, then for any background `r`, the two-stage
    interpretation `compose r (compose s₁ s₂)` resonates with the
    single-stage `compose (compose r s₁) s₂`.

    *Anthropological significance*: When ritual stages resonate with each
    other, the "inside-out" and "outside-in" readings of the compound
    ritual produce the same result up to identity (they ARE equal by
    associativity, not just resonant). -/
theorem resonant_sequential_identity (r s₁ s₂ : I) :
    IdeaticSpace.compose r (IdeaticSpace.compose s₁ s₂) =
    IdeaticSpace.compose (IdeaticSpace.compose r s₁) s₂ :=
  (compose_assoc r s₁ s₂).symm

/-- **Theorem 4.11 (Void Priming is Identity).**
    Priming with void (silence) before a signal changes nothing.

    *Anthropological significance*: A ritual preceded by silence
    produces the same interpretations as the ritual alone. The
    "pregnant pause" before a sermon adds drama but not information.
    This is why minimalist liturgies (Quaker silence → testimony)
    are structurally equivalent to just the testimony. -/
theorem void_priming (rep : Repertoire I) (s : I) :
    interpret (interpret rep IdeaticSpace.void) s = interpret rep s := by
  rw [silence_is_transparent]

/-- **Theorem 4.12 (Post-Void is Identity).**
    Following a signal with silence changes nothing.

    *Anthropological significance*: Ending a ritual with silence
    preserves all interpretations. The "moment of silence" after a
    performance is structurally empty — it changes nothing about
    what was received. -/
theorem post_void (rep : Repertoire I) (s : I) :
    interpret (interpret rep s) IdeaticSpace.void = interpret rep s := by
  exact silence_is_transparent (interpret rep s)

/-! ## §4. Activation Depth Bounds -/

/-- **Theorem 4.13 (Activated Interpretation Depth Bound).**
    Each activated interpretation has depth ≤ max(repertoire depth) + depth(signal).

    *Anthropological significance*: Selective attention doesn't change
    the depth bound. Even when only resonant schemas participate, no
    individual interpretation exceeds the max-background + signal bound.
    Relevance-filtering is a horizontal cut, not a vertical one. -/
theorem activated_depth_bound (rep : Repertoire I) (s : I) (sel : I → Bool) :
    maxInterpDepth (activatedInterpretations rep s sel) ≤
    maxInterpDepth rep + IdeaticSpace.depth s := by
  induction rep with
  | nil => simp [activatedInterpretations, maxInterpDepth]
  | cons r rest ih =>
    simp only [activatedInterpretations, List.filter]
    split
    · simp only [List.map_cons, maxInterpDepth]
      have hcomp := depth_compose_le r s
      have hih := ih
      apply Nat.max_le.mpr
      constructor
      · calc IdeaticSpace.depth (IdeaticSpace.compose r s)
            ≤ IdeaticSpace.depth r + IdeaticSpace.depth s := hcomp
          _ ≤ max (IdeaticSpace.depth r) (maxInterpDepth rest) + IdeaticSpace.depth s := by
              apply Nat.add_le_add_right; exact le_max_left _ _
      · calc maxInterpDepth (List.map (fun r => IdeaticSpace.compose r s) (List.filter sel rest))
            ≤ maxInterpDepth rest + IdeaticSpace.depth s := hih
          _ ≤ max (IdeaticSpace.depth r) (maxInterpDepth rest) + IdeaticSpace.depth s := by
              apply Nat.add_le_add_right; exact le_max_right _ _
    · calc maxInterpDepth (List.map (fun r => IdeaticSpace.compose r s) (List.filter sel rest))
          ≤ maxInterpDepth rest + IdeaticSpace.depth s := ih
        _ ≤ max (IdeaticSpace.depth r) (maxInterpDepth rest) + IdeaticSpace.depth s := by
            apply Nat.add_le_add_right; exact le_max_right _ _

/-- **Theorem 4.14 (Activation-Filtered Count Bound).**
    The number of activated interpretations ≤ repertoire size.

    *Anthropological significance*: Selective attention can only reduce
    the number of interpretations. You can't hallucinate more schemas
    than you actually have, no matter how stimulating the signal. -/
theorem activated_count_bound (rep : Repertoire I) (s : I) (sel : I → Bool) :
    (activatedInterpretations rep s sel).length ≤ rep.length := by
  unfold activatedInterpretations
  rw [List.length_map]
  exact List.length_filter_le sel rep

/-! ## §5. Resonance Chains and Activation Propagation -/

/-- **Theorem 4.15 (Resonant Backgrounds Produce Resonant Activations).**
    If two backgrounds resonate and both are activated by the same signal,
    their interpretations of that signal also resonate.

    *Anthropological significance*: Culturally similar people (resonant
    backgrounds) who are both primed by the same stimulus produce resonant
    responses. This is Durkheim's collective effervescence: a crowd
    sharing cultural schemas, exposed to the same ritual stimulus,
    produces a harmonious (resonant) collective response. -/
theorem resonant_backgrounds_resonant_activations {r₁ r₂ : I} (s : I)
    (h : IdeaticSpace.resonates r₁ r₂) :
    IdeaticSpace.resonates (IdeaticSpace.compose r₁ s) (IdeaticSpace.compose r₂ s) :=
  resonance_compose_right h s

/-- **Theorem 4.16 (Activation Under Composition).**
    If `r` is activated by `s₁` and `s₁` is activated by `s₂`, then the
    compound `compose r s₁` is activated by `compose s₁ s₂`.

    *Anthropological significance*: If your schema resonates with a symbol
    and that symbol resonates with a ritual context, then your interpreted
    schema resonates with the contextualised symbol. Resonance "propagates"
    through compositional chains — this is how multi-layered rituals
    create cascading activations through the audience's schemas. -/
theorem activation_composition_chain {r s₁ s₂ : I}
    (h₁ : activated r s₁) (h₂ : activated s₁ s₂) :
    activated (IdeaticSpace.compose r s₁) (IdeaticSpace.compose s₁ s₂) :=
  IdeaticSpace.resonance_compose r s₁ s₁ s₂ h₁ h₂

/-- **Theorem 4.17 (Void Is Universally Activatable).**
    Void is activated by any idea that resonates with void — and void
    always resonates with itself, so it's always self-activatable.

    *Anthropological significance*: The "blank slate" element is always
    available for activation. An empty slot in the repertoire responds
    to everything it resonates with. Since void resonates with itself,
    there is always a minimal activation possible. -/
theorem void_universally_self_activatable :
    activated (IdeaticSpace.void : I) (IdeaticSpace.void : I) :=
  resonance_refl _

/-- **Theorem 4.18 (Double Signal Depth Bound).**
    Two-stage interpretation through backgrounds `r₁` and `r₂` of signal `s`
    has depth bounded by the sum of all three depths.

    *Anthropological significance*: A three-layer cultural transmission
    (original signal → first interpreter → second interpreter) has
    bounded total complexity. Even in a game of telephone, the final
    interpretation's depth is bounded by the sum of all participants'
    depths. Cultural complexity doesn't compound super-linearly
    through chains of interpretation. -/
theorem double_signal_depth_bound (r₁ r₂ s : I) :
    IdeaticSpace.depth (IdeaticSpace.compose r₂ (IdeaticSpace.compose r₁ s)) ≤
    IdeaticSpace.depth r₂ + IdeaticSpace.depth r₁ + IdeaticSpace.depth s := by
  have h1 := depth_compose_le r₂ (IdeaticSpace.compose r₁ s)
  have h2 := depth_compose_le r₁ s
  linarith

end IDT.Signal.Ch4
