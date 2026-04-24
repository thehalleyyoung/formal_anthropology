import FormalAnthropology.IDT_Signal_Ch01

/-!
# Signalling Games in IDT — Chapter 2: The Signalling Problem

**Anthropological motivation.** In every human society, actors choose signals
strategically: a politician picks rhetoric, a suitor offers gifts, a priest
designs liturgy. The sender's fundamental problem is that they cannot control
how receivers will *interpret* the signal — each receiver composes the signal
with their own repertoire.

This chapter formalises the core game-theoretic structure:

- **SignallingGame**: a repertoire plus payoff functions
- **outcome**: the interpretation list produced by a signal
- **IsOptimalSignal**: no alternative yields strictly higher sender payoff
- **Babbling equilibrium**: the void signal always forms a (trivial) equilibrium
- **The Sender's Dilemma**: structural limits on what signals can achieve

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch2

open IDT IdeaticSpace IDT.Signal.Ch1

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. The Signalling Game -/

/-- A signalling game: a receiver has a repertoire, and each player gets a
    payoff from the resulting list of interpretations.
    In Spence's (1973) model, the sender is a job applicant, the signal is
    education, and the receiver's repertoire is their hiring criteria. -/
structure SignallingGame (I : Type*) [IdeaticSpace I] where
  /-- The receiver's repertoire: their stock of ideas through which they interpret -/
  repertoire : Repertoire I
  /-- Sender payoff: depends on interpretations produced in receiver's mind -/
  sender_payoff : List I → ℕ
  /-- Receiver payoff: depends on interpretations produced in their own mind -/
  receiver_payoff : List I → ℕ

/-- The outcome of sending signal `s` in game `g`: the list of interpretations
    produced in the receiver's mind. This is the *only* thing that determines payoffs. -/
def outcome (g : SignallingGame I) (s : I) : List I :=
  interpret g.repertoire s

/-- A signal is optimal for the sender if no alternative yields strictly higher payoff.
    This is the Nash equilibrium concept applied to the sender's problem. -/
def IsOptimalSignal (g : SignallingGame I) (s : I) : Prop :=
  ∀ s' : I, g.sender_payoff (outcome g s') ≤ g.sender_payoff (outcome g s)

/-- A game has a constant sender payoff: every interpretation list yields the same payoff.
    Models situations where the sender is indifferent to receiver's understanding. -/
def ConstantSenderPayoff (g : SignallingGame I) : Prop :=
  ∀ xs ys : List I, g.sender_payoff xs = g.sender_payoff ys

/-! ## §2. Babbling Equilibrium

"Silence is always an option, and sometimes the only equilibrium." -/

/-- **Theorem 2.1 (Babbling Outcome).**
    Sending void produces the original repertoire unchanged.

    *Anthropological significance*: The "babbling equilibrium" of Crawford & Sobel (1982)
    exists in every signalling game because silence is transparent — the receiver's
    mind is left exactly as it was. No signal is always a safe signal. -/
theorem babbling_outcome (g : SignallingGame I) :
    outcome g IdeaticSpace.void = g.repertoire := by
  unfold outcome
  exact silence_is_transparent g.repertoire

/-- **Theorem 2.2 (Constant Payoff Babbling Optimality).**
    If sender payoff is constant, every signal is optimal — including void.

    *Game-theoretic significance*: When the sender genuinely doesn't care what
    the receiver thinks, information transmission collapses entirely.
    This is the cheapest of cheap talk. -/
theorem constant_payoff_optimal (g : SignallingGame I) (s : I)
    (hconst : ConstantSenderPayoff g) :
    IsOptimalSignal g s := by
  intro s'
  unfold outcome
  exact le_of_eq (hconst _ _)

/-- **Theorem 2.3 (Outcome Length Invariance).**
    Every signal produces the same number of interpretations: |repertoire|.

    *Anthropological significance*: You cannot make someone think MORE thoughts
    by choosing a cleverer signal. The number of schemas activated is a fixed
    property of the receiver, not the sender. Mass media reaches N minds and
    produces exactly N interpretations, regardless of content. -/
theorem outcome_length (g : SignallingGame I) (s : I) :
    (outcome g s).length = g.repertoire.length := by
  unfold outcome
  exact interpretation_conserves_count g.repertoire s

/-- **Theorem 2.4 (Singleton Repertoire Outcome).**
    A receiver with a single idea `r` produces `[compose r s]`.

    *Anthropological significance*: The fanatic (single-idea mind) has a
    perfectly predictable interpretation of any signal. Totalitarian receivers
    are, paradoxically, the easiest to communicate with — their interpretation
    is a deterministic function of the signal. -/
theorem singleton_outcome (r s : I) :
    outcome ⟨[r], fun _ => 0, fun _ => 0⟩ s = [IdeaticSpace.compose r s] := by
  rfl

/-! ## §3. Audience Structure -/

/-- **Theorem 2.5 (Merged Audience).**
    Signalling to a combined audience = concatenation of separate outcomes.

    *Anthropological significance*: A political speech to a diverse audience
    (workers ∪ elites) produces interpretations that are the disjoint union
    of what each subgroup would have produced separately. There is no
    "synergistic" interpretation effect from mere co-presence. -/
theorem merged_audience_outcome (rep₁ rep₂ : Repertoire I) (s : I)
    (pay_s pay_r : List I → ℕ) :
    outcome ⟨rep₁ ++ rep₂, pay_s, pay_r⟩ s =
    outcome ⟨rep₁, pay_s, pay_r⟩ s ++ outcome ⟨rep₂, pay_s, pay_r⟩ s := by
  simp [outcome, interpret, List.map_append]

/-- **Theorem 2.6 (Empty Audience).**
    Signalling to no one produces nothing: the tree-falling-in-forest theorem.

    *Philosophical significance*: If nobody is there to interpret, there are
    no interpretations. A signal without a receiver is not a communicative act —
    formalising Wittgenstein's point that meaning requires use. -/
theorem empty_audience (s : I) (pay_s pay_r : List I → ℕ) :
    outcome ⟨[], pay_s, pay_r⟩ s = [] := by
  rfl

/-- **Theorem 2.7 (Blank Audience Transparency).**
    A receiver whose repertoire is all void interprets any signal as
    n copies of the signal itself.

    *Anthropological significance*: The "noble savage" fantasy — a mind
    with no cultural preconceptions — would receive every message exactly as
    sent. Cultural background IS interpretation bias. -/
theorem blank_audience (n : ℕ) (s : I) (pay_s pay_r : List I → ℕ) :
    outcome ⟨List.replicate n IdeaticSpace.void, pay_s, pay_r⟩ s =
    List.replicate n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [outcome, interpret] at ih ⊢
    simp only [List.replicate_succ, List.map_cons]
    rw [void_left]
    exact congrArg (List.cons s) ih

/-! ## §4. Depth Bounds on Outcomes -/

/-- **Theorem 2.8 (Outcome Depth Bound).**
    Total depth of outcome ≤ total repertoire depth + |rep| × depth(signal).

    *Game-theoretic significance*: The sender's capacity to inject complexity
    into the receiver's mind is linearly bounded. Deep signals cost depth but
    scale their impact with the audience size. This is why propaganda targets
    breadth (many receivers) rather than depth (one deep signal). -/
theorem outcome_depth_bound (g : SignallingGame I) (s : I) :
    depthSum (outcome g s) ≤
    depthSum g.repertoire + g.repertoire.length * IdeaticSpace.depth s := by
  exact total_hermeneutic_bound g.repertoire s

/-- **Theorem 2.9 (Void Signal Zero Cost).**
    The void signal adds zero total depth to the outcome.

    *Game-theoretic significance*: Babbling costs nothing in the depth metric.
    This is the formal reason why babbling equilibria always exist: they
    require zero investment from the sender. -/
theorem void_signal_zero_cost (g : SignallingGame I) :
    depthSum (outcome g IdeaticSpace.void) = depthSum g.repertoire := by
  unfold outcome
  exact silence_preserves_depthSum g.repertoire

/-! ## §5. Resonance in Game Outcomes -/

/-- **Theorem 2.10 (Resonant Repertoire Consensus).**
    If all elements in the repertoire resonate with a fixed idea `a`,
    then all interpretations of any signal also resonate with `compose a s`.

    *Anthropological significance*: A culturally homogeneous audience (everyone
    resonates with the same archetype) produces interpretations that all
    resonate with that archetype's interpretation. Cultural consensus is
    self-reinforcing through the signalling mechanism. -/
theorem resonant_repertoire_consensus (rep : Repertoire I) (a s : I)
    (h : ∀ r, r ∈ rep → IdeaticSpace.resonates r a) :
    ∀ x, x ∈ outcome ⟨rep, fun _ => 0, fun _ => 0⟩ s →
    IdeaticSpace.resonates x (IdeaticSpace.compose a s) := by
  intro x hx
  simp [outcome, interpret, List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  exact resonance_compose_right (h r hr) s

/-- **Theorem 2.11 (Resonant Signals Produce Resonant Outcomes).**
    If two signals resonate, the outcomes they produce in the same audience
    are element-wise resonant.

    *Anthropological significance*: Variations on a ritual theme (resonant
    signals) produce resonant sets of interpretations in any audience.
    Lévi-Strauss's "transformations" are structurally guaranteed. -/
theorem resonant_signals_resonant_outcomes
    (rep : Repertoire I) (s₁ s₂ : I)
    (hs : IdeaticSpace.resonates s₁ s₂) :
    List.Forall₂ IdeaticSpace.resonates
      (interpret rep s₁) (interpret rep s₂) := by
  induction rep with
  | nil => exact List.Forall₂.nil
  | cons r rest ih =>
    simp only [interpret, List.map_cons]
    exact List.Forall₂.cons (resonance_compose_left r hs) ih

/-! ## §6. Strategic Properties -/

/-- **Theorem 2.12 (Self-Signalling).**
    If the sender's own idea is in the receiver's repertoire and the sender's
    idea resonates with the signal, the outcome contains an interpretation
    resonant with `compose (sender_idea) signal`.

    *Game-theoretic significance*: An insider (someone whose perspective is
    represented in the audience) can always produce resonant interpretations
    by sending signals resonant with their own position. -/
theorem self_signalling {rep : Repertoire I} {sender_idea s : I}
    (hmem : sender_idea ∈ rep) :
    IdeaticSpace.compose sender_idea s ∈ outcome ⟨rep, fun _ => 0, fun _ => 0⟩ s := by
  simp [outcome, interpret, List.mem_map]
  exact ⟨sender_idea, hmem, rfl⟩

/-- **Theorem 2.13 (Composition Signal = Composed Outcome).**
    Sending `compose s₁ s₂` produces the same outcome as sending `s₂`
    to a repertoire where each element was pre-composed with `s₁`.

    *Anthropological significance*: A complex ritual (compound signal) has the
    same effect as first "priming" the audience and then delivering the second
    part. Ritual structure exploits associativity. -/
theorem composition_signal (rep : Repertoire I) (s₁ s₂ : I) :
    outcome ⟨rep, fun _ => 0, fun _ => 0⟩ (IdeaticSpace.compose s₁ s₂) =
    outcome ⟨interpret rep s₁, fun _ => 0, fun _ => 0⟩ s₂ := by
  simp only [outcome, interpret, List.map_map]
  congr 1
  funext r
  exact (compose_assoc r s₁ s₂).symm

/-- **Theorem 2.14 (Iterated Signal Decomposition).**
    The void signal is a left identity for signal composition in outcomes:
    `outcome(compose void s) = outcome(s)`.

    *Game-theoretic significance*: Prepending silence to a signal has no
    effect. You can't make a message more effective by pausing first —
    the void contributes nothing strategically. -/
theorem void_prepend_signal (rep : Repertoire I) (s : I) :
    outcome ⟨rep, fun _ => 0, fun _ => 0⟩ (IdeaticSpace.compose IdeaticSpace.void s) =
    outcome ⟨rep, fun _ => 0, fun _ => 0⟩ s := by
  simp only [outcome, interpret]
  congr 1
  funext r
  show IdeaticSpace.compose r (IdeaticSpace.compose IdeaticSpace.void s) =
       IdeaticSpace.compose r s
  rw [← compose_assoc, void_right]

/-- **Theorem 2.15 (Outcome Associativity).**
    Sequential signalling `s₁` then `s₂` through a repertoire =
    single signalling `compose s₁ s₂` through the same repertoire.

    *Anthropological significance*: Multi-stage rituals (initiation sequences,
    liturgical calendars) produce the same interpretive effect as a single
    complex ritual. Ceremonial structure is algebraically decomposable. -/
theorem sequential_signal (rep : Repertoire I) (s₁ s₂ : I) :
    interpret (interpret rep s₁) s₂ =
    interpret rep (IdeaticSpace.compose s₁ s₂) := by
  simp only [interpret, List.map_map]
  congr 1
  funext r
  exact compose_assoc r s₁ s₂

/-! ## §7. The Sender's Dilemma -/

/-- **Theorem 2.16 (Void Repertoire Element Captures Signal).**
    If the receiver has void in their repertoire, the raw signal always
    appears in the outcome, regardless of what else is in the repertoire.

    *Game-theoretic significance*: An "open-minded" receiver (one who retains
    void = pure receptivity) always captures the sender's intended signal.
    This is why intellectual humility aids communication: it provides an
    unfiltered channel alongside the culturally mediated ones. -/
theorem void_captures_signal (g : SignallingGame I) (s : I)
    (h : (IdeaticSpace.void : I) ∈ g.repertoire) :
    s ∈ outcome g s := by
  unfold outcome
  exact negative_capability h

/-- **Theorem 2.17 (MaxDepth Outcome Bound).**
    The maximum depth in any outcome is bounded by the max repertoire depth
    plus signal depth.

    *Anthropological significance*: No matter how profound a signal, the
    deepest interpretation anyone can produce is bounded by their existing
    depth plus the signal's depth. The receiver's capacity limits understanding,
    not the sender's intent — a formalisation of "you can't teach beyond
    the student's readiness." -/
theorem max_outcome_depth (g : SignallingGame I) (s : I) :
    maxInterpDepth (outcome g s) ≤
    maxInterpDepth g.repertoire + IdeaticSpace.depth s := by
  exact max_interp_depth_bound g.repertoire s

/-- **Theorem 2.18 (Payoff Invariance Under Silence).**
    Sending void yields the same payoff as if no signal were sent at all
    (i.e., the payoff of the raw repertoire).

    *Game-theoretic significance*: The babbling payoff equals the "status quo"
    payoff. This is the baseline against which all informative signals must be
    measured. A signal is worth sending only if it yields strictly more than
    silence — and silence always yields the "do nothing" payoff. -/
theorem babbling_payoff (g : SignallingGame I) :
    g.sender_payoff (outcome g IdeaticSpace.void) =
    g.sender_payoff g.repertoire := by
  rw [babbling_outcome]

end IDT.Signal.Ch2
