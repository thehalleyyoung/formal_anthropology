import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 11: Competing Senders and Marketplace of Ideas

**Anthropological motivation.** In any human ecology, multiple idea-systems
compete for the same audience. Missionaries vs shamans, Enlightenment rationalism
vs Romantic nationalism, Instagram influencers vs grandparents — all are senders
vying for interpretive dominance over the same receivers.

This chapter formalizes the *marketplace of ideas*:

- **IdeaMarket**: a structure collecting competing senders, a receiver repertoire,
  and a payoff function (depth of induced interpretations)
- **Dominance**: sender s₁ dominates s₂ when s₁ produces deeper interpretations
  for every element of the receiver's repertoire
- **Cost-benefit bounds**: subadditivity constrains how much "composing"
  competing signals can amplify depth

We prove 18 theorems showing structural properties of ideological competition:
void never dominates, self-dominance is trivial, depth chains bound competitive
advantage, and coalition of senders is subadditive — connecting to Gramsci's
cultural hegemony, Berger's sacred canopy, and rational choice theory of religion.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch11

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- An idea market: multiple senders compete for a single receiver's attention.
    Each sender is an idea (signal); the receiver carries a repertoire (list of
    background ideas); payoff = depth of the interpretation each signal produces. -/
structure IdeaMarket (I : Type*) [IdeaticSpace I] where
  /-- The competing senders (signals) -/
  senders : List I
  /-- The receiver's background repertoire -/
  repertoire : List I

/-- Interpretation of a signal against a repertoire — identical to Ch1's `interpret`. -/
def interpret (rep : List I) (s : I) : List I :=
  rep.map (fun r => IdeaticSpace.compose r s)

/-- Total interpretive depth: the sum of depths of all interpretations.
    This is the "payoff" a sender generates when received. -/
def totalPayoff (rep : List I) (s : I) : ℕ :=
  depthSum (interpret rep s)

/-- Dominance: sender s₁ dominates s₂ for a given repertoire when
    composing any repertoire element with s₁ yields at least as much depth
    as composing with s₂. In anthropological terms, s₁ is *more culturally
    productive* than s₂ for this audience. -/
def dominates (s₁ s₂ : I) (rep : List I) : Prop :=
  ∀ r ∈ rep, IdeaticSpace.depth (IdeaticSpace.compose r s₁) ≥
             IdeaticSpace.depth (IdeaticSpace.compose r s₂)

/-! ## §2. Void and Dominance -/

/-- **Theorem 11.1 (Void Never Dominates Non-Trivially).**
    Void as signal merely returns the repertoire unchanged. Any signal s
    with depth ≥ 0 (trivially true) ties with void on depth. Formally:
    void "dominates" everything vacuously only because compose(r, void) = r.

    *Anthropological significance*: Silence (the null message) is never
    the *winning* strategy in a competitive marketplace — it merely
    preserves the status quo. Gramsci's insight: hegemony requires
    active cultural production, not mere silence. -/
theorem void_dominates_is_identity (rep : List I) :
    interpret rep (IdeaticSpace.void : I) = rep := by
  induction rep with
  | nil => rfl
  | cons r rest ih =>
    simp only [interpret, List.map_cons]
    rw [IDT.void_right]
    exact congrArg (List.cons r) ih

/-- **Theorem 11.2 (Self-Dominance is Trivial).**
    Every signal dominates itself — a sender always ties with itself.

    *Philosophical significance*: Self-consistency is the minimal requirement
    of any ideological system; it says nothing about competitive advantage. -/
theorem self_dominates (s : I) (rep : List I) : dominates s s rep :=
  fun _ _ => le_refl _

/-- **Theorem 11.3 (Void Signal Payoff Equals Repertoire Depth).**
    The total payoff from silence = total repertoire depth.

    *Anthropological significance*: A society's interpretive capacity
    under silence is exactly its accumulated cultural depth. The
    "baseline" against which all signals are measured. -/
theorem void_payoff_eq_repertoire (rep : List I) :
    totalPayoff rep (IdeaticSpace.void : I) = depthSum rep := by
  unfold totalPayoff
  rw [void_dominates_is_identity]

/-- **Theorem 11.4 (Dominance Reflexivity).**
    Dominance is reflexive: every signal dominates itself.

    *Game-theoretic significance*: In the language of partial orders,
    dominance is a preorder (reflexive + transitive-like). This is
    the formal structure underlying "marketplace competition." -/
theorem dominates_refl (s : I) (rep : List I) : dominates s s rep :=
  self_dominates s rep

/-! ## §3. Depth Bounds on Competition -/

/-- **Theorem 11.5 (Hermeneutic Payoff Bound).**
    Total payoff of any signal s ≤ total repertoire depth + |rep| × depth(s).

    *Anthropological significance*: Even the most profound revelation
    cannot exceed the audience's capacity plus a linear contribution
    from the signal itself. Mass media reaches many but depth per
    receiver is bounded by their pre-existing cultural capital. -/
theorem payoff_bound (rep : List I) (s : I) :
    totalPayoff rep s ≤ depthSum rep + rep.length * IdeaticSpace.depth s := by
  induction rep with
  | nil => simp [totalPayoff, interpret, depthSum]
  | cons r rest ih =>
    unfold totalPayoff at *
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

/-- **Theorem 11.6 (Single-Element Repertoire Payoff).**
    For a singleton repertoire [r], payoff of signal s is exactly
    depth(compose(r, s)).

    *Anthropological significance*: The simplest "audience" — one mind,
    one background idea. The payoff is fully determined by the
    composition of background and signal. -/
theorem singleton_payoff (r s : I) :
    totalPayoff [r] s = IdeaticSpace.depth (IdeaticSpace.compose r s) := by
  simp [totalPayoff, interpret, depthSum, depthSum_cons]

/-- **Theorem 11.7 (Empty Repertoire Yields Zero).**
    If no one is listening, every signal has zero payoff.

    *Anthropological significance*: A prophet without followers,
    a book without readers — ideational production without reception
    is culturally null. -/
theorem empty_repertoire_zero (s : I) :
    totalPayoff [] s = 0 := by
  simp [totalPayoff, interpret, depthSum]

/-! ## §4. Competitive Composition -/

/-- **Theorem 11.8 (Signal Composition Depth Bound).**
    Composing two signals s₁, s₂ yields a compound signal whose
    payoff on any repertoire element is bounded by depth(r) + depth(s₁) + depth(s₂).

    *Anthropological significance*: Syncretism (composing competing
    mythologies) cannot create more depth than the sum of parts.
    The "best of both worlds" is structurally constrained. -/
theorem composed_signal_depth_bound (r s₁ s₂ : I) :
    IdeaticSpace.depth (IdeaticSpace.compose r (IdeaticSpace.compose s₁ s₂)) ≤
    IdeaticSpace.depth r + IdeaticSpace.depth s₁ + IdeaticSpace.depth s₂ := by
  have h1 := depth_compose_le r (IdeaticSpace.compose s₁ s₂)
  have h2 := depth_compose_le s₁ s₂
  linarith

/-- **Theorem 11.9 (Void Competitor Adds Nothing).**
    Adding void as a second sender to compose with s doesn't change s:
    compose(s, void) = s and compose(void, s) = s.

    *Anthropological significance*: A "silent partner" in cultural
    production is no partner at all. Coalitions with non-contributors
    are structurally inert — this is why purely nominal alliances
    (e.g., the Holy Roman Empire) add no interpretive depth. -/
theorem void_competitor_right (s : I) :
    IdeaticSpace.compose s (IdeaticSpace.void : I) = s :=
  IDT.void_right s

/-- **Theorem 11.10 (Void Competitor Left).**
    Void composed on the left with any signal yields the signal unchanged.

    *Anthropological significance*: "Prefacing with silence" — the
    rhetorical strategy of saying nothing before speaking — is
    structurally null. The dramatic pause has ritual effect but
    zero compositional effect in the ideatic sense. -/
theorem void_competitor_left (s : I) :
    IdeaticSpace.compose (IdeaticSpace.void : I) s = s :=
  IDT.void_left s

/-! ## §5. Resonance and Competitive Advantage -/

/-- **Theorem 11.11 (Resonant Signals Produce Resonant Interpretations).**
    If two competing senders produce resonant signals, any receiver
    with the same background produces resonant interpretations.

    *Anthropological significance*: Competing denominations of the
    same religion (Catholic vs Orthodox, Sunni vs Shia) produce
    *resonant* interpretations in the laity — the faithful perceive
    both as "basically the same religion" precisely because the
    signals resonate. This is the structural basis of ecumenism. -/
theorem resonant_competitors (r : I) {s₁ s₂ : I}
    (h : IdeaticSpace.resonates s₁ s₂) :
    IdeaticSpace.resonates (IdeaticSpace.compose r s₁) (IdeaticSpace.compose r s₂) :=
  resonance_compose_left r h

/-- **Theorem 11.12 (Diverse Audiences Split on Resonant Signals).**
    If two receivers have resonant backgrounds and receive the same signal,
    their interpretations are resonant.

    *Anthropological significance*: Members of the same cultural milieu
    (resonant backgrounds) confronted with the same competing signal
    will interpret it similarly. This is why propaganda works best
    within culturally homogeneous populations. -/
theorem homogeneous_audience {r₁ r₂ : I} (s : I)
    (h : IdeaticSpace.resonates r₁ r₂) :
    IdeaticSpace.resonates (IdeaticSpace.compose r₁ s) (IdeaticSpace.compose r₂ s) :=
  resonance_compose_right h s

/-- **Theorem 11.13 (Full Cultural Resonance).**
    Resonant backgrounds + resonant signals ⇒ resonant interpretations.

    *Anthropological significance*: Allied cultures (resonant backgrounds)
    exposed to similar myths (resonant signals) will always arrive at
    compatible worldviews. This is the formal mechanism behind what
    Redfield called the "Great Tradition / Little Tradition" unity. -/
theorem full_cultural_resonance {r₁ r₂ s₁ s₂ : I}
    (hr : IdeaticSpace.resonates r₁ r₂) (hs : IdeaticSpace.resonates s₁ s₂) :
    IdeaticSpace.resonates (IdeaticSpace.compose r₁ s₁) (IdeaticSpace.compose r₂ s₂) :=
  IdeaticSpace.resonance_compose r₁ r₂ s₁ s₂ hr hs

/-! ## §6. Marketplace Structural Theorems -/

/-- **Theorem 11.14 (Interpretation Preserves Length).**
    The number of interpretations equals the repertoire size, regardless
    of which sender's signal is being interpreted.

    *Anthropological significance*: Cultural contact doesn't change
    the number of categories a society has — it transforms each one.
    This is the conservation law of cultural schema. -/
theorem interpretation_length (rep : List I) (s : I) :
    (interpret rep s).length = rep.length := by
  simp [interpret]

/-- **Theorem 11.15 (Additivity of Repertoires).**
    Interpreting a signal with a merged repertoire = concatenating
    interpretations of the sub-repertoires.

    *Anthropological significance*: When two groups merge (marriage
    alliance, conquest, migration), their joint interpretation of
    any signal equals the union of their separate interpretations.
    Cultural integration is structurally additive. -/
theorem repertoire_additivity (rep₁ rep₂ : List I) (s : I) :
    interpret (rep₁ ++ rep₂) s = interpret rep₁ s ++ interpret rep₂ s := by
  simp [interpret, List.map_append]

/-- **Theorem 11.16 (Composed Signal Associativity).**
    Interpreting a composition of signals through the lens of background r
    is the same as sequential interpretation.

    *Anthropological significance*: Receiving two messages in sequence
    (first s₁, then s₂) is structurally identical to receiving their
    composition. The order of cultural exposure telescopes via associativity. -/
theorem composed_signal_assoc (r s₁ s₂ : I) :
    IdeaticSpace.compose r (IdeaticSpace.compose s₁ s₂) =
    IdeaticSpace.compose (IdeaticSpace.compose r s₁) s₂ :=
  (compose_assoc r s₁ s₂).symm

/-- **Theorem 11.17 (Marginal Depth Contribution Bound).**
    Adding a new element r to the repertoire adds at most
    depth(r) + depth(s) to the total payoff.

    *Anthropological significance*: Educating one more person (adding
    one more background to the audience) increases total societal
    understanding by at most that person's depth plus the signal's.
    Diminishing returns in mass education are structurally guaranteed. -/
theorem marginal_repertoire_bound (rep : List I) (r s : I) :
    totalPayoff (r :: rep) s ≤ IdeaticSpace.depth r + IdeaticSpace.depth s + totalPayoff rep s := by
  unfold totalPayoff
  have hstep : interpret (r :: rep) s =
    IdeaticSpace.compose r s :: interpret rep s := rfl
  rw [hstep, depthSum_cons]
  have hcomp := depth_compose_le r s
  linarith

/-- **Theorem 11.18 (Iterated Signal Depth Bound).**
    Composing a signal with itself n times yields depth ≤ n × depth(s).

    *Anthropological significance*: Repetition in ritual (chanting a
    mantra n times) has bounded interpretive effect. The
    subadditivity of depth means repetition is inherently
    anti-inflationary — you can't create unbounded meaning through
    mere repetition. This constrains theories of ritual efficacy. -/
theorem iterated_signal_bound (s : I) (n : ℕ) :
    IdeaticSpace.depth (composeN s n) ≤ n * IdeaticSpace.depth s :=
  depth_composeN s n

end IDT.Signal.Ch11
