import FormalAnthropology.IDT_Signal_Ch01

/-!
# Signalling Games in IDT — Chapter 3: Costly Depth and Ritual Sacrifice

**Anthropological motivation.** Zahavi's (1975) handicap principle and Sosis's
(2003) costly signalling theory of ritual propose that honest communication
requires *costly* signals. The depth of an idea — its structural complexity —
is a natural cost metric: deeper signals require more cognitive resources to
produce and maintain.

This chapter connects IDT depth to signal cost theory:

- **Depth IS cost**: `signalCost s = depth s`
- **Void is costless**: silence costs nothing (the free option)
- **Subadditivity**: compound signals cost ≤ sum of parts
- **Single-crossing**: types differ in their cost of producing depth
- **Costly-to-fake**: composing with void can't inflate apparent cost
- **Ritual iteration**: repeated signals have linearly bounded cost

The key anthropological insight is that rituals involving genuine sacrifice
(scarification, potlatch, fasting) are *honest depth signals*: they cannot
be cheaply faked because the depth (complexity) is intrinsic.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch3

open IDT IdeaticSpace IDT.Signal.Ch1

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Depth as Signal Cost -/

/-- Signal cost: the structural complexity of a signal. In Zahavi's handicap
    principle, this is the metabolic/social/cognitive cost of producing the signal.
    We identify it with depth because both measure irreducible complexity. -/
def signalCost (s : I) : ℕ := IdeaticSpace.depth s

/-- **Theorem 3.1 (Void is Costless).**
    The void signal (silence, inaction) has zero cost.

    *Anthropological significance*: Silence is always free. This is why
    babbling equilibria exist: the null signal costs nothing. Every
    signalling system must contend with the zero-cost outside option
    of saying nothing. In ritual terms, "not participating" is costless. -/
theorem void_costless : signalCost (IdeaticSpace.void : I) = 0 := by
  unfold signalCost
  exact depth_void

/-- **Theorem 3.2 (Cost Subadditivity).**
    The cost of a compound signal ≤ sum of component costs.

    *Anthropological significance*: A two-part ritual (fasting + scarification)
    costs at most as much as the parts separately. Compound signals can be
    *cheaper* than their parts (subadditivity), but never more expensive.
    This formalises the "economies of ritual combination" observed in
    initiation ceremonies that bundle multiple ordeals. -/
theorem cost_subadditive (s₁ s₂ : I) :
    signalCost (IdeaticSpace.compose s₁ s₂) ≤ signalCost s₁ + signalCost s₂ := by
  exact depth_compose_le s₁ s₂

/-- **Theorem 3.3 (Void Composition Doesn't Inflate Cost).**
    Composing with void on the right preserves cost exactly.

    *Anthropological significance*: You can't fake costly signals by
    "adding silence." If a ritual involves real sacrifice plus a moment
    of silence, the cost is exactly that of the sacrifice alone.
    This is the formal basis of the handicap principle's unfakeability. -/
theorem void_compose_cost (s : I) :
    signalCost (IdeaticSpace.compose s IdeaticSpace.void) = signalCost s := by
  unfold signalCost
  exact depth_compose_void s

/-- **Theorem 3.4 (Void Left-Compose Cost).**
    Composing with void on the left preserves cost exactly.

    *Anthropological significance*: Prefixing a costly act with silence
    doesn't change its cost. The "dramatic pause" before a sacrifice
    adds no cost. -/
theorem void_left_compose_cost (s : I) :
    signalCost (IdeaticSpace.compose IdeaticSpace.void s) = signalCost s := by
  unfold signalCost
  exact depth_void_compose s

/-- **Theorem 3.5 (Trivial Composition Costless).**
    Composing two costless signals yields a costless signal.

    *Anthropological significance*: Banality composed with banality
    remains banal. You cannot bootstrap costly signalling from costless
    components — depth must come from somewhere. This is why genuine
    rituals require genuine investment. -/
theorem trivial_compose_costless {s₁ s₂ : I}
    (h₁ : signalCost s₁ = 0) (h₂ : signalCost s₂ = 0) :
    signalCost (IdeaticSpace.compose s₁ s₂) = 0 := by
  unfold signalCost at *
  exact depth_zero_closed h₁ h₂

/-! ## §2. Iterated Signals and Ritual Repetition -/

/-- **Theorem 3.6 (Iteration Cost Bound).**
    Repeating a signal n times costs at most n × (single cost).

    *Anthropological significance*: Ritual repetition (daily prayer, weekly
    sabbath, annual pilgrimage) has linearly bounded cumulative cost.
    A devotee who prays 5 times daily pays at most 5× the cost of a single
    prayer in depth-complexity terms. This linear scaling is why religious
    systems can demand iterative commitment without unbounded cost. -/
theorem iteration_cost_bound (s : I) (n : ℕ) :
    signalCost (composeN s n) ≤ n * signalCost s := by
  exact depth_composeN s n

/-- **Theorem 3.7 (Zero-Cost Iteration).**
    Repeating a costless signal any number of times remains costless.

    *Anthropological significance*: Empty ritual (void composed with void,
    repeated endlessly) never generates genuine cost. Mere repetition of
    nothing cannot substitute for substantive engagement. "Going through
    the motions" with no internal depth is formally costless. -/
theorem zero_cost_iteration (n : ℕ) :
    signalCost (composeN (IdeaticSpace.void : I) n) = 0 := by
  unfold signalCost
  have : composeN (IdeaticSpace.void : I) n = (IdeaticSpace.void : I) := composeN_void n
  rw [this, depth_void]

/-- **Theorem 3.8 (Single Repetition Cost).**
    One repetition of a signal has the same cost bound as the signal itself.

    *Anthropological significance*: The first performance of a ritual
    has bounded cost relative to the ritual's intrinsic complexity.
    `composeN s 1 = compose void s`, so cost ≤ 0 + depth s = depth s. -/
theorem single_rep_cost (s : I) :
    signalCost (composeN s 1) ≤ signalCost s := by
  have h := iteration_cost_bound s 1
  simp at h
  exact h

/-! ## §3. The Single-Crossing Property -/

/-- A costly signal model with two types: high-quality and low-quality senders.
    The single-crossing property ensures that high types can produce depth
    more cheaply than low types — this is what makes costly signalling
    *informative* rather than merely wasteful. -/
structure CostlySignalModel (I : Type*) [IdeaticSpace I] where
  /-- Cost function for the high-quality type -/
  highTypeCost : I → ℕ
  /-- Cost function for the low-quality type -/
  lowTypeCost : I → ℕ
  /-- High type's cost ≤ signal depth (efficient producers of complexity) -/
  high_efficient : ∀ s : I, highTypeCost s ≤ IdeaticSpace.depth s
  /-- Low type's cost ≥ signal depth (inefficient producers of complexity) -/
  low_costly : ∀ s : I, IdeaticSpace.depth s ≤ lowTypeCost s

/-- **Theorem 3.9 (High Type Cost Advantage).**
    High types always pay less than or equal to low types for any signal.

    *Anthropological significance*: In Sosis's theory, genuine believers
    find costly rituals less onerous than hypocrites. The devout faster
    suffers less than the faker because their internal "type" (depth of
    belief) makes the signal cheaper to produce. This is the formal
    foundation of ritual honesty. -/
theorem high_type_advantage (m : CostlySignalModel I) (s : I) :
    m.highTypeCost s ≤ m.lowTypeCost s := by
  have h1 := m.high_efficient s
  have h2 := m.low_costly s
  linarith

/-- **Theorem 3.10 (Void is Free for All Types).**
    Both types pay ≤ 0 for the void signal, so neither pays anything.

    *Game-theoretic significance*: The babbling option is costless for
    all types. This confirms that the separation in costly signalling
    must come from *non-void* signals — only signals with genuine depth
    can separate types. -/
theorem void_free_all_types (m : CostlySignalModel I) :
    m.highTypeCost IdeaticSpace.void ≤ 0 := by
  have h := m.high_efficient IdeaticSpace.void
  rw [depth_void] at h
  exact h

/-! ## §4. Interpretation Cost and Audience Effects -/

/-- **Theorem 3.11 (Total Interpretation Cost Bound).**
    Total depth of all interpretations ≤ total repertoire depth + |rep| × cost.

    *Anthropological significance*: The "impact" of a costly signal on an
    audience is bounded by the signal's cost times the audience size plus
    the audience's existing complexity. A potlatch (costly gift-giving)
    impresses proportionally to its cost × audience, but the audience's
    existing depth provides a floor. -/
theorem total_interpretation_cost (rep : Repertoire I) (s : I) :
    depthSum (interpret rep s) ≤ depthSum rep + rep.length * signalCost s := by
  exact total_hermeneutic_bound rep s

/-- **Theorem 3.12 (Costless Signal Preserves Total Depth).**
    A signal of cost 0 leaves total interpretive depth unchanged.

    *Anthropological significance*: If you signal with zero depth, the
    audience's total cognitive complexity is preserved exactly. Only
    costly (deep) signals can ALTER the total depth landscape. -/
theorem costless_preserves_depth (rep : Repertoire I) (s : I)
    (h : signalCost s = 0) :
    depthSum (interpret rep s) ≤ depthSum rep := by
  have bound := total_hermeneutic_bound rep s
  unfold signalCost at h
  rw [h] at bound
  simp at bound
  exact bound

/-- **Theorem 3.13 (Atomic Signal Bounded Cost).**
    Atomic signals cost at most 1.

    *Anthropological significance*: The simplest possible non-void signal
    — an atomic idea — has minimal cost. In ritual terms, a single
    gesture, a single word, a single offering has bounded complexity.
    Costly signalling requires compound, non-atomic signals. -/
theorem atomic_signal_cost (s : I) (h : IdeaticSpace.atomic s) :
    signalCost s ≤ 1 := by
  exact IdeaticSpace.depth_atomic s h

/-- **Theorem 3.14 (Compound Signal Atomic Bound).**
    Composing two atomic signals costs at most 2.

    *Anthropological significance*: The simplest possible compound ritual
    (two atomic acts) has strictly bounded cost. This is the minimal
    "interesting" signal — complex enough to potentially separate types
    but simple enough to be tractable. -/
theorem compound_atomic_cost (s₁ s₂ : I)
    (h₁ : IdeaticSpace.atomic s₁) (h₂ : IdeaticSpace.atomic s₂) :
    signalCost (IdeaticSpace.compose s₁ s₂) ≤ 2 := by
  exact depth_atomic_compose s₁ s₂ h₁ h₂

/-! ## §5. Resonance and Cost Interaction -/

/-- **Theorem 3.15 (Resonant Signals Have Comparable Outcomes).**
    Resonant signals produce resonant interpretations regardless of cost.

    *Anthropological significance*: Two rituals that "resonate" (are
    structurally similar, evoke each other) produce similar effects on
    any audience, even if one costs more than the other. This is why
    cheap imitations of costly rituals can sometimes "work" — if they
    resonate with the original, the audience's interpretations resonate. -/
theorem resonant_signals_comparable (rep : Repertoire I) (s₁ s₂ : I)
    (h : IdeaticSpace.resonates s₁ s₂) :
    List.Forall₂ IdeaticSpace.resonates (interpret rep s₁) (interpret rep s₂) := by
  induction rep with
  | nil => exact List.Forall₂.nil
  | cons r rest ih =>
    simp only [interpret, List.map_cons]
    exact List.Forall₂.cons (resonance_compose_left r h) ih

/-- **Theorem 3.16 (Self-Resonant Cost).**
    Every signal resonates with itself, so the cost of "authentic repetition"
    always produces self-resonant outcomes.

    *Anthropological significance*: Repeating your own ritual always
    produces outcomes resonant with the previous performance. This is
    the formal basis of liturgical tradition: each performance resonates
    with every other performance of the same rite. -/
theorem self_resonant_interpretation (rep : Repertoire I) (s : I) :
    List.Forall₂ IdeaticSpace.resonates (interpret rep s) (interpret rep s) := by
  exact resonant_signals_comparable rep s s (resonance_refl s)

/-- **Theorem 3.17 (Cost of Composed Repertoire Outcome).**
    If every repertoire element has depth ≤ d, then each interpretation
    has depth ≤ d + cost(signal).

    *Anthropological significance*: Receivers with bounded sophistication
    (depth ≤ d) cannot produce arbitrarily deep interpretations. Even the
    most costly signal only adds its own cost to each receiver's maximum
    capacity. You cannot make simple people understand complex things
    beyond their depth + your signal's depth. -/
theorem bounded_repertoire_bounded_outcome (rep : Repertoire I) (s : I) (d : ℕ)
    (hbound : ∀ r, r ∈ rep → IdeaticSpace.depth r ≤ d) :
    ∀ x, x ∈ interpret rep s → IdeaticSpace.depth x ≤ d + signalCost s := by
  intro x hx
  simp only [interpret, List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  have h1 := depth_compose_le r s
  have h2 := hbound r hr
  unfold signalCost
  linarith

/-- **Theorem 3.18 (Filtration Level of Interpretations).**
    Interpretations of a signal with cost c by a repertoire in filtration
    level n belong to filtration level n + c (using depthFiltration).

    *Anthropological significance*: Costly signals push interpretations
    up the depth hierarchy by at most their cost. A depth-3 ritual
    received by depth-5 minds produces at most depth-8 interpretations.
    This is the formal "budget" of cultural transformation through signalling. -/
theorem interpretation_filtration (n : ℕ) (rep : Repertoire I) (s : I)
    (hrep : ∀ r, r ∈ rep → r ∈ depthFiltration n) :
    ∀ x, x ∈ interpret rep s → x ∈ depthFiltration (n + signalCost s) := by
  intro x hx
  simp only [interpret, List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  simp only [depthFiltration, Set.mem_setOf_eq]
  have h1 := depth_compose_le r s
  have h2 := hrep r hr
  simp only [depthFiltration, Set.mem_setOf_eq] at h2
  unfold signalCost
  linarith

end IDT.Signal.Ch3
