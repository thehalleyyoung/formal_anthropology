import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 11: Agreement Games and Coordination

**Core claim.** An "agreement game" is one where two players each choose an idea
and BOTH benefit when the composed outcome resonates with BOTH their original
ideas. This models coordination problems — agreeing on a meeting place, a shared
meaning, or a joint plan.

**Critical design principle**: Payoff is NOT depth. Utility comes from
**agreement** = **resonance**. "Having the same idea" means your idea resonates
with the other person's interpretation.

## 17 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch11

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Mutual agreement: both players see their idea reflected in the joint outcome. -/
def MutualAgreement (a b : I) : Prop :=
  IdeaticSpace.resonates a (IdeaticSpace.compose a b) ∧
  IdeaticSpace.resonates b (IdeaticSpace.compose a b)

/-- Coordination success: the simplest form — the two ideas resonate directly. -/
def CoordinationSuccess (a b : I) : Prop := IdeaticSpace.resonates a b

/-- The coordinated outcome: the joint composition of both ideas. -/
def CoordinatedOutcome (a b : I) : I := IdeaticSpace.compose a b

/-- Self-coordination: coordinating with yourself always works. -/
def SelfCoordination (a : I) : Prop :=
  IdeaticSpace.resonates a (IdeaticSpace.compose a a)

/-! ## §2. Basic Coordination Properties -/

/-- Theorem 1: Coordination is reflexive — you always agree with yourself. -/
theorem coordination_reflexive (a : I) : CoordinationSuccess a a :=
  resonance_refl a

/-- Theorem 2: Coordination is symmetric — if A agrees with B, B agrees with A. -/
theorem coordination_symmetric (a b : I) (h : CoordinationSuccess a b) :
    CoordinationSuccess b a :=
  resonance_symm h

/-- Theorem 3: Void coordinates with void — silence agrees with silence. -/
theorem void_void_coordination :
    CoordinationSuccess (IdeaticSpace.void : I) (IdeaticSpace.void : I) :=
  resonance_refl _

/-- Theorem 4: Coordinated outcomes resonate when inputs do.
    If a↔c and b↔d, then (a∘c) resonates with (b∘d). -/
theorem coordinated_outcomes_resonate (a b c d : I)
    (hac : CoordinationSuccess a c) (hbd : CoordinationSuccess b d) :
    IdeaticSpace.resonates (CoordinatedOutcome a b) (CoordinatedOutcome c d) :=
  IdeaticSpace.resonance_compose a c b d hac hbd

/-! ## §3. Void as Identity Coordinator -/

/-- Theorem 5a: The coordinated outcome with void on the left is the idea itself. -/
@[simp] theorem coordination_void_left (a : I) :
    CoordinatedOutcome (IdeaticSpace.void : I) a = a :=
  void_left a

/-- Theorem 5b: The coordinated outcome with void on the right is the idea itself. -/
@[simp] theorem coordination_void_right (a : I) :
    CoordinatedOutcome a (IdeaticSpace.void : I) = a :=
  void_right a

/-- Theorem 6: Coordination is preserved under right context.
    If a and b agree, they still agree when composed with the same idea. -/
theorem coordination_preserves_under_right_context (a b c : I)
    (h : CoordinationSuccess a b) :
    CoordinationSuccess (IdeaticSpace.compose a c) (IdeaticSpace.compose b c) :=
  resonance_compose_right h c

/-- Theorem 7: Coordination is preserved under left context.
    If a and b agree, they still agree when preceded by the same idea. -/
theorem coordination_preserves_under_left_context (a b c : I)
    (h : CoordinationSuccess a b) :
    CoordinationSuccess (IdeaticSpace.compose c a) (IdeaticSpace.compose c b) :=
  resonance_compose_left c h

/-! ## §4. Mutual Agreement -/

/-- Theorem 8: Mutual agreement from void-resonance.
    If void resonates with both a and b, then both see their ideas in the outcome.
    Proof: a = void∘a, so resonates a (a∘b) follows from resonance_compose
    applied to (void↔a) and (a↔b) after rewriting. -/
theorem mutual_agreement_via_void_resonance (a b : I)
    (hva : IdeaticSpace.resonates (IdeaticSpace.void : I) a)
    (hvb : IdeaticSpace.resonates (IdeaticSpace.void : I) b) :
    MutualAgreement a b := by
  constructor
  · -- resonates a (compose a b)
    have h := IdeaticSpace.resonance_compose a a (IdeaticSpace.void : I) b (resonance_refl a) hvb
    simp at h; exact h
  · -- resonates b (compose a b)
    have h := IdeaticSpace.resonance_compose (IdeaticSpace.void : I) a b b hva (resonance_refl b)
    simp at h; exact h

/-- Theorem 9: Self-coordination from void-resonance.
    If void resonates with a, then a resonates with a∘a. -/
theorem self_coordination_via_void (a : I)
    (hva : IdeaticSpace.resonates (IdeaticSpace.void : I) a) :
    SelfCoordination a := by
  unfold SelfCoordination
  have h := IdeaticSpace.resonance_compose a a (IdeaticSpace.void : I) a (resonance_refl a) hva
  simp at h; exact h

/-- Theorem 10: The coordinated outcome always self-resonates.
    Any composition resonates with itself — the outcome agrees with itself. -/
theorem outcome_always_self_resonates (a b : I) :
    IdeaticSpace.resonates (CoordinatedOutcome a b) (CoordinatedOutcome a b) :=
  resonance_refl _

/-- Theorem 11: If a and b agree, then both orderings of their composition resonate.
    compose a b resonates with compose b a. -/
theorem coordinated_pair_both_orders_resonate (a b : I)
    (hab : CoordinationSuccess a b) :
    IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose b a) :=
  IdeaticSpace.resonance_compose a b b a hab (resonance_symm hab)

/-! ## §5. Depth Bounds and Structure -/

/-- Theorem 12: The depth of a coordinated outcome is bounded by the sum
    of the individual depths. Structural property, NOT payoff. -/
theorem coordination_depth_bound (a b : I) :
    IdeaticSpace.depth (CoordinatedOutcome a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b :=
  depth_compose_le a b

/-- Theorem 13: When both inputs are atomic, the outcome has depth ≤ 2. -/
theorem atomic_coordination_depth (a b : I)
    (ha : IdeaticSpace.atomic a) (hb : IdeaticSpace.atomic b) :
    IdeaticSpace.depth (CoordinatedOutcome a b) ≤ 2 := by
  unfold CoordinatedOutcome
  have h1 := IdeaticSpace.depth_atomic a ha
  have h2 := IdeaticSpace.depth_atomic b hb
  have h3 := depth_compose_le a b
  omega

/-- Theorem 14: Void is a neutral coordinator — composing with void changes nothing. -/
theorem void_is_neutral_coordinator (a : I) :
    IdeaticSpace.compose (IdeaticSpace.void : I) a = a ∧
    IdeaticSpace.compose a (IdeaticSpace.void : I) = a :=
  ⟨void_left a, void_right a⟩

/-! ## §6. Chains and Replication -/

/-- Theorem 15: Coordination chain via mediator.
    If a↔b and b↔c, then (a∘b) resonates with (b∘c). -/
theorem coordination_chain (a b c : I)
    (hab : CoordinationSuccess a b) (hbc : CoordinationSuccess b c) :
    IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose b c) :=
  resonance_via_mediator hab hbc

/-- Theorem 16: Any n-fold self-composition self-resonates.
    Repetition always agrees with itself. -/
theorem replicate_coordination (a : I) (n : ℕ) :
    IdeaticSpace.resonates (composeN a n) (composeN a n) :=
  resonance_refl _

/-- Theorem 17: Coordinated outcomes of bounded-depth ideas stay in
    the appropriate depth filtration. -/
theorem coordination_filtration (a b : I) (n : ℕ)
    (ha : a ∈ depthFiltration n) (hb : b ∈ depthFiltration n) :
    CoordinatedOutcome a b ∈ depthFiltration (2 * n) :=
  depthFiltration_compose ha hb

end IDT.MG.Ch11
