import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 17: Bargaining Over Composition Order

**Anthropological motivation.** Composition in IDT is associative but NOT
commutative. `compose a b ≠ compose b a` in general. This asymmetry is
fundamental: who speaks first shapes the meaning of the entire exchange.

In Victor Turner's analysis of ritual process, the *order* of ritual stages
determines the transformation undergone by participants. In political discourse,
agenda-setting power — the ability to determine what is discussed first —
is a primary form of control.

This chapter formalizes:

- **compositionOrder**: the pair of both orderings
- **orderInvariant**: the rare case where order doesn't matter
- Depth bounds hold for BOTH orders (subadditivity is symmetric)
- Resonance between the two orderings
- Associativity means tripartite bargaining brackets don't matter

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch17

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- The composition order pair: `(compose a b, compose b a)`.
    This captures both possible sequencings of a bilateral exchange.
    In bargaining theory, this is the pair of "I go first" vs "you go first." -/
def compositionOrder (a b : I) : I × I :=
  (IdeaticSpace.compose a b, IdeaticSpace.compose b a)

/-- Order invariance: when the order of composition doesn't matter.
    This is a strong condition — most idea-compositions are NOT order-invariant.
    When it holds, there is no "agenda-setting advantage." -/
def orderInvariant (a b : I) : Prop :=
  IdeaticSpace.compose a b = IdeaticSpace.compose b a

/-- An order pair: tracks both compositions and whether they're equal. -/
structure OrderPair (I : Type*) [IdeaticSpace I] where
  left : I
  right : I
  first : I
  second : I
  ab_eq : first = IdeaticSpace.compose left right
  ba_eq : second = IdeaticSpace.compose right left

/-! ## §2. Fundamental Order Theorems -/

/-- **Theorem 17.1 (Void is Order-Invariant — Left).**
    Void commutes with everything: `compose void a = compose a void`.

    *Political theory*: Silence has no agenda-setting power.
    Whether you speak into silence or silence follows your speech,
    the result is the same — just your speech. -/
theorem void_order_invariant (a : I) : orderInvariant IdeaticSpace.void a := by
  simp [orderInvariant]

/-- **Theorem 17.2 (Self-Composition is Order-Invariant).**
    `compose a a = compose a a` trivially.

    *Psychology*: Internal dialogue with yourself has no ordering problem —
    you always agree with yourself on what comes first. -/
theorem self_order_invariant (a : I) : orderInvariant a a := by
  simp [orderInvariant]

/-- **Theorem 17.3 (Both Orders Have Same Depth Bound).**
    `depth(compose a b) ≤ depth a + depth b` AND
    `depth(compose b a) ≤ depth a + depth b`.

    *Game theory*: The "cost" of an exchange (measured by depth) is bounded
    the same way regardless of who goes first. Subadditivity is symmetric. -/
theorem both_orders_depth_bound (a b : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤ IdeaticSpace.depth a + IdeaticSpace.depth b ∧
    IdeaticSpace.depth (IdeaticSpace.compose b a) ≤ IdeaticSpace.depth a + IdeaticSpace.depth b := by
  constructor
  · exact depth_compose_le a b
  · have h := depth_compose_le b a; linarith

/-- **Theorem 17.4 (Composition Order First Component).**
    The first component of `compositionOrder` is `compose a b`.

    *Technical lemma*: Extracting the "a-goes-first" ordering. -/
theorem order_fst (a b : I) :
    (compositionOrder a b).1 = IdeaticSpace.compose a b := rfl

/-- **Theorem 17.5 (Composition Order Second Component).**
    The second component of `compositionOrder` is `compose b a`.

    *Technical lemma*: Extracting the "b-goes-first" ordering. -/
theorem order_snd (a b : I) :
    (compositionOrder a b).2 = IdeaticSpace.compose b a := rfl

/-- **Theorem 17.6 (Both Orders Self-Resonate).**
    Each ordering resonates with itself.

    *Hermeneutics*: Any completed exchange achieves internal coherence
    regardless of who spoke first. -/
theorem both_orders_self_resonate (a b : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose a b) ∧
    IdeaticSpace.resonates (IdeaticSpace.compose b a) (IdeaticSpace.compose b a) :=
  ⟨resonance_refl _, resonance_refl _⟩

/-- **Theorem 17.7 (Resonant Inputs Give Resonant Orders).**
    If `a` resonates with `b`, then `compose a b` resonates with `compose b a`.

    *Turner's ritual process*: When ritual actors are in resonance (communitas),
    reordering the ritual stages produces ceremonies that still "rhyme" with
    each other — the spirit of the ritual is preserved even if the sequence changes. -/
theorem resonant_orders {a b : I} (hab : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose b a) := by
  exact IdeaticSpace.resonance_compose a b b a hab (resonance_symm hab)

/-- **Theorem 17.8 (Order Invariance of Void Pair).**
    Void composed with void is order-invariant.

    *Logic*: Two silences are the same regardless of which comes first. -/
theorem void_void_invariant : orderInvariant (IdeaticSpace.void : I) IdeaticSpace.void := by
  simp [orderInvariant]

/-- **Theorem 17.9 (Associativity Resolves Three-Party Brackets).**
    In a three-party bargaining, the bracketing doesn't matter.

    *Negotiation theory*: Whether (A,B) form a coalition first and then
    bargain with C, or A bargains with a (B,C) coalition, the final
    composite meaning is identical. Associativity is the great equalizer. -/
theorem three_party_bracket_invariance (a b c : I) :
    IdeaticSpace.compose (IdeaticSpace.compose a b) c =
    IdeaticSpace.compose a (IdeaticSpace.compose b c) := by
  exact compose_assoc a b c

/-- **Theorem 17.10 (Depth Bound Under Reordering).**
    Reordering a pair doesn't affect the depth bound.

    *Information theory*: The maximum information capacity of an exchange
    is invariant under reordering — it's always ≤ depth(a) + depth(b). -/
theorem depth_reorder_bound (a b : I) :
    IdeaticSpace.depth (IdeaticSpace.compose b a) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b := by
  have h := depth_compose_le b a; linarith

/-- **Theorem 17.11 (Order Invariance is Symmetric).**
    If `a` is order-invariant with `b`, then `b` is order-invariant with `a`.

    *Social contract theory*: If swapping the order of A and B's contributions
    doesn't matter, then swapping B and A's doesn't matter either. -/
theorem order_invariant_symm {a b : I} (h : orderInvariant a b) :
    orderInvariant b a := by
  simp [orderInvariant]; exact h.symm

/-- **Theorem 17.12 (Void is Universally Order-Invariant).**
    Void commutes with everything: `compose a void = compose void a` for all `a`.

    *Silence*: The absence of contribution never creates ordering conflicts. -/
theorem void_universal_order_invariant (a : I) :
    orderInvariant a IdeaticSpace.void := by
  simp [orderInvariant]

/-- **Theorem 17.13 (Triple Depth Bound — Both Bracketings).**
    Regardless of how three ideas are bracketed, depth is bounded by the sum.

    *Organizational theory*: Three-way collaboration has bounded complexity
    no matter how sub-teams are formed. -/
theorem triple_depth_bound (a b c : I) :
    IdeaticSpace.depth (IdeaticSpace.compose (IdeaticSpace.compose a b) c) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + IdeaticSpace.depth c := by
  have h1 := depth_compose_le (IdeaticSpace.compose a b) c
  have h2 := depth_compose_le a b
  linarith

/-- **Theorem 17.14 (Order Pair Construction).**
    We can always construct an order pair from any two ideas.

    *Methodological*: Every bilateral exchange can be formally analyzed
    by examining both possible orderings. -/
theorem order_pair_exists (a b : I) :
    ∃ (p : OrderPair I), p.left = a ∧ p.right = b :=
  ⟨⟨a, b, IdeaticSpace.compose a b, IdeaticSpace.compose b a, rfl, rfl⟩, rfl, rfl⟩

/-- **Theorem 17.15 (Resonance Between Reordered Triples).**
    If all pairs resonate, both bracketings of the triple resonate with each other.

    *Turner*: When all ritual participants are in communitas, rearranging
    the ritual order produces ceremonies that deeply resonate. -/
theorem triple_reorder_resonance {a b c : I}
    (hab : IdeaticSpace.resonates a b) (hbc : IdeaticSpace.resonates b c) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose (IdeaticSpace.compose a b) c)
      (IdeaticSpace.compose a (IdeaticSpace.compose b c)) := by
  rw [compose_assoc]
  exact resonance_refl _

/-- **Theorem 17.16 (Depth Zero Invariance Under Order).**
    If both ideas have depth 0, the composition has depth 0 in either order.

    *Critical theory*: Trivial exchanges are trivial regardless of who goes first.
    You can't create depth by reordering banalities. -/
theorem depth_zero_both_orders {a b : I}
    (ha : IdeaticSpace.depth a = 0) (hb : IdeaticSpace.depth b = 0) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) = 0 ∧
    IdeaticSpace.depth (IdeaticSpace.compose b a) = 0 :=
  ⟨depth_zero_closed ha hb, depth_zero_closed hb ha⟩

/-- **Theorem 17.17 (Composition Order Swap is Involution).**
    Swapping the order pair twice returns to the original.

    *Dialectics*: The dialectical reversal of a reversal returns to the thesis. -/
theorem order_swap_involution (a b : I) :
    compositionOrder b a = ((compositionOrder a b).2, (compositionOrder a b).1) := by
  simp [compositionOrder]

/-- **Theorem 17.18 (Void Annihilates Order Difference).**
    When one party contributes void, the order difference collapses.

    *Game theory*: A player who contributes nothing has no bargaining
    power over ordering — there is nothing to order. -/
theorem void_annihilates_order (a : I) :
    (compositionOrder a IdeaticSpace.void).1 = (compositionOrder a IdeaticSpace.void).2 := by
  simp [compositionOrder]

end IDT.Signal.Ch17
