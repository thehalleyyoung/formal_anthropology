import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 8: Bargaining Over Composition Order

**Core claim.** Composition is non-commutative, so order matters. When two
players combine ideas, who "goes first" can change the outcome. We study
the structural properties of both orderings.

## 17 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch8

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Player 1's idea comes first. -/
def leftFirst (a b : I) : I := IdeaticSpace.compose a b

/-- Player 2's idea comes first. -/
def rightFirst (a b : I) : I := IdeaticSpace.compose b a

/-- Order invariance: both orderings give the same result. -/
def orderInvariant (a b : I) : Prop :=
  IdeaticSpace.compose a b = IdeaticSpace.compose b a

/-- Order resonance: both orderings produce resonant outcomes. -/
def orderResonant (a b : I) : Prop :=
  IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose b a)

/-- Bargaining outcome: record of both possible orderings. -/
structure BargainingOutcome (I : Type*) [IdeaticSpace I] where
  player1 : I
  player2 : I

/-! ## §2. Void Commutativity -/

/-- Void commutes on the left: void ∘ a = a ∘ void. -/
theorem void_order_invariant_left (a : I) :
    orderInvariant (IdeaticSpace.void : I) a := by
  simp [orderInvariant, void_left, void_right]

/-- Void commutes on the right: a ∘ void = void ∘ a. -/
theorem void_order_invariant_right (a : I) :
    orderInvariant a (IdeaticSpace.void : I) := by
  simp [orderInvariant, void_left, void_right]

/-- Self-composition is trivially order-invariant. -/
theorem self_order_invariant (a : I) :
    orderInvariant a a := by
  simp [orderInvariant]

/-- void ∘ void = void ∘ void = void. -/
theorem void_void_order_trivial :
    leftFirst (IdeaticSpace.void : I) (IdeaticSpace.void : I) =
    rightFirst (IdeaticSpace.void : I) (IdeaticSpace.void : I) := by
  simp [leftFirst, rightFirst, void_left]

/-- For any a, compose void a = compose a void = a. -/
theorem void_commutes_universally (a : I) :
    IdeaticSpace.compose (IdeaticSpace.void : I) a =
    IdeaticSpace.compose a (IdeaticSpace.void : I) := by
  simp [void_left, void_right]

/-! ## §3. Depth Symmetry -/

/-- Both orderings have the same depth upper bound. -/
theorem both_orders_same_depth_bound (a b : I) :
    IdeaticSpace.depth (leftFirst a b) ≤ IdeaticSpace.depth a + IdeaticSpace.depth b ∧
    IdeaticSpace.depth (rightFirst a b) ≤ IdeaticSpace.depth a + IdeaticSpace.depth b := by
  constructor
  · exact depth_compose_le a b
  · unfold rightFirst; have h := depth_compose_le b a; omega

/-- Depth bound is symmetric under reordering. -/
theorem order_depth_symmetric (a b : I) :
    IdeaticSpace.depth (rightFirst a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b := by
  unfold rightFirst
  have h := depth_compose_le b a; omega

/-- Both orderings are in the same filtration. -/
theorem bargaining_outcome_in_filtration (d : ℕ) (a b : I)
    (ha : a ∈ depthFiltration d) (hb : b ∈ depthFiltration d) :
    leftFirst a b ∈ depthFiltration (2 * d) ∧
    rightFirst a b ∈ depthFiltration (2 * d) := by
  constructor
  · exact depthFiltration_compose ha hb
  · exact depthFiltration_compose hb ha

/-! ## §4. Resonance Properties -/

/-- Any composition resonates with itself. -/
theorem order_resonant_reflexive (a b : I) :
    IdeaticSpace.resonates (leftFirst a b) (leftFirst a b) :=
  resonance_refl _

/-- If a resonates with b, then both orderings produce resonant outcomes. -/
theorem resonant_pair_both_orders (a b : I)
    (hab : IdeaticSpace.resonates a b) :
    orderResonant a b := by
  unfold orderResonant
  have hba := resonance_symm hab
  exact IdeaticSpace.resonance_compose a b b a hab hba

/-- Order invariance implies order resonance. -/
theorem order_invariant_implies_resonant (a b : I)
    (h : orderInvariant a b) : orderResonant a b := by
  unfold orderResonant
  rw [h]
  exact resonance_refl _

/-- compose a b resonates with compose a (compose b void). -/
theorem order_resonant_with_void_elaboration (a b : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose a b)
      (IdeaticSpace.compose a (IdeaticSpace.compose b (IdeaticSpace.void : I))) := by
  have : IdeaticSpace.compose b (IdeaticSpace.void : I) = b := void_right b
  rw [this]
  exact resonance_refl _

/-- Both orderings of atomic ideas have depth ≤ 2. -/
theorem atomic_bargaining_depth (a b : I)
    (ha : IdeaticSpace.atomic a) (hb : IdeaticSpace.atomic b) :
    IdeaticSpace.depth (leftFirst a b) ≤ 2 ∧
    IdeaticSpace.depth (rightFirst a b) ≤ 2 := by
  constructor
  · exact depth_atomic_compose a b ha hb
  · exact depth_atomic_compose b a hb ha

/-! ## §5. Bargaining with Void -/

/-- Bargaining with void is trivial: both orderings equal the other player's idea. -/
theorem void_bargaining_trivial (a : I) :
    leftFirst (IdeaticSpace.void : I) a = a ∧
    rightFirst (IdeaticSpace.void : I) a = a := by
  simp [leftFirst, rightFirst, void_left, void_right]

/-- Three orderings of 3 elements all have the same depth bound. -/
theorem three_orderings_depth (a b c : I) :
    IdeaticSpace.depth (IdeaticSpace.compose (IdeaticSpace.compose a b) c) ≤
      IdeaticSpace.depth a + IdeaticSpace.depth b + IdeaticSpace.depth c ∧
    IdeaticSpace.depth (IdeaticSpace.compose (IdeaticSpace.compose b a) c) ≤
      IdeaticSpace.depth a + IdeaticSpace.depth b + IdeaticSpace.depth c ∧
    IdeaticSpace.depth (IdeaticSpace.compose (IdeaticSpace.compose a c) b) ≤
      IdeaticSpace.depth a + IdeaticSpace.depth b + IdeaticSpace.depth c := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := depth_compose_le a b
    have h2 := depth_compose_le (IdeaticSpace.compose a b) c
    omega
  · have h1 := depth_compose_le b a
    have h2 := depth_compose_le (IdeaticSpace.compose b a) c
    omega
  · have h1 := depth_compose_le a c
    have h2 := depth_compose_le (IdeaticSpace.compose a c) b
    omega

/-- Depth of leftFirst equals depth of rightFirst when ideas commute. -/
theorem order_invariant_depth_eq (a b : I) (h : orderInvariant a b) :
    IdeaticSpace.depth (leftFirst a b) = IdeaticSpace.depth (rightFirst a b) := by
  unfold leftFirst rightFirst orderInvariant at *
  rw [h]

/-- Composing with void on either side gives same result. -/
theorem leftFirst_void_eq_rightFirst_void (a : I) :
    leftFirst a (IdeaticSpace.void : I) = rightFirst a (IdeaticSpace.void : I) := by
  simp [leftFirst, rightFirst, void_left, void_right]

end IDT.MG.Ch8
