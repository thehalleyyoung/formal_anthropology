import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 3: Best Responses and Dominance

**Core claim.** Dominance and best responses are defined with respect to a
general payoff function `u : I → ℕ` applied to composed outcomes. Payoff
measures how well the interaction outcome "resonates" with the player's goals
— NOT depth. Depth is only used as a structural bound.

## 17 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch3

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- The outcome of two strategies interacting: their composition. -/
def Outcome (s1 s2 : I) : I := IdeaticSpace.compose s1 s2

/-- Strategy a weakly dominates b against opponent under payoff u. -/
def WeaklyDominates (u : I → ℕ) (a b opponent : I) : Prop :=
  u (Outcome a opponent) ≥ u (Outcome b opponent)

/-- Strategy a strictly dominates b against opponent under payoff u. -/
def StrictlyDominates (u : I → ℕ) (a b opponent : I) : Prop :=
  u (Outcome a opponent) > u (Outcome b opponent)

/-- s is a best response among a repertoire against opponent under payoff u. -/
def BestResponseAmong (u : I → ℕ) (s opponent : I) (repertoire : List I) : Prop :=
  s ∈ repertoire ∧ ∀ (t : I), t ∈ repertoire → u (Outcome t opponent) ≤ u (Outcome s opponent)

/-- Constant payoff: indifference between all outcomes. -/
def ConstantPayoff (c : ℕ) : I → ℕ := fun _ => c

/-! ## §2. Void Outcome Theorems -/

/-- Outcome of (void, x) = x. -/
theorem void_outcome (x : I) :
    Outcome (IdeaticSpace.void : I) x = x := by
  simp [Outcome, void_left]

/-- Outcome of (x, void) = x. -/
theorem outcome_void_right (x : I) :
    Outcome x (IdeaticSpace.void : I) = x := by
  simp [Outcome, void_right]

/-- Outcome of (void, void) = void. -/
theorem void_vs_void_outcome :
    Outcome (IdeaticSpace.void : I) (IdeaticSpace.void : I) = (IdeaticSpace.void : I) := by
  simp [Outcome, void_left]

/-- Under constant payoff, void vs anything = c. -/
theorem void_constant_payoff (c : ℕ) (s : I) :
    ConstantPayoff c (Outcome (IdeaticSpace.void : I) s) = c := by
  simp [ConstantPayoff]

/-! ## §3. Dominance Theorems -/

/-- Every strategy weakly dominates itself. -/
theorem self_weakly_dominates (u : I → ℕ) (a opponent : I) :
    WeaklyDominates u a a opponent := by
  simp [WeaklyDominates]

/-- Weak dominance is transitive. -/
theorem weak_dominance_trans (u : I → ℕ) (a b c opponent : I)
    (hab : WeaklyDominates u a b opponent) (hbc : WeaklyDominates u b c opponent) :
    WeaklyDominates u a c opponent := by
  simp [WeaklyDominates] at *; omega

/-- Strict dominance implies weak dominance. -/
theorem strict_implies_weak (u : I → ℕ) (a b opponent : I)
    (h : StrictlyDominates u a b opponent) :
    WeaklyDominates u a b opponent := by
  simp [WeaklyDominates, StrictlyDominates] at *; omega

/-- Under constant payoff, no strategy dominates any other. -/
theorem constant_payoff_no_dominance (c : ℕ) (a b opponent : I) :
    WeaklyDominates (ConstantPayoff c) a b opponent := by
  simp [WeaklyDominates, ConstantPayoff]

/-- Outcome depth is always bounded by sum of strategy depths. -/
theorem outcome_depth_bounded (s1 s2 : I) :
    IdeaticSpace.depth (Outcome s1 s2) ≤ IdeaticSpace.depth s1 + IdeaticSpace.depth s2 := by
  exact depth_compose_le s1 s2

/-! ## §4. Best Response Theorems -/

/-- Best response is a member of the repertoire. -/
theorem best_response_in_repertoire (u : I → ℕ) (s opponent : I) (r : List I)
    (h : BestResponseAmong u s opponent r) :
    s ∈ r :=
  h.1

/-- In a singleton repertoire, the only element is the best response. -/
theorem singleton_best_response (u : I → ℕ) (s opponent : I) :
    BestResponseAmong u s opponent [s] := by
  constructor
  · exact List.mem_cons_self s []
  · intro t ht
    simp [List.mem_cons, List.mem_nil_iff] at ht
    rw [ht]

/-- Under constant payoff, every repertoire element is a best response. -/
theorem constant_payoff_all_best (c : ℕ) (s opponent : I) (r : List I)
    (hmem : s ∈ r) :
    BestResponseAmong (ConstantPayoff c) s opponent r := by
  constructor
  · exact hmem
  · intro t _; simp [ConstantPayoff]

/-! ## §5. Resonance and Outcome Structure -/

/-- Resonant strategies yield resonant outcomes against the same opponent. -/
theorem resonant_strategies_resonant_outcomes (a b opponent : I)
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (Outcome a opponent) (Outcome b opponent) :=
  resonance_compose_right h opponent

/-- Every outcome resonates with itself. -/
theorem outcome_resonance_refl (s1 s2 : I) :
    IdeaticSpace.resonates (Outcome s1 s2) (Outcome s1 s2) :=
  resonance_refl _

/-- Same strategy against resonant opponents yields resonant outcomes. -/
theorem resonant_opponents_resonant_outcomes (s o1 o2 : I)
    (h : IdeaticSpace.resonates o1 o2) :
    IdeaticSpace.resonates (Outcome s o1) (Outcome s o2) :=
  resonance_compose_left s h

/-- Outcome associativity: (a ∘ b) ∘ c = a ∘ (b ∘ c). -/
theorem outcome_assoc (a b c : I) :
    Outcome (Outcome a b) c = Outcome a (Outcome b c) := by
  simp [Outcome]; exact compose_assoc a b c

/-- Atomic strategy against any opponent: outcome depth ≤ 1 + opponent depth. -/
theorem atomic_outcome_bound (a opponent : I) (ha : IdeaticSpace.atomic a) :
    IdeaticSpace.depth (Outcome a opponent) ≤ 1 + IdeaticSpace.depth opponent := by
  have h1 := depth_compose_le a opponent
  have h2 := IdeaticSpace.depth_atomic a ha
  linarith

end IDT.MG.Ch3
