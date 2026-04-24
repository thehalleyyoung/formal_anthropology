import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 6: The Composition Dilemma

**Core claim.** Two-player games where each player chooses to contribute an idea
or play void. This creates a template for studying cooperation vs. defection
through composition.

## 18 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch6

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Both players contribute: full cooperation. -/
def CooperateOutcome (a b : I) : I := IdeaticSpace.compose a b

/-- Player 1 defects (plays void), player 2 contributes. -/
def DefectLeft (b : I) : I := b

/-- Player 2 defects (plays void), player 1 contributes. -/
def DefectRight (a : I) : I := a

/-- Both defect: mutual defection. -/
def MutualDefect : I := (IdeaticSpace.void : I)

/-- A composition dilemma: each player has an idea but may choose void. -/
structure CompositionDilemma (I : Type*) [IdeaticSpace I] where
  player1_idea : I
  player2_idea : I

/-! ## §2. Depth Properties of Outcomes -/

/-- Cooperation depth is bounded by sum of individual depths. -/
theorem cooperate_depth_bound (a b : I) :
    IdeaticSpace.depth (CooperateOutcome a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b :=
  depth_compose_le a b

/-- When player 1 defects, depth equals player 2's depth. -/
theorem defect_left_depth (b : I) :
    IdeaticSpace.depth (DefectLeft b) = IdeaticSpace.depth b := rfl

/-- When player 2 defects, depth equals player 1's depth. -/
theorem defect_right_depth (a : I) :
    IdeaticSpace.depth (DefectRight a) = IdeaticSpace.depth a := rfl

/-- Mutual defection has depth 0. -/
theorem mutual_defect_depth_zero :
    IdeaticSpace.depth (MutualDefect : I) = 0 := depth_void

/-- Cooperation outcome resonates with itself. -/
theorem cooperate_resonates_with_self (a b : I) :
    IdeaticSpace.resonates (CooperateOutcome a b) (CooperateOutcome a b) :=
  resonance_refl _

/-- Cooperating with void on the right = defection (player 2 defects). -/
theorem cooperate_void_right_eq_defect_right (a : I) :
    CooperateOutcome a (IdeaticSpace.void : I) = DefectRight a := by
  simp [CooperateOutcome, DefectRight, void_right]

/-- Cooperating with void on the left = defection (player 1 defects). -/
theorem cooperate_void_left_eq_defect_left (b : I) :
    CooperateOutcome (IdeaticSpace.void : I) b = DefectLeft b := by
  simp [CooperateOutcome, DefectLeft, void_left]

/-! ## §3. Ordering and Filtration -/

/-- Mutual defect depth (0) is ≤ any cooperation depth. -/
theorem dilemma_depth_ordering (a b : I) :
    IdeaticSpace.depth (MutualDefect : I) ≤
    IdeaticSpace.depth (CooperateOutcome a b) := by
  simp [MutualDefect, depth_void]

/-- Three-player cooperation depth bound. -/
theorem three_player_dilemma_depth (a b c : I) :
    IdeaticSpace.depth (IdeaticSpace.compose (IdeaticSpace.compose a b) c) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + IdeaticSpace.depth c := by
  have h1 := depth_compose_le a b
  have h2 := depth_compose_le (IdeaticSpace.compose a b) c
  omega

/-- If ideas resonate pairwise, cooperation outcomes resonate. -/
theorem dilemma_resonance_preserved (a a' b b' : I)
    (ha : IdeaticSpace.resonates a a') (hb : IdeaticSpace.resonates b b') :
    IdeaticSpace.resonates (CooperateOutcome a b) (CooperateOutcome a' b') := by
  exact IdeaticSpace.resonance_compose a a' b b' ha hb

/-- If both ideas are in filtration d, cooperation is in filtration 2*d. -/
theorem cooperation_in_filtration (d : ℕ) (a b : I)
    (ha : a ∈ depthFiltration d) (hb : b ∈ depthFiltration d) :
    CooperateOutcome a b ∈ depthFiltration (2 * d) := by
  exact depthFiltration_compose ha hb

/-- Defecting player's idea stays in its filtration level. -/
theorem defection_in_filtration (d : ℕ) (a : I) (ha : a ∈ depthFiltration d) :
    DefectRight a ∈ depthFiltration d := ha

/-! ## §4. Atomic and Iterated Properties -/

/-- Two atomic ideas cooperating gives depth ≤ 2. -/
theorem atomic_cooperation_bound (a b : I)
    (ha : IdeaticSpace.atomic a) (hb : IdeaticSpace.atomic b) :
    IdeaticSpace.depth (CooperateOutcome a b) ≤ 2 :=
  depth_atomic_compose a b ha hb

/-- n rounds of cooperation with same idea: depth bounded by n * depth a. -/
theorem iterated_cooperation_depth (a : I) (n : ℕ) :
    IdeaticSpace.depth (composeN a n) ≤ n * IdeaticSpace.depth a :=
  depth_composeN a n

/-- Void adds nothing: composing void with b gives same depth as b. -/
theorem void_is_costless_defection (b : I) :
    IdeaticSpace.depth (CooperateOutcome (IdeaticSpace.void : I) b) =
    IdeaticSpace.depth b := by
  simp [CooperateOutcome, void_left]

/-- If b resonates with c, then cooperation of (a,b) resonates with cooperation of (a,c). -/
theorem cooperation_resonance_propagation (a b c : I)
    (hbc : IdeaticSpace.resonates b c) :
    IdeaticSpace.resonates (CooperateOutcome a b) (CooperateOutcome a c) := by
  unfold CooperateOutcome
  exact resonance_compose_left a hbc

/-- Both playing void is just void. -/
theorem mutual_defect_is_void :
    CooperateOutcome (IdeaticSpace.void : I) (IdeaticSpace.void : I) =
    (MutualDefect : I) := by
  simp [CooperateOutcome, MutualDefect, void_left]

/-- Defection is depth-asymmetric: left and right defections have different depths in general.
    We state the precise claim: each defection depth equals the contributing player's depth. -/
theorem defection_asymmetry (a b : I) :
    IdeaticSpace.depth (DefectLeft b) = IdeaticSpace.depth b ∧
    IdeaticSpace.depth (DefectRight a) = IdeaticSpace.depth a :=
  ⟨rfl, rfl⟩

end IDT.MG.Ch6
