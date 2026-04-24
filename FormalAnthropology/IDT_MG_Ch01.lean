import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 1: Ideas as Strategies

**Core claim.** In the Meaning Game, strategies ARE ideas. Two players each
choose an idea from an ideatic space, and the *outcome* is the composition
of their choices. This is the simplest game-theoretic structure on ideatic
space: no payoff function yet, just the act of combining two players'
contributions into a joint meaning.

## Definitions

- `strategy_outcome s1 s2` — the composition of two players' ideas
- `Profile` — a pair of strategies (ideas)

## 18 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch1

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- The outcome of two players composing their chosen ideas. -/
def strategy_outcome (s1 s2 : I) : I := IdeaticSpace.compose s1 s2

/-- A strategy profile: the pair of ideas chosen by two players. -/
structure Profile (I : Type*) [IdeaticSpace I] where
  player1 : I
  player2 : I

/-- The outcome of a profile. -/
def Profile.outcome (p : Profile I) : I :=
  strategy_outcome p.player1 p.player2

/-! ## §2. Void Strategy Theorems -/

/-- Playing void doesn't change the other player's idea (left). -/
theorem void_strategy_identity_left (s : I) :
    strategy_outcome (IdeaticSpace.void : I) s = s := by
  simp [strategy_outcome, void_left]

/-- Playing void doesn't change the other player's idea (right). -/
theorem void_strategy_identity_right (s : I) :
    strategy_outcome s (IdeaticSpace.void : I) = s := by
  simp [strategy_outcome, void_right]

/-- Both playing void yields void. -/
theorem void_void_outcome :
    strategy_outcome (IdeaticSpace.void : I) (IdeaticSpace.void : I) =
    (IdeaticSpace.void : I) := by
  simp [strategy_outcome, void_left]

/-- If player 1 plays void, outcome = player 2's idea. -/
theorem outcome_void_left_player (s2 : I) :
    (Profile.mk (IdeaticSpace.void : I) s2).outcome = s2 := by
  simp [Profile.outcome, strategy_outcome, void_left]

/-- If player 2 plays void, outcome = player 1's idea. -/
theorem outcome_void_right_player (s1 : I) :
    (Profile.mk s1 (IdeaticSpace.void : I)).outcome = s1 := by
  simp [Profile.outcome, strategy_outcome, void_right]

/-! ## §3. Depth Bounds -/

/-- Depth of outcome ≤ sum of strategy depths. -/
theorem outcome_depth_bound (s1 s2 : I) :
    IdeaticSpace.depth (strategy_outcome s1 s2) ≤
    IdeaticSpace.depth s1 + IdeaticSpace.depth s2 := by
  exact depth_compose_le s1 s2

/-- If both play depth-0 ideas, outcome has depth 0. -/
theorem outcome_depth_zero_requires_zero (s1 s2 : I)
    (h1 : IdeaticSpace.depth s1 = 0) (h2 : IdeaticSpace.depth s2 = 0) :
    IdeaticSpace.depth (strategy_outcome s1 s2) = 0 := by
  unfold strategy_outcome
  exact depth_zero_closed h1 h2

/-- With 3 sequential players, depth ≤ sum of all three. -/
theorem three_player_depth_bound (s1 s2 s3 : I) :
    IdeaticSpace.depth (IdeaticSpace.compose (strategy_outcome s1 s2) s3) ≤
    IdeaticSpace.depth s1 + IdeaticSpace.depth s2 + IdeaticSpace.depth s3 := by
  have h1 := depth_compose_le (strategy_outcome s1 s2) s3
  have h2 := outcome_depth_bound s1 s2
  omega

/-- Compound strategy (compose s1 s2) depth bounded. -/
theorem compound_strategy_depth (s1 s2 : I) :
    IdeaticSpace.depth (IdeaticSpace.compose s1 s2) ≤
    IdeaticSpace.depth s1 + IdeaticSpace.depth s2 :=
  depth_compose_le s1 s2

/-! ## §4. Associativity / Sequential Play -/

/-- Three sequential plays associate: (s1·s2)·s3 = s1·(s2·s3). -/
theorem sequential_play_assoc (s1 s2 s3 : I) :
    strategy_outcome (strategy_outcome s1 s2) s3 =
    strategy_outcome s1 (strategy_outcome s2 s3) := by
  simp [strategy_outcome]
  exact compose_assoc s1 s2 s3

/-- Composing two strategies yields another strategy (closure — trivially true
    since strategies are just elements of I). -/
theorem strategy_compose_is_strategy (s1 s2 : I) :
    ∃ (s : I), s = strategy_outcome s1 s2 :=
  ⟨strategy_outcome s1 s2, rfl⟩

/-! ## §5. Resonance Theorems -/

/-- If strategies resonate, so do outcomes when elaborated with same context. -/
theorem outcome_resonance_from_strategies (s1 s2 c : I)
    (h : IdeaticSpace.resonates s1 s2) :
    IdeaticSpace.resonates (IdeaticSpace.compose s1 c)
                           (IdeaticSpace.compose s2 c) :=
  resonance_compose_right h c

/-- If outcome resonates with x, elaborated outcome resonates with elaborated x. -/
theorem outcome_resonance_preserved_left (s1 s2 x c : I)
    (h : IdeaticSpace.resonates (strategy_outcome s1 s2) x) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose (strategy_outcome s1 s2) c)
      (IdeaticSpace.compose x c) :=
  resonance_compose_right h c

/-- Right variant: if outcome resonates with x, elaborated outcome resonates. -/
theorem outcome_resonance_preserved_right (s1 s2 x c : I)
    (h : IdeaticSpace.resonates (strategy_outcome s1 s2) x) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose c (strategy_outcome s1 s2))
      (IdeaticSpace.compose c x) :=
  resonance_compose_left c h

/-- Every outcome resonates with itself. -/
theorem reflexive_resonance_of_outcome (s1 s2 : I) :
    IdeaticSpace.resonates (strategy_outcome s1 s2) (strategy_outcome s1 s2) :=
  resonance_refl _

/-- If game A's outcome resonates with game B's, vice versa. -/
theorem symmetric_outcome_resonance (p1 p2 : Profile I)
    (h : IdeaticSpace.resonates p1.outcome p2.outcome) :
    IdeaticSpace.resonates p2.outcome p1.outcome :=
  resonance_symm h

/-! ## §6. N-Player and Filtration Theorems -/

/-- n sequential players: depth ≤ sum. Uses composeN as iterated composition. -/
theorem n_player_depth_bound (s : I) (n : ℕ) :
    IdeaticSpace.depth (composeN s n) ≤ n * IdeaticSpace.depth s :=
  depth_composeN s n

/-- For any game, void is a valid strategy (trivially true by typing). -/
theorem void_is_always_available :
    ∃ (s : I), s = (IdeaticSpace.void : I) :=
  ⟨IdeaticSpace.void, rfl⟩

/-- Strategies from filtration n produce outcomes in filtration 2n. -/
theorem depth_monotone_in_filtration (n : ℕ) (s1 s2 : I)
    (h1 : s1 ∈ depthFiltration n) (h2 : s2 ∈ depthFiltration n) :
    strategy_outcome s1 s2 ∈ depthFiltration (2 * n) := by
  simp [strategy_outcome]
  exact depthFiltration_compose h1 h2

end IDT.MG.Ch1
