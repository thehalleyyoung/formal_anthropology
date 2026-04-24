import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 19: Cultural Evolution and Dynamics

**Core claim.** Over time, ideas evolve through mutagenic decay, selective
competition, and recombinant innovation. Each diffusion type captures a
distinct evolutionary mechanism.

## 17 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch19

open IDT IdeaticSpace

/-! ## §1. Core Definitions -/

variable {I : Type*} [IdeaticSpace I]

/-- Cultural state is just an idea. -/
abbrev CulturalState (I : Type*) [IdeaticSpace I] := I

/-! ## §2. Mutagenic Evolution -/

section Mutagenic
variable {I : Type*} [MutagenicDiffusion I]

/-- Mutagenic evolution: iterate transmit n times. -/
def MutagenicEvolution (a : I) (n : ℕ) : I :=
  Nat.iterate MutagenicDiffusion.transmit n a

/-- Theorem 1: Depth never increases under single transmission. -/
theorem mutagenic_depth_never_increases (a : I) :
    IdeaticSpace.depth (MutagenicDiffusion.transmit a) ≤ IdeaticSpace.depth a :=
  MutagenicDiffusion.transmit_depth_le a

/-- Theorem 2: Depth is monotonically non-increasing over generations. -/
theorem mutagenic_evolution_depth_monotone (a : I) :
    ∀ (n : ℕ), IdeaticSpace.depth (MutagenicEvolution a (n + 1)) ≤
    IdeaticSpace.depth (MutagenicEvolution a n) := by
  intro n
  unfold MutagenicEvolution
  rw [Function.iterate_succ_apply']
  exact MutagenicDiffusion.transmit_depth_le _

/-- Theorem 3: Transmitted idea resonates with original. -/
theorem mutagenic_preserves_resonance (a : I) :
    IdeaticSpace.resonates a (MutagenicDiffusion.transmit a) :=
  MutagenicDiffusion.transmit_resonant a

/-- Theorem 4: Consecutive transmissions resonate. -/
theorem mutagenic_chain_resonance (a : I) (n : ℕ) :
    IdeaticSpace.resonates (MutagenicEvolution a n) (MutagenicEvolution a (n + 1)) := by
  unfold MutagenicEvolution
  rw [Function.iterate_succ_apply']
  exact MutagenicDiffusion.transmit_resonant _

/-- Theorem 5: Transmitting void resonates with void and has depth ≤ 0. -/
theorem mutagenic_void_stable :
    IdeaticSpace.depth (MutagenicDiffusion.transmit (IdeaticSpace.void : I)) = 0 := by
  have h := MutagenicDiffusion.transmit_depth_le (IdeaticSpace.void : I)
  simp [depth_void] at h
  omega

/-- Theorem 6: Transmitting a composition → depth decays. -/
theorem mutagenic_composition_decay (a b : I) :
    IdeaticSpace.depth (MutagenicDiffusion.transmit (IdeaticSpace.compose a b)) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b := by
  have h1 := MutagenicDiffusion.transmit_depth_le (IdeaticSpace.compose a b)
  have h2 := depth_compose_le a b
  linarith

end Mutagenic

/-! ## §3. Selective Competition -/

section Selective
variable {I : Type*} [SelectiveDiffusion I]

/-- Selective competition: select the fitter of two ideas. -/
def SelectiveCompetition (a b : I) : I := SelectiveDiffusion.select a b

/-- Theorem 7: Selection picks one of the inputs. -/
theorem selection_picks_input (a b : I) :
    SelectiveCompetition a b = a ∨ SelectiveCompetition a b = b :=
  SelectiveDiffusion.select_is_input a b

/-- Theorem 8: Fitness of selected = max of inputs. -/
theorem selection_fitness_max (a b : I) :
    SelectiveDiffusion.fitness (SelectiveCompetition a b) =
    Nat.max (SelectiveDiffusion.fitness a) (SelectiveDiffusion.fitness b) :=
  SelectiveDiffusion.select_maximizes a b

/-- Theorem 9: Void has zero fitness. -/
theorem void_zero_fitness :
    SelectiveDiffusion.fitness (IdeaticSpace.void : I) = 0 :=
  SelectiveDiffusion.void_fitness

/-- Theorem 10: Selecting between a and void → fitness = fitness a. -/
theorem selection_vs_void (a : I) :
    SelectiveDiffusion.fitness (SelectiveCompetition a (IdeaticSpace.void : I)) =
    SelectiveDiffusion.fitness a := by
  simp [SelectiveCompetition, SelectiveDiffusion.select_maximizes,
        SelectiveDiffusion.void_fitness, Nat.max_eq_left (Nat.zero_le _)]

/-- Theorem 11: Positive fitness idea survives selection against void. -/
theorem positive_fitness_survives {a : I}
    (h : SelectiveDiffusion.fitness a > 0) :
    SelectiveCompetition a (IdeaticSpace.void : I) = a := by
  rcases SelectiveDiffusion.select_is_input a (IdeaticSpace.void : I) with h1 | h1
  · exact h1
  · exfalso
    have hmax := SelectiveDiffusion.select_maximizes a (IdeaticSpace.void : I)
    rw [h1, SelectiveDiffusion.void_fitness] at hmax
    simp [Nat.max_eq_left (Nat.zero_le _)] at hmax
    omega

/-- Theorem 12: Chained selection preserves max fitness. -/
theorem selection_chain_fitness (a b c : I) :
    SelectiveDiffusion.fitness (SelectiveCompetition (SelectiveCompetition a b) c) =
    Nat.max (Nat.max (SelectiveDiffusion.fitness a) (SelectiveDiffusion.fitness b))
            (SelectiveDiffusion.fitness c) := by
  simp [SelectiveCompetition, SelectiveDiffusion.select_maximizes]

end Selective

/-! ## §4. Recombinant Innovation -/

section Recombinant
variable {I : Type*} [RecombinantDiffusion I]

/-- Recombinant innovation: combine two ideas into a hybrid. -/
def RecombinantInnovation (a b : I) : I := RecombinantDiffusion.recombine a b

/-- Theorem 13: Hybrid resonates with first parent. -/
theorem recombinant_resonates_left (a b : I) :
    IdeaticSpace.resonates a (RecombinantInnovation a b) :=
  RecombinantDiffusion.recombine_resonant_left a b

/-- Theorem 14: Hybrid depth ≤ parent depths + 1. -/
theorem recombinant_depth_bounded (a b : I) :
    IdeaticSpace.depth (RecombinantInnovation a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + 1 :=
  RecombinantDiffusion.recombine_depth_bound a b

/-- Theorem 15: Both orderings of recombination resonate. -/
theorem recombinant_order_symmetric (a b : I) :
    IdeaticSpace.resonates (RecombinantInnovation a b) (RecombinantInnovation b a) :=
  RecombinantDiffusion.recombine_comm_resonant a b

/-- Theorem 16: Recombining void with b → resonates with b. -/
theorem recombinant_void_left (b : I) :
    IdeaticSpace.resonates b (RecombinantInnovation (IdeaticSpace.void : I) b) :=
  RecombinantDiffusion.recombine_resonant_right (IdeaticSpace.void : I) b

/-- Theorem 17: Recombining a with void → resonates with a. -/
theorem recombinant_void_right (a : I) :
    IdeaticSpace.resonates a (RecombinantInnovation a (IdeaticSpace.void : I)) :=
  RecombinantDiffusion.recombine_resonant_left a (IdeaticSpace.void : I)

end Recombinant

end IDT.MG.Ch19
