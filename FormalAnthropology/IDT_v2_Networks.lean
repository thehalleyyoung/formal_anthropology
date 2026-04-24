import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Networks of Ideatic Agents

Networks of agents, each holding an idea-vector. The resonance between
agents forms a Gram-like structure (positive semidefinite by construction).
This connects to social network analysis, opinion dynamics, and cultural
evolution.

## Key Concepts

- **Population**: a list of ideas, one per agent
- **Total self-resonance**: Σᵢ rs(aᵢ, aᵢ) — total "energy" in the network
- **Consecutive resonance**: Σᵢ rs(aᵢ, aᵢ₊₁) — chain agreement
- **Population compose**: the fold of all ideas under ⊕
- **Population diversity**: squared distance of composite from void

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Networks

/-! ## §1. Population and Total Self-Resonance -/

section TotalSelfResonance
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- A population is a list of ideas (each agent holds one idea). -/
abbrev Population (I : Type*) := List I

/-- Total self-resonance of a population: Σᵢ rs(aᵢ, aᵢ)
    In the RKHS embedding, this is Σᵢ ‖φ(aᵢ)‖². -/
noncomputable def totalSelfResonance : Population I → ℝ
  | [] => 0
  | a :: rest => resonanceStrength a a + totalSelfResonance rest

@[simp] theorem totalSelfResonance_nil :
    totalSelfResonance ([] : Population I) = 0 := rfl

theorem totalSelfResonance_cons (a : I) (rest : Population I) :
    totalSelfResonance (a :: rest) =
    resonanceStrength a a + totalSelfResonance rest := rfl

theorem totalSelfResonance_singleton (a : I) :
    totalSelfResonance [a] = resonanceStrength a a := by
  simp [totalSelfResonance]

theorem totalSelfResonance_nonneg : ∀ (pop : Population I),
    totalSelfResonance pop ≥ 0
  | [] => by simp [totalSelfResonance]
  | a :: rest => by
    simp only [totalSelfResonance]
    linarith [rs_self_pos' (I := I) a, totalSelfResonance_nonneg rest]

theorem totalSelfResonance_pos_of_nonempty (a : I) (rest : Population I) :
    totalSelfResonance (a :: rest) > 0 := by
  simp only [totalSelfResonance]
  linarith [rs_self_pos' (I := I) a, totalSelfResonance_nonneg (I := I) rest]

/-- Total self-resonance distributes over append -/
theorem totalSelfResonance_append : ∀ (l₁ l₂ : Population I),
    totalSelfResonance (l₁ ++ l₂) =
    totalSelfResonance l₁ + totalSelfResonance l₂
  | [], l₂ => by simp [totalSelfResonance]
  | a :: rest, l₂ => by
    show resonanceStrength a a + totalSelfResonance (rest ++ l₂) =
      (resonanceStrength a a + totalSelfResonance rest) + totalSelfResonance l₂
    linarith [totalSelfResonance_append rest l₂]

/-- Adding an agent never decreases total self-resonance -/
theorem add_agent_increases_total (a : I) (pop : Population I) :
    totalSelfResonance (a :: pop) ≥ totalSelfResonance pop := by
  simp only [totalSelfResonance]
  linarith [rs_self_pos' (I := I) a]

/-- Each agent contributes at least 1 to total self-resonance -/
theorem totalSelfResonance_ge_length : ∀ (pop : Population I),
    totalSelfResonance pop ≥ pop.length
  | [] => by simp [totalSelfResonance]
  | a :: rest => by
    simp only [totalSelfResonance, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [rs_self_ge_one (I := I) a, totalSelfResonance_ge_length rest]

end TotalSelfResonance

/-! ## §2. Consecutive Resonance -/

section ConsecutiveResonance
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- Consecutive pairwise resonance: Σᵢ rs(aᵢ, aᵢ₊₁)
    Measures agreement between adjacent agents in the population. -/
noncomputable def consecutiveResonance : List I → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => resonanceStrength a b + consecutiveResonance (b :: rest)

@[simp] theorem consecutiveResonance_nil :
    consecutiveResonance ([] : List I) = 0 := rfl

@[simp] theorem consecutiveResonance_singleton (a : I) :
    consecutiveResonance [a] = 0 := rfl

theorem consecutiveResonance_pair (a b : I) :
    consecutiveResonance [a, b] = resonanceStrength a b := by
  simp [consecutiveResonance]

theorem consecutiveResonance_cons (a b : I) (rest : List I) :
    consecutiveResonance (a :: b :: rest) =
    resonanceStrength a b + consecutiveResonance (b :: rest) := rfl

theorem consecutiveResonance_nonneg : ∀ (pop : List I),
    consecutiveResonance pop ≥ 0
  | [] => by simp
  | [_] => by simp
  | a :: b :: rest => by
    simp only [consecutiveResonance]
    linarith [rs_nonneg' (I := I) a b, consecutiveResonance_nonneg (b :: rest)]

/-- Consecutive resonance of a pair is symmetric -/
theorem consecutiveResonance_pair_comm (a b : I) :
    consecutiveResonance [a, b] = consecutiveResonance [b, a] := by
  simp only [consecutiveResonance_pair]
  exact rs_symm' a b

/-- Consecutive resonance of a triple satisfies a bound -/
theorem consecutiveResonance_triple (a b c : I) :
    consecutiveResonance [a, b, c] =
    resonanceStrength a b + resonanceStrength b c := by
  simp [consecutiveResonance]

end ConsecutiveResonance

/-! ## §3. Population Composition -/

section PopulationCompose
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- The composed idea of a population: fold via ideatic composition.
    This is the "consensus idea" — the summary of the whole population. -/
def populationCompose : List I → I
  | [] => void
  | a :: rest => compose a (populationCompose rest)

@[simp] theorem populationCompose_nil :
    populationCompose ([] : List I) = (void : I) := rfl

theorem populationCompose_cons (a : I) (rest : List I) :
    populationCompose (a :: rest) = compose a (populationCompose rest) := rfl

theorem populationCompose_singleton (a : I) :
    populationCompose [a] = a := by
  simp [populationCompose, IdeaticSpace2.void_right]

theorem populationCompose_pair (a b : I) :
    populationCompose [a, b] = compose a b := by
  simp [populationCompose, IdeaticSpace2.void_right]

/-- Composing void at the front is an identity on population compose -/
theorem populationCompose_void_left (rest : List I) :
    populationCompose ((void : I) :: rest) = populationCompose rest := by
  simp [populationCompose, IdeaticSpace2.void_left]

/-- A population of all voids composes to void -/
theorem all_void_populationCompose : ∀ (n : ℕ),
    populationCompose (List.replicate n (void : I)) = (void : I)
  | 0 => rfl
  | n + 1 => by
    simp [List.replicate_succ, populationCompose, IdeaticSpace2.void_left,
          all_void_populationCompose n]

/-- Composing void at the end is identity on population compose -/
theorem populationCompose_append_void (pop : List I) :
    populationCompose (pop ++ [(void : I)]) = populationCompose pop := by
  induction pop with
  | nil => simp [populationCompose, IdeaticSpace2.void_right]
  | cons a rest ih =>
    show compose a (populationCompose (rest ++ [(void : I)])) =
      compose a (populationCompose rest)
    rw [ih]

/-- Self-resonance of any population's composite is ≥ 1 -/
theorem populationCompose_self_rs_ge_one : ∀ (pop : List I),
    resonanceStrength (populationCompose pop) (populationCompose pop) ≥ 1
  | [] => by simp [populationCompose]; rw [IdeaticSpace2.rs_void_self]
  | _ :: _ => by
    simp only [populationCompose]
    exact rs_compose_ge_one _ (populationCompose _)

end PopulationCompose

/-! ## §4. Depth Bounds for Populations -/

section DepthBounds
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- Sum of depths of ideas in a population -/
def depthSum : List I → ℕ
  | [] => 0
  | a :: rest => depth a + depthSum rest

@[simp] theorem depthSum_nil : depthSum ([] : List I) = 0 := rfl

theorem depthSum_cons (a : I) (rest : List I) :
    depthSum (a :: rest) = depth a + depthSum rest := rfl

theorem depthSum_singleton (a : I) : depthSum [a] = depth a := by
  simp [depthSum]

/-- Depth of the composed population idea ≤ sum of individual depths -/
theorem populationCompose_depth_bound : ∀ (pop : List I),
    depth (populationCompose pop) ≤ depthSum pop
  | [] => by simp [populationCompose, depthSum, IdeaticSpace2.depth_void]
  | a :: rest => by
    simp only [populationCompose, depthSum]
    have h := IdeaticSpace2.depth_subadditive a (populationCompose rest)
    have ih := populationCompose_depth_bound rest
    omega

/-- Depth of a void population's composite is 0 -/
theorem depth_all_void_compose (n : ℕ) :
    depth (populationCompose (List.replicate n (void : I))) = 0 := by
  rw [all_void_populationCompose]; exact IdeaticSpace2.depth_void

/-- Depth sum distributes over append -/
theorem depthSum_append : ∀ (l₁ l₂ : List I),
    depthSum (l₁ ++ l₂) = depthSum l₁ + depthSum l₂
  | [], l₂ => by simp [depthSum]
  | a :: rest, l₂ => by
    show depth a + depthSum (rest ++ l₂) = (depth a + depthSum rest) + depthSum l₂
    have ih := depthSum_append rest l₂
    omega

end DepthBounds

/-! ## §5. Network Resonance Properties -/

section NetworkResonance
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- Adding an agent to the front increases composite self-resonance (right part) -/
theorem compose_resonance_ge_head (a : I) (pop : List I) :
    resonanceStrength (populationCompose (a :: pop))
      (populationCompose (a :: pop)) ≥ resonanceStrength a a := by
  simp only [populationCompose]
  exact rs_compose_self_right a (populationCompose pop)

/-- Adding an agent to the front increases composite self-resonance (tail part) -/
theorem compose_resonance_ge_tail (a : I) (pop : List I) :
    resonanceStrength (populationCompose (a :: pop))
      (populationCompose (a :: pop)) ≥
    resonanceStrength (populationCompose pop) (populationCompose pop) := by
  simp only [populationCompose]
  exact rs_compose_self_left (populationCompose pop) a

/-- Void population has unit resonance -/
theorem void_population_unit_resonance (n : ℕ) :
    resonanceStrength
      (populationCompose (List.replicate n (void : I)))
      (populationCompose (List.replicate n (void : I))) = 1 := by
  rw [all_void_populationCompose]; exact IdeaticSpace2.rs_void_self

/-- Composition context preserves resonance ordering -/
theorem population_resonance_context (a b c : I) :
    resonanceStrength (compose c a) (compose c b) ≥ resonanceStrength a b :=
  IdeaticSpace2.rs_compose_left_mono a b c

end NetworkResonance

/-! ## §6. Population Metrics and Diversity -/

section PopulationMetrics
variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-- Population diversity: squared distance from composite to void.
    Measures how far the "consensus" is from the neutral element. -/
noncomputable def populationDiversity (pop : List I) : ℝ :=
  squaredDistance (populationCompose pop) (void : I)

theorem populationDiversity_nil :
    populationDiversity ([] : List I) = 0 := by
  unfold populationDiversity; simp [populationCompose, squaredDistance_self]

theorem populationDiversity_nonneg (pop : List I) :
    populationDiversity pop ≥ 0 := by
  unfold populationDiversity; exact squaredDistance_nonneg _ _

/-- Pairwise agreement (normalized RS between two agents) -/
noncomputable def pairAgreement (a b : I) : ℝ := normalizedRS a b

theorem pairAgreement_symm (a b : I) :
    pairAgreement a b = pairAgreement b a := by
  unfold pairAgreement normalizedRS
  rw [IdeaticSpace2.rs_symm a b,
      mul_comm (resonanceStrength a a) (resonanceStrength b b)]

theorem pairAgreement_self (a : I) : pairAgreement a a = 1 :=
  normalizedRS_self a

theorem pairAgreement_le_one (a b : I) : pairAgreement a b ≤ 1 :=
  normalizedRS_le_one a b

theorem pairAgreement_nonneg (a b : I) : pairAgreement a b ≥ 0 :=
  normalizedRS_nonneg a b

end PopulationMetrics

end IDT2.Networks
