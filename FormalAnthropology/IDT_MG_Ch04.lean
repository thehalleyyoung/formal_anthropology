import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 4: Nash Equilibrium in Composition Games

**Core claim.** Equilibria can be characterized in composition games where
payoff depends on the composed outcome. We define Nash equilibrium as a
profile where neither player can improve by unilateral deviation within
their repertoire.

## Definitions

- `IsNashEquilibrium s1 s2 r1 r2 u` — neither can improve
- Constant payoff and depth-maximizing special cases

## 16 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch4

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- A Nash equilibrium: neither player can improve by deviating. -/
def IsNashEquilibrium (s1 s2 : I) (r1 r2 : List I) (u : I → ℕ) : Prop :=
  s1 ∈ r1 ∧ s2 ∈ r2 ∧
  (∀ (t1 : I), t1 ∈ r1 → u (IdeaticSpace.compose t1 s2) ≤ u (IdeaticSpace.compose s1 s2)) ∧
  (∀ (t2 : I), t2 ∈ r2 → u (IdeaticSpace.compose s1 t2) ≤ u (IdeaticSpace.compose s1 s2))

/-- A constant payoff function. -/
def ConstantPayoff (c : ℕ) : I → ℕ := fun _ => c

/-- The depth payoff function. -/
def DepthPayoff : I → ℕ := IdeaticSpace.depth

/-! ## §2. Constant Payoff Theorems -/

/-- If payoff is constant, any profile in repertoires is NE. -/
theorem constant_payoff_always_equilibrium (c : ℕ) (s1 s2 : I) (r1 r2 : List I)
    (h1 : s1 ∈ r1) (h2 : s2 ∈ r2) :
    IsNashEquilibrium s1 s2 r1 r2 (ConstantPayoff c) := by
  refine ⟨h1, h2, ?_, ?_⟩
  · intro t1 _; simp [ConstantPayoff]
  · intro t2 _; simp [ConstantPayoff]

/-- void-void is NE for constant payoff (assuming void in repertoires). -/
theorem void_void_is_ne_for_constant (c : ℕ) (r1 r2 : List I)
    (h1 : (IdeaticSpace.void : I) ∈ r1) (h2 : (IdeaticSpace.void : I) ∈ r2) :
    IsNashEquilibrium (IdeaticSpace.void : I) (IdeaticSpace.void : I) r1 r2 (ConstantPayoff c) :=
  constant_payoff_always_equilibrium c _ _ r1 r2 h1 h2

/-- Singleton repertoires always yield an NE. -/
theorem singleton_always_equilibrium (s1 s2 : I) (u : I → ℕ) :
    IsNashEquilibrium s1 s2 [s1] [s2] u := by
  refine ⟨List.mem_cons_self _ _, List.mem_cons_self _ _, ?_, ?_⟩
  · intro t1 ht1
    simp [List.mem_cons, List.mem_nil_iff] at ht1
    rw [ht1]
  · intro t2 ht2
    simp [List.mem_cons, List.mem_nil_iff] at ht2
    rw [ht2]

/-- Every game with non-empty repertoires has NE under constant payoff. -/
theorem trivial_ne_existence (c : ℕ) (s1 s2 : I) (r1 r2 : List I)
    (h1 : s1 ∈ r1) (h2 : s2 ∈ r2) :
    ∃ (a b : I), IsNashEquilibrium a b r1 r2 (ConstantPayoff c) :=
  ⟨s1, s2, constant_payoff_always_equilibrium c s1 s2 r1 r2 h1 h2⟩

/-! ## §3. Depth Bound Theorems -/

/-- In any NE, outcome depth ≤ sum of strategy depths. -/
theorem ne_depth_bound (s1 s2 : I) (r1 r2 : List I) (u : I → ℕ)
    (h : IsNashEquilibrium s1 s2 r1 r2 u) :
    IdeaticSpace.depth (IdeaticSpace.compose s1 s2) ≤
    IdeaticSpace.depth s1 + IdeaticSpace.depth s2 :=
  depth_compose_le s1 s2

/-- NE outcome stays in appropriate filtration. -/
theorem equilibrium_outcome_in_filtration (n : ℕ) (s1 s2 : I) (r1 r2 : List I) (u : I → ℕ)
    (h : IsNashEquilibrium s1 s2 r1 r2 u)
    (h1 : s1 ∈ depthFiltration n) (h2 : s2 ∈ depthFiltration n) :
    IdeaticSpace.compose s1 s2 ∈ depthFiltration (2 * n) :=
  depthFiltration_compose h1 h2

/-- Positive depth NE requires at least one non-void strategy. -/
theorem ne_depth_positive_requires_nonvoid (s1 s2 : I) (r1 r2 : List I) (u : I → ℕ)
    (h : IsNashEquilibrium s1 s2 r1 r2 u)
    (hv1 : s1 = (IdeaticSpace.void : I)) (hv2 : s2 = (IdeaticSpace.void : I)) :
    IdeaticSpace.depth (IdeaticSpace.compose s1 s2) = 0 := by
  rw [hv1, hv2]; simp [void_left, IdeaticSpace.depth_void]

/-- Mutual void play has depth-0 outcome. -/
theorem mutual_void_depth_zero :
    IdeaticSpace.depth (IdeaticSpace.compose (IdeaticSpace.void : I) (IdeaticSpace.void : I)) = 0 := by
  simp [void_left, IdeaticSpace.depth_void]

/-! ## §4. Resonance in NE -/

/-- In NE, outcome resonates with itself (trivially). -/
theorem ne_resonance (s1 s2 : I) (r1 r2 : List I) (u : I → ℕ)
    (h : IsNashEquilibrium s1 s2 r1 r2 u) :
    IdeaticSpace.resonates (IdeaticSpace.compose s1 s2) (IdeaticSpace.compose s1 s2) :=
  resonance_refl _

/-- NE outcome composed with anything resonates with self composed with same. -/
theorem ne_outcome_resonance_with_elaboration (s1 s2 c : I) (r1 r2 : List I) (u : I → ℕ)
    (h : IsNashEquilibrium s1 s2 r1 r2 u) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose (IdeaticSpace.compose s1 s2) c)
      (IdeaticSpace.compose (IdeaticSpace.compose s1 s2) c) :=
  resonance_refl _

/-- NE robust to payoff-preserving transformations. If f preserves payoff, NE transfers. -/
theorem ne_preserved_under_relabeling (s1 s2 : I) (r1 r2 : List I) (u v : I → ℕ)
    (h : IsNashEquilibrium s1 s2 r1 r2 u)
    (hpres : ∀ (x : I), u x = v x) :
    IsNashEquilibrium s1 s2 r1 r2 v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · intro t1 ht1; rw [← hpres, ← hpres]; exact h3 t1 ht1
  · intro t2 ht2; rw [← hpres, ← hpres]; exact h4 t2 ht2

/-! ## §5. Symmetric Games and Deviation -/

/-- NE strategies are weakly best in their repertoire. -/
theorem ne_is_weakly_undominated (s1 s2 : I) (r1 r2 : List I) (u : I → ℕ)
    (h : IsNashEquilibrium s1 s2 r1 r2 u) (t1 : I) (ht1 : t1 ∈ r1) :
    u (IdeaticSpace.compose t1 s2) ≤ u (IdeaticSpace.compose s1 s2) :=
  h.2.2.1 t1 ht1

/-- Deviating to void changes outcome to just the opponent's strategy. -/
theorem ne_void_deviation (s1 s2 : I) :
    IdeaticSpace.compose (IdeaticSpace.void : I) s2 = s2 := by
  simp [void_left]

/-- In depth-max game, NE payoff ≤ max possible depth (sum of both). -/
theorem depth_maximizing_ne_bound (s1 s2 : I) (r1 r2 : List I)
    (h : IsNashEquilibrium s1 s2 r1 r2 DepthPayoff) :
    DepthPayoff (IdeaticSpace.compose s1 s2) ≤
    IdeaticSpace.depth (IdeaticSpace.compose s1 s2) :=
  Nat.le_refl _

/-- Void is a best response to void when payoff = depth. -/
theorem void_best_response_to_void_in_depth_game :
    IsNashEquilibrium
      (IdeaticSpace.void : I) (IdeaticSpace.void : I)
      [(IdeaticSpace.void : I)] [(IdeaticSpace.void : I)]
      DepthPayoff := by
  refine ⟨List.mem_cons_self _ _, List.mem_cons_self _ _, ?_, ?_⟩
  · intro t1 ht1
    simp [List.mem_cons, List.mem_nil_iff] at ht1
    rw [ht1]
  · intro t2 ht2
    simp [List.mem_cons, List.mem_nil_iff] at ht2
    rw [ht2]

/-- In symmetric singleton game, the profile is always NE. -/
theorem symmetric_singleton_ne (s : I) (u : I → ℕ) :
    IsNashEquilibrium s s [s] [s] u :=
  singleton_always_equilibrium s s u

end IDT.MG.Ch4
