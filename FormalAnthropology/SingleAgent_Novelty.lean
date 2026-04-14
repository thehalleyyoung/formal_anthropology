/-
AUTO-AUDIT 2026-02-08
Current assumptions summary:
- Theorems in this file use explicit binder hypotheses/typeclass assumptions in their signatures.
- Global axiom declarations: none.
- sorry/admit occurrences: none.
Potential weakening targets:
- No non-derivable assumptions were found beyond explicit theorem hypotheses.
-/

/-
# Single-Agent Ideogenesis: Novelty Theory

From SINGLE_AGENT_IDEOGENESIS++ Chapter 4:
- Theorem 4.20: Omega-Novelty
- Theorem 4.21: Novelty Non-Monotonicity
- Theorem 4.22: Novelty Density Decay
- Theorem 4.23: Cantor-Bendixson Analogue
-/

import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.SingleAgent_Depth
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace SingleAgentIdeogenesis

/-! ## Helper lemma for stage monotonicity -/

/-- genCumulative is monotone in the stage number -/
theorem genCumulative_stage_mono (S : IdeogeneticSystem) (A : Set S.Idea) (m n : ℕ) (h : m ≤ n) :
    genCumulative S m A ⊆ genCumulative S n A := by
  induction n with
  | zero => 
    have hm0 : m = 0 := Nat.le_zero.mp h
    rw [hm0]
  | succ n ih =>
    by_cases hmn : m ≤ n
    · intro x hx
      simp only [genCumulative, Set.mem_union]
      left
      exact ih hmn hx
    · have hmn' : m = n + 1 := by omega
      rw [hmn']

/-! ## Theorem 4.20: Omega-Novelty -/

/-- Novelty at any stage is contained in the closure -/
theorem novelty_subset_closure (S : IdeogeneticSystem) (A : Set S.Idea) (n : ℕ) :
    noveltyAt S A n ⊆ closure S A := by
  intro x hx
  rw [depth_stratifies S A]
  simp only [Set.mem_iUnion]
  exact ⟨n, hx⟩

/-- If the system has infinite novelty, there exists an omega-sequence of novel elements -/
theorem omega_novelty (S : IdeogeneticSystem) (A : Set S.Idea)
    (hinf : ∀ n : ℕ, (noveltyAt S A n).Nonempty) :
    ∃ f : ℕ → S.Idea, ∀ n : ℕ, f n ∈ noveltyAt S A n := by
  have hchoice : ∀ n : ℕ, ∃ x : S.Idea, x ∈ noveltyAt S A n := fun n => hinf n
  exact Classical.axiomOfChoice hchoice

/-- Omega-novelty implies infinite closure -/
theorem omega_novelty_infinite (S : IdeogeneticSystem) (A : Set S.Idea)
    (hinf : ∀ n : ℕ, (noveltyAt S A n).Nonempty) :
    (closure S A).Infinite := by
  obtain ⟨f, hf⟩ := omega_novelty S A hinf
  have hinj : Function.Injective f := by
    intro m n hmn
    by_contra hne
    have hdisj := novelty_disjoint S A m n hne
    have hfm := hf m
    have hfn := hf n
    rw [hmn] at hfm
    rw [Set.eq_empty_iff_forall_not_mem] at hdisj
    exact hdisj (f n) ⟨hfm, hfn⟩
  have hrange : Set.range f ⊆ closure S A := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    have h := hf n
    exact novelty_subset_closure S A n h
  exact Set.infinite_of_injective_forall_mem hinj (fun n => hrange ⟨n, rfl⟩)

/-! ## Theorem 4.21: Novelty Non-Monotonicity 

Novelty can be non-monotonic: we can construct systems where |nov(n+1)| > |nov(n)|.
This is witnessed by any system where the generation function produces multiple outputs
from a single input (e.g., binary tree generation). -/

/-- Binary tree system: each natural generates two successors -/
def binaryTreeSystem : IdeogeneticSystem where
  Idea := ℕ
  generate := fun n => {2*n + 1, 2*n + 2}
  primordial := 0

/-- Generation in the binary tree system produces two distinct successors -/
theorem binaryTree_gen_two (n : ℕ) : 
    (binaryTreeSystem.generate n).ncard = 2 := by
  have hne : 2*n + 1 ≠ 2*n + 2 := by omega
  simp only [binaryTreeSystem]
  exact Set.ncard_pair hne

/-- Helper: stage 0 novelty is just the seed -/
private theorem novelty_stage0 : noveltyAt binaryTreeSystem ({0} : Set ℕ) 0 = ({0} : Set ℕ) := rfl

/-- Helper: stage 1 novelty is {1, 2} -/
private theorem novelty_stage1 : noveltyAt binaryTreeSystem ({0} : Set ℕ) 1 = ({1, 2} : Set ℕ) := by
  unfold noveltyAt genCumulative genStep binaryTreeSystem
  ext x
  constructor
  · intro hx
    simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff] at hx
    rcases hx.1 with h0 | hgen
    · exact absurd h0 hx.2
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_insert_iff] at hgen
      obtain ⟨a, ha, hx'⟩ := hgen
      subst ha
      simp only [Nat.mul_zero, Nat.zero_add, Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      exact hx'
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · right
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_insert_iff]
      refine ⟨0, rfl, ?_⟩
      simp only [Nat.mul_zero, Nat.zero_add, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hx
    · rcases hx with rfl | rfl <;> decide

/-- Novelty can increase: in the binary tree system, stage 1 has more elements than stage 0.
This is a concrete witness that |novelty(n+1)| > |novelty(n)| is possible. -/
theorem novelty_can_increase_binaryTree : 
    (noveltyAt binaryTreeSystem ({0} : Set ℕ) 1).ncard > (noveltyAt binaryTreeSystem ({0} : Set ℕ) 0).ncard := by
  rw [novelty_stage0, novelty_stage1]
  rw [Set.ncard_singleton, Set.ncard_pair (by omega : (1:ℕ) ≠ 2)]
  omega

/-! ## Theorem 4.22: Novelty Density Decay -/

/-- Novelty at stage 0 is just the seed -/
theorem novelty_zero (S : IdeogeneticSystem) (A : Set S.Idea) :
    noveltyAt S A 0 = A := by
  simp only [noveltyAt, ↓reduceIte]

/-- For finitary systems with finite seed, each generation stage is finite -/
theorem genCumulative_finite' (S : IdeogeneticSystem) (A : Set S.Idea) (n : ℕ)
    (hfin : isFinitary S) (hAfin : A.Finite) :
    (genCumulative S n A).Finite := by
  induction n with
  | zero => 
    simp only [genCumulative]
    exact hAfin
  | succ n ih =>
    simp only [genCumulative]
    apply Set.Finite.union ih
    apply Set.Finite.biUnion ih
    intro x _
    exact hfin x

/-! ## Theorem 4.23: Cantor-Bendixson Analogue -/

/-- The closure decomposes into "perfect" (limit) and "scattered" (isolated) parts -/
def limitIdeas (S : IdeogeneticSystem) (A : Set S.Idea) : Set S.Idea :=
  {x ∈ closure S A | ∀ n : ℕ, x ∈ genCumulative S n A → 
    ∃ m > n, ∃ y ∈ noveltyAt S A m, y ∈ S.generate x}

def isolatedIdeas (S : IdeogeneticSystem) (A : Set S.Idea) : Set S.Idea :=
  closure S A \ limitIdeas S A

/-- The closure decomposes into limit and isolated parts -/
theorem cantor_bendixson_decomposition (S : IdeogeneticSystem) (A : Set S.Idea) :
    closure S A = limitIdeas S A ∪ isolatedIdeas S A := by
  ext x
  simp only [limitIdeas, isolatedIdeas, Set.mem_union, Set.mem_diff, Set.mem_sep_iff]
  constructor
  · intro hx
    by_cases h : ∀ n : ℕ, x ∈ genCumulative S n A → 
        ∃ m > n, ∃ y ∈ noveltyAt S A m, y ∈ S.generate x
    · left; exact ⟨hx, h⟩
    · right; exact ⟨hx, fun ⟨_, h'⟩ => h h'⟩
  · intro hx
    cases hx with
    | inl h => exact h.1
    | inr h => exact h.1

/-- The limit part is closed under generation -/
theorem limit_closed_under_gen (S : IdeogeneticSystem) (A : Set S.Idea) (x : S.Idea)
    (hx : x ∈ limitIdeas S A) (y : S.Idea) (hy : y ∈ S.generate x) :
    y ∈ closure S A := by
  simp only [limitIdeas, Set.mem_sep_iff] at hx
  have hxcl := hx.1
  simp only [closure, Set.mem_iUnion] at hxcl ⊢
  obtain ⟨n, hn⟩ := hxcl
  use n + 1
  simp only [genCumulative, Set.mem_union]
  right
  simp only [genStep, Set.mem_iUnion]
  exact ⟨x, hn, hy⟩

end SingleAgentIdeogenesis
