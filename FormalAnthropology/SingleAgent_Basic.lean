/-
AUTO-AUDIT 2026-02-08
Current assumptions summary:
- Theorems in this file use explicit binder hypotheses/typeclass assumptions in their signatures.
- Global `axiom` declarations: none.
- `sorry`/`admit` occurrences: none.
Potential weakening targets:
- No non-derivable assumptions were found beyond explicit theorem hypotheses.
-/

/-
# Single-Agent Ideogenesis: Basic Definitions

This file contains the foundational definitions from SINGLE_AGENT_IDEOGENESIS++:
- Definition 3.1: Single-Agent Ideogenetic System
- Definition 3.3: Closure
- Definition 3.4: Depth
- Definition 3.9: Fixed Point
- Definition 3.14-3.18: System properties (Finitary, Grounded, etc.)
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

namespace SingleAgentIdeogenesis

/-! ## Definition 3.1: Ideogenetic System -/

/-- An ideogenetic system consists of a type of ideas, a generation operator,
    and a primordial idea. This is Definition 3.1 from IDEOGENESIS++. -/
structure IdeogeneticSystem where
  /-- The type of ideas -/
  Idea : Type*
  /-- The generation operator: each idea generates a set of successor ideas -/
  generate : Idea → Set Idea
  /-- The primordial idea: the conceptual seed from which all ideas grow -/
  primordial : Idea

variable {S : IdeogeneticSystem}

/-! ## Definition 3.2: Iterated Generation -/

/-- Single-step generation from a set of ideas -/
def genStep (S : IdeogeneticSystem) (A : Set S.Idea) : Set S.Idea :=
  ⋃ a ∈ A, S.generate a

/-- n-fold iterated generation (Definition 3.2) -/
def genIter (S : IdeogeneticSystem) : ℕ → Set S.Idea → Set S.Idea
  | 0, A => A
  | n + 1, A => genStep S (genIter S n A)

/-- Alternative: cumulative generation up to stage n -/
def genCumulative (S : IdeogeneticSystem) : ℕ → Set S.Idea → Set S.Idea
  | 0, A => A
  | n + 1, A => genCumulative S n A ∪ genStep S (genCumulative S n A)

/-! ## Definition 3.3: Closure -/

/-- The closure of a seed set under generation (Definition 3.3).
    This is the union of all finite generation stages. -/
def closure (S : IdeogeneticSystem) (A : Set S.Idea) : Set S.Idea :=
  ⋃ n, genCumulative S n A

/-- The closure starting from the primordial idea -/
def primordialClosure (S : IdeogeneticSystem) : Set S.Idea :=
  closure S {S.primordial}

/-! ## Definition 3.4: Depth -/

/-- Predicate that an idea appears by stage n -/
def appearsBy (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) (n : ℕ) : Prop :=
  a ∈ genCumulative S n A

/-- The depth of an idea is the minimum stage at which it appears (Definition 3.4).
    This is defined as the infimum of stages where the idea appears.
    We use Nat.find with classical decidability. -/
noncomputable def depth (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) : ℕ :=
  @dite ℕ (∃ n, a ∈ genCumulative S n A) (Classical.propDecidable _)
    (fun h => @Nat.find _ (Classical.decPred _) h)
    (fun _ => 0)

/-- If a is in the closure, it appears at stage depth(a) -/
theorem mem_genCumulative_depth (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea)
    (ha : a ∈ closure S A) : a ∈ genCumulative S (depth S A a) A := by
  simp only [closure, Set.mem_iUnion] at ha
  obtain ⟨n, hn⟩ := ha
  have hex : ∃ k, a ∈ genCumulative S k A := ⟨n, hn⟩
  unfold depth
  rw [dif_pos hex]
  haveI : DecidablePred fun k => a ∈ genCumulative S k A := Classical.decPred _
  have := @Nat.find_spec (fun k => a ∈ genCumulative S k A) _ hex
  convert this

/-- depth is at most the stage where we first found the element -/
theorem depth_le_of_mem (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) (n : ℕ)
    (h : a ∈ genCumulative S n A) : depth S A a ≤ n := by
  have hex : ∃ k, a ∈ genCumulative S k A := ⟨n, h⟩
  unfold depth
  rw [dif_pos hex]
  haveI : DecidablePred fun k => a ∈ genCumulative S k A := Classical.decPred _
  convert @Nat.find_le n (fun k => a ∈ genCumulative S k A) _ hex h

/-- If a is in the closure and depth is k, then a appears at generation step k -/
theorem depth_mem_genCumulative (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) (k : ℕ)
    (ha : a ∈ closure S A) (h : depth S A a = k) : a ∈ genCumulative S k A := by
  -- This is just mem_genCumulative_depth rephrased
  have := mem_genCumulative_depth S A a ha
  rw [h] at this
  exact this

/-- If depth is k > 0, then a does not appear at step k-1 -/
theorem depth_not_mem_pred (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) (k : ℕ)
    (h : depth S A a = k) (hk : k > 0) : a ∉ genCumulative S (k - 1) A := by
  intro h_mem
  -- If a ∈ genCumulative S (k-1) A, then depth ≤ k-1
  have : depth S A a ≤ k - 1 := depth_le_of_mem S A a (k - 1) h_mem
  -- But depth = k
  rw [h] at this
  -- So k ≤ k - 1, contradiction with k > 0
  omega

/-- An idea is reachable from A if it's in the closure -/
def isReachable (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) : Prop :=
  a ∈ closure S A

/-- Depth from the primordial idea -/
noncomputable def primordialDepth (S : IdeogeneticSystem) (a : S.Idea) : ℕ :=
  depth S {S.primordial} a

/-! ## Definition 3.9: Fixed Point -/

/-- An idea is a fixed point if it generates itself (Definition 3.9) -/
def isFixedPoint (S : IdeogeneticSystem) (a : S.Idea) : Prop :=
  a ∈ S.generate a

/-- The set of all fixed points -/
def fixedPoints (S : IdeogeneticSystem) : Set S.Idea :=
  {a | isFixedPoint S a}

/-! ## Definition 3.10: Limit Idea -/

/-- An idea is a limit idea if it first appears as a limit of a sequence,
    not through direct generation. In the finite setting, we approximate
    this as ideas reachable only through infinitely many steps. -/
def isLimitIdea (S : IdeogeneticSystem) (a : S.Idea) : Prop :=
  a ∈ primordialClosure S ∧ ∀ n, a ∉ genCumulative S n {S.primordial}

/-! ## Definition 3.11: Attractor -/

/-- A set is closed under generation -/
def isClosedUnderGen (S : IdeogeneticSystem) (A : Set S.Idea) : Prop :=
  genStep S A ⊆ A

/-- A set is an attractor if it's minimal among closed sets -/
def isAttractor (S : IdeogeneticSystem) (A : Set S.Idea) : Prop :=
  isClosedUnderGen S A ∧ ∀ B ⊆ A, isClosedUnderGen S B → B = ∅ ∨ B = A

/-! ## Definition 3.12: Novel Idea -/

/-- An idea is novel at stage n if it first appears at stage n (Definition 3.12) -/
def isNovelAt (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) (n : ℕ) : Prop :=
  a ∈ genCumulative S n A ∧ (n = 0 ∨ a ∉ genCumulative S (n - 1) A)

/-- The set of ideas novel at stage n (Definition 3.19) -/
def noveltyAt (S : IdeogeneticSystem) (A : Set S.Idea) (n : ℕ) : Set S.Idea :=
  if n = 0 then A else genCumulative S n A \ genCumulative S (n - 1) A

/-! ## Definition 3.14: Finitary System -/

/-- A system is finitary if every idea generates finitely many successors (Definition 3.14) -/
def isFinitary (S : IdeogeneticSystem) : Prop :=
  ∀ a, (S.generate a).Finite

/-! ## Definition 3.15: Well-Founded System -/

/-- A system is well-founded if there are no infinite descending generation chains -/
def isWellFounded (S : IdeogeneticSystem) : Prop :=
  WellFounded (fun a b => a ∈ S.generate b)

/-! ## Definition 3.16: Grounded System -/

/-- A system is grounded if every idea is reachable from the primordial (Definition 3.16) -/
def isGrounded (S : IdeogeneticSystem) : Prop :=
  ∀ a, isReachable S {S.primordial} a

/-! ## Definition 3.17: Complete System -/

/-- A system is complete if limits of reachable sequences are reachable -/
def isComplete (S : IdeogeneticSystem) : Prop :=
  ∀ (f : ℕ → S.Idea), (∀ n, isReachable S {S.primordial} (f n)) →
    (∀ n, f (n + 1) ∈ S.generate (f n)) →
    ∃ a, isReachable S {S.primordial} a ∧ ∀ n, f n ∈ S.generate a ∨ f n = a

/-! ## Definition 3.18: Reflexive System -/

/-- A system is reflexive if it can represent itself as an idea -/
structure ReflexiveSystem extends IdeogeneticSystem where
  /-- The idea representing the system itself -/
  selfIdea : Idea
  /-- The self-idea is in the closure -/
  selfIdea_reachable : selfIdea ∈ closure toIdeogeneticSystem {primordial}

/-! ## Definition 3.22: Eventual Stagnation -/

/-- A system eventually stagnates if no new ideas appear after some stage -/
def eventuallyStagnates (S : IdeogeneticSystem) (A : Set S.Idea) : Prop :=
  ∃ n, ∀ m ≥ n, noveltyAt S A m = ∅

/-! ## Definition 3.23: Perpetual Innovation -/

/-- A system exhibits perpetual innovation if new ideas appear at every stage -/
def perpetualInnovation (S : IdeogeneticSystem) (A : Set S.Idea) : Prop :=
  ∀ n, (noveltyAt S A n).Nonempty

/-! ## Basic Theorems -/

/-- The seed is always in its own closure -/
theorem seed_in_closure (S : IdeogeneticSystem) (A : Set S.Idea) : A ⊆ closure S A := by
  intro a ha
  simp only [closure, Set.mem_iUnion]
  exact ⟨0, by simp [genCumulative, ha]⟩

/-- The primordial is in the primordial closure -/
theorem primordial_in_closure (S : IdeogeneticSystem) : 
    S.primordial ∈ primordialClosure S := by
  apply seed_in_closure
  exact Set.mem_singleton _

/-- The base set A is contained in genCumulative at any stage -/
theorem genCumulative_contains_base (S : IdeogeneticSystem) (n : ℕ) (A : Set S.Idea) :
    A ⊆ genCumulative S n A := by
  induction n with
  | zero => simp only [genCumulative]; exact fun _ ha => ha
  | succ n ih =>
    intro a ha
    simp only [genCumulative, Set.mem_union]
    left
    exact ih ha

/-- Generation stages are monotonically increasing -/
theorem genCumulative_mono (S : IdeogeneticSystem) (A : Set S.Idea) (n m : ℕ) (h : n ≤ m) :
    genCumulative S n A ⊆ genCumulative S m A := by
  induction m with
  | zero => 
    simp only [Nat.le_zero] at h
    subst h
    rfl
  | succ m ih =>
    cases Nat.lt_or_eq_of_le h with
    | inl hlt =>
      have : n ≤ m := Nat.lt_succ_iff.mp hlt
      intro a ha
      simp only [genCumulative]
      left
      exact ih this ha
    | inr heq =>
      subst heq
      rfl

/-- Closure is idempotent -/
theorem closure_idempotent (S : IdeogeneticSystem) (A : Set S.Idea) :
    closure S (closure S A) = closure S A := by
  apply Set.eq_of_subset_of_subset
  · -- closure(closure(A)) ⊆ closure(A)
    intro a ha
    simp only [closure, Set.mem_iUnion] at ha
    obtain ⟨n, hn⟩ := ha
    -- We prove by strong induction on n
    have : ∀ (m : ℕ) (x : S.Idea), x ∈ genCumulative S m (⋃ n, genCumulative S n A) → 
           ∃ k, x ∈ genCumulative S k A := by
      intro m
      induction m with
      | zero => 
        intro x hx
        simp only [genCumulative] at hx
        simp only [Set.mem_iUnion] at hx
        exact hx
      | succ m ih =>
        intro x hx
        simp only [genCumulative, Set.mem_union] at hx
        cases hx with
        | inl hx' => exact ih x hx'
        | inr hx' =>
          simp only [genStep, Set.mem_iUnion] at hx'
          obtain ⟨b, hb, hxb⟩ := hx'
          obtain ⟨k, hk⟩ := ih b hb
          use k + 1
          simp only [genCumulative, genStep, Set.mem_union, Set.mem_iUnion]
          right
          exact ⟨b, hk, hxb⟩
    obtain ⟨k, hk⟩ := this n a hn
    simp only [closure, Set.mem_iUnion]
    exact ⟨k, hk⟩
  · -- closure(A) ⊆ closure(closure(A))
    exact seed_in_closure S (closure S A)

/-- Fixed points are in their own generation -/
theorem fixedPoint_self_gen (S : IdeogeneticSystem) (a : S.Idea) 
    (h : isFixedPoint S a) : a ∈ S.generate a := h

/-- If a is reachable, then so are all ideas it generates -/
theorem generate_preserves_reachable (S : IdeogeneticSystem) (a : S.Idea)
    (ha : isReachable S {S.primordial} a) (b : S.Idea) (hb : b ∈ S.generate a) :
    isReachable S {S.primordial} b := by
  simp only [isReachable, closure, Set.mem_iUnion] at ha ⊢
  obtain ⟨n, hn⟩ := ha
  use n + 1
  simp only [genCumulative, genStep, Set.mem_union, Set.mem_iUnion]
  right
  exact ⟨a, hn, hb⟩

/-- Generate preserves closure membership -/
theorem generate_preserves_closure (S : IdeogeneticSystem) (a : S.Idea)
    (ha : a ∈ primordialClosure S) (b : S.Idea) (hb : b ∈ S.generate a) :
    b ∈ primordialClosure S := by
  unfold primordialClosure at ha ⊢
  exact generate_preserves_reachable S a ha b hb

/-- The primordial has depth 0 -/
theorem primordial_depth_zero (S : IdeogeneticSystem) : 
    primordialDepth S S.primordial = 0 := by
  unfold primordialDepth depth
  have h0 : S.primordial ∈ genCumulative S 0 {S.primordial} := by
    simp only [genCumulative, Set.mem_singleton_iff]
  have hex : ∃ n, S.primordial ∈ genCumulative S n {S.primordial} := ⟨0, h0⟩
  simp only [dif_pos hex]
  -- Use depth_le_of_mem with n=0 to show depth ≤ 0
  have hle := depth_le_of_mem S {S.primordial} S.primordial 0 h0
  unfold depth at hle
  simp only [dif_pos hex] at hle
  exact Nat.le_zero.mp hle

/-- Generated idea has depth at most parent depth + 1 -/
theorem generate_increases_depth (S : IdeogeneticSystem) (a : S.Idea)
    (ha : a ∈ primordialClosure S) (b : S.Idea) (hb : b ∈ S.generate a) :
    primordialDepth S b ≤ primordialDepth S a + 1 := by
  unfold primordialDepth
  have ha_mem := mem_genCumulative_depth S {S.primordial} a ha
  have hb_clos := generate_preserves_closure S a ha b hb
  have hb_mem : b ∈ genCumulative S (depth S {S.primordial} a + 1) {S.primordial} := by
    simp only [genCumulative, genStep, Set.mem_union, Set.mem_iUnion]
    right
    exact ⟨a, ha_mem, hb⟩
  exact depth_le_of_mem S {S.primordial} b (depth S {S.primordial} a + 1) hb_mem

end SingleAgentIdeogenesis
