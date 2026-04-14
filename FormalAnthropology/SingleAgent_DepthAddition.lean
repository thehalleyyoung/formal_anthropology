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
# Depth Addition and Composition

From FORMAL_ANTHROPOLOGY++ Chapter 6: Core Theorems of Generation

This file proves fundamental properties about how depths compose under
sequential generation. These are basic structural results that establish
that depth behaves predictably under composition.

## Key Results:
- **Depth Subadditivity**: depth(closure of closure) ≤ sum of depths
- **Direct Generation Depth**: If b ∈ gen(a), then depth(b) ≤ depth(a) + 1
- **Path Length Lower Bound**: Generation sequences have length ≥ depth difference

## Mathematical Content:
These theorems establish that depth is well-behaved with respect to composition
of generation steps. They are foundational for understanding how complex ideas
build on simpler ones.
-/

import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.SingleAgent_Closure
import FormalAnthropology.SingleAgent_Depth
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace SingleAgentIdeogenesis

open Set

variable {S : IdeogeneticSystem}

/-! ## Section 1: Direct Generation Depth Bound -/

/-- **Theorem**: If b is directly generated from a, then the depth of b
    is at most one more than the depth of a.
    
    This is intuitive: generating from a requires first reaching a (at depth d),
    then one more generation step gives b (at depth at most d+1). -/
theorem depth_succ_of_generate (init : Set S.Idea) (a b : S.Idea)
    (ha : a ∈ closure S init) (hb : b ∈ S.generate a) :
    depth S init b ≤ depth S init a + 1 := by
  -- b ∈ gen(a) and a has depth da means b appears by stage da + 1
  let da := depth S init a
  -- a ∈ genCumulative da by definition of depth
  have ha_at_da : a ∈ genCumulative S da init := mem_genCumulative_depth S init a ha
  -- Therefore b ∈ genCumulative (da + 1)
  have hb_at_succ : b ∈ genCumulative S (da + 1) init := by
    unfold genCumulative
    right
    unfold genStep
    simp only [mem_iUnion]
    exact ⟨a, ha_at_da, hb⟩
  -- By definition of depth, depth(b) ≤ da + 1
  exact depth_le_of_mem S init b (da + 1) hb_at_succ

/-- **Corollary**: In any generation chain a₀ → a₁ → ... → aₙ,
    we have depth(aₙ) ≤ depth(a₀) + n -/
theorem depth_le_add_chain (init : Set S.Idea) (n : ℕ) (seq : ℕ → S.Idea)
    (h_chain : ∀ i < n, seq (i + 1) ∈ S.generate (seq i))
    (h_start : seq 0 ∈ closure S init) :
    depth S init (seq n) ≤ depth S init (seq 0) + n := by
  -- Prove by strong induction that for all m ≤ n:
  -- 1. seq m ∈ closure S init
  -- 2. depth S init (seq m) ≤ depth S init (seq 0) + m
  suffices ∀ m ≤ n, seq m ∈ closure S init ∧ depth S init (seq m) ≤ depth S init (seq 0) + m by
    exact (this n (le_refl n)).2
  intro m hm
  induction m with
  | zero =>
    constructor
    · exact h_start
    · simp
  | succ m ih_m =>
    have hm' : m ≤ n := Nat.le_of_succ_le hm
    have ⟨h_m_closure, h_m_depth⟩ := ih_m hm'
    constructor
    · -- seq (m + 1) ∈ closure
      have h_gen : seq (m + 1) ∈ S.generate (seq m) := h_chain m (Nat.lt_of_succ_le hm)
      have : seq (m + 1) ∈ genStep S (closure S init) := by
        unfold genStep; simp only [Set.mem_iUnion]
        exact ⟨seq m, h_m_closure, h_gen⟩
      exact closure_closed_under_gen S init this
    · -- depth bound
      have h_gen : seq (m + 1) ∈ S.generate (seq m) := h_chain m (Nat.lt_of_succ_le hm)
      have h_succ : depth S init (seq (m + 1)) ≤ depth S init (seq m) + 1 :=
        depth_succ_of_generate init (seq m) (seq (m + 1)) h_m_closure h_gen
      calc depth S init (seq (m + 1))
          ≤ depth S init (seq m) + 1         := h_succ
        _ ≤ (depth S init (seq 0) + m) + 1   := Nat.add_le_add_right h_m_depth 1
        _ = depth S init (seq 0) + (m + 1)   := by ring

/-! ## Section 2: Generation Step Increases Depth -/

/-- **Theorem**: Each generation step from a set A produces ideas
    at depth at most depth(A) + 1, where depth(A) is the maximum
    depth of elements in A. -/
theorem genStep_depth_bound (init A : Set S.Idea) (hA : A ⊆ closure S init)
    (d : ℕ) (hd : ∀ a ∈ A, depth S init a ≤ d) :
    ∀ b ∈ genStep S A, depth S init b ≤ d + 1 := by
  intro b hb
  -- b ∈ genStep A means ∃ a ∈ A, b ∈ gen(a)
  simp only [genStep, mem_iUnion] at hb
  obtain ⟨a, ha_in_A, hb_from_a⟩ := hb
  -- a ∈ closure by hA
  have ha_closure : a ∈ closure S init := hA ha_in_A
  -- depth(a) ≤ d by hd
  have ha_depth : depth S init a ≤ d := hd a ha_in_A
  -- depth(b) ≤ depth(a) + 1 by depth_succ_of_generate
  have hb_depth : depth S init b ≤ depth S init a + 1 :=
    depth_succ_of_generate init a b ha_closure hb_from_a
  -- Therefore depth(b) ≤ d + 1
  omega

/-! ## Section 3: Cumulative Generation Depth Bounds -/

/-- Helper lemma: If A ⊆ closure init, then genCumulative n A ⊆ closure init -/
lemma genCumulative_subset_closure (init A : Set S.Idea) (hA : A ⊆ closure S init) (n : ℕ) :
    genCumulative S n A ⊆ closure S init := by
  induction n with
  | zero =>
    simp only [genCumulative]
    exact hA
  | succ n ih_n =>
    intro x hx
    simp only [genCumulative, mem_union] at hx
    cases hx with
    | inl h => exact ih_n h
    | inr h =>
      simp only [genStep, mem_iUnion] at h
      obtain ⟨y, hy_cum, hx_gen⟩ := h
      have hy_closure : y ∈ closure S init := ih_n hy_cum
      have : x ∈ genStep S (closure S init) := by
        simp only [genStep, mem_iUnion]
        exact ⟨y, hy_closure, hx_gen⟩
      exact closure_closed_under_gen S init this

/-- **Theorem**: All ideas in genCumulative n A have depth at most
    d + n, where d bounds the depths in A. -/
theorem genCumulative_depth_bound (init A : Set S.Idea) (hA : A ⊆ closure S init)
    (d : ℕ) (hd : ∀ a ∈ A, depth S init a ≤ d) (n : ℕ) :
    ∀ b ∈ genCumulative S n A, depth S init b ≤ d + n := by
  induction n with
  | zero =>
    intro b hb
    simp only [genCumulative] at hb
    have : depth S init b ≤ d := hd b hb
    omega
  | succ n ih =>
    intro b hb
    simp only [genCumulative, mem_union] at hb
    cases hb with
    | inl h_prev =>
      have : depth S init b ≤ d + n := ih b h_prev
      omega
    | inr h_gen =>
      have h_bound : ∀ a ∈ genCumulative S n A, depth S init a ≤ d + n := ih
      have h_subset : genCumulative S n A ⊆ closure S init :=
        genCumulative_subset_closure init A hA n
      have : depth S init b ≤ (d + n) + 1 :=
        genStep_depth_bound init (genCumulative S n A) h_subset (d + n) h_bound b h_gen
      omega

/-! ## Section 4: Depth Monotonicity Under Closure -/

/-- **Theorem**: Taking closure from A only increases depth by the number
    of generation steps taken. For finitely-staged closures, we get a bound.
    
    Note: The original claim "closure doesn't increase depth beyond d" is FALSE
    in general - generating from elements at depth d produces elements at depth ≤ d+1,
    and iterating can increase depth arbitrarily.
    
    What IS true: if b ∈ genCumulative S n A, then depth S init b ≤ d + n
    (proved by `genCumulative_depth_bound`). 
    
    The correct statement requires knowing HOW MANY steps were taken. -/
theorem closure_depth_bound (init A : Set S.Idea)
    (hA : A ⊆ closure S init)
    (d : ℕ) (hd : ∀ a ∈ A, depth S init a ≤ d)
    (n : ℕ) :
    ∀ b ∈ genCumulative S n A, depth S init b ≤ d + n := 
  genCumulative_depth_bound init A hA d hd n

/-- Special case: if A ⊆ init, then A has depth 0 relative to init,
    and closure S A has depth = (steps taken). -/
theorem closure_from_init_depth (init : Set S.Idea) (n : ℕ) :
    ∀ b ∈ genCumulative S n init, depth S init b ≤ n := by
  have h0 : ∀ a ∈ init, depth S init a ≤ 0 := by
    intro a ha
    have : a ∈ closure S init := subset_closure ha
    rw [depth_zero_iff] at *
    left
    exact ha
  have hsub : init ⊆ closure S init := subset_closure
  have := genCumulative_depth_bound init init hsub 0 h0 n
  simp only [zero_add] at this
  exact this

/-! ## Section 5: The Main Depth Addition Theorem -/

/-- **Theorem (Depth Subadditivity)**: If we generate from init to reach A,
    and then generate from A to reach b, the total depth is bounded by
    the sum of the intermediate depths.
    
    More precisely: if all elements of A have depth ≤ d₁ relative to init,
    and b can be generated in n steps from A, then depth(b) relative to init
    is at most d₁ + n. -/
theorem depth_addition (init A : Set S.Idea) (b : S.Idea)
    (hA : A ⊆ closure S init)
    (d₁ : ℕ) (hd₁ : ∀ a ∈ A, depth S init a ≤ d₁)
    (n : ℕ) (hn : b ∈ genCumulative S n A) :
    depth S init b ≤ d₁ + n := by
  exact genCumulative_depth_bound init A hA d₁ hd₁ n b hn

/-- **Corollary**: The depth function is "sublinear" in path length:
    following a generation path of length k increases depth by at most k. -/
theorem depth_path_sublinear (init : Set S.Idea) (k : ℕ) (a b : S.Idea)
    (ha : a ∈ closure S init)
    (h_path : b ∈ genCumulative S k {a}) :
    depth S init b ≤ depth S init a + k := by
  apply depth_addition init {a} b
  · intro x hx
    rw [mem_singleton_iff] at hx
    rw [hx]
    exact ha
  · intro x hx
    rw [mem_singleton_iff] at hx
    rw [hx]
  · exact h_path

end SingleAgentIdeogenesis
