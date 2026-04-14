/-
# Depth Stratification Theorems

From FORMAL_ANTHROPOLOGY++ Chapter 6.4: Depth Theorems

This file proves fundamental theorems about depth stratification in
ideogenetic systems. The key insight is that depth partitions the closure
into disjoint strata, and ideas at different depths are fundamentally distinct.

## Key Results:
- Theorem 6.12: Depth Stratification - depth partitions the closure
- Theorem 6.13: Depth Lower Bound - prerequisites force depth increment
- Corollary: Novelty sets are disjoint
- Theorem: Depth respects subset ordering

## Mathematical Content:
The depth function creates a natural stratification of the ideogenetic
closure. Ideas appearing at stage n cannot appear at any earlier stage,
making depth a fundamental invariant that respects the generative structure.

## Dependencies:
- SingleAgent_Basic: IdeogeneticSystem, depth, noveltyAt
-/

import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.SingleAgent_DepthMonotonicity
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace DepthStratification

open SingleAgentIdeogenesis Set

variable {S : IdeogeneticSystem}

/-! ## Section 1: Novelty Disjointness -/

/-- Theorem 6.12 (Depth Stratification): Ideas appearing at different
    depths are distinct. The novelty sets partition the closure. -/
theorem novelty_disjoint (init : Set S.Idea) (m n : ℕ) (hmn : m ≠ n) :
    Disjoint (noveltyAt S init m) (noveltyAt S init n) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext a
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hm hn
  unfold noveltyAt at hm hn
  -- Case split on which of m, n is zero and which is larger
  by_cases h : m < n
  · -- Case m < n
    split_ifs at hm hn with hm0 hn0
    · -- Both m = 0 and n = 0: impossible since m < n
      omega
    · -- m = 0, n > 0
      subst hm0
      -- a ∈ init ⊆ gen^0 ⊆ gen^(n-1) since 0 ≤ n-1
      have : a ∈ genCumulative S (n - 1) init := by
        apply genCumulative_mono S init 0 (n - 1) _ hm
        omega
      exact hn.2 this
    · -- m > 0, n = 0: impossible since m < n
      omega
    · -- m > 0, n > 0
      -- a ∈ gen^m and a ∉ gen^(n-1), but gen^m ⊆ gen^(n-1) since m ≤ n-1
      have ha_m : a ∈ genCumulative S m init := hm.1
      have ha_not_n : a ∉ genCumulative S (n - 1) init := hn.2
      have : a ∈ genCumulative S (n - 1) init := by
        apply genCumulative_mono S init m (n - 1) _ ha_m
        omega
      exact ha_not_n this
  · -- Case n ≤ m
    push_neg at h
    have hnm : n < m := by omega
    split_ifs at hm hn with hm_eq0 hn_eq0 hm_ne0 hn_ne0
    · -- Both m = 0 and n = 0: impossible since n < m
      omega
    · -- m = 0 and n ≠ 0: impossible since n < m
      omega
    · -- m ≠ 0 and n = 0
      -- In this case, hn : a ∈ init, and hm says a ∈ genCumulative m init \ genCumulative (m-1) init
      have ha_in_init : a ∈ init := by
        rw [hn_eq0] at hn
        exact hn
      have : a ∈ genCumulative S (m - 1) init := by
        apply genCumulative_mono S init 0 (m - 1) _ ha_in_init
        omega
      exact hm.2 this
    · -- m ≠ 0 and n ≠ 0
      have ha_n : a ∈ genCumulative S n init := hn.1
      have ha_not_m : a ∉ genCumulative S (m - 1) init := hm.2
      have : a ∈ genCumulative S (m - 1) init := by
        apply genCumulative_mono S init n (m - 1) _ ha_n
        omega
      exact ha_not_m this

/-- Corollary: If an idea has depth m, it cannot have depth n for n ≠ m -/
theorem depth_unique (init : Set S.Idea) (a : S.Idea) (m n : ℕ)
    (hm : a ∈ noveltyAt S init m) (hn : a ∈ noveltyAt S init n) :
    m = n := by
  by_contra hmn
  have hd := novelty_disjoint init m n hmn
  rw [Set.disjoint_iff] at hd
  have ha_inter : a ∈ noveltyAt S init m ∩ noveltyAt S init n := ⟨hm, hn⟩
  have hempty := hd ha_inter
  exact hempty

/-! ## Section 2: Depth and Generation Steps -/

/-- If b is generated from a in one step, then depth increases by at most 1 -/
theorem depth_generation_step (init : Set S.Idea) (a b : S.Idea)
    (ha : a ∈ SingleAgentIdeogenesis.closure S init) (hb : b ∈ S.generate a) :
    depth S init b ≤ depth S init a + 1 := by
  have ha_cumul : a ∈ genCumulative S (depth S init a) init := 
    mem_genCumulative_depth S init a ha
  have hb_cumul : b ∈ genCumulative S (depth S init a + 1) init := by
    unfold genCumulative
    right
    use a
    exact ⟨ha_cumul, hb⟩
  have hb_in_closure : b ∈ SingleAgentIdeogenesis.closure S init := by
    rw [SingleAgentIdeogenesis.closure]
    simp only [Set.mem_iUnion]
    exact ⟨depth S init a + 1, hb_cumul⟩
  exact depth_le_of_mem S init b (depth S init a + 1) hb_cumul

/-- Structural lemma: Every element in genCumulative (n+1) either was already there at n,
    or was freshly generated from something at n -/
lemma genCumulative_succ_structure (n : ℕ) (init : Set S.Idea) (b : S.Idea)
    (hb : b ∈ genCumulative S (n + 1) init) :
    b ∈ genCumulative S n init ∨ ∃ a ∈ genCumulative S n init, b ∈ S.generate a := by
  unfold genCumulative at hb
  cases hb with
  | inl h => left; exact h
  | inr h =>
    right
    unfold genStep at h
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at h
    obtain ⟨a, ha, hgen⟩ := h
    exact ⟨a, ha, hgen⟩

/-- A system is novelty-producing if generation always creates ideas not in the source set.
    This is a structural property that can be verified for specific systems. -/
def isNoveltyProducing (S : IdeogeneticSystem) : Prop :=
  ∀ (A : Set S.Idea) (a : S.Idea), a ∈ A → S.generate a ∩ A = ∅

/-- Theorem: If a system is novelty-producing, then generation from an initial set
    produces ideas not in that set. This shows the axiom follows from the structural property. -/
theorem noveltyProducing_implies_novelty (S : IdeogeneticSystem)
    (h : isNoveltyProducing S) (init : Set S.Idea) (a : S.Idea) :
    a ∈ init → S.generate a ∩ init = ∅ :=
  h init a

/-- Theorem 6.13 (Depth Lower Bound): If b requires a as unique prerequisite,
    then depth(b) = depth(a) + 1.

    REVISED: Now requires a novelty hypothesis rather than relying on an axiom. -/
theorem depth_prerequisite (init : Set S.Idea) (a b : S.Idea)
    (ha : a ∈ SingleAgentIdeogenesis.closure S init)
    (hb : b ∈ S.generate a)
    (hunique : ∀ c : S.Idea, b ∈ S.generate c → c = a)
    (hnovelty : ∀ x ∈ init, S.generate x ∩ init = ∅) :
    depth S init b = depth S init a + 1 := by
  -- Upper bound from generation step
  have upper := depth_generation_step init a b ha hb

  -- Lower bound: show b ∉ genCumulative (depth a)
  have ha_at_da : a ∈ genCumulative S (depth S init a) init :=
    mem_genCumulative_depth S init a ha

  have hb_not_at_da : b ∉ genCumulative S (depth S init a) init := by
    intro hb_at_da
    -- We prove by induction on depth that if b ∈ genCumulative m and b ∈ generate a uniquely,
    -- then a ∈ genCumulative m
    have key : ∀ m, b ∈ genCumulative S m init → a ∈ genCumulative S m init := by
      intro m
      induction m with
      | zero =>
        intro hb0
        unfold genCumulative at hb0
        -- If b ∈ init and b ∈ generate a, then by novelty a ∈ init
        by_contra ha_not_init
        by_cases ha_in : a ∈ init
        · have : S.generate a ∩ init = ∅ := hnovelty a ha_in
          have : b ∈ S.generate a ∩ init := ⟨hb, hb0⟩
          rw [this] at this
          exact this
        · exact ha_not_init ha_in
      | succ m' ih =>
        intro hbm
        unfold genCumulative at hbm
        cases hbm with
        | inl h_prev =>
          -- b ∈ genCumulative m', use IH
          have ha_m' : a ∈ genCumulative S m' init := ih h_prev
          unfold genCumulative
          left
          exact ha_m'
        | inr h_gen_step =>
          -- b ∈ genStep (genCumulative m')
          unfold genStep at h_gen_step
          simp only [Set.mem_iUnion] at h_gen_step
          obtain ⟨c, hc, hb_from_c⟩ := h_gen_step
          -- By uniqueness: c = a
          have c_eq_a : c = a := hunique c hb_from_c
          subst c_eq_a
          unfold genCumulative
          left
          exact hc
    -- Apply key to depth a
    have ha_at_da' : a ∈ genCumulative S (depth S init a) init := key (depth S init a) hb_at_da
    -- But we already have this from ha_at_da, so no contradiction here
    -- The real issue is that if depth a > 0, then a ∉ genCumulative (depth a - 1)
    by_cases hda_zero : depth S init a = 0
    · -- If depth a = 0, then a ∈ init
      rw [hda_zero] at hb_at_da
      unfold genCumulative at hb_at_da
      unfold genCumulative at ha_at_da
      -- Both a and b are in init, but b ∈ generate a contradicts novelty
      have : S.generate a ∩ init = ∅ := hnovelty a ha_at_da
      have : b ∈ S.generate a ∩ init := ⟨hb, hb_at_da⟩
      rw [this] at this
      exact this
    · -- If depth a > 0, then a ∉ genCumulative (depth a - 1)
      -- But b ∈ genCumulative (depth a) means either:
      -- 1. b ∈ genCumulative (depth a - 1), or
      -- 2. b was generated from genCumulative (depth a - 1)
      have hda_pos : 0 < depth S init a := Nat.pos_of_ne_zero hda_zero
      have ha_not_earlier : a ∉ genCumulative S (depth S init a - 1) init := by
        intro ha_early
        have : depth S init a ≤ depth S init a - 1 :=
          depth_le_of_mem S init a (depth S init a - 1) ha_early
        omega
      -- Now analyze b's membership at depth a
      have : depth S init a = (depth S init a - 1) + 1 := by omega
      conv_lhs at hb_at_da => rw [this]
      unfold genCumulative at hb_at_da
      cases hb_at_da with
      | inl hb_earlier =>
        -- b ∈ genCumulative (depth a - 1)
        -- Then a ∈ genCumulative (depth a - 1) by key
        have : a ∈ genCumulative S (depth S init a - 1) init :=
          key (depth S init a - 1) hb_earlier
        exact ha_not_earlier this
      | inr hb_gen =>
        -- b ∈ genStep (genCumulative (depth a - 1))
        unfold genStep at hb_gen
        simp only [Set.mem_iUnion] at hb_gen
        obtain ⟨c, hc, hb_from_c⟩ := hb_gen
        -- By uniqueness c = a
        have : c = a := hunique c hb_from_c
        subst this
        exact ha_not_earlier hc

  -- b appears at depth a + 1
  have hb_at_succ : b ∈ genCumulative S (depth S init a + 1) init := by
    unfold genCumulative
    right
    unfold genStep
    simp only [Set.mem_iUnion]
    exact ⟨a, ha_at_da, hb⟩

  have hb_closure : b ∈ SingleAgentIdeogenesis.closure S init := by
    rw [SingleAgentIdeogenesis.closure]
    simp only [Set.mem_iUnion]
    exact ⟨depth S init a + 1, hb_at_succ⟩

  -- depth b ≥ depth a + 1 because b ∉ genCumulative (depth a)
  have lower : depth S init a + 1 ≤ depth S init b := by
    by_contra h_neg
    push_neg at h_neg
    -- So depth b ≤ depth a
    have hb_at_db : b ∈ genCumulative S (depth S init b) init :=
      mem_genCumulative_depth S init b hb_closure
    have : genCumulative S (depth S init b) init ⊆ genCumulative S (depth S init a) init := by
      apply genCumulative_mono
      omega
    have : b ∈ genCumulative S (depth S init a) init := this hb_at_db
    exact hb_not_at_da this

  omega

/-! ## Section 3: Depth Monotonicity -/

/-- If A ⊆ B, then depth with respect to A is at least depth with respect to B -/
theorem depth_antimono (a : S.Idea) (A B : Set S.Idea)
    (hAB : A ⊆ B) (ha : a ∈ SingleAgentIdeogenesis.closure S A) :
    depth S B a ≤ depth S A a := by
  have ha_at_dA : a ∈ genCumulative S (depth S A a) A := mem_genCumulative_depth S A a ha
  have mono : ∀ n, genCumulative S n A ⊆ genCumulative S n B := by
    intro n
    induction n with
    | zero =>
      unfold genCumulative
      exact hAB
    | succ k ih =>
      unfold genCumulative
      intro x hx
      cases hx with
      | inl h => left; exact ih h
      | inr h =>
        unfold genStep at h
        simp only [Set.mem_iUnion] at h
        obtain ⟨y, hy, hgen⟩ := h
        right
        unfold genStep
        simp only [Set.mem_iUnion]
        exact ⟨y, ih hy, hgen⟩
  have : a ∈ genCumulative S (depth S A a) B := mono (depth S A a) ha_at_dA
  exact depth_le_of_mem S B a (depth S A a) this

/-- Ideas reachable from the primordial have well-defined finite depth -/
theorem primordial_depth_welldef (a : S.Idea)
    (h : a ∈ SingleAgentIdeogenesis.closure S {S.primordial}) :
    ∃ n : ℕ, a ∈ noveltyAt S {S.primordial} n := by
  simp only [SingleAgentIdeogenesis.closure, Set.mem_iUnion] at h
  obtain ⟨n, hn⟩ := h
  use depth S {S.primordial} a
  unfold noveltyAt
  split_ifs with hd
  · have : depth S {S.primordial} a = 0 := hd
    rw [this]
    have ha_at_0 : a ∈ genCumulative S 0 {S.primordial} := by
      rw [←this]
      exact mem_genCumulative_depth S {S.primordial} a h
    unfold genCumulative at ha_at_0
    exact ha_at_0
  · constructor
    · exact mem_genCumulative_depth S {S.primordial} a h
    · intro ha_prev
      have : depth S {S.primordial} a ≤ depth S {S.primordial} a - 1 := 
        depth_le_of_mem S {S.primordial} a (depth S {S.primordial} a - 1) ha_prev
      omega

/-! ## Section 4: Depth Bounds and Inequalities -/

/-- Primordial has depth 0 -/
theorem primordial_depth_zero :
    depth S {S.primordial} S.primordial = 0 := by
  unfold depth
  have h0 : S.primordial ∈ genCumulative S 0 {S.primordial} := by
    unfold genCumulative
    exact Set.mem_singleton _
  have hex : ∃ n, S.primordial ∈ genCumulative S n {S.primordial} := ⟨0, h0⟩
  simp only [dif_pos hex]
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min'
  exact h0

/-- Depth is preserved by bijective morphisms -/
theorem depth_preserved_by_iso (S T : IdeogeneticSystem)
    (f : S.Idea → T.Idea) (hbij : Function.Bijective f)
    (hmorph : ∀ a : S.Idea, f '' (S.generate a) = T.generate (f a))
    (hprim : f S.primordial = T.primordial)
    (a_val : S.Idea) :
    depth T {T.primordial} (f a_val) = depth S {S.primordial} a_val := by
  have h_genCum : ∀ n, f '' (genCumulative S n {S.primordial}) = genCumulative T n {T.primordial} := by
    intro n
    induction n with
    | zero =>
      simp only [genCumulative, Set.image_singleton, hprim]
    | succ n ih =>
      simp only [genCumulative, Set.image_union, ih]
      congr 1
      ext b
      constructor
      · intro ⟨c, hc, hfcb⟩
        unfold genStep at hc ⊢
        simp only [Set.mem_iUnion] at hc ⊢
        obtain ⟨a', ha', hc'⟩ := hc
        use f a'
        refine ⟨?_, ?_⟩
        · have : f a' ∈ f '' genCumulative S n {S.primordial} := Set.mem_image_of_mem f ha'
          rw [ih] at this
          exact this
        · rw [←hmorph a']
          rw [←hfcb]
          exact Set.mem_image_of_mem f hc'
      · intro hb
        unfold genStep at hb ⊢
        simp only [Set.mem_iUnion, exists_prop] at hb ⊢
        obtain ⟨b', hb', hbb'⟩ := hb
        have hb'_in_image : b' ∈ f '' genCumulative S n {S.primordial} := by
          rw [ih]; exact hb'
        obtain ⟨a', ha', hfa'b'⟩ := hb'_in_image
        subst hfa'b'
        rw [←hmorph a'] at hbb'
        obtain ⟨c, hc, hfcb⟩ := hbb'
        exact ⟨c, ⟨a', ha', hc⟩, hfcb⟩
  by_cases ha_val : a_val ∈ SingleAgentIdeogenesis.closure S {S.primordial}
  · have hfa_val : f a_val ∈ SingleAgentIdeogenesis.closure T {T.primordial} := by
      rw [SingleAgentIdeogenesis.closure, Set.mem_iUnion] at ha_val ⊢
      obtain ⟨n, hn⟩ := ha_val
      use n
      rw [←h_genCum]
      exact Set.mem_image_of_mem f hn
    unfold depth
    simp only [dif_pos ha_val, dif_pos hfa_val]
    apply Nat.find_eq_iff.mpr
    constructor
    · rw [←h_genCum]
      exact Set.mem_image_of_mem f (Nat.find_spec ha_val)
    · intro m hm hcontra
      rw [←h_genCum] at hcontra
      obtain ⟨a', ha', hfa'⟩ := hcontra
      have : a_val = a' := hbij.1 hfa'
      rw [this] at ha'
      exact Nat.find_min ha_val hm ha'
  · have hfa_val : f a_val ∉ SingleAgentIdeogenesis.closure T {T.primordial} := by
      intro hcontra
      apply ha_val
      rw [SingleAgentIdeogenesis.closure, Set.mem_iUnion] at hcontra ⊢
      obtain ⟨n, hn⟩ := hcontra
      rw [h_genCum] at hn
      obtain ⟨a', ha', hfa'⟩ := hn
      use n
      have : a_val = a' := hbij.1 hfa'
      rw [this]
      exact ha'
    unfold depth
    rw [dif_neg ha_val, dif_neg hfa_val]

/-! ## Section 5: Depth Comparison and Ordering -/

/-- If a generates b directly and b is novel at depth(a), then depth strictly increases. -/
theorem generation_increases_depth (init : Set S.Idea) (a b : S.Idea)
    (ha : a ∈ SingleAgentIdeogenesis.closure S init) (hb : b ∈ S.generate a)
    (hb_novel : b ∉ genCumulative S (depth S init a) init) :
    depth S init a < depth S init b := by
  have hdepth := proper_generation_increases_depth S init a b (depth S init a) rfl ha hb hb_novel
  simpa [hdepth] using Nat.lt_succ_self (depth S init a)

/-- A generation path: each successive element is generated from the previous one. -/
inductive GenPath : List S.Idea → Prop
  | nil : GenPath []
  | single (a : S.Idea) : GenPath [a]
  | cons {a b : S.Idea} {l : List S.Idea} (h : b ∈ S.generate a) (ht : GenPath (b :: l)) :
      GenPath (a :: b :: l)

/-- Along a generation path, depth can increase by at most the path length. -/
theorem depth_partial_order (init : Set S.Idea) :
    ∀ path : List S.Idea, GenPath path →
    ∀ a b : S.Idea, path.head? = some a → path.getLast? = some b →
    a ∈ SingleAgentIdeogenesis.closure S init →
    depth S init b ≤ depth S init a + path.length := by
  intro path hpath
  induction hpath with
  | nil =>
      intro a b hhead hlast _
      simp at hhead
  | single a' =>
      intro a b hhead hlast _
      simp at hhead hlast
      subst hhead hlast
      simp
  | cons hstep ht ih =>
      intro a_start b_end hhead hlast ha_start
      -- The path has form a_cons :: b_cons :: tail where hstep : b_cons ∈ S.generate a_cons
      -- and ht : GenPath (b_cons :: tail)
      -- We need to match this against the actual path
      have ⟨a_first, b_second, rest, hpath_eq⟩ : ∃ a_first b_second rest, path = a_first :: b_second :: rest := by
        match path with
        | [] => cases hhead
        | [x] => cases ht
        | x :: y :: zs => exact ⟨x, y, zs, rfl⟩
      subst hpath_eq
      simp at hhead hlast
      -- hhead says a_start = a_first
      subst hhead
      -- Now a_start is in closure, b_second ∈ generate a_start (via hstep)
      have hb_second_in_closure : b_second ∈ SingleAgentIdeogenesis.closure S init := by
        have hb_second_cumul : b_second ∈ genCumulative S (depth S init a_start + 1) init := by
          unfold genCumulative
          right
          use a_start
          exact ⟨mem_genCumulative_depth S init a_start ha_start, hstep⟩
        simp only [SingleAgentIdeogenesis.closure, Set.mem_iUnion]
        exact ⟨depth S init a_start + 1, hb_second_cumul⟩
      have hstep_depth : depth S init b_second ≤ depth S init a_start + 1 :=
        depth_generation_step init a_start b_second ha_start hstep
      have htail_head : (b_second :: rest).head? = some b_second := by rfl
      -- Apply IH: for path (b_second :: rest), from b_second to b_end
      have ih_applied := ih b_second b_end htail_head hlast hb_second_in_closure
      have hlen : (a_start :: b_second :: rest).length = 1 + (b_second :: rest).length := by simp
      calc depth S init b_end
          ≤ depth S init b_second + (b_second :: rest).length := ih_applied
        _ ≤ (depth S init a_start + 1) + (b_second :: rest).length := by linarith
        _ = depth S init a_start + (1 + (b_second :: rest).length) := by ring
        _ = depth S init a_start + (a_start :: b_second :: rest).length := by rw [←hlen]

/-! ## Section 6: Complete Theorems -/

/-- The closure is the union of all novelty sets -/
theorem closure_eq_union_novelty (init : Set S.Idea) :
    SingleAgentIdeogenesis.closure S init = ⋃ n : ℕ, noveltyAt S init n := by
  ext a
  constructor
  · intro ha
    rw [SingleAgentIdeogenesis.closure, Set.mem_iUnion] at ha
    obtain ⟨n, hn⟩ := ha
    simp only [Set.mem_iUnion]
    use depth S init a
    unfold noveltyAt
    split_ifs with hd_zero
    · -- Case: depth = 0
      have ha_closure : a ∈ SingleAgentIdeogenesis.closure S init := by
        rw [SingleAgentIdeogenesis.closure, Set.mem_iUnion]
        exact ⟨n, hn⟩
      have ha_at_zero : a ∈ genCumulative S (depth S init a) init :=
        mem_genCumulative_depth S init a ha_closure
      rw [hd_zero] at ha_at_zero
      unfold genCumulative at ha_at_zero
      exact ha_at_zero
    · -- Case: depth > 0
      constructor
      · have ha_closure : a ∈ SingleAgentIdeogenesis.closure S init := by
          rw [SingleAgentIdeogenesis.closure, Set.mem_iUnion]
          exact ⟨n, hn⟩
        exact mem_genCumulative_depth S init a ha_closure
      · intro ha_prev
        have : depth S init a ≤ depth S init a - 1 :=
          depth_le_of_mem S init a (depth S init a - 1) ha_prev
        omega
  · intro ha
    simp only [Set.mem_iUnion] at ha
    obtain ⟨n, hn⟩ := ha
    unfold noveltyAt at hn
    split_ifs at hn with h0
    · rw [SingleAgentIdeogenesis.closure, Set.mem_iUnion]
      use 0
      exact hn
    · rw [SingleAgentIdeogenesis.closure, Set.mem_iUnion]
      use n
      exact hn.1

/-- Novelty at stage n is bounded by generation from stage n-1 -/
theorem novelty_generated_from_prev (init : Set S.Idea) (n : ℕ) (hn : n > 0) :
    noveltyAt S init n ⊆ ⋃ a ∈ genCumulative S (n - 1) init, S.generate a := by
  intro b hb
  unfold noveltyAt at hb
  rw [if_neg (Nat.pos_iff_ne_zero.mp hn)] at hb
  have hb_in_n : b ∈ genCumulative S n init := hb.1
  have hb_not_pred : b ∉ genCumulative S (n - 1) init := hb.2
  -- Rewrite n as (n-1) + 1
  have hn_succ : n = (n - 1) + 1 := by omega
  rw [hn_succ] at hb_in_n
  unfold genCumulative at hb_in_n
  cases hb_in_n with
  | inl h => exact absurd h hb_not_pred
  | inr h =>
    simp only [Set.mem_iUnion]
    exact h

/-! ## Section 7: Auxiliary Complete Proofs -/

/-- Novelty at stage 0 contains only the initial ideas -/
theorem novelty_at_zero (init : Set S.Idea) :
    noveltyAt S init 0 = init := by
  unfold noveltyAt
  simp

/-- Novelty sets are monotone in the initial set for disjoint additions -/
theorem novelty_monotone_in_init (init₁ init₂ : Set S.Idea) (n : ℕ)
    (hsub : init₁ ⊆ init₂) :
    noveltyAt S init₁ n ⊆ genCumulative S n init₂ := by
  intro a ha
  unfold noveltyAt at ha
  split_ifs at ha with h
  · have : n = 0 := h
    rw [this]
    unfold genCumulative
    exact hsub ha
  · have hcumul_mono : genCumulative S n init₁ ⊆ genCumulative S n init₂ := by
      intro x
      induction n generalizing x with
      | zero =>
        intro hx
        unfold genCumulative at hx ⊢
        exact hsub hx
      | succ k ih =>
        intro hx
        unfold genCumulative at hx ⊢
        cases hx with
        | inl hprev => left; exact ih hprev
        | inr hstep =>
          right
          unfold genStep at hstep ⊢
          simp only [Set.mem_iUnion] at hstep ⊢
          obtain ⟨y, hy, hgen⟩ := hstep
          exact ⟨y, ih hy, hgen⟩
    exact hcumul_mono ha.1

/-- If init is finite and generation is finitary, then each novelty set is finite -/
theorem novelty_finite_of_finitary (init : Set S.Idea) (n : ℕ)
    (hinit : init.Finite)
    (hgen : ∀ a : S.Idea, (S.generate a).Finite) :
    (noveltyAt S init n).Finite := by
  have hcumul : (genCumulative S n init).Finite := by
    induction n with
    | zero =>
      unfold genCumulative
      exact hinit
    | succ k ih =>
      unfold genCumulative
      apply Set.Finite.union ih
      have : (⋃ a ∈ genCumulative S k init, S.generate a).Finite := by
        apply Set.Finite.biUnion ih
        intro a _
        exact hgen a
      unfold genStep
      simp only [Set.mem_iUnion]
      exact this
  apply Set.Finite.subset hcumul
  intro a ha
  unfold noveltyAt at ha
  split_ifs at ha with h
  · have : n = 0 := h
    rw [this]
    unfold genCumulative
    exact ha
  · exact ha.1

end DepthStratification
