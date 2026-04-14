/-
# Depth Monotonicity Properties

## CURRENT ASSUMPTIONS AND WEAKENINGS (Updated 2026-02-08)

### Eliminated/Weakened Assumptions:
1. **IsNoveltyProducing** (Definition 3.1):
   - OLD: Required ALL generated ideas from closure to be novel (∀ a b, a ∈ closure → b ∈ generate a → b ∉ init)
   - NEW: Only requires SPECIFIC idea b to be novel when used (b ∈ generate a → b ∉ init for specific a,b)
   - IMPACT: Now applies to systems with partial rediscovery; theorems only assume novelty where needed

2. **IsLocallyBounded** (Definition 3.2):
   - OLD: Required all systems to have bounded depth from every reachable idea
   - NEW: Only required for specific theorems about closure diameter (3.4)
   - IMPACT: Core monotonicity theorems (3.1, 3.2, 3.3) now work for ALL systems, even with unbounded branching

3. **Primordial/Initial Set Requirements**:
   - OLD: Some theorems implicitly required nonempty initial sets
   - NEW: Made explicit and minimal; most theorems work for arbitrary initial sets
   - IMPACT: Theorems now apply to arbitrary seed sets, not just single primordial ideas

### Theorems Strengthened by Weakenings:
- **Theorem 3.1** (generation_preserves_depth_bounds): Now requires NO special properties, works for all systems
- **Theorem 3.2** (generated_idea_positive_depth): Only requires specific idea to be novel, not whole system
- **Theorem 3.3** (proper_generation_increases_depth): Only requires specific idea to be novel
- **Theorem 3.4** (depth_difference_bound_in_closure): Only theorem requiring IsLocallyBounded (inherent to diameter concept)

### Sorry/Admit Locations:
- **NONE** - All proofs remain complete with weakened assumptions

### Global Axioms:
- **NONE** - Only uses explicit hypotheses in theorem signatures
- Uses Classical.propDecidable and Classical.decPred for depth computation (standard in Lean)

### Key Insight:
By moving from global system properties to local conditions on specific ideas, these theorems now apply to a much broader class of ideogenetic systems while maintaining full rigor.

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.SingleAgent_Basic

namespace SingleAgentIdeogenesis

open Set

/-! ## Section 0: Weakened Property Definitions

We define properties that can be checked locally rather than globally, making
theorems applicable to a much broader class of systems.
-/

/-- **Definition 3.1 (Weakened): Local Novelty Property**

    An idea b is novel with respect to initial set init if it's not in init.
    This is a property of individual ideas, not whole systems.

    CONTRAST with old IsNoveltyProducing: That required ALL generated ideas
    to be novel. This only checks specific ideas, allowing partial rediscovery. -/
def isNovel (S : IdeogeneticSystem) (init : Set S.Idea) (b : S.Idea) : Prop :=
  b ∉ init

/-- A generator produces a novel idea if that specific generated idea is not in init.
    This is much weaker than requiring all generated ideas to be novel. -/
def producesNovel (S : IdeogeneticSystem) (init : Set S.Idea) (a b : S.Idea) : Prop :=
  b ∈ S.generate a → isNovel S init b

/-! ## Definition 3.2: Locally Bounded Systems (Keep for diameter theorem only)

This property is only needed for closure diameter bounds. All other theorems
work without it.
-/

/-- An ideogenetic system is locally bounded if ideas reachable from any single idea
    have bounded depth relative to that idea.

    NOTE: This is only used in depth_difference_bound_in_closure (Theorem 3.4).
    All other theorems work for unbounded systems. -/
def IsLocallyBounded (S : IdeogeneticSystem) (init : Set S.Idea) : Prop :=
  ∀ a ∈ closure S init, ∃ n, ∀ b ∈ closure S {a}, depth S init b ≤ depth S init a + n

/-- For locally bounded systems, ideas reachable from a single idea have bounded depth. -/
theorem closure_depth_bounded (S : IdeogeneticSystem) (init : Set S.Idea)
    (hbounded : IsLocallyBounded S init) (a : S.Idea)
    (ha : a ∈ closure S init) :
    ∃ n, ∀ b ∈ closure S {a}, depth S init b ≤ depth S init a + n := by
  exact hbounded a ha

/-! ## Section 1: Basic Depth Properties (NO SPECIAL ASSUMPTIONS NEEDED) -/

/-- **Theorem 3.1: Generation Preserves Depth Bounds**

    If all ideas in a set A have depth at most d, then all ideas generated
    from A have depth at most d + 1.

    **STRENGTHENED**: Now requires NO special system properties.
    Works for ALL ideogenetic systems, even with unbounded branching.

    This establishes that generation increases depth by at most 1. -/
theorem generation_preserves_depth_bounds (S : IdeogeneticSystem)
    (init : Set S.Idea) (A : Set S.Idea) (d : ℕ)
    (hA : A ⊆ genCumulative S d init)
    (a : S.Idea) (ha : a ∈ A) :
    ∀ b ∈ S.generate a, depth S init b ≤ d + 1 := by
  intro b hb
  -- b ∈ generate a, and a ∈ genCumulative d
  -- So b ∈ genCumulative (d+1) by definition
  have ha_depth : depth S init a ≤ d := depth_le_of_mem S init a d (hA ha)
  -- b is generated from a, so appears at stage ≤ d+1
  have hb_cumu : b ∈ genCumulative S (d + 1) init := by
    unfold genCumulative
    right
    unfold genStep
    simp only [Set.mem_iUnion]
    use a, hA ha, hb
  exact depth_le_of_mem S init b (d + 1) hb_cumu

/-- **Theorem 3.2: Depth Lower Bound for Generated Ideas**

    If b is generated from a reachable idea and b is novel (not in init),
    then depth b > 0.

    **STRENGTHENED**: Only requires b to be novel, not the whole system.
    Works for systems where some ideas can be rediscovered.

    Generated novel ideas are never primordial. -/
theorem generated_idea_positive_depth (S : IdeogeneticSystem)
    (init : Set S.Idea) (a b : S.Idea) (d : ℕ)
    (ha : a ∈ genCumulative S d init)
    (hb : b ∈ S.generate a)
    (hb_novel : isNovel S init b) :
    depth S init b > 0 := by
  -- b is generated, so not in init by novelty property
  have hb_not_init : b ∉ init := hb_novel

  -- b appears at some stage since it's generated from a reachable idea
  have hb_cumu : b ∈ genCumulative S (d + 1) init := by
    unfold genCumulative
    right
    unfold genStep
    simp only [Set.mem_iUnion]
    use a, ha, hb

  -- So depth b is defined and b appears at stage depth b
  have hb_closure : b ∈ closure S init := by
    simp only [closure, Set.mem_iUnion]
    exact ⟨d + 1, hb_cumu⟩

  have hb_at_depth : b ∈ genCumulative S (depth S init b) init :=
    mem_genCumulative_depth S init b hb_closure

  -- If depth b = 0, then b ∈ genCumulative 0 init = init
  by_contra h
  push_neg at h
  have hb_zero : depth S init b = 0 := by omega

  -- So b ∈ genCumulative 0 init
  rw [hb_zero] at hb_at_depth
  simp only [genCumulative] at hb_at_depth

  -- But b ∉ init, contradiction
  exact hb_not_init hb_at_depth

/-- **Theorem: Depth Semi-Monotonicity**

    If A ⊆ B ⊆ genCumulative d, then for all a ∈ A, depth a ≤ d.

    **STRENGTHENED**: Requires NO special system properties.

    This is a restatement of depth_le_of_mem, emphasizing monotonicity. -/
theorem depth_semi_monotone (S : IdeogeneticSystem)
    (init : Set S.Idea) (A B : Set S.Idea) (d : ℕ)
    (hAB : A ⊆ B) (hB : B ⊆ genCumulative S d init) :
    ∀ a ∈ A, depth S init a ≤ d := by
  intro a ha
  have : a ∈ B := hAB ha
  exact depth_le_of_mem S init a d (hB this)

/-! ## Section 2: Strict Depth Relationships (MINIMAL ASSUMPTIONS) -/

/-- **Helper Lemma: Closure Shift**

    If a appears at stage da from init, then ideas reachable from {a}
    appear at stage ≥ da from init.

    **STRENGTHENED**: Requires NO special system properties. -/
lemma closure_shift (S : IdeogeneticSystem) (init : Set S.Idea) (a b : S.Idea)
    (da : ℕ) (ha : a ∈ genCumulative S da init) (n : ℕ)
    (hb : b ∈ genCumulative S n {a}) :
    b ∈ genCumulative S (da + n) init := by
  induction n generalizing b with
  | zero =>
    -- genCumulative 0 {a} = {a}
    simp only [genCumulative] at hb
    have : b = a := hb
    rw [this]
    simp only [Nat.add_zero]
    exact ha
  | succ n ih =>
    -- genCumulative (n+1) {a} = genCumulative n {a} ∪ genStep (genCumulative n {a})
    unfold genCumulative at hb
    rcases hb with hb_old | hb_new
    · -- b ∈ genCumulative n {a}
      have : b ∈ genCumulative S (da + n) init := ih b hb_old
      -- genCumulative is monotone
      have mono : genCumulative S (da + n) init ⊆ genCumulative S (da + n + 1) init := by
        intro x hx
        unfold genCumulative
        left
        exact hx
      have hrw : da + (n + 1) = da + n + 1 := by omega
      rw [hrw]
      exact mono this
    · -- b ∈ genStep (genCumulative n {a})
      unfold genStep at hb_new
      simp only [Set.mem_iUnion] at hb_new
      obtain ⟨c, hc_in_n, hb_gen⟩ := hb_new
      -- c ∈ genCumulative n {a}, so c ∈ genCumulative (da + n) init by IH
      have hc : c ∈ genCumulative S (da + n) init := ih c hc_in_n
      -- b ∈ generate c, so b ∈ genStep (genCumulative (da + n) init)
      have hb_step : b ∈ genStep S (genCumulative S (da + n) init) := by
        unfold genStep
        simp only [Set.mem_iUnion]
        exact ⟨c, hc, hb_gen⟩
      -- Therefore b ∈ genCumulative (da + n + 1) init
      have hrw : da + (n + 1) = da + n + 1 := by omega
      rw [hrw]
      unfold genCumulative
      right
      exact hb_step

/-- **Helper Lemma: Closure Shift (Strong Form)**

    If a appears at stage da from init and b is reachable from {a} in n steps with n > 0,
    then b appears at stage > da from init.

    **STRENGTHENED**: Requires NO special system properties. -/
lemma closure_shift_strong (S : IdeogeneticSystem) (init : Set S.Idea) (a b : S.Idea)
    (da : ℕ) (ha : a ∈ genCumulative S da init) (n : ℕ) (hn_pos : n > 0)
    (hb : b ∈ genCumulative S n {a}) (hb_ne : b ≠ a) :
    ∃ m > da, b ∈ genCumulative S m init := by
  -- Since n > 0 and b ≠ a, b must be generated from some idea in closure {a}
  have : b ∈ genCumulative S (da + n) init := closure_shift S init a b da ha n hb

  -- We claim that if b ≠ a and n > 0, then b appears after stage da
  -- Proof: b ∈ genCumulative n {a} with n > 0 means either:
  --  1) b ∈ genCumulative (n-1) {a}, or
  --  2) b ∈ genStep (genCumulative (n-1) {a})

  use da + n
  constructor
  · omega
  · exact this

/-- **Theorem: Novel Path Implies Depth Ordering**

    If b is reachable from a (i.e., b ∈ closure {a}) and b does not appear
    before a (i.e., depth b ≥ depth a from init), then the path from a to b
    is depth-preserving.

    **STRENGTHENED**: Requires NO special system properties.

    This is the correct statement: if a is necessary to reach b (b doesn't
    appear earlier), then depth b ≥ depth a.

    Note: The original statement "b ∈ closure {a} implies depth b ≥ depth a"
    is FALSE because b could appear earlier through a different path. -/
theorem novel_path_implies_depth_ordering (S : IdeogeneticSystem)
    (init : Set S.Idea) (a b : S.Idea)
    (ha : a ∈ closure S init)
    (hb : b ∈ closure S init)
    (hpath : b ∈ closure S {a})
    (hnovel : b ∉ genCumulative S (depth S init a - 1) init) :
    depth S init b ≥ depth S init a := by
  -- Let da = depth a and db = depth b
  let da := depth S init a
  let db := depth S init b

  -- a first appears at stage da
  have ha_at_da : a ∈ genCumulative S da init := mem_genCumulative_depth S init a ha

  -- b first appears at stage db
  have hb_at_db : b ∈ genCumulative S db init := mem_genCumulative_depth S init b hb

  -- To prove db ≥ da, assume db < da for contradiction
  by_contra h_contra
  push_neg at h_contra
  -- So db < da

  -- If db < da, then db ≤ da - 1 (since they're natural numbers)
  have hdb_bound : db ≤ da - 1 := by omega

  -- Since b appears at stage db, and db ≤ da - 1:
  have hb_early : b ∈ genCumulative S (da - 1) init :=
    genCumulative_mono S init db (da - 1) hdb_bound hb_at_db

  -- But this contradicts hnovel
  exact hnovel hb_early

/-- **Theorem 3.3: Proper Generation Increases Depth**

    If b ∈ generate a and b ∉ genCumulative (depth a), then depth b = depth a + 1.

    **STRENGTHENED**: Requires NO special system properties.
    Works for all systems, even those with rediscovery.

    This is the key theorem showing strict depth increase for novel generation. -/
theorem proper_generation_increases_depth (S : IdeogeneticSystem)
    (init : Set S.Idea) (a b : S.Idea) (da : ℕ)
    (ha_depth : depth S init a = da)
    (ha_reach : a ∈ closure S init)
    (hb : b ∈ S.generate a)
    (hb_novel : b ∉ genCumulative S da init) :
    depth S init b = da + 1 := by
  -- b is generated at stage da + 1 (first appearance)
  have ha_at_da : a ∈ genCumulative S da init := by
    rw [← ha_depth]
    exact mem_genCumulative_depth S init a ha_reach

  have hb_at_next : b ∈ genCumulative S (da + 1) init := by
    unfold genCumulative
    right
    unfold genStep
    simp only [Set.mem_iUnion]
    use a, ha_at_da, hb

  -- b does not appear at any stage ≤ da (by hb_novel and predecessors)
  have hb_not_earlier : ∀ k ≤ da, b ∉ genCumulative S k init := by
    intro k hk
    intro hb_early
    cases hk.lt_or_eq with
    | inl hlt =>
      -- b ∈ genCumulative k and k < da
      -- Then b ∈ genCumulative da (by monotonicity)
      have : b ∈ genCumulative S da init := genCumulative_mono S init k da (Nat.le_of_lt hlt) hb_early
      contradiction
    | inr heq =>
      -- k = da
      rw [heq] at hb_early
      contradiction

  -- Therefore, depth b is the minimal n such that b ∈ genCumulative n
  -- We have b ∈ genCumulative (da + 1) and b ∉ genCumulative k for all k ≤ da
  -- So depth b = da + 1
  have hex : ∃ n, b ∈ genCumulative S n init := ⟨da + 1, hb_at_next⟩
  unfold depth
  rw [dif_pos hex]
  haveI : DecidablePred (fun k => b ∈ genCumulative S k init) := Classical.decPred _
  -- Nat.find gives the minimal n satisfying the property
  -- We need to show that da + 1 is the minimal such n
  have hspec := @Nat.find_spec (fun k => b ∈ genCumulative S k init) _ hex
  have hle := @Nat.find_le (da + 1) (fun k => b ∈ genCumulative S k init) _ hex hb_at_next
  -- Nat.find hex ≤ da + 1 and Nat.find hex ∈ genCumulative
  -- If Nat.find hex < da + 1, then Nat.find hex ≤ da
  by_cases h : Nat.find hex < da + 1
  · have : Nat.find hex ≤ da := Nat.lt_succ_iff.mp h
    exact absurd hspec (hb_not_earlier (Nat.find hex) this)
  · -- We need: Nat.find hex = da + 1
    -- We have: hle : Nat.find hex ≤ da + 1 and h : ¬(Nat.find hex < da + 1)
    -- From h, we get da + 1 ≤ Nat.find hex
    -- Combined with hle, we get Nat.find hex = da + 1
    have hge : da + 1 ≤ Nat.find hex := Nat.le_of_not_lt h
    have hfind_eq : Nat.find hex = da + 1 := le_antisymm hle hge
    convert hfind_eq

/-! ## Section 3: Depth Difference Bounds (MINIMAL ASSUMPTIONS) -/

/-- **Theorem: Direct Generation Has Depth Difference ≤ 1**

    If b ∈ generate a and a is at depth da, then either:
    1. b is at depth da + 1 (novel generation), or
    2. b was already present at depth ≤ da (rediscovery)

    **STRENGTHENED**: Requires NO special system properties.

    This partitions generated ideas by their novelty. -/
theorem direct_generation_depth_difference (S : IdeogeneticSystem)
    (init : Set S.Idea) (a b : S.Idea) (da : ℕ)
    (ha : depth S init a = da)
    (ha_reach : a ∈ closure S init)
    (hb : b ∈ S.generate a) :
    (depth S init b = da + 1) ∨ (depth S init b ≤ da) := by
  by_cases h : b ∈ genCumulative S da init
  · -- Case: b already exists at depth ≤ da
    right
    exact depth_le_of_mem S init b da h
  · -- Case: b does not exist at depth ≤ da
    left
    exact proper_generation_increases_depth S init a b da ha ha_reach hb h

/-- **Theorem 3.4: Depth Difference Bounds for Closure**

    For any ideas a, b in primordialClosure, if b ∈ closure {a}, then:
    depth b ≤ depth a + diameter(closure {a})

    where diameter is the maximum depth difference within the closure.

    **NOTE**: This is the ONLY theorem requiring IsLocallyBounded, since
    diameter is inherently about bounding distances.

    This bounds how far "downstream" generated ideas can be. -/
noncomputable def closure_diameter (S : IdeogeneticSystem) (init : Set S.Idea) (a : S.Idea) : ℕ :=
  -- Infimum of all n such that depth b ≤ depth a + n for all b in closure {a}
  sInf {n | ∀ b ∈ closure S {a}, depth S init b ≤ depth S init a + n}

theorem depth_difference_bound_in_closure (S : IdeogeneticSystem)
    (hbounded : IsLocallyBounded S {S.primordial})
    (a b : S.Idea)
    (ha : a ∈ primordialClosure S)
    (hb : b ∈ closure S {a}) :
    primordialDepth S b ≤ primordialDepth S a + closure_diameter S {S.primordial} a := by
  unfold closure_diameter primordialDepth primordialClosure at *

  -- Apply the theorem to get bounded depth in closure {a}
  obtain ⟨n, hn⟩ := closure_depth_bounded S {S.primordial} hbounded a ha

  -- sInf satisfies the property (it's the minimum witness)
  have h_exists : ∃ m, ∀ b' ∈ closure S {a}, depth S {S.primordial} b' ≤ depth S {S.primordial} a + m := ⟨n, hn⟩
  have h_sInf_prop : ∀ b' ∈ closure S {a}, depth S {S.primordial} b' ≤ depth S {S.primordial} a +
      sInf {m | ∀ b' ∈ closure S {a}, depth S {S.primordial} b' ≤ depth S {S.primordial} a + m} :=
    Nat.sInf_mem h_exists

  -- Apply to b
  exact h_sInf_prop b hb

/-! ## Section 4: Completeness Results (NO SPECIAL ASSUMPTIONS) -/

/-- **Theorem: Depth Function is Well-Defined**

    For any idea reachable from init, the depth function returns a finite value.

    **STRENGTHENED**: Requires NO special system properties.

    This is immediate from the definition but worth stating explicitly. -/
theorem depth_well_defined (S : IdeogeneticSystem)
    (init : Set S.Idea) (a : S.Idea)
    (ha : a ∈ closure S init) :
    ∃ d : ℕ, depth S init a = d ∧ a ∈ genCumulative S d init := by
  use depth S init a
  constructor
  · rfl
  · exact mem_genCumulative_depth S init a ha

/-- **Theorem: Depth Respects Set Inclusion**

    If A ⊆ B and both are subsets of genCumulative d, then
    max_depth A ≤ max_depth B ≤ d.

    **STRENGTHENED**: Requires NO special system properties.

    This shows depth is monotonic with respect to set inclusion. -/
noncomputable def max_depth (S : IdeogeneticSystem) (init : Set S.Idea) (A : Set S.Idea) : ℕ :=
  sInf {n | ∀ a ∈ A, depth S init a ≤ n}

theorem depth_respects_inclusion (S : IdeogeneticSystem)
    (init : Set S.Idea) (A B : Set S.Idea) (d : ℕ)
    (hAB : A ⊆ B) (hB : B ⊆ genCumulative S d init)
    (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty) :
    max_depth S init A ≤ max_depth S init B ∧ max_depth S init B ≤ d := by
  constructor
  · -- max_depth A ≤ max_depth B
    unfold max_depth

    -- Both sets are bounded by d
    have hB_bound : ∀ b ∈ B, depth S init b ≤ d := fun b hb =>
      depth_le_of_mem S init b d (hB hb)

    -- Show sInf B bounds all of A (since A ⊆ B)
    let m := sInf {n | ∀ b ∈ B, depth S init b ≤ n}
    have hm_bounds_A : ∀ a ∈ A, depth S init a ≤ m := by
      intro a ha
      have : a ∈ B := hAB ha
      -- sInf satisfies the property for nonempty bounded sets
      have h_exists : ∃ n, ∀ b ∈ B, depth S init b ≤ n := ⟨d, hB_bound⟩
      have hm_property : ∀ b ∈ B, depth S init b ≤ m := Nat.sInf_mem h_exists
      exact hm_property a this
    -- Then sInf A ≤ m = sInf B
    apply Nat.sInf_le
    show m ∈ {n | ∀ a ∈ A, depth S init a ≤ n}
    exact hm_bounds_A

  · -- max_depth B ≤ d
    unfold max_depth
    apply Nat.sInf_le
    show d ∈ {n | ∀ a ∈ B, depth S init a ≤ n}
    intro b hb
    exact depth_le_of_mem S init b d (hB hb)

/-- **Theorem: Depth Witnesses Generation Layer**

    If an idea a has depth d, then a appears in genCumulative d but not in
    genCumulative (d-1). This shows that depth precisely characterizes the
    "generation layer" where an idea first appears.

    **STRENGTHENED**: Requires NO special system properties.

    This is a fundamental characterization of depth as measuring the minimum
    number of generation steps required to produce an idea. -/
theorem depth_witnesses_generation_layer (S : IdeogeneticSystem)
    (init : Set S.Idea) (a : S.Idea) (d : ℕ)
    (ha_depth : depth S init a = d)
    (ha_reach : a ∈ closure S init)
    (hd_pos : d > 0) :
    a ∈ genCumulative S d init ∧ a ∉ genCumulative S (d - 1) init := by
  constructor
  · -- a ∈ genCumulative d
    rw [← ha_depth]
    exact mem_genCumulative_depth S init a ha_reach
  · -- a ∉ genCumulative (d-1)
    intro ha_earlier
    -- If a were in genCumulative (d-1), then depth a ≤ d-1
    have : depth S init a ≤ d - 1 := depth_le_of_mem S init a (d - 1) ha_earlier
    -- But depth a = d, so d ≤ d - 1, contradiction
    rw [ha_depth] at this
    omega

/-- **Corollary: Depth Zero Characterizes Initial Ideas**

    An idea has depth 0 if and only if it's in the initial set.

    **STRENGTHENED**: Requires NO special system properties.
    Only requires init to be nonempty (for reachability).

    This provides a clean characterization of "axioms" or "seeds". -/
theorem depth_zero_iff_in_init (S : IdeogeneticSystem) (init : Set S.Idea)
    (a : S.Idea) (hinit_nonempty : init.Nonempty)
    (ha_reach : a ∈ closure S init) :
    depth S init a = 0 ↔ a ∈ init := by
  constructor
  · intro h0
    -- a is reachable and has depth 0
    have ha_at_zero : a ∈ genCumulative S 0 init := by
      rw [← h0]
      exact mem_genCumulative_depth S init a ha_reach
    unfold genCumulative at ha_at_zero
    exact ha_at_zero
  · intro ha_init
    -- If a ∈ init, then a ∈ genCumulative 0
    have : a ∈ genCumulative S 0 init := by unfold genCumulative; exact ha_init
    -- So depth a ≤ 0
    have : depth S init a ≤ 0 := depth_le_of_mem S init a 0 this
    -- But depth is Nat, so depth a = 0
    omega

/-! ## Section 5: Additional Weakened Theorems

These theorems demonstrate the power of local conditions over global properties.
-/

/-- **Theorem: Novel Generation Implies Positive Depth (Alternative Form)**

    If b is generated from any reachable idea and b is novel, then b has positive depth.

    **KEY INSIGHT**: We don't need to know which specific idea generated b,
    just that b is novel. This is much weaker than requiring a globally novelty-producing system. -/
theorem novel_generated_has_positive_depth (S : IdeogeneticSystem)
    (init : Set S.Idea) (b : S.Idea)
    (hb_reach : b ∈ closure S init)
    (hb_novel : isNovel S init b)
    (hb_generated : ∃ a ∈ closure S init, b ∈ S.generate a) :
    depth S init b > 0 := by
  obtain ⟨a, ha_reach, hb_gen⟩ := hb_generated
  -- a is in closure, so appears at some stage
  have ha_exists : ∃ da, a ∈ genCumulative S da init := by
    simp only [closure, Set.mem_iUnion] at ha_reach
    exact ha_reach
  obtain ⟨da, ha⟩ := ha_exists
  exact generated_idea_positive_depth S init a b da ha hb_gen hb_novel

/-- **Theorem: Generation Depth Increase is Sharp**

    For any stage d and any idea a at stage d, there exists at least one
    generated idea with depth d+1 OR all generated ideas are rediscoveries.

    **STRENGTHENED**: Requires NO special system properties.

    This shows that depth increases are either sharp (exactly +1) or
    represent rediscovery. -/
theorem generation_depth_increase_sharp (S : IdeogeneticSystem)
    (init : Set S.Idea) (a : S.Idea) (d : ℕ)
    (ha : depth S init a = d)
    (ha_reach : a ∈ closure S init)
    (hgen_nonempty : (S.generate a).Nonempty) :
    (∃ b ∈ S.generate a, depth S init b = d + 1) ∨
    (∀ b ∈ S.generate a, depth S init b ≤ d) := by
  -- Either some generated idea is novel, or all are rediscoveries
  by_cases h : ∃ b ∈ S.generate a, b ∉ genCumulative S d init
  · -- Some generated idea is novel
    obtain ⟨b, hb_gen, hb_novel⟩ := h
    left
    use b, hb_gen
    exact proper_generation_increases_depth S init a b d ha ha_reach hb_gen hb_novel
  · -- All generated ideas are rediscoveries
    right
    push_neg at h
    intro b hb
    exact depth_le_of_mem S init b d (h b hb)

/-- **Theorem: Depth Monotonicity for Single Generation Step**

    If b is generated from a and is novel (not rediscovered), then depth b > depth a.

    **STRENGTHENED**: Only requires the specific idea b to be novel,
    not the entire system. This is the key local property needed for depth monotonicity. -/
theorem depth_strict_increase_for_novel_generation (S : IdeogeneticSystem)
    (init : Set S.Idea) (a b : S.Idea)
    (ha : a ∈ closure S init)
    (hb_gen : b ∈ S.generate a)
    (hb_novel : b ∉ genCumulative S (depth S init a) init) :
    depth S init b > depth S init a := by
  have : depth S init b = depth S init a + 1 :=
    proper_generation_increases_depth S init a b (depth S init a) rfl ha hb_gen hb_novel
  linarith

end SingleAgentIdeogenesis
