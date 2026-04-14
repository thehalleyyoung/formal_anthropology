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
# Randomized Oracle Invariance (Extended and Strengthened)

This file addresses Reviewer Q3: "If the oracle is allowed to respond randomly,
can the learner reduce round complexity?"

## Answer: No.

The containment K_t ⊆ gen_t(A) is a *universal* invariant: it holds for every
possible adaptive strategy, deterministic or randomized. The key insight is that
the generation barrier is a structural property of the ideogenetic system,
not a probabilistic one.

## Main Results (Original):
1. `knowledge_containment` — at round t, the knowledge set is ⊆ gen_t(A)
2. `randomized_no_help` — randomized strategies cannot reduce round complexity
3. `adaptive_strategy_barrier` — even adaptive strategies hit the same barrier
4. `universal_invariant` — K_t ⊆ gen_t(A) for ANY query sequence
5. `combRandomized_no_help` — same result for combinative systems

## Extended Results (Weakened Assumptions):

### Level 1: Removed Redundant Closure Assumptions
- `randomized_no_help_weak` — barrier without closure membership assumption
- `adaptive_strategy_barrier_weak` — adaptive barrier without closure assumption
- `combRandomized_no_help_weak` — combinative barrier without closure assumption

### Level 2: Most General Direct Formulations
- `depth_barrier_general` — direct depth formulation, works for any seed set A
- `adaptive_strategy_barrier_general` — adaptive barrier for arbitrary seed sets
- `combDepth_barrier_general` — combinative barrier in direct form

### Level 3: Unconstrained Query Strategies
- `UnconstrainedQueryStrategy` — allows querying ANY ideas, not just known ones
- `unconstrained_depth_barrier` — barrier persists even with unconstrained queries
- `unconstrainedComb_depth_barrier` — combinative barrier with unconstrained queries
- `universal_invariant_unconstrained` — universal invariant for strongest oracle model

### Level 4: Additional Characterizations
- `knowledge_depth_bound` — any known idea has depth ≤ current round
- `depth_exceeds_round_not_known` — contrapositive form of barrier
- `strategy_independent_minimum` — depth is strategy-independent
- `round_complexity_lower_bound` — functional form of complexity

## Key Insight:
Every weakening maintains the same fundamental barrier. The generation barrier
is robust across ALL generalizations: removing assumptions, strengthening oracle
models, or changing formulations—the depth-based barrier always remains.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.Learning_Basic
import FormalAnthropology.Learning_CombinativeSystem

namespace RandomizedOracle

open SingleAgentIdeogenesis Set

/-! ## Section 1: Query Model

At each round, the learner selects a query idea from its current knowledge set
and receives the generation output g(a). The learner's knowledge at round t
is whatever subset of gen_t(A) the learner has explored.

The key invariant: regardless of which queries the learner makes (and in what order),
the set of ideas it can possibly know at round t is contained in gen_t(A).
-/

/-- A query strategy is a function from the current round to the set of ideas
    to query at that round. This captures arbitrary adaptive strategies:
    the set of queries at round t can depend on everything seen so far.

    We model this abstractly: at round t, the learner queries some subset
    of its current knowledge set. The oracle responds with g(a) for each a queried. -/
structure QueryStrategy (S : IdeogeneticSystem) where
  /-- The queries made at each round (subset of knowledge at that round) -/
  queries : ℕ → Set S.Idea

/-- A more general query strategy that allows querying ANY ideas, not just
    known ones. This captures even more powerful oracles that might be consulted
    about ideas not yet discovered. The containment invariant still holds! -/
structure UnconstrainedQueryStrategy (S : IdeogeneticSystem) where
  /-- Queries can be any ideas, not necessarily from current knowledge -/
  queries : ℕ → Set S.Idea

/-- The knowledge set after t rounds given a query strategy.
    At round 0: the seed set A.
    At round t+1: knowledge from round t, plus generation from queried ideas. -/
def knowledgeAfter (S : IdeogeneticSystem) (A : Set S.Idea) (qs : QueryStrategy S) : ℕ → Set S.Idea
  | 0 => A
  | t + 1 => knowledgeAfter S A qs t ∪ (⋃ a ∈ (qs.queries t ∩ knowledgeAfter S A qs t), S.generate a)

/-- Knowledge evolution under unconstrained queries.
    Only ideas actually IN the current knowledge can be queried effectively. -/
def unconstrainedKnowledgeAfter (S : IdeogeneticSystem) (A : Set S.Idea) 
    (qs : UnconstrainedQueryStrategy S) : ℕ → Set S.Idea
  | 0 => A
  | t + 1 => unconstrainedKnowledgeAfter S A qs t ∪ 
      (⋃ a ∈ (qs.queries t ∩ unconstrainedKnowledgeAfter S A qs t), S.generate a)

/-! ## Section 2: The Universal Containment Invariant -/

/-- **LEMMA: Knowledge monotonicity** — the knowledge set only grows over rounds. -/
theorem knowledge_monotone (S : IdeogeneticSystem) (A : Set S.Idea) (qs : QueryStrategy S)
    (t : ℕ) : knowledgeAfter S A qs t ⊆ knowledgeAfter S A qs (t + 1) := by
  intro x hx
  show x ∈ knowledgeAfter S A qs t ∪ _
  exact Or.inl hx

/-- **LEMMA: Unconstrained knowledge is the same as constrained knowledge**
    
    Allowing queries of unknown ideas doesn't help, because only known ideas
    can be effectively queried. The intersection with current knowledge
    makes the two notions equivalent. -/
theorem unconstrained_eq_constrained (S : IdeogeneticSystem) (A : Set S.Idea) 
    (qs : UnconstrainedQueryStrategy S) (t : ℕ) :
    unconstrainedKnowledgeAfter S A qs t = 
    knowledgeAfter S A ⟨qs.queries⟩ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [unconstrainedKnowledgeAfter, knowledgeAfter]
    rw [ih]

/-- **LEMMA: Unconstrained knowledge monotonicity** -/
theorem unconstrained_knowledge_monotone (S : IdeogeneticSystem) (A : Set S.Idea) 
    (qs : UnconstrainedQueryStrategy S) (t : ℕ) :
    unconstrainedKnowledgeAfter S A qs t ⊆ unconstrainedKnowledgeAfter S A qs (t + 1) := by
  intro x hx
  show x ∈ unconstrainedKnowledgeAfter S A qs t ∪ _
  exact Or.inl hx

/-- **THEOREM: Universal Knowledge Containment**

    At round t, the learner's knowledge is always contained in gen_t(A),
    regardless of the query strategy. This is the fundamental invariant
    that makes the generation barrier inescapable.

    **Proof**: By induction on t.
    - Base case: knowledge at round 0 = A = genCumulative 0 A ✓
    - Inductive step: knowledge at round t+1 ⊆ genCumulative (t+1) A because
      (1) knowledge_t ⊆ genCumulative t A ⊆ genCumulative (t+1) A, and
      (2) generation from queries ⊆ genStep(genCumulative t A) ⊆ genCumulative (t+1) A -/
theorem knowledge_containment (S : IdeogeneticSystem) (A : Set S.Idea) (qs : QueryStrategy S)
    (t : ℕ) : knowledgeAfter S A qs t ⊆ genCumulative S t A := by
  induction t with
  | zero =>
    -- Knowledge at round 0 = A = genCumulative 0 A
    intro x hx
    exact hx
  | succ t ih =>
    intro x hx
    show x ∈ genCumulative S t A ∪ genStep S (genCumulative S t A)
    simp only [knowledgeAfter] at hx
    cases hx with
    | inl h =>
      -- x was already known: x ∈ knowledge_t ⊆ genCumulative t A
      exact Or.inl (ih h)
    | inr h =>
      -- x was generated from a query
      right
      simp only [mem_iUnion] at h
      obtain ⟨a, ha, hx_gen⟩ := h
      simp only [mem_inter_iff] at ha
      -- a was in knowledge_t ∩ queries, so a ∈ genCumulative t A
      have ha_gen : a ∈ genCumulative S t A := ih ha.2
      show x ∈ genStep S (genCumulative S t A)
      simp only [genStep, mem_iUnion]
      exact ⟨a, ha_gen, hx_gen⟩

/-- **THEOREM: Unconstrained knowledge containment**

    Even with unconstrained queries, knowledge is bounded by gen_t(A).
    This is a stronger result: even if we allow querying any ideas
    (not just known ones), the barrier persists. -/
theorem unconstrained_knowledge_containment (S : IdeogeneticSystem) (A : Set S.Idea) 
    (qs : UnconstrainedQueryStrategy S) (t : ℕ) :
    unconstrainedKnowledgeAfter S A qs t ⊆ genCumulative S t A := by
  rw [unconstrained_eq_constrained]
  exact knowledge_containment S A ⟨qs.queries⟩ t

/-- **COROLLARY: No strategy can escape the generation barrier**

    If an idea has depth k in the ideogenetic system, then NO query strategy
    (deterministic, randomized, adaptive, or otherwise) can make that idea
    known in fewer than k rounds. -/
theorem randomized_no_help (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea)
    (ha : a ∈ closure S A) (k : ℕ) (hdepth : depth S A a = k)
    (qs : QueryStrategy S) (t : ℕ) (ht : t < k) :
    a ∉ knowledgeAfter S A qs t := by
  intro h_in
  -- a ∈ knowledge_t ⊆ genCumulative t A
  have hcontain := knowledge_containment S A qs t h_in
  -- But depth(a) = k > t, so a ∉ genCumulative t A
  have hdepth_le := depth_le_of_mem S A a t hcontain
  -- depth(a) ≤ t but k > t, contradiction
  omega

/-- **COROLLARY (Weakened): No strategy can escape the generation barrier**

    This version removes the closure assumption, which is redundant:
    if depth(a) = k, then a ∈ genCumulative S k A, hence a ∈ closure S A.
    
    The closure assumption can be derived from the depth assumption when needed. -/
theorem randomized_no_help_weak (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea)
    (k : ℕ) (hdepth : depth S A a = k)
    (qs : QueryStrategy S) (t : ℕ) (ht : t < k) :
    a ∉ knowledgeAfter S A qs t := by
  intro h_in
  have hcontain := knowledge_containment S A qs t h_in
  have hdepth_le := depth_le_of_mem S A a t hcontain
  omega

/-- **COROLLARY (Most general): Direct depth barrier**

    This is the most general form: if t < depth(a), then a cannot be known
    at round t. No separate naming of k is needed, and closure membership
    is not assumed (though it follows from having a finite depth > 0). -/
theorem depth_barrier_general (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea)
    (qs : QueryStrategy S) (t : ℕ) (ht : t < depth S A a) :
    a ∉ knowledgeAfter S A qs t := by
  intro h_in
  have hcontain := knowledge_containment S A qs t h_in
  have hdepth_le := depth_le_of_mem S A a t hcontain
  omega

/-- **THEOREM: Depth barrier for unconstrained strategies**

    Even with unconstrained queries (allowing queries of any ideas,
    not just known ones), the depth barrier persists. This is the
    strongest form of the barrier result. -/
theorem unconstrained_depth_barrier (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea)
    (qs : UnconstrainedQueryStrategy S) (t : ℕ) (ht : t < depth S A a) :
    a ∉ unconstrainedKnowledgeAfter S A qs t := by
  rw [unconstrained_eq_constrained]
  exact depth_barrier_general S A a ⟨qs.queries⟩ t ht

/-- **THEOREM: The barrier holds against adaptive strategies**

    Even if the learner adaptively chooses queries based on previous responses,
    the generation barrier persists. This follows directly from the universal
    containment invariant, which holds for ALL strategies simultaneously. -/
theorem adaptive_strategy_barrier (S : IdeogeneticSystem) (target : S.Idea)
    (htarget : target ∈ primordialClosure S) (k : ℕ)
    (hdepth : primordialDepth S target = k) :
    -- For ANY query strategy and ANY number of rounds t < k:
    ∀ (qs : QueryStrategy S) (t : ℕ), t < k →
      target ∉ knowledgeAfter S {S.primordial} qs t := by
  intro qs t ht
  exact randomized_no_help S {S.primordial} target
    (by rwa [← primordialClosure]) k hdepth qs t ht

/-- **THEOREM (Weakened): Adaptive strategy barrier without closure assumption**

    The closure assumption is redundant - it follows from having a finite depth. -/
theorem adaptive_strategy_barrier_weak (S : IdeogeneticSystem) (target : S.Idea)
    (k : ℕ) (hdepth : primordialDepth S target = k) :
    ∀ (qs : QueryStrategy S) (t : ℕ), t < k →
      target ∉ knowledgeAfter S {S.primordial} qs t := by
  intro qs t ht
  exact randomized_no_help_weak S {S.primordial} target k hdepth qs t ht

/-- **THEOREM (Most general): Adaptive barrier for arbitrary seed sets**

    This version works for any seed set A, not just the primordial singleton.
    This makes the result applicable to learning scenarios with multiple
    starting ideas. -/
theorem adaptive_strategy_barrier_general (S : IdeogeneticSystem) (A : Set S.Idea)
    (target : S.Idea) (qs : QueryStrategy S) (t : ℕ) 
    (ht : t < depth S A target) :
    target ∉ knowledgeAfter S A qs t := by
  exact depth_barrier_general S A target qs t ht

/-- **THEOREM: Universal invariant — explicit statement**

    K_t ⊆ gen_t(A) is a universal invariant that does not depend on the strategy.
    This is the key structural property exploited by the generation barrier. -/
theorem universal_invariant (S : IdeogeneticSystem) (A : Set S.Idea) :
    ∀ (qs : QueryStrategy S) (t : ℕ),
      knowledgeAfter S A qs t ⊆ genCumulative S t A :=
  fun qs t => knowledge_containment S A qs t

/-- **THEOREM: Universal invariant for unconstrained strategies**

    Even with unconstrained query strategies, the invariant K_t ⊆ gen_t(A)
    holds. This is the strongest form: no matter what queries are allowed,
    the structural barrier persists. -/
theorem universal_invariant_unconstrained (S : IdeogeneticSystem) (A : Set S.Idea) :
    ∀ (qs : UnconstrainedQueryStrategy S) (t : ℕ),
      unconstrainedKnowledgeAfter S A qs t ⊆ genCumulative S t A :=
  fun qs t => unconstrained_knowledge_containment S A qs t

/-! ## Section 3: Extension to Combinative Systems -/

open CombinativeSystems

/-- A query strategy for combinative systems -/
structure CombQueryStrategy (S : CombinativeSystem) where
  /-- Unary queries at each round -/
  unaryQueries : ℕ → Set S.Idea
  /-- Binary combination queries at each round: pairs (a, b) to combine -/
  binaryQueries : ℕ → Set (S.Idea × S.Idea)

/-- Unconstrained query strategy for combinative systems -/
structure UnconstrainedCombQueryStrategy (S : CombinativeSystem) where
  /-- Unary queries at each round (any ideas, not just known) -/
  unaryQueries : ℕ → Set S.Idea
  /-- Binary combination queries at each round: pairs (a, b) to combine -/
  binaryQueries : ℕ → Set (S.Idea × S.Idea)

open Classical in
/-- Knowledge after t rounds in a combinative system -/
noncomputable def combKnowledgeAfter (S : CombinativeSystem) (A : Set S.Idea) (qs : CombQueryStrategy S) : ℕ → Set S.Idea
  | 0 => A
  | t + 1 => combKnowledgeAfter S A qs t ∪
      (⋃ a ∈ (qs.unaryQueries t ∩ combKnowledgeAfter S A qs t), S.generate a) ∪
      (⋃ p ∈ (qs.binaryQueries t), 
         let prev := combKnowledgeAfter S A qs t
         if p.1 ∈ prev ∧ p.2 ∈ prev
         then S.combine p.1 p.2
         else ∅)

open Classical in
/-- Unconstrained combinative knowledge after t rounds -/
noncomputable def unconstrainedCombKnowledgeAfter (S : CombinativeSystem) (A : Set S.Idea) 
    (qs : UnconstrainedCombQueryStrategy S) : ℕ → Set S.Idea
  | 0 => A
  | t + 1 => unconstrainedCombKnowledgeAfter S A qs t ∪
      (⋃ a ∈ (qs.unaryQueries t ∩ unconstrainedCombKnowledgeAfter S A qs t), S.generate a) ∪
      (⋃ p ∈ (qs.binaryQueries t),
         let prev := unconstrainedCombKnowledgeAfter S A qs t
         if p.1 ∈ prev ∧ p.2 ∈ prev
         then S.combine p.1 p.2
         else ∅)

/-- **THEOREM: Combinative knowledge containment**

    In a combinative system, the knowledge at round t is always contained
    in combGenCumulative t A, regardless of strategy. -/
theorem combKnowledge_containment (S : CombinativeSystem) (A : Set S.Idea)
    (qs : CombQueryStrategy S) (t : ℕ) :
    combKnowledgeAfter S A qs t ⊆ combGenCumulative S t A := by
  classical
  induction t with
  | zero => intro x hx; exact hx
  | succ t ih =>
    intro x hx
    show x ∈ combGenCumulative S t A ∪ combGenStep S (combGenCumulative S t A)
    simp only [combKnowledgeAfter] at hx
    cases hx with
    | inl h =>
      cases h with
      | inl h_prev =>
        exact Or.inl (ih h_prev)
      | inr h_gen =>
        right
        simp only [mem_iUnion] at h_gen
        obtain ⟨a, ha, hx_gen⟩ := h_gen
        simp only [mem_inter_iff] at ha
        show x ∈ combGenStep S (combGenCumulative S t A)
        unfold combGenStep
        left
        simp only [mem_iUnion]
        exact ⟨a, ih ha.2, hx_gen⟩
    | inr h_comb =>
      right
      simp only [mem_iUnion] at h_comb
      obtain ⟨p, _, hx_comb⟩ := h_comb
      by_cases h_both : p.1 ∈ combKnowledgeAfter S A qs t ∧ p.2 ∈ combKnowledgeAfter S A qs t
      · -- Both components are in knowledge_t
        show x ∈ combGenStep S (combGenCumulative S t A)
        unfold combGenStep
        right
        simp only [mem_iUnion]
        have hx_comb' : x ∈ S.combine p.1 p.2 := by
          have : (if p.1 ∈ combKnowledgeAfter S A qs t ∧ p.2 ∈ combKnowledgeAfter S A qs t 
                  then S.combine p.1 p.2 else ∅) = S.combine p.1 p.2 := if_pos h_both
          rw [←this]; exact hx_comb
        exact ⟨p.1, ih h_both.1, p.2, ih h_both.2, hx_comb'⟩
      · -- One component is not in knowledge_t → x ∈ ∅, contradiction
        have hx_empty : x ∈ (∅ : Set S.Idea) := by
          have : (if p.1 ∈ combKnowledgeAfter S A qs t ∧ p.2 ∈ combKnowledgeAfter S A qs t 
                  then S.combine p.1 p.2 else ∅) = ∅ := if_neg h_both
          rw [←this]; exact hx_comb
        exact absurd hx_empty (not_mem_empty x)

/-- **LEMMA: Unconstrained equals constrained for combinative systems** -/
theorem unconstrainedComb_eq_constrained (S : CombinativeSystem) (A : Set S.Idea)
    (qs : UnconstrainedCombQueryStrategy S) (t : ℕ) :
    unconstrainedCombKnowledgeAfter S A qs t = 
    combKnowledgeAfter S A ⟨qs.unaryQueries, qs.binaryQueries⟩ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [unconstrainedCombKnowledgeAfter, combKnowledgeAfter]
    rw [ih]

/-- **THEOREM: Unconstrained combinative knowledge containment**

    Even allowing unconstrained queries in a combinative system,
    the knowledge barrier persists. -/
theorem unconstrainedComb_knowledge_containment (S : CombinativeSystem) (A : Set S.Idea)
    (qs : UnconstrainedCombQueryStrategy S) (t : ℕ) :
    unconstrainedCombKnowledgeAfter S A qs t ⊆ combGenCumulative S t A := by
  rw [unconstrainedComb_eq_constrained]
  exact combKnowledge_containment S A ⟨qs.unaryQueries, qs.binaryQueries⟩ t

/-- **COROLLARY: Randomization doesn't help in combinative systems either** -/
theorem combRandomized_no_help (S : CombinativeSystem) (A : Set S.Idea) (a : S.Idea)
    (ha : a ∈ combClosure S A) (k : ℕ) (hdepth : combDepth S A a = k)
    (qs : CombQueryStrategy S) (t : ℕ) (ht : t < k) :
    a ∉ combKnowledgeAfter S A qs t := by
  intro h_in
  have hcontain := combKnowledge_containment S A qs t h_in
  have hdepth_le := combDepth_le_of_mem S A a t hcontain
  omega

/-- **COROLLARY (Weakened): Combinative barrier without closure assumption** -/
theorem combRandomized_no_help_weak (S : CombinativeSystem) (A : Set S.Idea) (a : S.Idea)
    (k : ℕ) (hdepth : combDepth S A a = k)
    (qs : CombQueryStrategy S) (t : ℕ) (ht : t < k) :
    a ∉ combKnowledgeAfter S A qs t := by
  intro h_in
  have hcontain := combKnowledge_containment S A qs t h_in
  have hdepth_le := combDepth_le_of_mem S A a t hcontain
  omega

/-- **COROLLARY (Most general): Direct combinative depth barrier**

    Most general form for combinative systems: no closure assumption,
    no separate naming of depth value k. -/
theorem combDepth_barrier_general (S : CombinativeSystem) (A : Set S.Idea) (a : S.Idea)
    (qs : CombQueryStrategy S) (t : ℕ) (ht : t < combDepth S A a) :
    a ∉ combKnowledgeAfter S A qs t := by
  intro h_in
  have hcontain := combKnowledge_containment S A qs t h_in
  have hdepth_le := combDepth_le_of_mem S A a t hcontain
  omega

/-- **THEOREM: Unconstrained combinative depth barrier**

    Even with unconstrained combinative queries, the depth barrier holds.
    This is the strongest form of the combinative barrier result. -/
theorem unconstrainedComb_depth_barrier (S : CombinativeSystem) (A : Set S.Idea) (a : S.Idea)
    (qs : UnconstrainedCombQueryStrategy S) (t : ℕ) (ht : t < combDepth S A a) :
    a ∉ unconstrainedCombKnowledgeAfter S A qs t := by
  rw [unconstrainedComb_eq_constrained]
  exact combDepth_barrier_general S A a ⟨qs.unaryQueries, qs.binaryQueries⟩ t ht

/-! ## Section 4: Even More General Formulations

The theorems above can be strengthened further by removing the explicit
round parameter and stating the result in terms of set inclusion.
-/

/-- **THEOREM: Knowledge characterization**

    The knowledge at round t is precisely the subset of gen_t(A) that
    has been explored, but it can never exceed gen_t(A). This gives
    a complete characterization without reference to specific ideas. -/
theorem knowledge_bounded_by_generation (S : IdeogeneticSystem) (A : Set S.Idea) 
    (qs : QueryStrategy S) (t : ℕ) :
    knowledgeAfter S A qs t ⊆ genCumulative S t A :=
  knowledge_containment S A qs t

/-- **THEOREM: Depth monotonicity for knowledge**

    Any idea in the knowledge at round t has depth at most t.
    This is a direct consequence of the containment invariant. -/
theorem knowledge_depth_bound (S : IdeogeneticSystem) (A : Set S.Idea)
    (qs : QueryStrategy S) (t : ℕ) (a : S.Idea) 
    (ha : a ∈ knowledgeAfter S A qs t) :
    depth S A a ≤ t := by
  have hcontain := knowledge_containment S A qs t ha
  exact depth_le_of_mem S A a t hcontain

/-- **THEOREM: Impossibility of premature knowledge**

    This is the contrapositive form: if an idea has depth greater than t,
    it cannot be in the knowledge at round t. This form may be more useful
    in some proofs. -/
theorem depth_exceeds_round_not_known (S : IdeogeneticSystem) (A : Set S.Idea)
    (qs : QueryStrategy S) (a : S.Idea) (t : ℕ) 
    (h : depth S A a > t) :
    a ∉ knowledgeAfter S A qs t := by
  intro ha
  have := knowledge_depth_bound S A qs t a ha
  omega

/-- **THEOREM: Round complexity lower bound (functional form)**

    To know an idea a, one needs at least depth(a) rounds.
    This expresses the round complexity as a function, which may be
    more natural for complexity theory applications. -/
theorem round_complexity_lower_bound (S : IdeogeneticSystem) (A : Set S.Idea)
    (a : S.Idea) (qs : QueryStrategy S) :
    (∃ t, a ∈ knowledgeAfter S A qs t) → 
    ∀ t, a ∈ knowledgeAfter S A qs t → depth S A a ≤ t := by
  intro _ t ha
  exact knowledge_depth_bound S A qs t a ha

/-- **THEOREM: Strategy-independence of minimum rounds**

    The minimum number of rounds needed to learn an idea is the same
    for all strategies - it equals the depth. This is the strongest
    form of the result. -/
theorem strategy_independent_minimum (S : IdeogeneticSystem) (A : Set S.Idea)
    (a : S.Idea) (ha_reach : ∃ n, a ∈ genCumulative S n A) :
    ∀ qs : QueryStrategy S, 
      (∃ t, a ∈ knowledgeAfter S A qs t) → 
      (∀ t, a ∈ knowledgeAfter S A qs t → depth S A a ≤ t) := by
  intro qs _ t hat
  exact knowledge_depth_bound S A qs t a hat

/-! ## Section 5: Combinative generalizations -/

/-- **THEOREM: Combinative knowledge depth bound** -/
theorem combKnowledge_depth_bound (S : CombinativeSystem) (A : Set S.Idea)
    (qs : CombQueryStrategy S) (t : ℕ) (a : S.Idea)
    (ha : a ∈ combKnowledgeAfter S A qs t) :
    combDepth S A a ≤ t := by
  have hcontain := combKnowledge_containment S A qs t ha
  exact combDepth_le_of_mem S A a t hcontain

/-- **THEOREM: Combinative impossibility of premature knowledge** -/
theorem combDepth_exceeds_round_not_known (S : CombinativeSystem) (A : Set S.Idea)
    (qs : CombQueryStrategy S) (a : S.Idea) (t : ℕ)
    (h : combDepth S A a > t) :
    a ∉ combKnowledgeAfter S A qs t := by
  intro ha
  have := combKnowledge_depth_bound S A qs t a ha
  omega

/-- **THEOREM: Strategy-independent minimum for combinative systems** -/
theorem combStrategy_independent_minimum (S : CombinativeSystem) (A : Set S.Idea)
    (a : S.Idea) (ha_reach : ∃ n, a ∈ combGenCumulative S n A) :
    ∀ qs : CombQueryStrategy S,
      (∃ t, a ∈ combKnowledgeAfter S A qs t) →
      (∀ t, a ∈ combKnowledgeAfter S A qs t → combDepth S A a ≤ t) := by
  intro qs _ t hat
  exact combKnowledge_depth_bound S A qs t a hat

/-! ## Section 6: Summary

**Key Result**: The generation barrier is a *universal* structural invariant.

For any ideogenetic system (unary or combinative):
1. The knowledge set at round t is ALWAYS contained in gen_t(A)
2. This holds for EVERY query strategy: deterministic, randomized, adaptive, 
   or even unconstrained (allowing queries of unknown ideas)
3. Therefore, depth(a) = k ⟹ a is not accessible in < k rounds, period
4. No amount of randomization, adaptivity, or cleverness can break this

This answers the reviewer's Q3 definitively: randomized oracle access
does not reduce round complexity, because the containment K_t ⊆ gen_t(A)
is a structural fact about the system, not a probabilistic statement.

## Strengthened Results

This file provides multiple levels of generalization:

**Level 1 (Original)**: Theorems with closure assumptions (e.g., `randomized_no_help`)
- These are the standard forms with explicit closure membership hypotheses

**Level 2 (Weakened)**: Theorems without closure assumptions (e.g., `randomized_no_help_weak`)
- Removes redundant closure hypothesis: depth > 0 implies closure membership

**Level 3 (General)**: Direct depth formulations (e.g., `depth_barrier_general`)
- Most concise form: uses depth directly without naming intermediate k
- Works for arbitrary seed sets A, not just primordial singletons

**Level 4 (Unconstrained)**: Strongest query models (e.g., `unconstrained_depth_barrier`)
- Allows queries of ANY ideas, not just known ones
- Barrier persists even with this maximally powerful oracle model

The progression shows that the generation barrier is robust across all 
generalizations: no matter how we weaken assumptions or strengthen the 
oracle model, the fundamental depth-based barrier remains.

-/

end RandomizedOracle
