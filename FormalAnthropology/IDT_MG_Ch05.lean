import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 5: Information and Belief

**Core claim.** Uncertainty about the opponent's repertoire affects
strategic choice. A player's *belief* about what the opponent might play
determines worst-case and best-case payoffs (measured by depth).

## Definitions

- `Belief := List I` — possible opponent strategies
- `worstCaseDepth s belief` — min depth of compose s b for b in belief
- `bestCaseDepth s belief` — max depth of compose s b for b in belief
- `CommonRepertoire r1 r2` — ideas present in both repertoires

## 16 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch5

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- A belief: the set of opponent strategies the player considers possible. -/
abbrev Belief (I : Type*) := List I

/-- Depth of composing s with b — the payoff for strategy s against b. -/
def outcomeDepth (s b : I) : ℕ := IdeaticSpace.depth (IdeaticSpace.compose s b)

/-- Worst-case depth: minimum depth achievable against any element of belief.
    For empty belief, returns 0 (vacuously). -/
def worstCaseDepth (s : I) (belief : Belief I) : ℕ :=
  match belief with
  | [] => 0
  | b :: bs => List.foldl (fun acc x => min acc (outcomeDepth s x)) (outcomeDepth s b) bs

/-- Best-case depth: maximum depth achievable against any element of belief. -/
def bestCaseDepth (s : I) (belief : Belief I) : ℕ :=
  match belief with
  | [] => 0
  | b :: bs => List.foldl (fun acc x => max acc (outcomeDepth s x)) (outcomeDepth s b) bs

/-- Common repertoire: ideas that appear in both players' lists. -/
def commonRepertoire (r1 r2 : List I) [DecidableEq I] : List I :=
  r1.filter (fun x => x ∈ r2)

/-! ## §2. Void and Empty Belief Theorems -/

/-- Void worst case against singleton: just the opponent's depth. -/
theorem void_worst_case_singleton (b : I) :
    worstCaseDepth (IdeaticSpace.void : I) [b] = IdeaticSpace.depth b := by
  simp [worstCaseDepth, outcomeDepth, void_left]

/-- Void best case against singleton: just the opponent's depth. -/
theorem void_best_case_singleton (b : I) :
    bestCaseDepth (IdeaticSpace.void : I) [b] = IdeaticSpace.depth b := by
  simp [bestCaseDepth, outcomeDepth, void_left]

/-- Empty belief yields 0 worst-case depth (vacuously). -/
theorem empty_belief_worst_case (s : I) :
    worstCaseDepth s ([] : Belief I) = 0 := by
  simp [worstCaseDepth]

/-- Empty belief yields 0 best-case depth (vacuously). -/
theorem empty_belief_best_case (s : I) :
    bestCaseDepth s ([] : Belief I) = 0 := by
  simp [bestCaseDepth]

/-- Single-element belief = certainty: worst = best = outcomeDepth. -/
theorem singleton_belief_certain (s b : I) :
    worstCaseDepth s [b] = bestCaseDepth s [b] := by
  simp [worstCaseDepth, bestCaseDepth]

/-! ## §3. Depth Bound Under Uncertainty -/

/-- Outcome depth against any single opponent is bounded. -/
theorem depth_bound_single_opponent (s b : I) :
    outcomeDepth s b ≤ IdeaticSpace.depth s + IdeaticSpace.depth b := by
  exact depth_compose_le s b

/-- Void guarantees non-negative payoff (trivially ≥ 0 since ℕ). -/
theorem void_guaranteed_nonneg (s : I) :
    outcomeDepth (IdeaticSpace.void : I) s ≥ 0 := by
  omega

/-- If opponent might play void, your idea is a possible outcome depth. -/
theorem void_belief_outcome (s : I) :
    outcomeDepth s (IdeaticSpace.void : I) = IdeaticSpace.depth s := by
  simp [outcomeDepth, void_right]

/-- Atomic belief bound: if opponent is atomic, payoff ≤ depth s + 1. -/
theorem atomic_belief_bound (s b : I) (hb : IdeaticSpace.atomic b) :
    outcomeDepth s b ≤ IdeaticSpace.depth s + 1 := by
  unfold outcomeDepth
  have h1 := depth_compose_le s b
  have h2 := IdeaticSpace.depth_atomic b hb
  omega

/-! ## §4. Resonance Propagation -/

/-- If all beliefs resonate with s, all outcomes resonate with compose s s. -/
theorem belief_resonance_propagation (s : I) (belief : Belief I)
    (h : ∀ (b : I), b ∈ belief → IdeaticSpace.resonates s b) (b : I)
    (hb : b ∈ belief) :
    IdeaticSpace.resonates (IdeaticSpace.compose s b) (IdeaticSpace.compose s s) :=
  IdeaticSpace.resonance_compose s s b s (resonance_refl s) (resonance_symm (h b hb))

/-- Every outcome resonates with itself (trivially by reflexivity). -/
theorem outcome_self_resonance (s b : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose s b) (IdeaticSpace.compose s b) :=
  resonance_refl _

/-- If belief is coherent (consecutive elements resonate), consecutive
    outcomes resonate when composed with the same strategy on left. -/
theorem coherent_belief_chain_resonance (s a b : I) (rest : List I)
    (h : Coherent (a :: b :: rest)) :
    IdeaticSpace.resonates (IdeaticSpace.compose s a) (IdeaticSpace.compose s b) :=
  resonance_compose_left s h.1

/-! ## §5. Common Repertoire -/

/-- Common repertoire symmetry: if x is in common(r1,r2), it's in both. -/
theorem common_repertoire_in_both [DecidableEq I] (r1 r2 : List I) (x : I)
    (hx : x ∈ commonRepertoire r1 r2) :
    x ∈ r1 ∧ x ∈ r2 := by
  simp [commonRepertoire, List.mem_filter] at hx
  exact hx

/-- Elements of common repertoire composed with each other resonate (via refl).
    Any element composed with itself resonates. -/
theorem composed_common_resonates [DecidableEq I] (r1 r2 : List I) (x : I)
    (hx : x ∈ commonRepertoire r1 r2) :
    IdeaticSpace.resonates (IdeaticSpace.compose x x) (IdeaticSpace.compose x x) :=
  resonance_refl _

/-! ## §6. Guaranteed Depth and Filtration -/

/-- Guaranteed depth from filtration: if s is in filtration n and
    all beliefs are in filtration m, outcomes are in filtration (n+m). -/
theorem guaranteed_depth_vs_filtration (n m : ℕ) (s : I) (b : I)
    (hs : s ∈ depthFiltration n) (hb : b ∈ depthFiltration m) :
    IdeaticSpace.compose s b ∈ depthFiltration (n + m) := by
  simp [depthFiltration] at hs hb ⊢
  have h := depth_compose_le s b
  omega

/-- Outcome complexity bounded by sum of individual depths. -/
theorem belief_outcome_depth_bound (s b : I) :
    outcomeDepth s b ≤ IdeaticSpace.depth s + IdeaticSpace.depth b :=
  depth_compose_le s b

end IDT.MG.Ch5
