/-
# Single-Agent Ideogenesis: Basic Definitions (v2)

This file contains the foundational definitions from SINGLE_AGENT_IDEOGENESIS++,
now built on top of the Core/Agent learning-theoretic definitions:

- Definition 3.1: Single-Agent Ideogenetic System (as GenerativeCapability)
- Definition 3.3: Closure (via Core.GenerativeCapability.closure)
- Definition 3.4: Depth (via Core.GenerativeCapability.depth)
- Definition 3.9: Fixed Point
- Definition 3.14-3.18: System properties (Finitary, Grounded, etc.)

The key insight is that a single-agent ideogenetic system is fundamentally
a GenerativeCapability with a distinguished primordial idea.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.Core_Agent

namespace SingleAgentIdeogenesis

open Core

/-! ## Definition 3.1: Ideogenetic System

An ideogenetic system is a GenerativeCapability with a primordial idea.
-/

/-- An ideogenetic system consists of a type of ideas, a generation operator,
    and a primordial idea. This is Definition 3.1 from IDEOGENESIS++.
    
    This is now defined in terms of Core.GenerativeCapability. -/
structure IdeogeneticSystem where
  /-- The type of ideas -/
  Idea : Type*
  /-- The generative capability (generation operator with properties) -/
  genCap : GenerativeCapability Idea
  /-- The primordial idea: the conceptual seed from which all ideas grow -/
  primordial : Idea

/-- Extract the generation function -/
def IdeogeneticSystem.generate (S : IdeogeneticSystem) : S.Idea → Set S.Idea :=
  S.genCap.generate

variable {S : IdeogeneticSystem}

/-! ## Definition 3.2: Iterated Generation 

These are now wrappers around Core.GenerativeCapability functions.
-/

/-- Single-step generation from a set of ideas -/
def genStep (S : IdeogeneticSystem) (A : Set S.Idea) : Set S.Idea :=
  ⋃ a ∈ A, S.generate a

/-- n-fold iterated generation (Definition 3.2) -/
def genIter (S : IdeogeneticSystem) : ℕ → Set S.Idea → Set S.Idea
  | 0, A => A
  | n + 1, A => genStep S (genIter S n A)

/-- Cumulative generation up to stage n (uses Core definition) -/
def genCumulative (S : IdeogeneticSystem) (n : ℕ) (A : Set S.Idea) : Set S.Idea :=
  S.genCap.genCumulative n A

/-! ## Definition 3.3: Closure 

The closure is now inherited from Core.GenerativeCapability.
-/

/-- The closure of a seed set under generation (Definition 3.3).
    This is the union of all finite generation stages. -/
def closure (S : IdeogeneticSystem) (A : Set S.Idea) : Set S.Idea :=
  S.genCap.closure A

/-- The closure starting from the primordial idea -/
def primordialClosure (S : IdeogeneticSystem) : Set S.Idea :=
  closure S {S.primordial}

/-! ## Definition 3.4: Depth 

Depth is now inherited from Core.GenerativeCapability.
-/

/-- Predicate that an idea appears by stage n -/
def appearsBy (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) (n : ℕ) : Prop :=
  a ∈ genCumulative S n A

/-- The depth of an idea from a seed set (Definition 3.4).
    Uses the Core definition. -/
noncomputable def depth (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) : ℕ :=
  S.genCap.depth A a

/-- If a is in the closure, it appears at stage depth(a) -/
theorem mem_genCumulative_depth (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea)
    (ha : a ∈ closure S A) : a ∈ genCumulative S (depth S A a) A := by
  have hreach : S.genCap.isReachable A a := ha
  exact GenerativeCapability.depth_spec S.genCap A a hreach

/-- depth is at most the stage where we first found the element -/
theorem depth_le_of_mem (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) (n : ℕ)
    (h : a ∈ genCumulative S n A) : depth S A a ≤ n :=
  GenerativeCapability.depth_le_of_mem S.genCap A a n h

/-- An idea is reachable from A if it's in the closure -/
def isReachable (S : IdeogeneticSystem) (A : Set S.Idea) (a : S.Idea) : Prop :=
  S.genCap.isReachable A a

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

/-- An idea is a limit idea if it's reachable but not by any finite stage -/
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
  S.genCap.isFinitary

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

/-! ## Conversion to LearningAgent

An ideogenetic system can be viewed as a learning agent.
-/

/-- Convert an ideogenetic system to a learning agent -/
def IdeogeneticSystem.toLearningAgent (S : IdeogeneticSystem) : LearningAgent S.Idea where
  genCap := S.genCap
  hypotheses := Set.univ  -- All subsets (unrestricted hypothesis class)
  prior := { prob := fun _ => 1 }
  lossFunc := { loss := fun _ _ => 0 }
  primordials := {S.primordial}

/-! ## Basic Theorems -/

/-- The seed is always in its own closure -/
theorem seed_in_closure (S : IdeogeneticSystem) (A : Set S.Idea) : A ⊆ closure S A :=
  GenerativeCapability.seed_in_closure S.genCap A

/-- The primordial is in the primordial closure -/
theorem primordial_in_closure (S : IdeogeneticSystem) : 
    S.primordial ∈ primordialClosure S := by
  apply seed_in_closure
  exact Set.mem_singleton _

/-- The base set A is contained in genCumulative at any stage -/
theorem genCumulative_contains_base (S : IdeogeneticSystem) (n : ℕ) (A : Set S.Idea) :
    A ⊆ genCumulative S n A := by
  intro a ha
  have : A ⊆ S.genCap.genCumulative n A := by
    induction n with
    | zero => simp only [GenerativeCapability.genCumulative]; exact fun _ h => h
    | succ n ih =>
      intro x hx
      simp only [GenerativeCapability.genCumulative, Set.mem_union]
      left
      exact ih hx
  exact this ha

/-- Generation stages are monotonically increasing -/
theorem genCumulative_mono (S : IdeogeneticSystem) (A : Set S.Idea) (n m : ℕ) (h : n ≤ m) :
    genCumulative S n A ⊆ genCumulative S m A :=
  GenerativeCapability.genCumulative_mono S.genCap A n m h

/-- Fixed points are in their own generation -/
theorem fixedPoint_self_gen (S : IdeogeneticSystem) (a : S.Idea) 
    (h : isFixedPoint S a) : a ∈ S.generate a := h

/-- If a is reachable, then so are all ideas it generates -/
theorem generate_preserves_reachable (S : IdeogeneticSystem) (a : S.Idea)
    (ha : isReachable S {S.primordial} a) (b : S.Idea) (hb : b ∈ S.generate a) :
    isReachable S {S.primordial} b := by
  simp only [isReachable, GenerativeCapability.isReachable, 
             GenerativeCapability.closure, Set.mem_iUnion] at ha ⊢
  obtain ⟨n, hn⟩ := ha
  use n + 1
  simp only [GenerativeCapability.genCumulative, Set.mem_union, Set.mem_iUnion]
  right
  exact ⟨a, hn, hb⟩

end SingleAgentIdeogenesis
