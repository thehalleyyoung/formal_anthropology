/-
# Theorem N1: Adaptive = Union Depth

This file provides a clean, reusable framework for set-level generators and
formalizes the Paper A revision theorem that adaptive reachability equals
reachability under the union generator.
-/

import FormalAnthropology.SingleAgent_Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace AdaptiveGenerators

open Set SingleAgentIdeogenesis
attribute [local instance] Classical.propDecidable

/-! ## Set-level generators and cumulative reachability -/

/-- A finite set of generators on sets. -/
structure GeneratorSet (Idea : Type*) where
  generators : Finset (Set Idea -> Set Idea)
  nonempty : generators.Nonempty

/-- Cumulative generation using a set-level generator. -/
def genCumulativeWith {Idea : Type*} (g : Set Idea -> Set Idea) :
    Nat -> Set Idea -> Set Idea
  | 0, A => A
  | n + 1, A => genCumulativeWith g n A ∪ g (genCumulativeWith g n A)

/-- Closure under a set-level generator. -/
def closureWith {Idea : Type*} (g : Set Idea -> Set Idea) (A : Set Idea) : Set Idea :=
  ⋃ n, genCumulativeWith g n A

/-- Depth with a set-level generator: the least stage where `c` appears. -/
noncomputable def depthWith {Idea : Type*} (g : Set Idea -> Set Idea)
    (A : Set Idea) (c : Idea) : Nat :=
  @dite Nat (Exists fun n => c ∈ genCumulativeWith g n A)
    (Classical.propDecidable _)
    (fun h => @Nat.find _ (Classical.decPred _) h)
    (fun _ => 0)

lemma depthWith_le_of_mem {Idea : Type*} (g : Set Idea -> Set Idea)
    (A : Set Idea) (c : Idea) (n : Nat)
    (h : c ∈ genCumulativeWith g n A) : depthWith g A c <= n := by
  have hex : Exists fun k => c ∈ genCumulativeWith g k A := ⟨n, h⟩
  simp only [depthWith, dif_pos hex]
  exact Nat.find_le h

lemma mem_genCumulativeWith_depth {Idea : Type*} (g : Set Idea -> Set Idea)
    (A : Set Idea) (c : Idea) (hc : c ∈ closureWith g A) :
    c ∈ genCumulativeWith g (depthWith g A c) A := by
  simp only [closureWith, Set.mem_iUnion] at hc
  obtain ⟨n, hn⟩ := hc
  have hex : Exists fun k => c ∈ genCumulativeWith g k A := ⟨n, hn⟩
  simp only [depthWith, dif_pos hex]
  exact Nat.find_spec hex

lemma genCumulativeWith_mono {Idea : Type*} (g : Set Idea -> Set Idea)
    (A : Set Idea) (n m : Nat) (h : n <= m) :
    genCumulativeWith g n A ⊆ genCumulativeWith g m A := by
  induction m with
  | zero =>
      simp at h
      subst h
      rfl
  | succ m ih =>
      cases Nat.lt_or_eq_of_le h with
      | inl hlt =>
          have : n <= m := Nat.lt_succ_iff.mp hlt
          exact Set.subset_union_of_subset_left (ih this) _
      | inr heq =>
          subst heq
          rfl

/-! ## Union generator and adaptive reachability -/

/-- Union generator over a finite generator set. -/
def unionGen {Idea : Type*} (G : GeneratorSet Idea) (A : Set Idea) : Set Idea :=
  ⋃ g ∈ (G.generators : Set (Set Idea -> Set Idea)), g A

/-- Adaptive reachability: iterating the union generator. -/
def adaptiveReach {Idea : Type*} (G : GeneratorSet Idea) (A : Set Idea) (t : Nat) : Set Idea :=
  genCumulativeWith (unionGen G) t A

/-- Adaptive depth: depth under the union generator. -/
noncomputable def adaptiveDepth {Idea : Type*} (G : GeneratorSet Idea)
    (A : Set Idea) (c : Idea) : Nat :=
  depthWith (unionGen G) A c

/-! ## Theorem N1: Adaptive = Union Depth -/

/-- Adaptive reachability equals union-generator reachability. -/
theorem adaptiveReach_eq_union {Idea : Type*} (G : GeneratorSet Idea)
    (A : Set Idea) (t : Nat) :
    adaptiveReach G A t = genCumulativeWith (unionGen G) t A := by
  rfl

/-- Therefore adaptive depth equals union-generator depth. -/
theorem adaptiveDepth_eq_union {Idea : Type*} (G : GeneratorSet Idea)
    (A : Set Idea) (c : Idea) :
    adaptiveDepth G A c = depthWith (unionGen G) A c := by
  rfl

end AdaptiveGenerators
