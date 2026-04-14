/-
# Theorem N2: Conditional Equality (No Cross-Composition)

This file proves that if mixing generators does not create new depth-
shortcuts, then depth under the union generator equals the minimum
single-generator depth.
-/

import FormalAnthropology.Learning_AdaptiveGenerators
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace MultiGeneratorSystems

open Set AdaptiveGenerators
attribute [local instance] Classical.propDecidable

/-! ## Predicate: reachable by some generator at depth n -/

def reachableBySomeGenAt {Idea : Type*} (G : GeneratorSet Idea)
    (A : Set Idea) (c : Idea) (n : Nat) : Prop :=
  ∃ g ∈ G.generators, c ∈ genCumulativeWith g n A

/-- Minimal depth over all single generators. -/
noncomputable def depthMin {Idea : Type*} (G : GeneratorSet Idea)
    (A : Set Idea) (c : Idea) : Nat :=
  @dite Nat (Exists fun n => reachableBySomeGenAt G A c n)
    (Classical.propDecidable _)
    (fun h => @Nat.find _ (Classical.decPred _) h)
    (fun _ => 0)

/-- No cross-composition at each depth: union depth equals union of single depths. -/
def noCrossComposition {Idea : Type*} (G : GeneratorSet Idea) (A : Set Idea) : Prop :=
  ∀ n,
    genCumulativeWith (unionGen G) n A =
      ⋃ g ∈ (G.generators : Set (Set Idea -> Set Idea)), genCumulativeWith g n A

lemma noCrossComposition_closure {Idea : Type*} (G : GeneratorSet Idea) (A : Set Idea)
    (h : noCrossComposition G A) :
    closureWith (unionGen G) A =
      ⋃ g ∈ (G.generators : Set (Set Idea -> Set Idea)), closureWith g A := by
  ext c
  constructor
  · intro hc
    simp only [closureWith, Set.mem_iUnion] at hc
    obtain ⟨n, hn⟩ := hc
    have : c ∈ ⋃ g ∈ (G.generators : Set (Set Idea -> Set Idea)),
        genCumulativeWith g n A := by
      simpa [h n] using hn
    -- Lift to closures.
    obtain ⟨g, hg, hgn⟩ := by
      simpa using this
    exact ⟨g, hg, n, hgn⟩
  · intro hc
    simp only [closureWith, Set.mem_iUnion] at hc
    obtain ⟨g, hg, n, hn⟩ := hc
    have : c ∈ genCumulativeWith (unionGen G) n A := by
      -- Use the no-cross-composition equality in the reverse direction.
      have : c ∈ ⋃ g ∈ (G.generators : Set (Set Idea -> Set Idea)),
          genCumulativeWith g n A := by
        simpa using ⟨g, hg, hn⟩
      simpa [h n] using this
    exact ⟨n, this⟩

/-! ## Theorem N2: depth under union equals min single-generator depth -/

theorem depth_union_eq_min {Idea : Type*} (G : GeneratorSet Idea)
    (A : Set Idea) (c : Idea) (h_no_cross : noCrossComposition G A) :
    depthWith (unionGen G) A c = depthMin G A c := by
  -- Predicate equivalence at each depth.
  have hpred : ∀ n,
      (c ∈ genCumulativeWith (unionGen G) n A) ↔ reachableBySomeGenAt G A c n := by
    intro n
    have hEq := h_no_cross n
    constructor
    · intro hn
      have : c ∈ ⋃ g ∈ (G.generators : Set (Set Idea -> Set Idea)),
          genCumulativeWith g n A := by
        simpa [hEq] using hn
      simpa using this
    · intro hn
      have : c ∈ ⋃ g ∈ (G.generators : Set (Set Idea -> Set Idea)),
          genCumulativeWith g n A := by
        simpa using hn
      simpa [hEq] using this
  -- Handle reachable vs unreachable cases.
  by_cases hreach : ∃ n, c ∈ genCumulativeWith (unionGen G) n A
  · have hreach' : ∃ n, reachableBySomeGenAt G A c n := by
      obtain ⟨n, hn⟩ := hreach
      exact ⟨n, (hpred n).1 hn⟩
    haveI : DecidablePred fun n => c ∈ genCumulativeWith (unionGen G) n A :=
      Classical.decPred _
    haveI : DecidablePred fun n => reachableBySomeGenAt G A c n :=
      Classical.decPred _
    unfold depthWith depthMin
    rw [dif_pos hreach, dif_pos hreach']
    apply le_antisymm
    · apply Nat.find_le
      exact (hpred _).2 (Nat.find_spec hreach')
    · apply Nat.find_le
      exact (hpred _).1 (Nat.find_spec hreach)
  · have hreach' : ¬ ∃ n, reachableBySomeGenAt G A c n := by
      intro h'
      obtain ⟨n, hn⟩ := h'
      exact hreach ⟨n, (hpred n).2 hn⟩
    unfold depthWith depthMin
    rw [dif_neg hreach, dif_neg hreach']

/-! ## Dominance-based adaptive depth characterization -/

/-- Monotone generator on sets. -/
def isMonotone {Idea : Type*} (g : Set Idea -> Set Idea) : Prop :=
  ∀ A B, A ⊆ B → g A ⊆ g B

/-- Pointwise dominance: g* subsumes g on all seeds. -/
def dominates {Idea : Type*} (g* g : Set Idea -> Set Idea) : Prop :=
  ∀ A, g A ⊆ g* A

/-- g* dominates every generator in G and is a member. -/
def dominatesSet {Idea : Type*} (G : GeneratorSet Idea) (g* : Set Idea -> Set Idea) : Prop :=
  g* ∈ G.generators ∧ ∀ g ∈ G.generators, dominates g* g

lemma unionGen_eq_of_dominates {Idea : Type*} (G : GeneratorSet Idea)
    (g* : Set Idea -> Set Idea) (hdom : dominatesSet G g*) :
    unionGen G = g* := by
  funext A
  apply Set.eq_of_subset_of_subset
  · intro x hx
    simp [unionGen] at hx
    obtain ⟨g, hg, hxg⟩ := hx
    exact (hdom.2 g hg) A hxg
  · intro x hx
    exact ⟨g*, hdom.1, hx⟩

lemma genCumulativeWith_subset_of_dominates {Idea : Type*}
    (g g* : Set Idea -> Set Idea) (hmono : isMonotone g*) (hdom : dominates g* g) :
    ∀ n A, genCumulativeWith g n A ⊆ genCumulativeWith g* n A := by
  intro n
  induction n with
  | zero =>
      intro A
      simp [genCumulativeWith]
  | succ n ih =>
      intro A x hx
      simp [genCumulativeWith] at hx
      cases hx with
      | inl hmem =>
          exact Or.inl (ih _ hmem)
      | inr hmem =>
          have hstep : g (genCumulativeWith g n A) ⊆ g* (genCumulativeWith g n A) :=
            hdom _
          have hmono' : g* (genCumulativeWith g n A) ⊆ g* (genCumulativeWith g* n A) :=
            hmono _ _ (ih _)
          exact Or.inr (hmono' (hstep hmem))

lemma reachableBySomeGenAt_iff_dominant {Idea : Type*} (G : GeneratorSet Idea)
    (A : Set Idea) (c : Idea) (n : Nat) (g* : Set Idea -> Set Idea)
    (hdom : dominatesSet G g*) (hmono : isMonotone g*) :
    reachableBySomeGenAt G A c n ↔ c ∈ genCumulativeWith g* n A := by
  constructor
  · rintro ⟨g, hg, hc⟩
    have hdomg := hdom.2 g hg
    exact (genCumulativeWith_subset_of_dominates g g* hmono hdomg n A) hc
  · intro hc
    exact ⟨g*, hdom.1, hc⟩

/--
**Theorem N3 (Dominance Condition)**: If a generator g* pointwise dominates all others,
then adaptive depth equals g* depth and equals the minimum single-generator depth.
-/
theorem adaptive_depth_characterization_under_dominance {Idea : Type*}
    (G : GeneratorSet Idea) (A : Set Idea) (g* : Set Idea -> Set Idea)
    (hdom : dominatesSet G g*) (hmono : isMonotone g*) (c : Idea) :
    depthWith (unionGen G) A c = depthWith g* A c ∧
    depthMin G A c = depthWith g* A c := by
  have hunion : unionGen G = g* := unionGen_eq_of_dominates G g* hdom
  constructor
  · simpa [hunion]
  · have hpred :
        ∀ n, reachableBySomeGenAt G A c n ↔ c ∈ genCumulativeWith g* n A := by
        intro n
        exact reachableBySomeGenAt_iff_dominant G A c n g* hdom hmono
    by_cases hreach : ∃ n, c ∈ genCumulativeWith g* n A
    · have hreach' : ∃ n, reachableBySomeGenAt G A c n := by
        obtain ⟨n, hn⟩ := hreach
        exact ⟨n, (hpred n).2 hn⟩
      haveI : DecidablePred fun n => c ∈ genCumulativeWith g* n A :=
        Classical.decPred _
      haveI : DecidablePred fun n => reachableBySomeGenAt G A c n :=
        Classical.decPred _
      unfold depthMin depthWith
      rw [dif_pos hreach', dif_pos hreach]
      apply le_antisymm
      · apply Nat.find_le
        exact (hpred _).2 (Nat.find_spec hreach)
      · apply Nat.find_le
        exact (hpred _).1 (Nat.find_spec hreach')
    · have hreach' : ¬ ∃ n, reachableBySomeGenAt G A c n := by
        intro h'
        obtain ⟨n, hn⟩ := h'
        exact hreach ⟨n, (hpred n).1 hn⟩
      unfold depthMin depthWith
      rw [dif_neg hreach', dif_neg hreach]

end MultiGeneratorSystems
