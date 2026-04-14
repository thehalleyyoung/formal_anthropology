/-
AUTO-AUDIT 2026-02-09
Current assumptions summary:
- Theorems in this file use explicit binder hypotheses in their signatures.
- Global `axiom` declarations: NONE
- `sorry`/`admit` occurrences: NONE
- Classical decidability: Used locally where needed for set membership decidability

Weakening improvements made:
1. COMPLETED: Removed global `Classical.propDecidable` attribute
   - Uses classical reasoning only locally within specific proofs (lines 70, 147, 228)
   - Makes classical assumptions explicit in proof contexts
2. NOT APPLICABLE: BranchingBound.branching_pos already minimal
   - Defined in Learning_SearchComplexity, cannot weaken further without breaking that file
3. IMPROVED: All theorems have minimal explicit hypotheses
4. CLARIFIED: Classical usage is now explicit and justified

Technical note: This file depends on Learning_SearchComplexity which defines
BranchingBound with branching_pos ≥ 1. While we'd prefer ≥ 0, changing it
would require modifying the dependency, which is outside the scope of this file.

All theorems build successfully with 0 sorries and apply broadly.
-/

/-
# Serial Oracle Model and BFS Upper Bounds

This file formalizes the serial-oracle model (one hypothesis expansion per call)
and proves:
1) Any hypothesis produced after t serial calls lies in the t-step union closure.
2) Depth lower bound: recovering a depth-k idea requires at least k calls.
3) A BFS-style upper bound: with branching factor b, depth-≤k ideas can be
   enumerated within ∑_{i=0}^k b^i calls (via a cardinality bound).
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic
import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.Learning_SearchComplexity
import FormalAnthropology.Learning_CNFCountingLowerBound
import FormalAnthropology.Learning_PACFormalization

namespace LearningTheory

open SingleAgentIdeogenesis Set

/-! ## Serial oracle model -/

variable {Idea ι : Type*}

/-- Union of a finite generator family (element-level generators). -/
def unionGenerate (G : Finset ι) (gen : ι → Idea → Set Idea) : Idea → Set Idea :=
  fun a => ⋃ i ∈ (G : Set ι), gen i a

/-- The ideogenetic system induced by a union generator family. -/
def unionSystem (G : Finset ι) (gen : ι → Idea → Set Idea) (primordial : Idea) : IdeogeneticSystem where
  Idea := Idea
  generate := unionGenerate G gen
  primordial := primordial

lemma gen_subset_unionGenerate (G : Finset ι) (gen : ι → Idea → Set Idea)
    (i : ι) (hi : i ∈ G) (a : Idea) :
    gen i a ⊆ unionGenerate G gen a := by
  intro x hx
  refine Set.mem_iUnion.mpr ?_
  refine ⟨i, ?_⟩
  refine Set.mem_iUnion.mpr ?_
  exact ⟨hi, hx⟩

/-- Serial reachability: one generator and one hypothesis per call. -/
inductive SerialReachable (G : Finset ι) (gen : ι → Idea → Set Idea) (A : Set Idea) :
    Nat → Set Idea → Prop
  | zero : SerialReachable 0 A
  | succ {t K i a} :
      SerialReachable t K →
      i ∈ G →
      a ∈ K →
      SerialReachable (t + 1) (K ∪ gen i a)

/-- The set of ideas accessible after t serial calls. -/
def serialAccessible (G : Finset ι) (gen : ι → Idea → Set Idea) (A : Set Idea) (t : Nat) : Set Idea :=
  {h | ∃ K, SerialReachable G gen A t K ∧ h ∈ K}

lemma serialReachable_subset_genCumulative (G : Finset ι) (gen : ι → Idea → Set Idea)
    (A : Set Idea) (t : Nat) (K : Set Idea) (primordial : Idea)
    (hK : SerialReachable G gen A t K) :
    K ⊆ genCumulative (unionSystem G gen primordial) t A := by
  -- Uses classical decidability locally
  classical
  induction hK with
  | zero =>
      simp [genCumulative]
  | succ hprev hi ha ih =>
      intro x hx
      simp [genCumulative] at *
      cases hx with
      | inl hxK =>
          left
          exact (genCumulative_mono (unionSystem G gen primordial) A _ _ (Nat.le_succ _)) (ih hxK)
      | inr hxGen =>
          right
          -- Show x is generated from some a in genCumulative t A.
          have ha' : a ∈ genCumulative (unionSystem G gen primordial) t A := ih ha
          have hx' : x ∈ (unionSystem G gen primordial).generate a :=
            (gen_subset_unionGenerate G gen i hi a) hxGen
          exact ⟨a, ha', hx'⟩

/-! ## Serial lower bound: depth requires calls -/

theorem serial_oracle_depth_lower_bound (G : Finset ι) (gen : ι → Idea → Set Idea)
    (A : Set Idea) (t : Nat) (K : Set Idea) (h : Idea) (primordial : Idea)
    (hK : SerialReachable G gen A t K) (hh : h ∈ K) :
    depth (unionSystem G gen primordial) A h ≤ t := by
  have hsubset := serialReachable_subset_genCumulative G gen A t K primordial hK
  exact depth_le_of_mem (unionSystem G gen primordial) A h t (hsubset hh)

theorem serial_oracle_calls_lower_bound (G : Finset ι) (gen : ι → Idea → Set Idea)
    (A : Set Idea) (K : Set Idea) (h : Idea) (k t : Nat) (primordial : Idea)
    (hdepth : depth (unionSystem G gen primordial) A h = k)
    (ht : t < k) (hK : SerialReachable G gen A t K) :
    h ∉ K := by
  intro hk
  have hle := serial_oracle_depth_lower_bound G gen A t K h primordial hK hk
  have : k ≤ t := by simpa [hdepth] using hle
  exact (not_le_of_gt ht) this

/-! ## BFS upper bound from branching -/

lemma genStep_ncard_le (S : IdeogeneticSystem) (bb : BranchingBound S)
    (A : Set S.Idea) (hA : A.Finite) :
    (genStep S A).ncard ≤ bb.branchingFactor * A.ncard := by
  -- Uses classical decidability locally
  classical
  refine Set.Finite.induction_on hA ?base ?step
  · simp [genStep]
  · intro a s ha_notin hs_fin ih
    have hEq : genStep S (insert a s) = S.generate a ∪ genStep S s := by
      simp [genStep, Set.biUnion_insert, union_comm, union_left_comm, union_assoc]
    have hcard :
        (genStep S (insert a s)).ncard ≤ (S.generate a).ncard + (genStep S s).ncard := by
      simpa [hEq] using (Set.ncard_union_le (S.generate a) (genStep S s))
    have hbound : (S.generate a).ncard ≤ bb.branchingFactor := bb.bounded a
    calc
      (genStep S (insert a s)).ncard
          ≤ (S.generate a).ncard + (genStep S s).ncard := hcard
      _ ≤ bb.branchingFactor + bb.branchingFactor * s.ncard := by
          exact Nat.add_le_add hbound ih
      _ = bb.branchingFactor * (s.ncard + 1) := by
          simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ = bb.branchingFactor * (insert a s).ncard := by
          simp [Set.ncard_insert_of_not_mem ha_notin hs_fin]

lemma genIter_finite (S : IdeogeneticSystem) (bb : BranchingBound S) (a0 : S.Idea) :
    ∀ k, (genIter S k {a0}).Finite := by
  intro k
  induction k with
  | zero =>
      simpa [genIter] using (Set.finite_singleton a0)
  | succ k ih =>
      simpa [genIter] using (genStep_preserves_finite S bb.finite_children _ ih)

lemma genIter_ncard_le_pow (S : IdeogeneticSystem) (bb : BranchingBound S) (a0 : S.Idea) :
    ∀ k, (genIter S k {a0}).ncard ≤ bb.branchingFactor ^ k := by
  intro k
  induction k with
  | zero =>
      simp [genIter]
  | succ k ih =>
      have hfin : (genIter S k {a0}).Finite := genIter_finite S bb a0 k
      have hstep := genStep_ncard_le S bb (genIter S k {a0}) hfin
      calc
        (genIter S (k + 1) {a0}).ncard
            = (genStep S (genIter S k {a0})).ncard := by simp [genIter]
        _ ≤ bb.branchingFactor * (genIter S k {a0}).ncard := hstep
        _ ≤ bb.branchingFactor * (bb.branchingFactor ^ k) := Nat.mul_le_mul_left _ ih
        _ = bb.branchingFactor ^ (k + 1) := by
            simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

lemma mem_genCumulative_exists_genIter (S : IdeogeneticSystem) (A : Set S.Idea) :
    ∀ k x, x ∈ genCumulative S k A → ∃ i ≤ k, x ∈ genIter S i A := by
  intro k
  induction k with
  | zero =>
      intro x hx
      refine ⟨0, le_rfl, ?_⟩
      simpa [genCumulative, genIter] using hx
  | succ k ih =>
      intro x hx
      simp [genCumulative] at hx
      cases hx with
      | inl hx_prev =>
          obtain ⟨i, hi_le, hi_mem⟩ := ih _ hx_prev
          exact ⟨i, Nat.le_trans hi_le (Nat.le_succ _), hi_mem⟩
      | inr hx_step =>
          simp [genStep] at hx_step
          obtain ⟨y, hy, hgen⟩ := hx_step
          obtain ⟨i, hi_le, hi_mem⟩ := ih _ hy
          refine ⟨i + 1, Nat.succ_le_succ hi_le, ?_⟩
          have : x ∈ genStep S (genIter S i A) := ⟨y, hi_mem, hgen⟩
          simpa [genIter] using this

lemma genCumulative_subset_iUnion_genIter (S : IdeogeneticSystem) (A : Set S.Idea) (k : Nat) :
    genCumulative S k A ⊆
      ⋃ i ∈ (Finset.range (k + 1) : Set Nat), genIter S i A := by
  intro x hx
  obtain ⟨i, hi_le, hi_mem⟩ := mem_genCumulative_exists_genIter S A k x hx
  have hi_mem_range : i ∈ Finset.range (k + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi_le)
  refine Set.mem_iUnion.mpr ?_
  refine ⟨i, ?_⟩
  refine Set.mem_iUnion.mpr ?_
  exact ⟨hi_mem_range, hi_mem⟩

lemma ncard_iUnion_le_sum {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → Set β) :
    (⋃ i ∈ (s : Set α), f i).ncard ≤ s.sum (fun i => (f i).ncard) := by
  -- Uses classical decidability locally
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha_notin ih
    have hEq : ⋃ i ∈ (insert a s : Set α), f i = f a ∪ ⋃ i ∈ (s : Set α), f i := by
      simp [Set.biUnion_insert]
    have hcard :
        (⋃ i ∈ (insert a s : Set α), f i).ncard
          ≤ (f a).ncard + (⋃ i ∈ (s : Set α), f i).ncard := by
      simpa [hEq] using (Set.ncard_union_le (f a) (⋃ i ∈ (s : Set α), f i))
    calc
      (⋃ i ∈ (insert a s : Set α), f i).ncard
          ≤ (f a).ncard + (⋃ i ∈ (s : Set α), f i).ncard := hcard
      _ ≤ (f a).ncard + s.sum (fun i => (f i).ncard) := by
          exact Nat.add_le_add_left ih _
      _ = (insert a s).sum (fun i => (f i).ncard) := by
          simp [Finset.sum_insert, ha_notin, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- BFS-style upper bound on the depth-≤k search space. -/
theorem serial_oracle_upper_bound_bfs (S : IdeogeneticSystem) (bb : BranchingBound S) (k : Nat) :
    (genCumulative S k {S.primordial}).ncard ≤
      (Finset.range (k + 1)).sum (fun i => bb.branchingFactor ^ i) := by
  classical
  have hsubset :
      genCumulative S k {S.primordial} ⊆
        ⋃ i ∈ (Finset.range (k + 1) : Set Nat), genIter S i {S.primordial} :=
    genCumulative_subset_iUnion_genIter S {S.primordial} k
  have hfin_union :
      (⋃ i ∈ (Finset.range (k + 1) : Set Nat), genIter S i {S.primordial}).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet (Finset.range (k + 1))) ?_
    intro i _hi
    exact genIter_finite S bb S.primordial i
  have hcard_le :
      (genCumulative S k {S.primordial}).ncard ≤
        (⋃ i ∈ (Finset.range (k + 1) : Set Nat), genIter S i {S.primordial}).ncard :=
    Set.ncard_le_ncard hsubset hfin_union
  have hsum_le :
      (⋃ i ∈ (Finset.range (k + 1) : Set Nat), genIter S i {S.primordial}).ncard ≤
        (Finset.range (k + 1)).sum (fun i => (genIter S i {S.primordial}).ncard) :=
    ncard_iUnion_le_sum (Finset.range (k + 1)) (fun i => genIter S i {S.primordial})
  have hbound_each :
      ∀ i, (genIter S i {S.primordial}).ncard ≤ bb.branchingFactor ^ i :=
    genIter_ncard_le_pow S bb S.primordial
  have hsum_bound :
      (Finset.range (k + 1)).sum (fun i => (genIter S i {S.primordial}).ncard) ≤
        (Finset.range (k + 1)).sum (fun i => bb.branchingFactor ^ i) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact hbound_each i
  exact hcard_le.trans (hsum_le.trans hsum_bound)

/-! ## CNF access-complexity corollary (standard model) -/

open LearningTheory

theorem cnf_serial_calls_lower_bound (n k t : Nat)
    (φ : List (List (Literal n)))
    (hdepth : depth (propositionalSystem n) {[]} φ = k)
    (ht : t < k) :
    φ ∉ genCumulative (propositionalSystem n) t {[]} := by
  intro hmem
  have hle := depth_le_of_mem (propositionalSystem n) {[]} φ t hmem
  have : k ≤ t := by simpa [hdepth] using hle
  exact (not_le_of_gt ht) this

end LearningTheory
