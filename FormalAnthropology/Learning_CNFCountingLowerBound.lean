/-
# Standard-Model Counting Lower Bound (CNF Generator)

We prove a counting bound for the propositional CNF generator:
the number of depth-k formulas is at most (2n)^k, which implies
there exist Boolean functions requiring depth > k when k is small.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic
import FormalAnthropology.Learning_PropositionalDepth

namespace LearningTheory

open Set SingleAgentIdeogenesis

abbrev Literal (n : Nat) := Bool × Fin n
abbrev Assignment (n : Nat) := Fin n → Bool

/-- Convert a list of literals into a CNF with one literal per clause. -/
def toCNF {n : Nat} (l : List (Literal n)) : List (List (Literal n)) :=
  l.map (fun lit => [lit])

/-! ## Reachability of singleton-clause CNFs -/

lemma append_toCNF_reachable {n : Nat} :
    ∀ (l : List (Literal n)) (k : Nat) (φ : List (List (Literal n))),
      φ ∈ genCumulative (propositionalSystem n) k {[]} →
      φ ++ toCNF l ∈ genCumulative (propositionalSystem n) (k + l.length) {[]} := by
  intro l
  induction l with
  | nil =>
      intro k φ hφ
      simp [toCNF, hφ]
  | cons lit l ih =>
      intro k φ hφ
      cases lit with
      | mk pol var =>
          have hstep :
              φ ++ [[(pol, var)]] ∈ genCumulative (propositionalSystem n) (k + 1) {[]} := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (propositional_append_clause_reachable n k φ hφ pol var)
          have hrec := ih (k + 1) (φ ++ [[(pol, var)]]) hstep
          simpa [toCNF, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrec

lemma toCNF_reachable {n : Nat} (l : List (Literal n)) :
    toCNF l ∈ genCumulative (propositionalSystem n) l.length {[]} := by
  have h0 :
      ([] : List (List (Literal n))) ∈ genCumulative (propositionalSystem n) 0 {[]} := by
    simp [genCumulative]
  have h := append_toCNF_reachable (n := n) l 0 [] h0
  simpa using h

lemma depth_toCNF_eq_length {n : Nat} (l : List (Literal n)) :
    depth (propositionalSystem n) {[]} (toCNF l) = l.length := by
  have hreach := toCNF_reachable (n := n) l
  have hle := depth_le_of_mem (propositionalSystem n) {[]} (toCNF l) l.length hreach
  have hcl : toCNF l ∈ closure (propositionalSystem n) {[]} := by
    exact ⟨l.length, hreach⟩
  have hge := propositional_depth_ge_length n (toCNF l) hcl
  exact le_antisymm hle hge

lemma genCumulative_toCNF {n : Nat} :
    ∀ (k : Nat) (φ : List (List (Literal n))),
      φ ∈ genCumulative (propositionalSystem n) k {[]} →
      ∃ l : List (Literal n), φ = toCNF l ∧ l.length ≤ k := by
  intro k
  induction k with
  | zero =>
      intro φ hφ
      simp [genCumulative] at hφ
      subst hφ
      refine ⟨[], by simp [toCNF], by simp⟩
  | succ k ih =>
      intro φ hφ
      simp [genCumulative] at hφ
      cases hφ with
      | inl hprev =>
          obtain ⟨l, hl, hlen⟩ := ih _ hprev
          exact ⟨l, hl, Nat.le_succ_of_le hlen⟩
      | inr hstep =>
          simp [genStep, propositionalSystem] at hstep
          obtain ⟨ψ, hψ, hgen⟩ := hstep
          obtain ⟨l, hψ_eq, hlen⟩ := ih _ hψ
          cases hgen with
          | inl htrue =>
              obtain ⟨i, rfl⟩ := htrue
              refine ⟨l ++ [(true, i)], ?_, ?_⟩
              · simp [toCNF, hψ_eq, List.map_append, List.append_assoc]
              · exact Nat.add_le_add_right hlen 1
          | inr hfalse =>
              obtain ⟨i, rfl⟩ := hfalse
              refine ⟨l ++ [(false, i)], ?_, ?_⟩
              · simp [toCNF, hψ_eq, List.map_append, List.append_assoc]
              · exact Nat.add_le_add_right hlen 1

/-! ## Depth-k formulas and counting -/

def DepthKFormula (n k : Nat) :=
  { φ : List (List (Literal n)) // φ ∈ closure (propositionalSystem n) {[]} ∧
      depth (propositionalSystem n) {[]} φ = k }

def vectorToCNF {n k : Nat} (v : List.Vector (Literal n) k) :
    List (List (Literal n)) :=
  toCNF v.toList

def vectorToDepthFormula {n k : Nat} (v : List.Vector (Literal n) k) :
    DepthKFormula n k := by
  refine ⟨vectorToCNF v, ?_⟩
  have hreach :
      vectorToCNF v ∈ genCumulative (propositionalSystem n) k {[]} := by
    simpa [vectorToCNF, v.toList_length] using
      (toCNF_reachable (n := n) v.toList)
  have hcl : vectorToCNF v ∈ closure (propositionalSystem n) {[]} :=
    ⟨k, hreach⟩
  have hdepth : depth (propositionalSystem n) {[]} (vectorToCNF v) = k := by
    simpa [vectorToCNF, v.toList_length] using
      (depth_toCNF_eq_length (n := n) v.toList)
  exact ⟨hcl, hdepth⟩

lemma vectorToDepthFormula_surjective {n k : Nat} :
    Function.Surjective (vectorToDepthFormula (n := n) (k := k)) := by
  intro φ
  rcases φ with ⟨φ, hcl, hdepth⟩
  have hmem : φ ∈ genCumulative (propositionalSystem n) k {[]} := by
    have hmem' := mem_genCumulative_depth (propositionalSystem n) {[]} φ hcl
    simpa [hdepth] using hmem'
  obtain ⟨l, hl_eq, _hlen⟩ := genCumulative_toCNF (n := n) k φ hmem
  have hlen : l.length = k := by
    have hdepth_l : depth (propositionalSystem n) {[]} (toCNF l) = l.length :=
      depth_toCNF_eq_length (n := n) l
    have hdepth' : depth (propositionalSystem n) {[]} (toCNF l) = k := by
      simpa [hl_eq] using hdepth
    exact hdepth_l.symm.trans hdepth'
  refine ⟨⟨l, hlen⟩, ?_⟩
  apply Subtype.ext
  simp [vectorToDepthFormula, vectorToCNF, hl_eq, hlen]

/-- **Theorem**: Depth-k propositional formulas are at most (2n)^k. -/
theorem cnf_counting_lower_bound (n k : Nat) :
    Fintype.card (DepthKFormula n k) ≤ (2 * n) ^ k := by
  classical
  let f : List.Vector (Literal n) k → DepthKFormula n k :=
    vectorToDepthFormula (n := n) (k := k)
  have hsurj : Function.Surjective f :=
    vectorToDepthFormula_surjective (n := n) (k := k)
  have _hfinite : Finite (DepthKFormula n k) := Finite.of_surjective f hsurj
  classical
  let _ : Fintype (DepthKFormula n k) := Fintype.ofFinite (DepthKFormula n k)
  have hcard : Fintype.card (DepthKFormula n k) ≤
      Fintype.card (List.Vector (Literal n) k) :=
    Fintype.card_le_of_surjective f hsurj
  have hcard_vec : Fintype.card (List.Vector (Literal n) k) = (2 * n) ^ k := by
    simpa [Literal, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] using
      (card_vector (α := Literal n) k)
  simpa [hcard_vec] using hcard

/-! ## Corollary: existence of unrepresentable Boolean functions -/

theorem exists_unrepresentable_function (n k : Nat)
    (h : (2 * n) ^ k < 2 ^ (2 ^ n)) :
    ∃ f : Assignment n → Bool,
      ¬∃ φ, φ ∈ closure (propositionalSystem n) {[]} ∧
        depth (propositionalSystem n) {[]} φ = k ∧ evalCNF n φ = f := by
  classical
  have _hfinite : Finite (DepthKFormula n k) := by
    exact Finite.of_surjective
      (vectorToDepthFormula (n := n) (k := k))
      (vectorToDepthFormula_surjective (n := n) (k := k))
  let _ : Fintype (DepthKFormula n k) := Fintype.ofFinite (DepthKFormula n k)
  by_contra hforall
  push_neg at hforall
  let f : DepthKFormula n k → Assignment n → Bool := fun φ => evalCNF n φ.1
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨φ, hcl, hdepth, hrep⟩ := hforall g
    refine ⟨⟨φ, hcl, hdepth⟩, ?_⟩
    simpa [f] using hrep
  have hcard_funcs :
      Fintype.card (Assignment n → Bool) = 2 ^ (2 ^ n) := by
    simp [Assignment, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hcard_bound :
      Fintype.card (Assignment n → Bool) ≤ (2 * n) ^ k := by
    have hcard :
        Fintype.card (Assignment n → Bool) ≤ Fintype.card (DepthKFormula n k) :=
      Fintype.card_le_of_surjective f hsurj
    exact hcard.trans (cnf_counting_lower_bound n k)
  have : 2 ^ (2 ^ n) ≤ (2 * n) ^ k := by
    simpa [hcard_funcs] using hcard_bound
  exact (not_le_of_gt h) this

end LearningTheory
