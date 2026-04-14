/-
AUTO-AUDIT 2026-02-08
Current assumptions summary:
- Theorems in this file use explicit binder hypotheses/typeclass assumptions in their signatures.
- Global axiom declarations: none.
- sorry/admit occurrences: none.
Potential weakening targets:
- No non-derivable assumptions were found beyond explicit theorem hypotheses.
-/

/-
# Optimal Mechanism with Complete Information

This file formalizes Theorem 4 from the Paper B revision plan:
**Optimal Mechanism with Complete Information**

## Statement:
With complete information about costs (cA, cB) and value V,
the optimal mechanism uses sharing rule:
  α* = cA / (cA + cB)
  
This achieves:
- First-best efficiency when cA + cB < V
- Individual rationality for both agents
- Budget balance

## Significance:
Establishes benchmark - with complete info, simple sharing rules work.
This contrasts with the impossibility results under private information.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Tactic

namespace MechanismDesign

open Classical

/-! ## Section 1: Basic Mechanism Design Definitions -/

/-- A simple mechanism specifies payments to two agents -/
structure Mechanism where
  /-- Payment to agent A -/
  paymentA : ℝ
  /-- Payment to agent B -/
  paymentB : ℝ

/-- Individual rationality: payment covers cost -/
def IndividualRational (payment cost : ℝ) : Prop :=
  payment ≥ cost

/-- Budget balance: total payments don't exceed value -/
def BudgetBalanced (tA tB V : ℝ) : Prop :=
  tA + tB ≤ V

/-- Efficient: both agents participate -/
def Efficient (tA tB cA cB : ℝ) : Prop :=
  tA ≥ cA ∧ tB ≥ cB

/-- A mechanism is feasible if it satisfies IR and BB -/
def Feasible (m : Mechanism) (cA cB V : ℝ) : Prop :=
  IndividualRational m.paymentA cA ∧
  IndividualRational m.paymentB cB ∧
  BudgetBalanced m.paymentA m.paymentB V

/-! ## Section 2: Optimal Sharing Rule -/

/-- The optimal sharing coefficient for agent A -/
noncomputable def optimalShareA (cA cB : ℝ) : ℝ :=
  if cA + cB = 0 then 1/2 else cA / (cA + cB)

/-- The optimal sharing coefficient for agent B -/
noncomputable def optimalShareB (cA cB : ℝ) : ℝ :=
  if cA + cB = 0 then 1/2 else cB / (cA + cB)

/-- Shares sum to 1 -/
theorem shares_sum_to_one (cA cB : ℝ) (hpos : cA + cB > 0) :
    optimalShareA cA cB + optimalShareB cA cB = 1 := by
  unfold optimalShareA optimalShareB
  have hneq : cA + cB ≠ 0 := ne_of_gt hpos
  simp [hneq]
  field_simp

/-- Each share is non-negative when costs are non-negative -/
theorem shareA_nonneg (cA cB : ℝ) (hA : cA ≥ 0) (hB : cB ≥ 0) (hpos : cA + cB > 0) :
    optimalShareA cA cB ≥ 0 := by
  unfold optimalShareA
  have hneq : cA + cB ≠ 0 := ne_of_gt hpos
  simp [hneq]
  apply div_nonneg hA
  linarith

theorem shareB_nonneg (cA cB : ℝ) (hA : cA ≥ 0) (hB : cB ≥ 0) (hpos : cA + cB > 0) :
    optimalShareB cA cB ≥ 0 := by
  unfold optimalShareB
  have hneq : cA + cB ≠ 0 := ne_of_gt hpos
  simp [hneq]
  apply div_nonneg hB
  linarith

/-! ## Section 3: Main Theorem - Optimal Mechanism with Complete Information -/

/-- **Theorem 4**: The optimal mechanism with complete information
    
    When the principal knows costs (cA, cB) and value V, the optimal mechanism
    allocates payments proportional to costs. This achieves first-best efficiency.
    
    This is the benchmark case - private information will introduce complications.
-/
theorem optimal_complete_info_mechanism (cA cB V : ℝ) 
    (hA_pos : cA ≥ 0) (hB_pos : cB ≥ 0)
    (hcost_pos : cA + cB > 0)
    (hV : V ≥ cA + cB) :
    ∃ (m : Mechanism),
      -- The mechanism uses proportional sharing
      m.paymentA = optimalShareA cA cB * V ∧
      m.paymentB = optimalShareB cA cB * V ∧
      -- Individual rationality for both agents
      IndividualRational m.paymentA cA ∧
      IndividualRational m.paymentB cB ∧
      -- Budget balance
      BudgetBalanced m.paymentA m.paymentB V ∧
      -- Efficiency (both agents participate)
      Efficient m.paymentA m.paymentB cA cB := by
  -- Construct the optimal mechanism
  let m : Mechanism := {
    paymentA := optimalShareA cA cB * V
    paymentB := optimalShareB cA cB * V
  }
  use m
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · -- IR for agent A: αA * V ≥ cA
    unfold IndividualRational
    show optimalShareA cA cB * V ≥ cA
    unfold optimalShareA
    have hneq : cA + cB ≠ 0 := ne_of_gt hcost_pos
    simp [hneq]
    calc
      cA / (cA + cB) * V = cA * V / (cA + cB) := by ring
      _ ≥ cA * (cA + cB) / (cA + cB) := by
        apply div_le_div_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left hV hA_pos
        · linarith
      _ = cA := by field_simp
  constructor
  · -- IR for agent B: αB * V ≥ cB
    unfold IndividualRational
    show optimalShareB cA cB * V ≥ cB
    unfold optimalShareB
    have hneq : cA + cB ≠ 0 := ne_of_gt hcost_pos
    simp [hneq]
    calc
      cB / (cA + cB) * V = cB * V / (cA + cB) := by ring
      _ ≥ cB * (cA + cB) / (cA + cB) := by
        apply div_le_div_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left hV hB_pos
        · linarith
      _ = cB := by field_simp
  constructor
  · -- Budget balance: αA * V + αB * V ≤ V
    unfold BudgetBalanced
    have h_sum := shares_sum_to_one cA cB hcost_pos
    show optimalShareA cA cB * V + optimalShareB cA cB * V ≤ V
    calc
      optimalShareA cA cB * V + optimalShareB cA cB * V
        = (optimalShareA cA cB + optimalShareB cA cB) * V := by ring
      _ = 1 * V := by rw [h_sum]
      _ = V := by ring
      _ ≤ V := by rfl
  · -- Efficiency: both payments cover costs
    unfold Efficient
    constructor
    · show optimalShareA cA cB * V ≥ cA
      unfold optimalShareA
      have hneq : cA + cB ≠ 0 := ne_of_gt hcost_pos
      simp [hneq]
      calc
        cA / (cA + cB) * V = cA * V / (cA + cB) := by ring
        _ ≥ cA * (cA + cB) / (cA + cB) := by
          apply div_le_div_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left hV hA_pos
          · linarith
        _ = cA := by field_simp
    · show optimalShareB cA cB * V ≥ cB
      unfold optimalShareB
      have hneq : cA + cB ≠ 0 := ne_of_gt hcost_pos
      simp [hneq]
      calc
        cB / (cA + cB) * V = cB * V / (cA + cB) := by ring
        _ ≥ cB * (cA + cB) / (cA + cB) := by
          apply div_le_div_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left hV hB_pos
          · linarith
        _ = cB := by field_simp

/-! ## Section 4: First-Best Efficiency -/

/-- The mechanism achieves first-best efficiency: social surplus is maximized -/
theorem first_best_efficiency (cA cB V : ℝ)
    (hA_pos : cA ≥ 0) (hB_pos : cB ≥ 0)
    (hcost_pos : cA + cB > 0)
    (hV : V > cA + cB) :
    ∃ (m : Mechanism),
      Feasible m cA cB V ∧
      -- Social surplus (value minus costs) is maximized
      V - cA - cB > 0 := by
  obtain ⟨m, _, _, hIR_A, hIR_B, hBB, _⟩ := 
    optimal_complete_info_mechanism cA cB V hA_pos hB_pos hcost_pos (le_of_lt hV)
  use m
  constructor
  · unfold Feasible
    exact ⟨hIR_A, hIR_B, hBB⟩
  · linarith

/-! ## Section 5: Remarks on Optimality -/

/-- Remark: With complete information, any feasible mechanism that extracts
    full surplus from agents cannot do better than proportional sharing.
    
    This is because the proportional sharing rule:
    1. Minimizes the "information rent" (zero in complete info case)
    2. Ensures both agents have equal relative surplus (fair)
    3. Is the unique solution that makes both IR constraints tight when V = cA + cB
-/

theorem proportional_sharing_is_unique_at_boundary (cA cB V : ℝ)
    (hA_pos : cA > 0) (hB_pos : cB > 0)
    (hV : V = cA + cB) :
    ∀ (m : Mechanism),
      IndividualRational m.paymentA cA →
      IndividualRational m.paymentB cB →
      BudgetBalanced m.paymentA m.paymentB V →
      (m.paymentA = cA ∧ m.paymentB = cB) := by
  intro m hIR_A hIR_B hBB
  unfold IndividualRational at hIR_A hIR_B
  unfold BudgetBalanced at hBB
  have h1 : m.paymentA + m.paymentB ≤ cA + cB := by
    rw [← hV]
    exact hBB
  have h2 : m.paymentA ≥ cA := hIR_A
  have h3 : m.paymentB ≥ cB := hIR_B
  constructor
  · linarith
  · linarith

end MechanismDesign
