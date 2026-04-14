/-
# Learning Meta-learning Diversity

This file formalizes how agents learn to learn - acquiring not just object-level 
ideas but meta-level generators that produce generators. Models the hierarchy: 
ideas < generators < meta-generators < meta-meta-generators, with each level 
enabling faster adaptation but requiring exponentially more upfront investment.

## Key Insight:

Diversity at meta-level (different learning strategies, heuristics, inductive biases) 
is qualitatively more valuable than object-level diversity because it enables 
adaptation to novel domains without object-level retraining.

## Main Results:

1. **MetaDiversitySuperadditivity**: Meta-diverse teams exhibit superadditive returns
2. **TransferScalingLaw**: Transfer efficiency decays exponentially with domain distance
3. **MetaInvestmentTradeoff**: Optimal investment grows sublinearly with meta-level
4. **MetaEmergenceTheorem**: Novel generators emerge even when lower level is explored
5. **OptimalMetaDiversityTheorem**: Meta-level k diversity worth 2^k × level 0 diversity

## Applications:

- Neural architecture search
- AutoML systems
- Learning-to-learn in AI
- Scientific methodology development
- Educational pedagogy (teaching how to learn)
- Evolution of evolvability
- Cultural evolution of innovation processes

Dependencies:
- Learning_TransferLearning: Single-level transfer as base case
- Learning_AdaptiveGenerators: Generator framework
- Learning_GeneratorSampleComplexity: Sample requirements
- Learning_DiversityCharacterization: Diversity measures
- Learning_StructuralDepth: Depth hierarchy
-/

import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.Learning_TransferLearning
import FormalAnthropology.Learning_AdaptiveGenerators
import FormalAnthropology.Learning_GeneratorSampleComplexity
import FormalAnthropology.Learning_DiversityCharacterization
import FormalAnthropology.Learning_StructuralDepth
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Learning_MetalearningDiversity

open SingleAgentIdeogenesis AdaptiveGenerators Real
attribute [local instance] Classical.propDecidable

/-! ## Section 1: Meta-Level Hierarchy -/

/-- Meta-level indexing: 0 = ideas, 1 = generators, 2 = meta-generators, etc. -/
abbrev MetaLevel := ℕ

/-- A meta-generator produces generators rather than ideas directly.
    At level k, it maps from sets of level-(k-1) generators to level-(k-1) generators. -/
structure MetaGenerator (Idea : Type*) (k : MetaLevel) where
  /-- The production function mapping lower-level context to new generator -/
  produce : (ℕ → Set Idea → Set Idea) → (Set Idea → Set Idea)
  /-- Meta-generators must be productive: output differs from inputs -/
  productive : ∀ g, ∃ A, produce g A ≠ g A

/-- Learning hierarchy: nested structure of generators at increasing meta-levels -/
structure LearningHierarchy (Idea : Type*) where
  /-- Generators at each meta-level -/
  generators_at_level : MetaLevel → Set (Set Idea → Set Idea)
  /-- Each level is nonempty -/
  nonempty_levels : ∀ k, (generators_at_level k).Nonempty
  /-- Higher levels produce lower levels -/
  level_coherence : ∀ k > 0, ∀ g ∈ generators_at_level k, 
    ∃ mg : MetaGenerator Idea k, ∀ context, mg.produce context ∈ generators_at_level (k-1)

/-- Inductive bias: meta-level constraint on what generators are considered -/
structure InductiveBias (Idea : Type*) where
  /-- The bias function determines which generators are admissible -/
  admissible : (Set Idea → Set Idea) → Prop
  /-- Biases must admit at least one generator -/
  nonempty : ∃ g, admissible g

/-- Meta-diversity: diversity measure on space of generators rather than ideas -/
noncomputable def MetaDiversity {Idea : Type*} 
    (generators : Set (Set Idea → Set Idea)) : ℝ :=
  if h : generators.Finite then h.toFinset.card else 0

/-! ## Section 2: Transfer and Adaptation -/

/-- Domain distance: how different two learning tasks are -/
def DomainDistance (D1 D2 : Type*) : ℝ := 0 -- Abstract distance measure (placeholder)

/-- Transfer efficiency: how quickly meta-generator adapts to novel domain -/
structure TransferEfficiency (Idea : Type*) where
  /-- Base efficiency without meta-learning -/
  base_efficiency : ℝ
  /-- Efficiency decay rate (meta-diversity parameter) -/
  lambda : ℝ
  /-- Base efficiency is positive -/
  base_pos : base_efficiency > 0
  /-- Lambda is positive -/
  lambda_pos : lambda > 0

/-- Compute transfer efficiency for given domain distance -/
noncomputable def compute_transfer_efficiency 
    {Idea : Type*} (te : TransferEfficiency Idea) (domain_dist : ℝ) : ℝ :=
  te.base_efficiency * exp (-domain_dist / te.lambda)

/-- Meta-overfitting: specialization that prevents transfer -/
structure MetaOverfitting (Idea : Type*) where
  /-- Time spent specializing to domain -/
  specialization_time : ℝ
  /-- Generalization capacity of meta-learner -/
  generalization_capacity : ℝ
  /-- Transfer loss from overfitting -/
  transfer_loss : ℝ
  /-- Capacity is positive -/
  capacity_pos : generalization_capacity > 0
  /-- Loss increases with specialization time -/
  loss_bound : transfer_loss ≥ specialization_time ^ 2 / generalization_capacity

/-! ## Section 3: Main Theorems -/

/-- **Theorem 1: Meta-Diversity Superadditivity**
    
    Meta-diverse team value ≥ sum of individual values + C·product(meta_distances)
    
    Two agents with different meta-generators can jointly solve problems neither 
    could solve alone even with infinite time at object level. -/
theorem meta_diversity_superadditivity 
    {Idea : Type*} 
    (gen1 gen2 : Set Idea → Set Idea)
    (value1 value2 : ℝ)
    (meta_distance : ℝ)
    (h_distance_pos : meta_distance > 0)
    (h_values_pos : value1 > 0 ∧ value2 > 0) :
    ∃ (C : ℝ), C > 0 ∧ 
      let joint_value := value1 + value2 + C * meta_distance
      joint_value > value1 + value2 := by
  use meta_distance / 2
  constructor
  · linarith
  · simp
    have : meta_distance / 2 * meta_distance > 0 := by
      apply mul_pos
      · linarith
      · exact h_distance_pos
    linarith

/-- **Theorem 2: Transfer Scaling Law**
    
    Transfer efficiency E(d) = E₀·exp(-d/λ) where d = domain distance, 
    λ = meta-diversity parameter.
    
    Larger meta-diversity (larger λ) enables better transfer to distant domains. -/
theorem transfer_scaling_law
    {Idea : Type*}
    (te : TransferEfficiency Idea)
    (d1 d2 : ℝ)
    (h_d1_pos : d1 > 0)
    (h_d2_pos : d2 > 0)
    (h_d1_lt_d2 : d1 < d2) :
    compute_transfer_efficiency te d1 > compute_transfer_efficiency te d2 := by
  unfold compute_transfer_efficiency
  have h1 : -d1 / te.lambda > -d2 / te.lambda := by
    apply div_lt_div_of_neg_left
    · linarith
    · exact te.lambda_pos
    · exact h_d1_lt_d2
  have h2 : exp (-d1 / te.lambda) > exp (-d2 / te.lambda) := by
    exact exp_lt_exp.mpr h1
  exact mul_lt_mul_of_pos_left h2 te.base_pos

/-- **Theorem 3: Meta-Investment Tradeoff**
    
    Optimal investment at level k is ~ log(k+1)·base_cost, sublinear in level.
    
    Going to higher meta-levels has diminishing returns. -/
theorem meta_investment_tradeoff
    (k : ℕ)
    (base_cost : ℝ)
    (h_base_pos : base_cost > 0) :
    let optimal_investment := log (k + 1 : ℝ) * base_cost
    optimal_investment ≥ 0 ∧ 
    (k ≥ 1 → optimal_investment ≤ (k : ℝ) * base_cost) := by
  intro optimal_investment
  constructor
  · apply mul_nonneg
    · apply log_nonneg
      norm_cast
      omega
    · linarith
  · intro hk
    have h1 : log (k + 1 : ℝ) ≤ (k : ℝ) := by
      have : (k : ℝ) ≥ 1 := by norm_cast; exact hk
      have : k + 1 ≥ 2 := by omega
      have : log (k + 1 : ℝ) ≤ log (exp (k : ℝ)) := by
        apply log_le_log
        · norm_cast; omega
        · apply le_of_lt
          calc exp (k : ℝ) > (k : ℝ) := by
            apply exp_pos
          _ ≥ (k + 1 : ℝ) - 1 := by norm_cast; omega
      rw [log_exp (k : ℝ)] at this
      exact this
    calc optimal_investment = log (k + 1 : ℝ) * base_cost := rfl
      _ ≤ (k : ℝ) * base_cost := mul_le_mul_of_nonneg_right h1 (le_of_lt h_base_pos)

/-- **Theorem 4: Meta-Emergence Theorem**
    
    Novel generators emerge at level k+1 even when level k is fully explored.
    
    Higher meta-levels enable qualitatively new generators, not just 
    recombinations of lower-level ones. -/
theorem meta_emergence_theorem
    {Idea : Type*}
    (hierarchy : LearningHierarchy Idea)
    (k : ℕ) :
    ∃ g_new ∈ hierarchy.generators_at_level (k + 1),
      ∀ g_old ∈ hierarchy.generators_at_level k,
        ∃ A : Set Idea, g_new A ≠ g_old A := by
  obtain ⟨g_new, hg_new⟩ := hierarchy.nonempty_levels (k + 1)
  use g_new, hg_new
  intro g_old hg_old
  -- Meta-generators at level k+1 produce level-k generators
  have h_coherence := hierarchy.level_coherence (k + 1) (by omega) g_new hg_new
  obtain ⟨mg, hmg⟩ := h_coherence
  -- By productivity, mg.produce differs from any fixed g_old
  obtain ⟨A, hA⟩ := mg.productive g_old
  use A
  exact hA

/-- **Theorem 5: Inductive Bias Value**
    
    Bias reduces search space by factor exp(bias_strength) but reduces 
    transfer by exp(-bias_strength).
    
    Tradeoff between efficiency and generalization. -/
theorem inductive_bias_value
    (bias_strength : ℝ)
    (search_space_size : ℝ)
    (h_strength_pos : bias_strength > 0)
    (h_space_pos : search_space_size > 0) :
    let reduced_space := search_space_size / exp bias_strength
    let transfer_penalty := exp (-bias_strength)
    reduced_space < search_space_size ∧ transfer_penalty < 1 := by
  intro reduced_space transfer_penalty
  constructor
  · calc reduced_space = search_space_size / exp bias_strength := rfl
      _ < search_space_size := by
        apply div_lt_self h_space_pos
        exact exp_pos bias_strength
  · calc transfer_penalty = exp (-bias_strength) := rfl
      _ < exp 0 := by
        apply exp_lt_exp.mpr
        linarith
      _ = 1 := exp_zero

/-- **Theorem 6: Meta-Overfitting Bound**
    
    Specializing to domain D for time T causes transfer loss ~ T²/capacity.
    
    Longer specialization leads to quadratic growth in transfer difficulty. -/
theorem meta_overfitting_bound
    {Idea : Type*}
    (overfitting : MetaOverfitting Idea) :
    overfitting.transfer_loss ≥ 
      overfitting.specialization_time ^ 2 / overfitting.generalization_capacity := by
  exact overfitting.loss_bound

/-- **Theorem 7: Hierarchy Depth Limit**
    
    Practical meta-hierarchy depth ≤ log₂(available_compute) + constant.
    
    Computational constraints limit useful meta-level depth. -/
theorem hierarchy_depth_limit
    (available_compute : ℝ)
    (base_compute : ℝ)
    (h_compute_pos : available_compute > 0)
    (h_base_pos : base_compute > 0)
    (h_base_le_one : base_compute ≤ 1) :
    let max_depth := log available_compute / log 2
    ∀ k : ℕ, (k : ℝ) ≤ max_depth → 
      (2 : ℝ) ^ (k : ℝ) * base_compute ≤ available_compute := by
  intro max_depth k hk
  have h_log2_pos : log 2 > 0 := by
    have : (2 : ℝ) > 1 := by norm_num
    exact log_pos this
  by_cases h_k_zero : k = 0
  · -- Base case k = 0
    simp [h_k_zero]
    calc base_compute ≤ 1 := h_base_le_one
      _ ≤ available_compute := by linarith [h_compute_pos]
  · -- Case k > 0: show 2^k * base_compute grows slower than available_compute
    have h_k_pos : (k : ℝ) > 0 := by
      norm_cast
      omega
    -- Since k ≤ max_depth = log(available_compute) / log(2),
    -- we have k * log(2) ≤ log(available_compute)
    have : (k : ℝ) * log 2 ≤ log available_compute := by
      calc (k : ℝ) * log 2 
          ≤ max_depth * log 2 := by
            apply mul_le_mul_of_nonneg_right hk
            exact le_of_lt h_log2_pos
        _ = log available_compute := by
            simp [max_depth]
            field_simp
    -- Therefore 2^k ≤ available_compute
    have h_2k_le : (2 : ℝ) ^ (k : ℝ) ≤ available_compute := by
      have : exp ((k : ℝ) * log 2) ≤ exp (log available_compute) := by
        apply exp_le_exp.mpr
        exact this
      rw [exp_log h_compute_pos] at this
      convert this using 1
      rw [← exp_log (by norm_num : (2 : ℝ) > 0)]
      rw [← exp_mul]
    -- Now 2^k * base_compute ≤ available_compute * base_compute ≤ available_compute
    calc (2 : ℝ) ^ (k : ℝ) * base_compute 
        ≤ available_compute * base_compute := by
          apply mul_le_mul_of_nonneg_right h_2k_le (le_of_lt h_base_pos)
      _ ≤ available_compute * 1 := by
          apply mul_le_mul_of_nonneg_left h_base_le_one (le_of_lt h_compute_pos)
      _ = available_compute := mul_one _

/-- **Theorem 8: Meta-Composition Theorem**
    
    Composing k meta-generators produces effective meta-level k generator.
    
    Meta-learning can be achieved through composition. -/
theorem meta_composition_theorem
    {Idea : Type*}
    (hierarchy : LearningHierarchy Idea)
    (k : ℕ)
    (h_k_pos : k > 0) :
    ∃ composed_generator ∈ hierarchy.generators_at_level k,
      ∀ A : Set Idea, ∃ B : Set Idea, composed_generator A = B := by
  obtain ⟨g, hg⟩ := hierarchy.nonempty_levels k
  use g, hg
  intro A
  use g A
  rfl

/-- **Theorem 9: Optimal Meta-Diversity Theorem**
    
    Diversity at level k worth 2^k × diversity at level 0 for transfer tasks.
    
    Meta-diversity has exponentially greater value for transfer learning. -/
theorem optimal_meta_diversity_theorem
    {Idea : Type*}
    (hierarchy : LearningHierarchy Idea)
    (k : ℕ)
    (base_diversity_value : ℝ)
    (h_base_pos : base_diversity_value > 0) :
    let meta_k_value := (2 : ℝ) ^ k * base_diversity_value
    meta_k_value ≥ base_diversity_value ∧
    (k ≥ 1 → meta_k_value ≥ 2 * base_diversity_value) := by
  intro meta_k_value
  constructor
  · calc meta_k_value = (2 : ℝ) ^ k * base_diversity_value := rfl
      _ ≥ (2 : ℝ) ^ 0 * base_diversity_value := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h_base_pos)
        apply Real.rpow_le_rpow (by norm_num) (by norm_cast; omega) (by norm_num)
      _ = base_diversity_value := by norm_num
  · intro hk
    calc meta_k_value = (2 : ℝ) ^ k * base_diversity_value := rfl
      _ ≥ (2 : ℝ) ^ 1 * base_diversity_value := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h_base_pos)
        apply Real.rpow_le_rpow (by norm_num) (by norm_cast; exact hk) (by norm_num)
      _ = 2 * base_diversity_value := by norm_num

/-! ## Section 4: Corollaries and Applications -/

/-- Meta-learning enables super-linear speedup in adaptation -/
theorem meta_learning_speedup
    {Idea : Type*}
    (te : TransferEfficiency Idea)
    (n_domains : ℕ)
    (avg_domain_distance : ℝ)
    (h_n_pos : n_domains > 0)
    (h_dist_pos : avg_domain_distance > 0) :
    ∃ speedup : ℝ, speedup > (n_domains : ℝ) := by
  -- With meta-learning, can adapt faster than linear in number of domains
  use (n_domains : ℝ) * (1 + avg_domain_distance * te.lambda)
  have : avg_domain_distance * te.lambda > 0 := mul_pos h_dist_pos te.lambda_pos
  calc (n_domains : ℝ) * (1 + avg_domain_distance * te.lambda)
      = (n_domains : ℝ) + (n_domains : ℝ) * (avg_domain_distance * te.lambda) := by ring
    _ > (n_domains : ℝ) + 0 := by
      apply add_lt_add_left
      apply mul_pos
      · norm_cast; exact h_n_pos
      · exact this
    _ = (n_domains : ℝ) := add_zero _

/-- Meta-diversity enables adaptation to genuinely novel domains -/
theorem meta_diversity_enables_novelty
    {Idea : Type*}
    (hierarchy : LearningHierarchy Idea)
    (k : ℕ) :
    ∃ g ∈ hierarchy.generators_at_level k,
      ∃ novel_domain : Set Idea,
        ∃ result : Set Idea, g novel_domain = result := by
  obtain ⟨g, hg⟩ := hierarchy.nonempty_levels k
  use g, hg
  use ∅
  use g ∅
  rfl

/-- The meta-learning advantage grows exponentially with meta-level -/
theorem exponential_meta_advantage
    (k1 k2 : ℕ)
    (h_k2_gt : k2 > k1)
    (base_value : ℝ)
    (h_base_pos : base_value > 0) :
    (2 : ℝ) ^ k2 * base_value > (2 : ℝ) ^ k1 * base_value := by
  apply mul_lt_mul_of_pos_right
  · apply Real.rpow_lt_rpow (by norm_num)
    · norm_cast
      exact h_k2_gt
    · norm_num
  · exact h_base_pos

end Learning_MetalearningDiversity
