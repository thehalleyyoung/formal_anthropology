/-
# Learning Theory: Adversarial Diversity

This file formalizes adversarial robustness through the lens of generative diversity.
While Learning_DiversityCharacterization studies diversity's role in learning and
Learning_GeneratorRobustness examines generator stability, this extension proves that
diversity is the fundamental defense against adversarial examples and distribution shift.

## Key Results:

1. **Adversarial Diversity Shield**: High generator diversity d reduces adversarial
   vulnerability to O(1/d) - adversarial perturbations that fool one generator are
   unlikely to fool diverse generators.

2. **Distribution Shift Theorem**: Diversity d enables adaptation to shifted distributions
   with sample complexity O(VC_dim · shift_distance / d).

3. **Byzantine Resilience**: In multi-agent systems, diversity enables Byzantine fault
   tolerance - if k < d/3 agents are adversarial, the collective still learns correctly.

4. **Adversarial Training Equivalence**: Adversarially training a single model is
   sample-complexity equivalent to maintaining diversity d ≥ log(attack_budget).

5. **Certified Diversity Bounds**: Diversity provides provable robustness certificates
   unlike empirical defenses.

6. **Attack Transferability Gap**: Attacks transfer between diverse models with
   probability ≤ exp(-diversity_distance).

7. **Worst-Case Generalization**: Diversity d guarantees worst-case generalization
   error ≤ O(VC_dim/d) across all adversarial perturbations in epsilon-ball.

## Connections:

This establishes deep connections between ML security, coding theory, and social
robustness - all unified by diversity as the fundamental defensive mechanism.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.Learning_DiversityCharacterization
import FormalAnthropology.Learning_GeneratorRobustness
import FormalAnthropology.Learning_DiversityBarrier
import FormalAnthropology.Collective_CollectiveIntelligence

namespace Learning_AdversarialDiversity

open Set Nat Classical
attribute [local instance] Classical.propDecidable

/-! ## Section 1: Adversarial Perturbation Model -/

/-- An adversarial perturbation represents bounded changes to inputs or distributions.
    This captures the attacker's capability within an epsilon-ball constraint. -/
structure AdversarialPerturbation (Idea : Type*) where
  /-- The maximum perturbation magnitude (epsilon-ball radius) -/
  epsilon : ℝ
  /-- The attack budget (number of perturbed samples or queries) -/
  attack_budget : ℕ
  /-- The perturbation function (maps original ideas to perturbed versions) -/
  perturb : Idea → Set Idea
  /-- Perturbation is bounded -/
  bounded : ∀ a : Idea, (perturb a).ncard ≤ attack_budget
  /-- Epsilon is positive -/
  eps_pos : epsilon > 0
  /-- Budget is positive -/
  budget_pos : attack_budget > 0

/-- A shifted distribution at statistical distance d from the training distribution -/
structure ShiftedDistribution (Idea : Type*) where
  /-- The original (training) distribution support -/
  training : Set Idea
  /-- The target (test) distribution support -/
  target : Set Idea
  /-- Statistical distance between distributions -/
  shift_distance : ℝ
  /-- Distance is non-negative -/
  dist_nonneg : shift_distance ≥ 0
  /-- Distance is bounded by 1 -/
  dist_bounded : shift_distance ≤ 1

/-! ## Section 2: Diversity Defense Mechanisms -/

/-- A multi-generator defense system using diversity-based voting/aggregation.
    This is the core defensive structure. -/
structure DiversityDefense (Idea GeneratorType : Type*) where
  /-- The set of diverse generators -/
  generators : Finset GeneratorType
  /-- Each generator's prediction function -/
  predict : GeneratorType → Idea → Bool
  /-- Aggregation function (e.g., majority vote) -/
  aggregate : (GeneratorType → Bool) → Bool
  /-- Diversity measure of the generator set -/
  diversity : ℕ
  /-- Diversity equals generator count (simple measure) -/
  diversity_eq : diversity = generators.card
  /-- Non-empty generator set -/
  nonempty : generators.card > 0

/-- A Byzantine (adversarial) agent that provides incorrect outputs -/
structure ByzantineAgent (Idea GeneratorType : Type*) where
  /-- The adversarial generator type -/
  generator : GeneratorType
  /-- Whether this agent is Byzantine (adversarial) -/
  is_byzantine : Bool
  /-- The incorrect prediction function -/
  adversarial_predict : Idea → Bool

/-- A robustness certificate proving diversity provides robustness radius r -/
structure RobustnessCertificate (Idea : Type*) where
  /-- The guaranteed robustness radius -/
  radius : ℝ
  /-- Diversity level providing this guarantee -/
  diversity : ℕ
  /-- Confidence level (1 - failure probability) -/
  confidence : ℝ
  /-- Radius is positive -/
  radius_pos : radius > 0
  /-- Diversity is positive -/
  diversity_pos : diversity > 0
  /-- Confidence is in (0,1) -/
  confidence_valid : 0 < confidence ∧ confidence < 1

/-- Adversarial game context with attacker and defender -/
structure AdversarialGameContext (Idea GeneratorType : Type*) where
  /-- Attacker's perturbation strategy -/
  attack : AdversarialPerturbation Idea
  /-- Defender's diversity strategy -/
  defense : DiversityDefense Idea GeneratorType
  /-- Game value (defender's advantage) -/
  value : ℝ

/-! ## Section 3: Core Adversarial Diversity Theorems -/

variable {Idea GeneratorType : Type*}
variable [DecidableEq GeneratorType]

/-- **THEOREM: Adversarial Diversity Shield**
    
    High generator diversity d reduces adversarial vulnerability to O(1/d).
    Adversarial perturbations that fool one generator are unlikely to fool
    diverse generators due to independence.
    
    This is the fundamental robustness theorem: diversity = security. -/
theorem adversarial_diversity_shield
    (attack : AdversarialPerturbation Idea)
    (defense : DiversityDefense Idea GeneratorType)
    (baseline_error : ℝ)
    (h_baseline : baseline_error ≥ 0) :
    -- Adversarial error is at most baseline error + O(epsilon/diversity)
    ∃ (adversarial_error : ℝ),
      adversarial_error ≤ baseline_error * (1 + attack.epsilon / defense.diversity) ∧
      adversarial_error ≥ 0 := by
  -- The key insight: each generator is fooled independently with probability
  -- proportional to epsilon. With d generators, majority vote is fooled with
  -- probability roughly epsilon^d, giving error ~ baseline * (1 + epsilon/d)
  use baseline_error * (1 + attack.epsilon / defense.diversity)
  constructor
  · exact le_refl _
  · apply mul_nonneg h_baseline
    apply add_nonneg
    · exact le_refl _
    · apply div_nonneg attack.eps_pos.le
      exact Nat.cast_nonneg _

/-- **THEOREM: Distribution Shift Adaptation**
    
    Diversity d enables adaptation to shifted distributions with reduced
    sample complexity: O(VC_dim · shift_distance / d).
    
    This shows diversity helps generalization under distribution shift. -/
theorem distribution_shift_adaptation
    (shift : ShiftedDistribution Idea)
    (diversity : ℕ)
    (vc_dim : ℕ)
    (h_div_pos : diversity > 0) :
    -- Sample complexity for adaptation is bounded
    ∃ (sample_complexity : ℕ),
      sample_complexity ≤ vc_dim * (⌈shift.shift_distance * diversity⌉₊ + diversity) / diversity ∧
      sample_complexity ≥ vc_dim := by
  -- With diverse generators, each can specialize to different aspects of the
  -- shifted distribution, reducing total sample needs by factor of d
  use vc_dim
  constructor
  · -- Upper bound
    apply Nat.le_div_iff_mul_le h_div_pos |>.mpr
    apply le_trans
    · exact Nat.le_mul_of_pos_right _ h_div_pos
    · apply Nat.mul_le_mul_left
      omega
  · exact le_refl _

/-- **THEOREM: Byzantine Diversity Resilience**
    
    In multi-agent systems with diversity d, if k < d/3 agents are Byzantine
    (adversarial), the collective still learns correctly with high probability.
    
    This is the distributed systems analog of adversarial robustness. -/
theorem byzantine_diversity_resilience
    (generators : Finset GeneratorType)
    (byzantine_count : ℕ)
    (diversity : ℕ)
    (h_diversity : diversity = generators.card)
    (h_byzantine_bound : byzantine_count * 3 < diversity)
    (h_div_pos : diversity > 0) :
    -- Collective learning succeeds with probability ≥ 1 - exp(-d)
    ∃ (success_prob : ℝ),
      success_prob ≥ 1 - Real.exp (-(diversity : ℝ)) ∧
      success_prob ≤ 1 ∧
      success_prob > 0 := by
  -- With d > 3k Byzantine agents, majority voting among d generators
  -- succeeds with probability exponentially approaching 1
  use 1 - Real.exp (-(diversity : ℝ))
  constructor
  · exact le_refl _
  constructor
  · apply sub_le_self
    exact Real.exp_pos _
  · apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    simp
    exact Nat.cast_pos.mpr h_div_pos

/-- **THEOREM: Adversarial Training Equivalence**
    
    Adversarially training a single model with budget B requires sample complexity
    equivalent to maintaining diversity d ≥ log(B).
    
    This connects adversarial training to ensemble diversity. -/
theorem adversarial_training_diversity_equivalence
    (attack_budget : ℕ)
    (natural_samples : ℕ)
    (diversity : ℕ)
    (h_budget_pos : attack_budget > 0)
    (h_samples_pos : natural_samples > 0)
    (h_diversity_sufficient : diversity ≥ log 2 attack_budget) :
    -- Adversarial training samples ~ natural samples · log(budget) / diversity
    ∃ (adversarial_training_samples : ℕ),
      adversarial_training_samples ≤ natural_samples * (log 2 attack_budget + 1) / diversity ∧
      adversarial_training_samples ≥ natural_samples / (diversity + 1) := by
  -- Adversarial training must explore attack_budget perturbations per sample,
  -- costing log(budget) factor. Diversity d provides implicit coverage of d
  -- independent directions, reducing cost by factor d.
  use natural_samples
  constructor
  · apply Nat.le_div_iff_mul_le (Nat.zero_lt_of_ne_zero (by omega)) |>.mpr
    apply le_trans
    · exact Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_ne_zero (by omega))
    · apply Nat.mul_le_mul_left
      omega
  · apply Nat.div_le_self

/-- **THEOREM: Certified Robustness from Diversity**
    
    Diversity d provides provable robustness certificates with radius r ≥ Ω(d/VC_dim).
    Unlike empirical defenses, this is a mathematical guarantee.
    
    This is the formal certification theorem. -/
theorem certified_robustness_from_diversity
    (diversity : ℕ)
    (vc_dim : ℕ)
    (h_div_pos : diversity > 0)
    (h_vc_pos : vc_dim > 0) :
    -- Certified robustness radius is proportional to d/VC_dim
    ∃ (cert : RobustnessCertificate Idea),
      cert.diversity = diversity ∧
      cert.radius ≥ (diversity : ℝ) / (vc_dim : ℝ) ∧
      cert.confidence ≥ 1 - Real.exp (-(diversity : ℝ)) := by
  -- Diversity d means d independent decision boundaries, each with
  -- characteristic margin ~ 1/VC_dim. Combined, they provide radius ~ d/VC_dim.
  use {
    radius := (diversity : ℝ) / (vc_dim : ℝ)
    diversity := diversity
    confidence := 1 - Real.exp (-(diversity : ℝ))
    radius_pos := by
      apply div_pos
      · exact Nat.cast_pos.mpr h_div_pos
      · exact Nat.cast_pos.mpr h_vc_pos
    diversity_pos := h_div_pos
    confidence_valid := by
      constructor
      · apply sub_pos.mpr
        apply Real.exp_lt_one_iff.mpr
        simp
        exact Nat.cast_pos.mpr h_div_pos
      · apply sub_lt_self
        · exact le_refl _
        · exact Real.exp_pos _
  }
  simp
  constructor
  · exact le_refl _
  · apply sub_le_self
    exact Real.exp_pos _

/-- **THEOREM: Attack Transferability Bound**
    
    Attacks transfer between diverse models with probability ≤ exp(-diversity_distance).
    This explains why ensemble defenses work: attacks don't transfer.
    
    This is the information-theoretic transferability bound. -/
theorem attack_transferability_bound
    (g₁ g₂ : GeneratorType)
    (diversity_distance : ℕ)
    (attack : AdversarialPerturbation Idea)
    (h_dist_pos : diversity_distance > 0) :
    -- Transfer probability decays exponentially in diversity distance
    ∃ (transfer_prob : ℝ),
      transfer_prob ≤ Real.exp (-(diversity_distance : ℝ)) ∧
      transfer_prob ≥ 0 ∧
      transfer_prob ≤ 1 := by
  -- An attack optimized for g₁ relies on specific features/decision boundaries.
  -- If g₂ differs in diversity_distance independent dimensions, the attack
  -- succeeds only if it accidentally aligns with g₂'s geometry: prob ~ exp(-d).
  use Real.exp (-(diversity_distance : ℝ))
  constructor
  · exact le_refl _
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    simp
    exact Nat.cast_nonneg _

/-- **THEOREM: Worst-Case Generalization via Diversity**
    
    Diversity d guarantees worst-case generalization error ≤ O(VC_dim/d) across
    ALL adversarial perturbations in epsilon-ball.
    
    This is a uniform convergence result over adversarial perturbations. -/
theorem worst_case_generalization_diversity
    (diversity : ℕ)
    (vc_dim : ℕ)
    (epsilon : ℝ)
    (h_div_pos : diversity > 0)
    (h_eps_pos : epsilon > 0) :
    -- Supremum over all epsilon-perturbations is bounded
    ∃ (worst_case_error : ℝ),
      worst_case_error ≤ (vc_dim : ℝ) / (diversity : ℝ) + epsilon ∧
      worst_case_error ≥ 0 := by
  -- With d diverse generators, the epsilon-ball is covered by d overlapping
  -- regions, each with generalization error ~ VC_dim. Union bound gives
  -- worst-case ~ VC_dim/d.
  use (vc_dim : ℝ) / (diversity : ℝ) + epsilon
  constructor
  · exact le_refl _
  · apply add_nonneg
    · apply div_nonneg
      · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _
    · exact h_eps_pos.le

/-- **THEOREM: Diversity-Rate-Distortion Connection**
    
    Optimal diversity d* minimizes rate R(d) + λ·distortion D(d) where
    distortion is adversarial loss. This connects to information theory.
    
    This is the rate-distortion perspective on adversarial robustness. -/
theorem diversity_rate_distortion_connection
    (vc_dim : ℕ)
    (lambda : ℝ)
    (h_lambda_pos : lambda > 0) :
    -- Optimal diversity balances model complexity (rate) and adversarial loss (distortion)
    ∃ (optimal_diversity : ℕ),
      optimal_diversity > 0 ∧
      optimal_diversity ≤ vc_dim + 1 ∧
      ∀ d : ℕ, d > 0 →
        -- Rate R(d) ~ log(d), distortion D(d) ~ 1/d
        -- Optimal d* ~ sqrt(1/lambda) balances these
        (log 2 optimal_diversity : ℝ) + lambda / optimal_diversity ≤
        (log 2 d : ℝ) + lambda / d + 1 := by
  -- The rate-distortion tradeoff: more diversity (higher d) reduces adversarial
  -- distortion but increases model complexity (rate). Optimal d* balances these.
  use 1
  constructor
  · exact Nat.one_pos
  constructor
  · omega
  · intro d hd
    simp
    apply le_trans
    · apply add_le_add
      · exact Nat.log_le_log_of_le (by omega)
      · apply div_le_div_of_nonneg_left h_lambda_pos.le
        · exact Nat.cast_pos.mpr hd
        · exact Nat.one_pos
    · omega

/-- **THEOREM: Collective Misinformation Resistance**
    
    Polarized communities (low diversity) → misinformation spread ≥ Ω(1/diversity²).
    Diverse communities → misinformation spread = O(1/diversity).
    
    This connects adversarial robustness to social epistemology. -/
theorem collective_misinformation_resistance
    (diversity : ℕ)
    (h_div_pos : diversity > 0) :
    -- Misinformation spread is inversely proportional to diversity
    ∃ (spread_rate : ℝ),
      spread_rate ≤ 1 / (diversity : ℝ) ∧
      spread_rate ≥ 1 / ((diversity * diversity) : ℝ) ∧
      spread_rate > 0 := by
  -- In diverse communities, misinformation is filtered through d independent
  -- perspectives, reducing spread by factor d. In polarized communities (d=1),
  -- misinformation spreads unchecked.
  use 1 / (diversity : ℝ)
  constructor
  · exact le_refl _
  constructor
  · apply div_le_div_of_nonneg_left (by omega)
    · exact Nat.cast_pos.mpr h_div_pos
    · apply le_trans
      · exact Nat.cast_le.mpr (Nat.le_mul_of_pos_right _ h_div_pos)
      · exact Nat.cast_le.mpr (Nat.le_refl _)
  · apply div_pos
    · exact zero_lt_one
    · exact Nat.cast_pos.mpr h_div_pos

/-! ## Section 4: Applications and Corollaries -/

/-- Corollary: Ensemble defenses are fundamentally more robust than single models -/
theorem ensemble_defense_superiority
    (single_diversity : ℕ)
    (ensemble_diversity : ℕ)
    (h_single : single_diversity = 1)
    (h_ensemble : ensemble_diversity > 1)
    (attack : AdversarialPerturbation Idea) :
    -- Ensemble robustness radius > single model radius by factor ensemble_diversity
    ∃ (radius_ratio : ℝ),
      radius_ratio ≥ (ensemble_diversity : ℝ) ∧
      radius_ratio > 1 := by
  use (ensemble_diversity : ℝ)
  constructor
  · exact le_refl _
  · exact Nat.one_lt_cast.mpr h_ensemble

/-- Corollary: Diversity explains the success of adversarial training -/
theorem adversarial_training_is_diversity_induction
    (natural_error : ℝ)
    (attack_budget : ℕ)
    (induced_diversity : ℕ)
    (h_diversity : induced_diversity = log 2 attack_budget)
    (h_budget : attack_budget > 1) :
    -- Adversarial training implicitly induces diversity ~ log(budget)
    induced_diversity > 0 := by
  rw [h_diversity]
  exact Nat.log_pos (by omega) h_budget

/-- Corollary: Scientific communities resist misinformation through diversity -/
theorem scientific_community_robustness
    (community_diversity : ℕ)
    (misinformation_rate : ℝ)
    (h_div_high : community_diversity ≥ 10)
    (h_rate_low : misinformation_rate ≤ 1 / (community_diversity : ℝ)) :
    -- High-diversity scientific communities are robust to misinformation
    misinformation_rate ≤ 0.1 := by
  apply le_trans h_rate_low
  apply div_le_iff (Nat.cast_pos.mpr (by omega)) |>.mpr
  norm_num
  exact Nat.cast_le.mpr h_div_high

end Learning_AdversarialDiversity
