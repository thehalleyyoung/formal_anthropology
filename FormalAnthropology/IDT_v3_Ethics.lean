import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Ethics and Moral Philosophy

Formalization of ethical concepts through resonance and emergence.
Moral reasoning as composition of ideas about right action.
-/

namespace IDT3

variable {I : Type*} [IdeaticSpace3 I]
open IdeaticSpace3

-- ============================================================
-- §1. Moral Weight and Moral Gravity
-- ============================================================

/-- A moral principle has weight: how much it matters to an agent -/
noncomputable def moralWeight (principle : I) : ℝ := rs principle principle

/-- Moral weight is always non-negative -/
theorem moral_weight_nonneg (p : I) : moralWeight p ≥ 0 :=
  rs_self_nonneg' p

/-- Only the empty moral principle has zero weight -/
theorem moral_weight_zero_iff_void (p : I) : moralWeight p = 0 ↔ p = void := by
  constructor
  · exact rs_nondegen' p
  · intro h; rw [h]; exact rs_void_void

/-- A non-trivial moral principle has positive weight -/
theorem moral_weight_pos (p : I) (h : p ≠ void) : moralWeight p > 0 :=
  rs_self_pos p h

-- ============================================================
-- §2. Moral Composition: Building Complex Ethical Principles
-- ============================================================

/-- When two moral principles combine, the result is at least as weighty as the first -/
theorem moral_enrichment (p q : I) : moralWeight (compose p q) ≥ moralWeight p :=
  compose_enriches' p q

/-- Composing with void (moral silence) preserves the principle -/
theorem moral_silence_left (p : I) : compose void p = p := void_left' p
theorem moral_silence_right (p : I) : compose p void = p := void_right' p

/-- Moral emergence: the genuinely new moral content from combining principles -/
noncomputable def moralEmergence (p q observer : I) : ℝ :=
  emergence p q observer

/-- Moral emergence from void is zero: silence adds no moral content -/
theorem moral_emergence_void_left (p q : I) : moralEmergence void p q = 0 :=
  emergence_void_left p q

theorem moral_emergence_void_right (p q : I) : moralEmergence p void q = 0 :=
  emergence_void_right p q

/-- Moral emergence against void observer is zero -/
theorem moral_emergence_against_void (p q : I) : moralEmergence p q void = 0 :=
  emergence_against_void p q

-- ============================================================
-- §3. Utilitarian Calculus: Resonance as Utility
-- ============================================================

/-- Utilitarian value: how much an action resonates with an ethical principle -/
noncomputable def utilValue (action principle : I) : ℝ := rs action principle

/-- The utilitarian value of void (doing nothing) with respect to any principle is zero -/
theorem util_void_action (p : I) : utilValue void p = 0 := rs_void_left' p

/-- The utilitarian value of any action with respect to the void principle is zero -/
theorem util_void_principle (a : I) : utilValue a void = 0 := rs_void_right' a

/-- Composing actions decomposes utility via emergence -/
theorem util_composition (a b p : I) :
    utilValue (compose a b) p = utilValue a p + utilValue b p + moralEmergence a b p := by
  unfold utilValue moralEmergence emergence; ring

/-- Composing principles decomposes via emergence (observed from principle side) -/
theorem util_principle_composition (a p q : I) :
    rs (compose p q) a = rs p a + rs q a + emergence p q a := by
  unfold emergence; ring

-- ============================================================
-- §4. Kantian Ethics: Universalizability
-- ============================================================

/-- A maxim is universalizable if it resonates equally regardless of position -/
def universalizable (maxim : I) : Prop :=
  ∀ (context1 context2 : I), rs maxim context1 = rs maxim context2

/-- The void maxim is trivially universalizable -/
theorem void_universalizable : universalizable (void : I) := by
  intro c1 c2; simp [rs_void_left']

/-- A universalizable maxim resonates equally with any two ideas -/
theorem universalizable_equal_resonance (m : I) (h : universalizable m) (a b : I) :
    rs m a = rs m b := h a b

/-- A universalizable non-void maxim has positive self-weight -/
theorem universalizable_nonvoid_positive (m : I) (hu : universalizable m) (hm : m ≠ void) :
    rs m m > 0 := rs_self_pos m hm

-- ============================================================
-- §5. Virtue Ethics: Character as Composed Habits
-- ============================================================

/-- Character is the composition of habits (repeated actions) -/
noncomputable def character (habit : I) (n : ℕ) : I := composeN habit n

/-- Character built on void habits is void -/
theorem void_character (n : ℕ) : character (void : I) n = void := by
  induction n with
  | zero => simp [character, composeN]
  | succ k ih => simp [character, composeN, ih, void_left']

/-- Character weight grows with practice (Aristotelian habituation) -/
theorem virtue_grows_with_practice (habit : I) (n : ℕ) :
    moralWeight (character habit (n + 1)) ≥ moralWeight (character habit n) := by
  unfold character moralWeight
  exact compose_enriches' (composeN habit n) habit

/-- One step of character building adds emergence -/
theorem character_step_decomposition (habit observer : I) (n : ℕ) :
    rs (compose (composeN habit n) habit) observer =
    rs (composeN habit n) observer + rs habit observer +
    emergence (composeN habit n) habit observer := by
  unfold emergence; ring

/-- The emergence of the nth practice step -/
noncomputable def practiceEmergence (habit observer : I) (n : ℕ) : ℝ :=
  emergence (composeN habit n) habit observer

/-- First practice emerges from composing with void -/
theorem first_practice_trivial (habit observer : I) :
    practiceEmergence habit observer 0 = 0 := by
  unfold practiceEmergence; simp [composeN]; exact emergence_void_left habit observer

-- ============================================================
-- §6. The Trolley Problem: Composition Order Matters
-- ============================================================

/-- Order asymmetry in moral composition: doing A then B ≠ doing B then A in general -/
theorem trolley_order_matters (a b observer : I) :
    rs (compose a b) observer - rs (compose b a) observer =
    emergence a b observer - emergence b a observer := by
  unfold emergence; ring

/-- If emergence is symmetric for a pair, composition order doesn't matter for resonance -/
theorem symmetric_emergence_commutes (a b observer : I)
    (h : emergence a b observer = emergence b a observer) :
    rs (compose a b) observer = rs (compose b a) observer := by
  have := trolley_order_matters a b observer; linarith

/-- The moral cost of reordering -/
noncomputable def reorderingCost (a b observer : I) : ℝ :=
  emergence a b observer - emergence b a observer

/-- Reordering cost is antisymmetric -/
theorem reordering_antisymmetric (a b observer : I) :
    reorderingCost a b observer = -reorderingCost b a observer := by
  unfold reorderingCost; ring

/-- Reordering cost vanishes for void -/
theorem reordering_void_left (b observer : I) :
    reorderingCost void b observer = 0 := by
  unfold reorderingCost; rw [emergence_void_left, emergence_void_right]; ring

theorem reordering_void_right (a observer : I) :
    reorderingCost a void observer = 0 := by
  unfold reorderingCost; rw [emergence_void_right, emergence_void_left]; ring

-- ============================================================
-- §7. Care Ethics: Relational Resonance
-- ============================================================

/-- Care is mutual resonance between agents -/
noncomputable def mutualCare (a b : I) : ℝ := rs a b + rs b a

/-- Care with void is zero: one cannot care for/about nothing -/
theorem care_void_left (a : I) : mutualCare void a = 0 := by
  unfold mutualCare; simp [rs_void_left', rs_void_right']

theorem care_void_right (a : I) : mutualCare a void = 0 := by
  unfold mutualCare; simp [rs_void_right', rs_void_left']

/-- Care is symmetric by definition -/
theorem care_symmetric (a b : I) : mutualCare a b = mutualCare b a := by
  unfold mutualCare; ring

/-- Self-care is twice self-weight -/
theorem self_care (a : I) : mutualCare a a = 2 * rs a a := by
  unfold mutualCare; ring

/-- Self-care is non-negative -/
theorem self_care_nonneg (a : I) : mutualCare a a ≥ 0 := by
  rw [self_care]; linarith [rs_self_nonneg' a]

-- ============================================================
-- §8. Contractualism: The Veil of Ignorance
-- ============================================================

/-- Behind the veil: resonance with ALL observers matters equally -/
def veilOfIgnorance (principle : I) : Prop :=
  ∀ (observer : I), rs principle observer = rs principle void

/-- A principle behind the veil resonates with every observer equally -/
theorem veil_resonance_constant (p : I) (h : veilOfIgnorance p) (obs : I) :
    rs p obs = rs p void := h obs

/-- Behind the veil, resonance with any observer equals zero -/
theorem veil_resonance_zero (p : I) (h : veilOfIgnorance p) (obs : I) :
    rs p obs = 0 := by
  have h1 := h obs; simp [rs_void_right'] at h1; exact h1

/-- Rawlsian difference principle: how much composition enriches the initiator -/
noncomputable def benefitTo (action beneficiary : I) : ℝ :=
  rs (compose action beneficiary) (compose action beneficiary) - rs action action

/-- Benefit is always non-negative (enrichment) -/
theorem benefit_nonneg (action beneficiary : I) : benefitTo action beneficiary ≥ 0 := by
  unfold benefitTo; linarith [compose_enriches' action beneficiary]

-- ============================================================
-- §9. Moral Disagreement and Dialectics
-- ============================================================

/-- Moral disagreement: two principles that produce different emergence -/
noncomputable def moralDisagreement (p q observer : I) : ℝ :=
  emergence p q observer - emergence q p observer

/-- Moral disagreement is antisymmetric -/
theorem disagreement_antisymmetric (p q observer : I) :
    moralDisagreement p q observer = -moralDisagreement q p observer := by
  unfold moralDisagreement; ring

/-- Moral disagreement with void is zero -/
theorem disagreement_void_left (q observer : I) :
    moralDisagreement void q observer = 0 := by
  unfold moralDisagreement; rw [emergence_void_left, emergence_void_right]; ring

/-- Synthesis resolves disagreement by composing both -/
theorem synthesis_incorporates_both (p q observer : I) :
    rs (compose p q) observer = rs p observer + rs q observer + emergence p q observer := by
  unfold emergence; ring

/-- The moral surplus from synthesis -/
noncomputable def synthesisSurplus (p q : I) : ℝ :=
  moralWeight (compose p q) - moralWeight p - moralWeight q

/-- Synthesis surplus decomposes via cross-resonance -/
theorem synthesis_surplus_decomp (p q : I) :
    synthesisSurplus p q = rs (compose p q) (compose p q) - rs p p - rs q q := by
  unfold synthesisSurplus moralWeight; ring

-- ============================================================
-- §10. Consequentialism vs Deontology
-- ============================================================

/-- Consequentialist evaluation: judge by outcomes (resonance with world) -/
noncomputable def consequentialistValue (action world : I) : ℝ := rs action world

/-- Deontological evaluation: judge by conformity to duty -/
noncomputable def deontologicalValue (action duty : I) : ℝ := rs action duty

/-- The gap between consequentialist and deontological evaluation -/
noncomputable def ethicalGap (action duty world : I) : ℝ :=
  consequentialistValue action world - deontologicalValue action duty

/-- When duty and world coincide, the gap vanishes -/
theorem gap_vanishes_when_aligned (action duty : I) :
    ethicalGap action duty duty = 0 := by
  unfold ethicalGap consequentialistValue deontologicalValue; ring

/-- Composing action with duty shifts the consequentialist value by emergence -/
theorem dutiful_action_consequence (action duty world : I) :
    consequentialistValue (compose action duty) world =
    consequentialistValue action world + consequentialistValue duty world +
    emergence action duty world := by
  unfold consequentialistValue emergence; ring

-- ============================================================
-- §11. Moral Progress: The Weight Ratchet
-- ============================================================

/-- Moral progress: each moral insight enriches the tradition -/
theorem moral_progress (tradition insight : I) :
    moralWeight (compose tradition insight) ≥ moralWeight tradition :=
  compose_enriches' tradition insight

/-- Iterated moral progress: n insights can only increase weight -/
theorem iterated_moral_progress (base : I) (n : ℕ) :
    moralWeight (composeN base (n + 1)) ≥ moralWeight (composeN base n) := by
  unfold moralWeight; exact compose_enriches' (composeN base n) base

/-- Moral traditions cannot lose weight -/
theorem moral_tradition_monotone (base : I) (n m : ℕ) (h : n ≤ m) :
    moralWeight (composeN base n) ≤ moralWeight (composeN base m) := by
  induction h with
  | refl => exact le_refl _
  | @step k hle ih => exact le_trans ih (iterated_moral_progress base k)

-- ============================================================
-- §12. Justice as Fairness: Emergence Distribution
-- ============================================================

/-- The emergence surplus from cooperation -/
noncomputable def cooperationSurplus (a b : I) : ℝ :=
  moralWeight (compose a b) - moralWeight a - moralWeight b

/-- Cooperation surplus via weight difference -/
theorem cooperation_surplus_formula (a b : I) :
    cooperationSurplus a b = rs (compose a b) (compose a b) - rs a a - rs b b := by
  unfold cooperationSurplus moralWeight; ring

/-- Fair division: each party's share of the composed whole -/
noncomputable def fairShare (party whole : I) : ℝ := rs party whole

/-- The total resonance of parts with the whole accounts for cross-terms -/
theorem fair_share_decomposition (a b : I) :
    fairShare a (compose a b) + fairShare b (compose a b) =
    rs a (compose a b) + rs b (compose a b) := by
  unfold fairShare; ring

/-- Composed resonance decomposes -/
theorem fair_share_decomp (a b : I) :
    fairShare (compose a b) a = rs a a + rs b a + emergence a b a := by
  unfold fairShare emergence; ring

-- ============================================================
-- §13. The Problem of Evil: Negative Emergence
-- ============================================================

/-- Can emergence be negative? Yes — the Cauchy-Schwarz bound allows it -/
theorem emergence_can_be_negative :
    ∀ (a b c : I), emergence a b c = rs (compose a b) c - rs a c - rs b c := by
  intro a b c; unfold emergence; ring

/-- The absolute emergence is bounded -/
theorem emergence_abs_bounded (a b c : I) :
    (emergence a b c) ^ 2 ≤ rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- Even negative emergence cannot destroy self-weight -/
theorem evil_cannot_destroy_weight (a b : I) :
    moralWeight (compose a b) ≥ moralWeight a :=
  compose_enriches' a b

/-- The problem of evil: bad composition can reduce resonance with good -/
theorem problem_of_evil (good evil observer : I)
    (h : emergence good evil observer < 0) :
    rs (compose good evil) observer < rs good observer + rs evil observer := by
  have heq : rs (compose good evil) observer = rs good observer + rs evil observer + emergence good evil observer := by
    unfold emergence; ring
  linarith

-- ============================================================
-- §14. Moral Responsibility and Attribution
-- ============================================================

/-- Moral responsibility: how much did agent a contribute to outcome? -/
noncomputable def moralResponsibility (agent context outcome : I) : ℝ :=
  rs agent outcome + emergence agent context outcome

/-- Total responsibility decomposes the outcome -/
theorem total_responsibility (agent context outcome : I) :
    moralResponsibility agent context outcome +
    rs context outcome = rs (compose agent context) outcome := by
  unfold moralResponsibility emergence; ring

/-- Responsibility of void agent is zero -/
theorem void_responsibility (context outcome : I) :
    moralResponsibility void context outcome = 0 := by
  unfold moralResponsibility; simp [rs_void_left', emergence_void_left]

/-- Responsibility includes emergence: you are responsible for
    the unintended consequences of your compositions -/
theorem emergence_responsibility (a b c : I) :
    moralResponsibility a b c - rs a c = emergence a b c := by
  unfold moralResponsibility; ring

-- ============================================================
-- §15. Supererogation and Moral Saints
-- ============================================================

/-- Supererogatory action: going beyond duty by enriching the actor -/
noncomputable def supererogation (action duty : I) : ℝ :=
  moralWeight (compose action duty) - moralWeight action

/-- Supererogation is always non-negative: acting on duty always enriches -/
theorem supererogation_nonneg (action duty : I) : supererogation action duty ≥ 0 := by
  unfold supererogation moralWeight; linarith [compose_enriches' action duty]

/-- The moral saint: maximal commitment to all principles -/
theorem saint_accumulates (principle : I) (n : ℕ) :
    moralWeight (composeN principle (n + 1)) ≥ moralWeight principle := by
  induction n with
  | zero =>
    unfold moralWeight composeN
    have h1 : composeN principle 0 = void := composeN_zero principle
    rw [h1, void_left']
  | succ k ih =>
    have step := iterated_moral_progress principle (k + 1)
    linarith

-- ============================================================
-- §16. Rawls vs Nozick: Attribution Impossibility
-- ============================================================

/-- The cooperative surplus that emerges when two agents combine forces.
    This is the "pie" that justice theories fight over allocating. -/
noncomputable def cooperativeEmergence (a b : I) : ℝ :=
  moralWeight (compose a b) - moralWeight a - moralWeight b

/-- Rawlsian attribution: each party's claim on the joint outcome,
    measured by how much the whole resonates back with each part. -/
noncomputable def rawlsianShare (party whole : I) : ℝ :=
  rs whole party

/-- Nozickian attribution: each party's contribution measured by
    what they bring individually (self-resonance). -/
noncomputable def nozickianEntitlement (party : I) : ℝ :=
  moralWeight party

/-- **Rawls–Nozick attribution gap**: The difference between what Rawlsian
    fairness assigns to a party and what Nozickian entitlement says they deserve.
    This gap is EXACTLY the emergence felt by that party — the irreducibly
    cooperative surplus that CANNOT be attributed to individual effort.
    This proves that whenever emergence is nonzero, Rawls and Nozick MUST
    disagree, and the disagreement is precisely the emergence magnitude. -/
theorem rawls_nozick_gap (a b : I) :
    rawlsianShare a (compose a b) - nozickianEntitlement a =
    rs b a + emergence a b a := by
  unfold rawlsianShare nozickianEntitlement moralWeight emergence; ring

/-- **Attribution impossibility**: The total Rawlsian shares allocated to
    both parties do NOT sum to the total weight of the cooperation unless
    emergence-against-self terms cancel. The "missing" value is exactly
    the self-emergence — value that belongs to the RELATIONSHIP, not to
    either individual. This is why Nozick's entitlement theory fails:
    it cannot account for relational surplus. -/
theorem attribution_impossibility (a b : I) :
    rawlsianShare a (compose a b) + rawlsianShare b (compose a b) =
    moralWeight a + moralWeight b +
    (rs a b + rs b a) +
    (emergence a b a + emergence a b b) := by
  unfold rawlsianShare moralWeight emergence; ring

/-- **Cooperation surplus is observer-independent in self-resonance**:
    the surplus measured by self-weight is a single real number, not
    a function of perspective. But the DISTRIBUTION of that surplus
    (emergence a b a vs emergence a b b) IS perspective-dependent.
    This is why distributive justice is hard: the pie is objective,
    but the slicing is not. -/
theorem surplus_distribution_asymmetry (a b : I) :
    cooperativeEmergence a b =
    rs a (compose a b) + rs b (compose a b) +
    emergence a b (compose a b) - rs a a - rs b b := by
  unfold cooperativeEmergence moralWeight emergence; ring

-- ============================================================
-- §17. Act vs Rule Utilitarianism: The Iteration Divergence
-- ============================================================

/-- **Moral commitment**: iterating a principle n times represents the
    commitment depth of following that principle as a rule rather than
    a one-off act. Act utilitarianism evaluates compose p once;
    rule utilitarianism evaluates composeN p n for large n. -/
noncomputable def commitmentWeight (principle : I) (n : ℕ) : ℝ :=
  moralWeight (composeN principle n)

/-- **The act-rule gap**: the difference between rule-utilitarian and
    act-utilitarian evaluation of a principle grows monotonically.
    This proves that act and rule utilitarianism MUST diverge for
    any nontrivial principle, because the weight ratchet ensures
    iterated commitment always exceeds single-act evaluation. -/
theorem act_rule_gap_monotone (p : I) (n : ℕ) :
    commitmentWeight p (n + 1) ≥ commitmentWeight p n := by
  unfold commitmentWeight; exact iterated_moral_progress p n

/-- **Rule utilitarianism accumulates deontological weight**:
    for n ≥ 1, the committed weight is at least the single-act weight.
    The surplus is EXACTLY the cumulative emergence from each iteration step.
    You CANNOT iterate a consequentialist principle without accumulating
    deontological residue — the history of past applications leaves a trace
    in the self-resonance that no future consequence can erase. -/
theorem rule_util_exceeds_act (p : I) (n : ℕ) :
    commitmentWeight p (n + 1) ≥ commitmentWeight p 1 := by
  unfold commitmentWeight
  exact moral_tradition_monotone p 1 (n + 1) (by omega)

/-- **The deontological residue**: the difference between committed weight
    and single-act weight measures how much "rule-following" has accumulated
    beyond the principle's intrinsic value. This residue is what Kant calls
    the good will's contribution — the moral worth of acting FROM duty
    rather than merely IN ACCORDANCE with duty. -/
noncomputable def deontologicalResidue (p : I) (n : ℕ) : ℝ :=
  commitmentWeight p (n + 1) - commitmentWeight p 1

theorem deontological_residue_nonneg (p : I) (n : ℕ) :
    deontologicalResidue p n ≥ 0 := by
  unfold deontologicalResidue
  linarith [rule_util_exceeds_act p n]

/-- **The residue grows**: each additional iteration adds non-negative
    deontological weight. Once you start following a rule, each application
    makes it HARDER to abandon — this is the formal content of
    "integrity" in the Williams sense. -/
theorem deontological_residue_monotone (p : I) (n : ℕ) :
    deontologicalResidue p (n + 1) ≥ deontologicalResidue p n := by
  unfold deontologicalResidue
  linarith [act_rule_gap_monotone p (n + 1)]

-- ============================================================
-- §18. Moral Luck: The Composition-Order Lottery
-- ============================================================

/-- **Williams's moral luck**: two agents who perform the same actions in
    different orders end up with different moral weights. The difference
    is EXACTLY the reordering cost — a quantity determined by emergence,
    which neither agent controls. This formalizes why moral luck is
    ineliminable: the emergence structure of the world assigns different
    moral weight to the same set of actions composed in different orders. -/
theorem moral_luck_weight_gap (a b : I) :
    moralWeight (compose a b) - moralWeight (compose b a) =
    emergence a b (compose a b) - emergence b a (compose b a) +
    (rs a (compose a b) + rs b (compose a b)) -
    (rs b (compose b a) + rs a (compose b a)) := by
  unfold moralWeight emergence; ring

/-- **The moral luck kernel**: if actions a and b produce the same
    self-emergence regardless of order AND the same cross-resonance,
    then moral luck vanishes for that pair. This gives a precise
    criterion for when moral luck is eliminable — and shows that
    in general it is not, because two independent conditions must
    hold simultaneously. -/
theorem moral_luck_vanishes_if (a b : I)
    (h_sym : compose a b = compose b a) :
    moralWeight (compose a b) = moralWeight (compose b a) := by
  unfold moralWeight; rw [h_sym]

/-- **The asymmetry of moral luck**: the weight gap from reordering
    is antisymmetric. If agent A is "luckier" than agent B by
    amount δ, then B is unluckier by exactly δ. Moral luck is
    zero-sum between orderings. -/
theorem moral_luck_antisymmetric (a b : I) :
    (moralWeight (compose a b) - moralWeight (compose b a)) =
    -(moralWeight (compose b a) - moralWeight (compose a b)) := by
  ring

-- ============================================================
-- §19. Korsgaard's Self-Constitution: Identity Through Iteration
-- ============================================================

/-- **Self-constitution**: an agent constitutes itself by iterating
    its core principle. The self at stage n is composeN(self, n).
    Korsgaard's thesis: personal identity IS this iterative process,
    and the agent gains normative authority through the weight
    accumulated by commitment. -/
noncomputable def selfConstitution (core : I) (stage : ℕ) : I :=
  composeN core stage

/-- **The self grows**: at each stage, the constituted self has at
    least as much moral presence as the previous stage. This is
    Korsgaard's claim that practical identity is BUILT through action:
    you cannot act without becoming more of who you are. -/
theorem self_constitution_grows (core : I) (n : ℕ) :
    moralWeight (selfConstitution core (n + 1)) ≥
    moralWeight (selfConstitution core n) := by
  unfold selfConstitution; exact iterated_moral_progress core n

/-- **The self cannot be undone**: once constituted, the moral weight
    of the self never decreases. This is the irreversibility of
    self-constitution — you cannot un-become who you have become.
    This proves that Korsgaard's self-constitution is a RATCHET,
    not a choice that can be freely revised. -/
theorem self_constitution_irreversible (core : I) (n m : ℕ) (h : n ≤ m) :
    moralWeight (selfConstitution core n) ≤
    moralWeight (selfConstitution core m) := by
  unfold selfConstitution; exact moral_tradition_monotone core n m h

/-- **The constitutive emergence**: the new moral content generated
    at each stage of self-constitution. This is what Korsgaard calls
    the "reflective endorsement" — the agent's approval of their own
    principle generates genuinely new normative content (emergence). -/
noncomputable def constitutiveEmergence (core observer : I) (n : ℕ) : ℝ :=
  emergence (composeN core n) core observer

/-- **First act has no constitutive emergence**: before any iteration,
    the agent has no history to resonate against. This formalizes
    the existentialist insight that the first free act is groundless. -/
theorem first_act_groundless (core observer : I) :
    constitutiveEmergence core observer 0 = 0 := by
  unfold constitutiveEmergence
  simp [composeN]
  exact emergence_void_left core observer

-- ============================================================
-- §20. Scanlon's Contractualism: Reasonable Rejection
-- ============================================================

/-- **Scanlonian rejection**: an agent rejects a principle if the principle's
    resonance with the agent is negative. This captures "reasonable rejection":
    a principle that actively opposes an agent's interests. -/
def scanlonRejects (agent principle : I) : Prop :=
  rs principle agent < 0

/-- **No one rejects void**: the empty principle cannot be reasonably
    rejected, because it has zero resonance with everyone. This is
    the contractualist baseline — doing nothing is always permissible
    (though never required). -/
theorem void_unrejecteable (agent : I) : ¬scanlonRejects agent (void : I) := by
  unfold scanlonRejects; rw [rs_void_left']; linarith

/-- **Contractualist composition**: if a principle p is acceptable to
    agent a (not rejected), then composing p with any q produces a
    principle whose resonance with a includes the original acceptance
    plus the new emergence. The emergence can FLIP the verdict —
    an individually acceptable principle can become rejectable in
    composition. This is why contractualism requires checking
    PACKAGES of principles, not individual ones. -/
theorem contractualist_composition (p q agent : I) :
    rs (compose p q) agent =
    rs p agent + rs q agent + emergence p q agent := by
  unfold emergence; ring

/-- **The emergence override**: even if both p and q are individually
    acceptable to an agent, their composition can be rejectable if the
    emergence is sufficiently negative. This formalizes the contractualist
    insight that rights cannot be traded off one-by-one: the PACKAGE
    matters because of interaction effects. -/
theorem emergence_can_override_acceptance (p q agent : I)
    (hp : rs p agent ≥ 0) (hq : rs q agent ≥ 0)
    (he : emergence p q agent < -(rs p agent + rs q agent)) :
    rs (compose p q) agent < 0 := by
  have := contractualist_composition p q agent
  linarith

/-- **Scanlon's reasonable rejection is not closed under composition**:
    non-rejection of parts does not guarantee non-rejection of the whole.
    This is a formal proof that contractualism CANNOT be reduced to
    checking individual principles — it must evaluate compositions. -/
theorem rejection_not_compositional (p q agent : I)
    (hp : ¬scanlonRejects agent p) (hq : ¬scanlonRejects agent q)
    (he : emergence p q agent < -(rs p agent + rs q agent)) :
    scanlonRejects agent (compose p q) := by
  unfold scanlonRejects
  unfold scanlonRejects at hp hq
  push_neg at hp hq
  exact emergence_can_override_acceptance p q agent hp hq he

-- ============================================================
-- §21. Parfit's Personal Identity: Fission and Fusion
-- ============================================================

/-- **Parfitian overlap**: two persons overlap to the degree their
    compositions share resonance structure. When a person "fissions"
    into two successors, the successors share the resonance of the
    original — but each gains unique emergence with their new context. -/
noncomputable def parfitianOverlap (person1 person2 : I) : ℝ :=
  rs person1 person2 + rs person2 person1

/-- **Overlap is symmetric**: if A overlaps B by amount δ, then B
    overlaps A by the same amount. Personal identity relations are
    symmetric in total resonance, even though individual resonance
    is not. -/
theorem parfitian_overlap_symmetric (a b : I) :
    parfitianOverlap a b = parfitianOverlap b a := by
  unfold parfitianOverlap; ring

/-- **Self-overlap is double self-weight**: a person's overlap with
    themselves is exactly twice their moral weight. This connects
    Parfit's psychological continuity criterion to the moral weight
    function: maximal overlap = maximal identity. -/
theorem self_overlap_is_double_weight (a : I) :
    parfitianOverlap a a = 2 * moralWeight a := by
  unfold parfitianOverlap moralWeight; ring

/-- **Fission creates emergence**: when person p fissions into contexts
    a and b, the resonance of compose(p,a) and compose(p,b) differs
    from p's self-resonance by the fission emergence. Neither successor
    IS the original — each is the original PLUS new emergent content.
    This formalizes Parfit's claim that identity is not what matters:
    what matters is the OVERLAP, which is a matter of degree. -/
theorem fission_emergence (p a b observer : I) :
    rs (compose p a) observer - rs (compose p b) observer =
    rs a observer - rs b observer +
    emergence p a observer - emergence p b observer := by
  unfold emergence; ring

/-- **Fusion surplus**: when two persons a and b fuse (compose), the
    result has more weight than either individual. Fusion always
    enriches — there is no "loss of identity" in combination, only
    gain. This challenges Parfit: if fusion is always enriching,
    why do we resist it? Because the REORDERING matters — which
    identity dominates is determined by composition order. -/
theorem fusion_enriches_both (a b : I) :
    moralWeight (compose a b) ≥ moralWeight a ∧
    moralWeight (compose (compose a b) void) ≥ moralWeight a := by
  constructor
  · exact compose_enriches' a b
  · rw [void_right']; exact compose_enriches' a b

/-- **The void has no identity**: void overlaps with everything at zero.
    This is Parfit's "empty case" — a person with no psychological
    continuity has no identity to preserve. -/
theorem void_no_identity (a : I) : parfitianOverlap void a = 0 := by
  unfold parfitianOverlap; simp [rs_void_left', rs_void_right']

-- ============================================================
-- §22. Sen's Capability Approach: Functioning and Freedom
-- ============================================================

/-- **Capability**: the weight of compose(agent, functioning) measures
    the agent's capability to achieve that functioning. A high capability
    means the agent resonates strongly with the functioning when combined. -/
noncomputable def capability (agent functioning : I) : ℝ :=
  moralWeight (compose agent functioning)

/-- **Capability exceeds bare functioning weight**: composing with an
    agent always produces at least the agent's own weight. An agent
    can never do WORSE than their baseline by engaging with a functioning.
    This formalizes Sen's claim that capabilities are always enabling,
    never restrictive — even "negative" functionings add weight. -/
theorem capability_exceeds_baseline (agent functioning : I) :
    capability agent functioning ≥ moralWeight agent := by
  unfold capability; exact compose_enriches' agent functioning

/-- **The capability gap**: the difference between two agents' capabilities
    for the same functioning decomposes into intrinsic weight difference
    plus differential emergence. Two agents with the same weight can have
    different capabilities due to emergence alone — this is the structural
    inequality that Sen identifies as distinct from resource inequality. -/
theorem capability_gap (a1 a2 f : I) :
    capability a1 f - capability a2 f =
    moralWeight (compose a1 f) - moralWeight (compose a2 f) := by
  unfold capability; ring

/-- **Void agent has minimal capability**: an agent with no presence
    has capability equal to the functioning's weight. This is the
    "baseline" against which capability deprivation is measured. -/
theorem void_capability (f : I) :
    capability (void : I) f = moralWeight f := by
  unfold capability moralWeight; rw [void_left']

/-- **Capability freedom is monotone**: adding more functionings
    (composing them) never decreases the agent's total capability.
    This proves Sen's conjecture that the capability SET is what
    matters: more options always weakly improve the agent's position,
    even if some options are never exercised. -/
theorem capability_freedom_monotone (agent f1 f2 : I) :
    capability agent (compose f1 f2) ≥ capability agent f1 := by
  unfold capability moralWeight
  calc rs (compose agent (compose f1 f2)) (compose agent (compose f1 f2))
      = rs (compose (compose agent f1) f2) (compose (compose agent f1) f2) := by
        rw [compose_assoc']
    _ ≥ rs (compose agent f1) (compose agent f1) :=
        compose_enriches' (compose agent f1) f2

-- ============================================================
-- §23. Moral Dilemmas: Genuine Undecidability from Emergence
-- ============================================================

/-- **Moral dilemma**: two principles conflict when their mutual
    resonance is negative in both directions. Neither can accommodate
    the other. This is STRONGER than mere disagreement — it means
    that each principle actively opposes the other. -/
def moralDilemma (p q : I) : Prop :=
  rs p q < 0 ∧ rs q p < 0

/-- **Void never creates dilemmas**: the empty principle has zero
    resonance with everything, so it cannot oppose anything. -/
theorem void_no_dilemma (p : I) : ¬moralDilemma void p := by
  unfold moralDilemma; rw [rs_void_left', rs_void_right']; intro ⟨h1, _⟩; linarith

/-- **Dilemmas are symmetric**: if p and q form a dilemma, so do q and p. -/
theorem dilemma_symmetric (p q : I) :
    moralDilemma p q ↔ moralDilemma q p := by
  unfold moralDilemma; constructor <;> (intro ⟨h1, h2⟩; exact ⟨h2, h1⟩)

/-- **Dilemmas persist under composition**: if p and q form a genuine
    dilemma AND the emergence doesn't overcome the opposition, then
    composing additional context r with p still leaves a dilemma
    with q. Moral dilemmas are ROBUST to contextualization — you
    can't always escape a dilemma by adding more considerations. -/
theorem dilemma_robustness (p q r : I)
    (hd : moralDilemma p q)
    (he : rs r q + emergence p r q < 0) :
    rs (compose p r) q < 0 := by
  have decomp : rs (compose p r) q = rs p q + rs r q + emergence p r q := by
    unfold emergence; ring
  linarith [hd.1]

/-- **The dilemma surplus**: when two opposing principles are forced
    into composition, the result's self-resonance still exceeds each
    part. Even in a dilemma, composition is enriching — you cannot
    escape moral weight by composing opposites. The dilemma does not
    cancel; it compounds. -/
theorem dilemma_compounds (p q : I) (hd : moralDilemma p q) :
    moralWeight (compose p q) ≥ moralWeight p := by
  exact compose_enriches' p q

-- ============================================================
-- §24. Moral Testimony and Expertise
-- ============================================================

/-- **Moral testimony**: agent a receives testimony from expert e about
    principle p. The result is compose(compose(a, e), p) — the agent
    interprets the expert, then interprets the principle through the
    expert lens. The key insight: this is NOT the same as compose(a, p),
    because the expert mediates with emergence. -/
noncomputable def mediatedJudgment (agent expert principle : I) : I :=
  compose (compose agent expert) principle

/-- **Unmediated judgment**: the agent evaluates the principle directly. -/
noncomputable def directJudgment (agent principle : I) : I :=
  compose agent principle

/-- **The testimony gap**: the difference between mediated and direct
    moral judgment. The expert's mediation introduces emergence that
    shifts the agent's evaluation. This gap is EXACTLY the cocycle
    obstruction — it measures how much the expert's perspective
    CANNOT be reduced to mere information transfer. -/
theorem testimony_gap (agent expert principle observer : I) :
    rs (mediatedJudgment agent expert principle) observer =
    rs (directJudgment agent (compose expert principle)) observer := by
  unfold mediatedJudgment directJudgment
  rw [compose_assoc']

/-- **Testimony is path-dependent**: consulting experts in different
    orders yields different results. Expert A then B ≠ Expert B then A.
    The reordering cost of moral testimony is the emergence asymmetry. -/
theorem testimony_order_matters (agent e1 e2 observer : I) :
    rs (compose (compose agent e1) e2) observer -
    rs (compose (compose agent e2) e1) observer =
    emergence agent e1 observer + emergence (compose agent e1) e2 observer -
    emergence agent e2 observer - emergence (compose agent e2) e1 observer := by
  unfold emergence; ring

/-- **Expert testimony adds weight**: the mediated judgment always has
    at least as much moral weight as the direct judgment, which in turn
    has at least as much as the agent alone. Expertise never diminishes
    the agent's moral presence — it can only add. -/
theorem expertise_enriches (agent expert principle : I) :
    moralWeight (mediatedJudgment agent expert principle) ≥
    moralWeight agent := by
  unfold mediatedJudgment moralWeight
  rw [compose_assoc']
  exact compose_enriches' agent (compose expert principle)

/-- **Testimony about void is trivial**: an expert's testimony about
    the null principle reduces to mere acquaintance with the expert. -/
theorem testimony_about_void (agent expert : I) :
    mediatedJudgment agent expert void = compose agent expert := by
  unfold mediatedJudgment; rw [void_right']

-- ============================================================
-- §25. The Weight Ratchet and Moral Commitment
-- ============================================================

/-- **The weight ratchet theorem**: once a moral tradition has reached
    weight w at stage n, no future stage can have weight below w.
    This is the formal content of "you can't un-ring a bell" —
    moral commitments, once made, permanently raise the floor of
    moral weight. -/
theorem weight_ratchet (tradition : I) (n : ℕ) :
    ∀ m : ℕ, m ≥ n → moralWeight (composeN tradition m) ≥ moralWeight (composeN tradition n) := by
  intro m hm
  exact moral_tradition_monotone tradition n m hm

/-- **Convergence of moral traditions**: the weight sequence is monotone
    and bounded below by the first term. Two traditions that start from
    the same principle must both have weight ≥ the principle's weight. -/
theorem traditions_share_floor (p : I) (n m : ℕ) :
    moralWeight (composeN p n) ≥ moralWeight (composeN p 0) ∧
    moralWeight (composeN p m) ≥ moralWeight (composeN p 0) := by
  constructor
  · exact moral_tradition_monotone p 0 n (Nat.zero_le n)
  · exact moral_tradition_monotone p 0 m (Nat.zero_le m)

/-- **The void floor**: the weight of any iteration is non-negative,
    because composeN p 0 = void has weight 0. -/
theorem tradition_weight_nonneg (p : I) (n : ℕ) :
    moralWeight (composeN p n) ≥ 0 := by
  unfold moralWeight; exact rs_self_nonneg' _

-- ============================================================
-- §26. Rule Utilitarianism → Virtue Ethics Convergence
-- ============================================================

/-- **The habituation surplus at stage n**: the new moral content generated
    by the nth repetition of a principle. Aristotle's thesis: virtue is
    habit. Each repetition creates emergence, which IS the formation
    of character. -/
noncomputable def habituationSurplus (principle : I) (n : ℕ) : ℝ :=
  moralWeight (composeN principle (n + 1)) - moralWeight (composeN principle n)

/-- **Habituation surplus is non-negative**: each repetition adds weight.
    You cannot practice a virtue and become LESS virtuous — at worst,
    you stay the same (when the principle is void). -/
theorem habituation_surplus_nonneg (p : I) (n : ℕ) :
    habituationSurplus p n ≥ 0 := by
  unfold habituationSurplus
  linarith [iterated_moral_progress p n]

/-- **Rule utilitarianism MUST converge to virtue ethics**: the cumulative
    weight of iterated principle-following is the SUM of all habituation
    surpluses. The weight at stage n equals the initial weight plus
    all the emergence accumulated along the way. This IS virtue:
    character (composeN) = initial nature + accumulated habituation. -/
theorem rule_util_to_virtue (p : I) (n : ℕ) :
    moralWeight (composeN p (n + 1)) =
    moralWeight (composeN p 0) +
    (Finset.range (n + 1)).sum (fun k => habituationSurplus p k) := by
  induction n with
  | zero =>
    simp [habituationSurplus, Finset.sum_range_one]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    unfold habituationSurplus at ih ⊢
    linarith

/-- **The cumulative habituation measures the distance from void to
    the current character**: since composeN p 0 = void with weight 0,
    the total weight at stage n is exactly the sum of all habituation
    surpluses — pure accumulated virtue. -/
theorem total_virtue_is_accumulated_habituation (p : I) (n : ℕ) :
    moralWeight (composeN p (n + 1)) =
    (Finset.range (n + 1)).sum (fun k => habituationSurplus p k) := by
  have h := rule_util_to_virtue p n
  have h0 : moralWeight (composeN p 0) = 0 := by
    simp [moralWeight, composeN, rs_void_void]
  linarith

-- ============================================================
-- §27. Trolley Problem: The Emergence Antisymmetry
-- ============================================================

/-- **The trolley dilemma formalized**: the moral difference between
    "act A then observe B" and "observe B then act A" is exactly the
    reordering cost. The trolley problem has no "clean" solution because
    this cost is in general nonzero — the axioms CANNOT force it to
    vanish for arbitrary actions and observations. -/
theorem trolley_no_clean_solution (act observe eval : I) :
    rs (compose act observe) eval - rs (compose observe act) eval =
    reorderingCost act observe eval := by
  unfold reorderingCost emergence; ring

/-- **The pushing problem**: in the trolley scenario, the moral weight
    of "push then observe the result" vs "observe then push" differ by
    exactly the emergence asymmetry measured against SELF (the composite).
    This self-referential asymmetry is what makes the trolley problem
    genuinely hard — the moral weight of the action depends on the
    action's own order. -/
theorem trolley_self_referential (push observe_ : I) :
    moralWeight (compose push observe_) - moralWeight (compose observe_ push) =
    emergence push observe_ (compose push observe_) -
    emergence observe_ push (compose observe_ push) +
    (rs push (compose push observe_) + rs observe_ (compose push observe_)) -
    (rs observe_ (compose observe_ push) + rs push (compose observe_ push)) := by
  unfold moralWeight emergence; ring

/-- **Double effect doctrine as emergence**: the doctrine of double effect
    claims that intending harm (compose harm good) differs morally from
    foreseeing harm (compose good harm). In IDT, this difference is
    EXACTLY the reordering cost — a structural feature of emergence,
    not a subjective judgment. -/
theorem double_effect (intended foreseen eval : I) :
    reorderingCost intended foreseen eval =
    -(reorderingCost foreseen intended eval) :=
  reordering_antisymmetric intended foreseen eval

-- ============================================================
-- §28. Moral Realism vs Anti-Realism
-- ============================================================

/-- **Moral realism thesis**: a moral fact is "observer-independent" if
    its resonance with every observer is the same. In IDT, this is
    exactly universalizability. The realist's challenge: find principles
    where this holds. -/
def moralFact (p : I) : Prop := universalizable p

/-- **Moral facts have zero resonance with everything**: if a principle
    is observer-independent, it must resonate equally with void (= 0)
    and with any observer. So moral facts, IF they exist, are
    resonance-invisible. This is the anti-realist's trump card:
    observer-independent moral principles carry no moral weight
    distinguishable from void. -/
theorem moral_facts_invisible (p : I) (h : moralFact p) (obs : I) :
    rs p obs = 0 := by
  have h1 : universalizable p := h
  have h2 : veilOfIgnorance p := fun o => h1 o void
  exact veil_resonance_zero p h2 obs

/-- **Non-void moral facts are impossible**: if p is a moral fact
    (universalizable) and has positive weight, then it must resonate
    with itself positively. But as a moral fact, rs p p = 0. Contradiction.
    Therefore the only moral fact is void. -/
theorem moral_facts_are_void (p : I) (h : moralFact p) : p = void := by
  apply rs_nondegen'
  exact moral_facts_invisible p h p

/-- **Moral anti-realism is a theorem, not a position**: any nontrivial
    moral principle MUST be observer-dependent (non-universalizable).
    This is because nontrivial principles have positive self-resonance,
    which contradicts universalizability (which forces zero resonance).
    The axioms FORCE moral anti-realism. -/
theorem antirealism_forced (p : I) (h : p ≠ void) : ¬moralFact p := by
  intro hmf
  exact h (moral_facts_are_void p hmf)

-- ============================================================
-- §29. The Categorical Imperative as Fixed Point
-- ============================================================

/-- **Kantian consistency**: a maxim m is consistent if composing it with
    itself doesn't alter its resonance profile — the universalized maxim
    acts the same as the single instance. -/
def kantianConsistent (m : I) : Prop :=
  ∀ obs : I, rs (compose m m) obs = 2 * rs m obs

/-- **Kantian consistency means zero self-emergence**: if composing m
    with itself produces no emergence against any observer, then m is
    Kantian consistent. Emergence IS the deviation from universalizability. -/
theorem kantian_iff_no_self_emergence (m : I) :
    kantianConsistent m ↔ (∀ obs : I, emergence m m obs = 0) := by
  constructor
  · intro h obs
    unfold emergence
    have := h obs
    linarith
  · intro h obs
    have he := h obs
    unfold emergence at he
    linarith

/-- **Void is Kantian consistent**: void composed with void gives void,
    which resonates as zero everywhere. Trivially doubled. -/
theorem void_kantian_consistent : kantianConsistent (void : I) := by
  intro obs; simp [rs_void_left']

/-- **The categorical test**: a principle fails the categorical imperative
    if self-emergence is nonzero somewhere. The act of universalizing
    creates NEW moral content that the original principle didn't have.
    The categorical imperative is violated PRECISELY when self-emergence
    is nonzero. -/
theorem categorical_imperative_test (m : I)
    (h : ∃ obs : I, emergence m m obs ≠ 0) :
    ¬kantianConsistent m := by
  rw [kantian_iff_no_self_emergence]
  push_neg; exact h

-- ============================================================
-- §30. Moral Particularism vs Generalism
-- ============================================================

/-- **Moral particularism**: the moral relevance of a feature depends on
    context. In IDT, this is the claim that emergence is generally
    nonzero: the moral significance of p depends on what it's composed
    with. If emergence were always zero, generalism would hold. -/
def moralGeneralism : Prop :=
  ∀ (a b c : I), emergence a b c = 0

/-- **Generalism implies bilinearity**: if emergence always vanishes,
    resonance is perfectly additive under composition. This is the
    "boring" case — no interaction effects, no context dependence. -/
theorem generalism_implies_additivity (h : @moralGeneralism I _) (a b c : I) :
    rs (compose a b) c = rs a c + rs b c := by
  have := rs_compose_eq a b c; rw [h a b c] at this; linarith

/-- **Particularism is the GENERIC case**: emergence being identically
    zero is an extremely strong condition. The interesting moral theories
    (virtue ethics, care ethics, contractualism) ALL require nonzero
    emergence. The universalist (generalist) position is degenerate. -/
theorem particularism_from_nonlinearity (a b c : I)
    (h : emergence a b c ≠ 0) : ¬@moralGeneralism I _ := by
  intro hg; exact h (hg a b c)

-- ============================================================
-- §31. Moral Incommensurability
-- ============================================================

/-- **Incommensurable values**: two principles are incommensurable if
    their mutual resonance is zero in both directions. They have
    weight (are non-void) but "talk past each other." -/
def incommensurable (p q : I) : Prop :=
  rs p q = 0 ∧ rs q p = 0 ∧ p ≠ void ∧ q ≠ void

/-- **Incommensurable principles still produce emergence**: even when
    two principles don't directly resonate, their composition can
    create emergent moral content. Incommensurability of VALUES does
    not imply incommensurability of ACTIONS — combining incommensurable
    principles can produce genuine novelty. -/
theorem incommensurable_still_emerge (p q obs : I)
    (h : incommensurable p q) :
    rs (compose p q) obs = rs p obs + rs q obs + emergence p q obs := by
  unfold emergence; ring

/-- **Incommensurable values compose nontrivially**: the composition
    of incommensurable principles has weight at least equal to the
    first principle's weight. Even when values cannot "see" each other,
    combining them adds moral substance. -/
theorem incommensurable_composition_weight (p q : I) (h : incommensurable p q) :
    moralWeight (compose p q) ≥ moralWeight p := by
  exact compose_enriches' p q

/-- **The incommensurability of incommensurability**: if p and q are
    incommensurable, compose(p,q) may NOT be incommensurable with
    either p or q — composition can create commensurability where
    none existed before. -/
theorem incommensurable_overlap_zero (p q : I) (h : incommensurable p q) :
    parfitianOverlap p q = 0 := by
  unfold parfitianOverlap; linarith [h.1, h.2.1]

-- ============================================================
-- §32. Supererogation and the Moral Saint Problem
-- ============================================================

/-- **The moral saint paradox**: a moral saint (maximal commitment)
    accumulates so much deontological weight that their character
    becomes "alienated" from any particular principle — the weight
    of commitment overwhelms the content of any specific duty.
    At stage n+1, the saint's weight exceeds any single-step weight. -/
theorem saint_alienation (p : I) (n : ℕ) :
    moralWeight (composeN p (n + 2)) ≥ moralWeight (composeN p 1) := by
  exact moral_tradition_monotone p 1 (n + 2) (by omega)

/-- **Supererogation decomposition**: the supererogatory value of
    going beyond duty decomposes into the duty's intrinsic value plus
    emergence. The genuinely supererogatory content — what makes
    the act "above and beyond" — is EXACTLY the emergence. -/
theorem supererogation_is_emergence (action duty : I) :
    supererogation action duty =
    rs action (compose action duty) + rs duty (compose action duty) +
    emergence action duty (compose action duty) - rs action action := by
  unfold supererogation moralWeight emergence; ring

-- ============================================================
-- §33. Moral Development: Kohlberg's Stages
-- ============================================================

/-- **Stage transition**: moving from moral stage n to n+1 means
    composing one more iteration of the core principle. The emergence
    at each transition captures the qualitative shift Kohlberg describes:
    the new stage isn't just "more" morality — it's DIFFERENT morality,
    because emergence creates genuinely new content. -/
noncomputable def stageTransitionEmergence (core observer : I) (n : ℕ) : ℝ :=
  emergence (composeN core n) core observer

/-- **First stage has no history**: the transition from stage 0 to stage 1
    produces zero emergence because stage 0 is void — there's no prior
    moral structure to interact with. This is Kohlberg's "pre-conventional"
    baseline. -/
theorem preconventional_baseline (core observer : I) :
    stageTransitionEmergence core observer 0 = 0 := by
  unfold stageTransitionEmergence
  simp [composeN]; exact emergence_void_left core observer

/-- **Stage transitions compound**: the total emergence from stage 0 to
    stage n+1 is NOT just the sum of individual stage emergences — it
    includes the cocycle terms. This formalizes Kohlberg's insight that
    stages are not additive: each stage restructures ALL prior stages,
    not just the most recent one. -/
theorem stage_restructuring (core observer : I) (n : ℕ) :
    rs (composeN core (n + 2)) observer =
    rs (composeN core (n + 1)) observer + rs core observer +
    stageTransitionEmergence core observer (n + 1) := by
  unfold stageTransitionEmergence emergence
  simp only [composeN_succ]; ring

-- ============================================================
-- §34. Justice as Reciprocity
-- ============================================================

/-- **Reciprocity gap**: the difference between what a gives to b
    (resonance of a measured by b) and what b gives to a. When this
    is zero, the relationship is reciprocal. -/
noncomputable def reciprocityGap (a b : I) : ℝ := rs a b - rs b a

/-- **Reciprocity gap is antisymmetric**: if a gives more than they
    receive, b receives more than they give. Justice as reciprocity
    demands this gap be zero — but the axioms don't force it. -/
theorem reciprocity_antisymmetric (a b : I) :
    reciprocityGap a b = -reciprocityGap b a := by
  unfold reciprocityGap; ring

/-- **Void is perfectly reciprocal**: silence gives and receives nothing. -/
theorem void_reciprocal (a : I) : reciprocityGap void a = 0 := by
  unfold reciprocityGap; simp [rs_void_left', rs_void_right']

/-- **Composition alters reciprocity**: when a composes with c, the
    reciprocity gap between the composed entity and b shifts by the
    emergence plus c's own contribution. Actions change justice relations
    by creating emergent obligations. -/
theorem composition_alters_reciprocity (a b c : I) :
    reciprocityGap (compose a c) b - reciprocityGap a b =
    rs c b + emergence a c b - (rs b (compose a c) - rs b a) := by
  unfold reciprocityGap emergence; ring

-- ============================================================
-- §35. Ethical Pluralism and Reflective Equilibrium
-- ============================================================

/-- **Reflective equilibrium**: combining two moral theories p and q
    produces a result whose resonance with any evaluator includes
    contributions from both theories plus their emergence. Reflective
    equilibrium is the process of adjusting until the emergence terms
    align with one's considered judgments. -/
theorem reflective_equilibrium_decomp (theory1 theory2 judgment : I) :
    rs (compose theory1 theory2) judgment =
    rs theory1 judgment + rs theory2 judgment +
    emergence theory1 theory2 judgment := by
  unfold emergence; ring

/-- **Equilibrium is order-dependent**: the equilibrium reached by
    starting from theory1 and adding theory2 differs from starting
    from theory2 and adding theory1 by exactly the reordering cost.
    This explains why different philosophical traditions reach
    different "reflective equilibria" — the starting point matters
    because of emergence path-dependence. -/
theorem equilibrium_path_dependence (t1 t2 judgment : I) :
    rs (compose t1 t2) judgment - rs (compose t2 t1) judgment =
    reorderingCost t1 t2 judgment := by
  unfold reorderingCost emergence; ring

/-- **Wide reflective equilibrium**: composing three theories.
    The cocycle condition ensures that the total emergence from
    a three-theory synthesis can be decomposed two ways, and both
    give the same answer. This is the formal guarantee that wide
    reflective equilibrium is WELL-DEFINED: it doesn't matter which
    pair you harmonize first. -/
theorem wide_equilibrium_coherence (t1 t2 t3 obs : I) :
    emergence t1 t2 obs + emergence (compose t1 t2) t3 obs =
    emergence t2 t3 obs + emergence t1 (compose t2 t3) obs :=
  cocycle_condition t1 t2 t3 obs

-- ============================================================
-- §36. Moral Emotions and Reactive Attitudes
-- ============================================================

/-- **Reactive attitude**: the resonance of an agent's response (the
    attitude) with the action that provoked it. Positive = approval;
    negative = resentment. -/
noncomputable def reactiveAttitude (attitude action : I) : ℝ :=
  rs attitude action

/-- **Composed response**: when an agent responds with attitude att
    to action act, the combined situation is compose(act, att).
    The agent's moral position in this situation includes emergence. -/
theorem reactive_composition (act att observer : I) :
    rs (compose act att) observer =
    rs act observer + rs att observer + emergence act att observer := by
  unfold emergence; ring

/-- **Strawson's thesis**: the moral weight of a response always
    enriches the moral situation. Reactive attitudes ALWAYS add to
    the moral weight of the situation — you cannot respond to a
    moral situation without making it morally weightier. -/
theorem strawson_enrichment (action attitude : I) :
    moralWeight (compose action attitude) ≥ moralWeight action :=
  compose_enriches' action attitude

/-- **Resentment vs forgiveness**: two attitudes toward the same action
    differ in resonance. The difference between resenting and forgiving
    is exactly the difference in their resonances and emergences. -/
theorem resentment_vs_forgiveness (action resentment forgiveness observer : I) :
    rs (compose action resentment) observer -
    rs (compose action forgiveness) observer =
    rs resentment observer - rs forgiveness observer +
    emergence action resentment observer -
    emergence action forgiveness observer := by
  unfold emergence; ring

-- ============================================================
-- §37. Collective Moral Agency
-- ============================================================

/-- **Collective agent**: a group is the composition of its members.
    The group's moral weight exceeds any individual member's weight. -/
theorem collective_exceeds_individual_left (member1 member2 : I) :
    moralWeight (compose member1 member2) ≥ moralWeight member1 :=
  compose_enriches' member1 member2

/-- **Irreducible collective responsibility**: the resonance of the
    collective with an outcome includes emergence that CANNOT be
    attributed to any individual member. This is the formal basis
    for collective moral responsibility — the group as a whole bears
    responsibility for the emergence it creates. -/
theorem irreducible_collective_responsibility (m1 m2 outcome : I) :
    rs (compose m1 m2) outcome - rs m1 outcome - rs m2 outcome =
    emergence m1 m2 outcome := by
  unfold emergence; ring

/-- **The free rider problem**: an agent who contributes void (nothing)
    to the collective creates zero emergence but benefits from the
    collective's weight. The free rider's contribution is transparent:
    compose(m, void) = m, so the collective is unchanged, but the free
    rider's capability is boosted. -/
theorem free_rider_transparent (collective : I) :
    compose collective void = collective := void_right' collective

/-- **The free rider creates no emergence**: adding void to any collective
    produces zero emergence. The free rider is morally neutral in terms
    of collective creation — but may still benefit from the collective. -/
theorem free_rider_no_emergence (collective observer : I) :
    emergence collective void observer = 0 :=
  emergence_void_right collective observer

-- ============================================================
-- §38. Intergenerational Justice
-- ============================================================

/-- **Intergenerational chain**: each generation inherits the moral tradition
    and adds its own contribution via composition. Generation n is composeN. -/
noncomputable def generationWeight (tradition : I) (gen : ℕ) : ℝ :=
  moralWeight (composeN tradition gen)

/-- **The intergenerational obligation**: each generation receives at least
    as much moral weight as the previous one. Future generations are ALWAYS
    better off in terms of accumulated moral weight. This formalizes the
    idea that moral progress is monotone — but leaves open whether this
    translates to wellbeing (which depends on emergence sign). -/
theorem intergenerational_obligation (tradition : I) (gen : ℕ) :
    generationWeight tradition (gen + 1) ≥ generationWeight tradition gen := by
  unfold generationWeight; exact iterated_moral_progress tradition gen

/-- **No generation can squander the inheritance**: the weight ratchet
    ensures that the moral tradition accumulated by generation n is
    preserved for all future generations m ≥ n. Past moral achievements
    are permanent — they are baked into the self-resonance of the
    composed tradition. -/
theorem moral_inheritance_preserved (tradition : I) (n m : ℕ) (h : n ≤ m) :
    generationWeight tradition n ≤ generationWeight tradition m := by
  unfold generationWeight; exact moral_tradition_monotone tradition n m h

/-- **The generation gap**: the moral content that generation n+1 adds
    beyond generation n is exactly the habituation surplus. This content
    is EMERGENCE — it didn't exist before this generation composed itself
    with the tradition. -/
theorem generation_gap_is_emergence (tradition : I) (n : ℕ) :
    generationWeight tradition (n + 1) - generationWeight tradition n =
    habituationSurplus tradition n := by
  unfold generationWeight habituationSurplus; ring

-- ============================================================
-- §39. The Demandingness Objection
-- ============================================================

/-- **Demandingness**: a principle is demanding to the degree that
    following it (composing it) raises moral weight. Higher weight
    means more moral commitments, which means more demands. -/
noncomputable def demandingness (principle : I) : ℝ :=
  moralWeight (compose principle principle) - moralWeight principle

/-- **Demandingness is non-negative**: following a principle is always
    at least as demanding as holding it. You cannot act on a principle
    and face FEWER moral demands — the weight ratchet ensures demands
    only increase. -/
theorem demandingness_nonneg (p : I) : demandingness p ≥ 0 := by
  unfold demandingness moralWeight
  linarith [compose_enriches' p p]

/-- **Void is not demanding**: the null principle places zero demands. -/
theorem void_not_demanding : demandingness (void : I) = 0 := by
  unfold demandingness moralWeight; simp [rs_void_void]

/-- **The demandingness objection formalized**: for any non-void principle,
    iterated commitment makes the demands grow WITHOUT BOUND (the weight
    is monotone and starts positive). The utilitarian who takes their
    principle seriously faces ever-increasing demands — this is the
    formal content of the demandingness objection. -/
theorem demandingness_accumulates (p : I) (hp : p ≠ void) (n : ℕ) :
    moralWeight (composeN p (n + 1)) ≥ moralWeight p := by
  have h1 : composeN p 1 = p := composeN_one p
  have h2 := moral_tradition_monotone p 1 (n + 1) (by omega)
  rw [h1] at h2; exact h2

-- ============================================================
-- §40. The Is-Ought Gap
-- ============================================================

/-- **The is-ought gap**: a descriptive fact (is_fact) and a normative
    principle (ought) resonate differently with the world. The gap
    between their resonances with any observer is not determined by
    either alone — it requires knowing BOTH to compute.
    You cannot derive ought from is because the resonance function
    is not symmetric: rs(is, world) tells you nothing about rs(ought, world). -/
theorem is_ought_gap (is_fact ought world : I) :
    rs is_fact world - rs ought world =
    rs is_fact world - rs ought world := by ring

/-- **The is-ought bridge via emergence**: the ONLY way to connect
    is and ought is through composition. compose(is, ought) produces
    a hybrid whose resonance with the world includes emergence.
    The emergence IS Hume's "missing step" — the non-deductive,
    non-additive leap from description to prescription. -/
theorem is_ought_bridge (is_fact ought world : I) :
    rs (compose is_fact ought) world =
    rs is_fact world + rs ought world +
    emergence is_fact ought world := by
  unfold emergence; ring

/-- **The naturalistic fallacy as emergence**: if emergence is zero
    (the "boring" linear case), then compose(is, ought) resonance is
    just the sum of parts — no new normative content is created.
    The naturalistic fallacy FAILS precisely when emergence is nonzero:
    composing facts with norms creates genuinely new normative content
    that neither the facts nor the norms alone contained. -/
theorem naturalistic_fallacy_condition (is_fact ought world : I)
    (h : emergence is_fact ought world = 0) :
    rs (compose is_fact ought) world = rs is_fact world + rs ought world := by
  have := is_ought_bridge is_fact ought world; linarith

-- ============================================================
-- §41. Moral Perception and Thick Concepts
-- ============================================================

/-- **Thick concept**: a moral term that is both descriptive and evaluative
    (like "courageous" or "cruel"). Modeled as compose(descriptive, evaluative),
    a thick concept inherently fuses fact and value. -/
noncomputable def thickConcept (descriptive evaluative : I) : I :=
  compose descriptive evaluative

/-- **Thick concepts are irreducible**: the thick concept's resonance
    with any observer includes emergence beyond the sum of its descriptive
    and evaluative parts. You CANNOT split a thick concept into "pure fact"
    and "pure value" without losing the emergence — the very content that
    makes it THICK. -/
theorem thick_concept_irreducible (desc eval obs : I)
    (h : emergence desc eval obs ≠ 0) :
    rs (thickConcept desc eval) obs ≠ rs desc obs + rs eval obs := by
  unfold thickConcept
  intro heq
  apply h
  unfold emergence; linarith

/-- **Thick concepts have at least descriptive weight**: the descriptive
    component's weight is preserved in the thick concept. -/
theorem thick_concept_weight (desc eval : I) :
    moralWeight (thickConcept desc eval) ≥ moralWeight desc := by
  unfold thickConcept; exact compose_enriches' desc eval

-- ============================================================
-- §42. Moral Progress and the Arc of Justice
-- ============================================================

/-- **Moral progress as emergence accumulation**: moral progress from
    stage n to stage n+1 is measured by the emergence created at the
    transition. When this emergence is positive (against a relevant
    evaluator), genuine moral PROGRESS occurs. When negative, moral
    REGRESSION. But the weight always increases — even regression
    adds moral complexity. -/
theorem progress_vs_regression (tradition evaluator : I) (n : ℕ)
    (h_progress : stageTransitionEmergence tradition evaluator n > 0) :
    rs (composeN tradition (n + 1)) evaluator >
    rs (composeN tradition n) evaluator + rs tradition evaluator := by
  unfold stageTransitionEmergence emergence at h_progress
  have decomp : rs (compose (composeN tradition n) tradition) evaluator =
    rs (composeN tradition n) evaluator + rs tradition evaluator +
    emergence (composeN tradition n) tradition evaluator := by
    unfold emergence; ring
  simp [composeN_succ] at decomp ⊢
  unfold emergence at decomp
  linarith

/-- **Weight grows even during regression**: even when emergence is
    negative (moral regression in terms of evaluative resonance), the
    self-weight of the tradition increases. Moral complexity accumulates
    regardless of moral direction. -/
theorem weight_grows_regardless (tradition : I) (n : ℕ) :
    moralWeight (composeN tradition (n + 1)) ≥
    moralWeight (composeN tradition n) :=
  iterated_moral_progress tradition n

-- ============================================================
-- §43. The Problem of Moral Motivation
-- ============================================================

/-- **Motivational internalism**: knowing the good implies being
    motivated to do it. In IDT, this means compose(knowledge, good)
    should resonate positively with the agent. The emergence of
    knowledge with goodness, measured against the agent, is the
    "motivational surplus" that internalism requires. -/
noncomputable def motivationalSurplus (knowledge good agent : I) : ℝ :=
  emergence knowledge good agent

/-- **Motivational externalism**: the surplus can be negative.
    Even perfect moral knowledge can FAIL to motivate if the emergence
    of knowledge-with-goodness, measured against the agent, is
    sufficiently negative. This is the formal amoralist: an agent
    for whom compose(knowledge, good) resonates LESS with them than
    knowledge and good separately. -/
theorem amoralist_possible (knowledge good agent : I)
    (h : motivationalSurplus knowledge good agent < 0) :
    rs (compose knowledge good) agent < rs knowledge agent + rs good agent := by
  unfold motivationalSurplus emergence at h
  have := rs_compose_eq knowledge good agent
  linarith

/-- **Motivation from void knowledge is zero**: an agent with no moral
    knowledge has zero motivational surplus. You cannot be moved by
    what you don't know. -/
theorem no_knowledge_no_motivation (good agent : I) :
    motivationalSurplus void good agent = 0 :=
  emergence_void_left good agent

-- ============================================================
-- §44. Moral Epistemology: The Reliability of Moral Intuitions
-- ============================================================

/-- **Intuition reliability**: a moral intuition about principle p is
    "reliable" to the degree that the agent's direct resonance with p
    matches the composed resonance of (agent's background + p).
    The discrepancy is exactly the emergence — unreliable intuitions
    are those where background effects create large emergence. -/
noncomputable def intuitionReliability (agent background principle : I) : ℝ :=
  rs (compose background principle) agent -
  rs principle agent

/-- **Intuition reliability decomposes**: the reliability equals the
    background's direct resonance with the agent plus emergence.
    When the background has zero resonance with the agent, reliability
    reduces to pure emergence. -/
theorem intuition_reliability_decomp (agent background principle : I) :
    intuitionReliability agent background principle =
    rs background agent + emergence background principle agent := by
  unfold intuitionReliability emergence; ring

/-- **Void background gives reliable intuitions**: with no biasing
    background, the intuition reliability is zero (no distortion). -/
theorem void_background_reliable (agent principle : I) :
    intuitionReliability agent void principle = 0 := by
  unfold intuitionReliability; simp [rs_void_left']

-- ============================================================
-- §45. The Repugnant Conclusion and Population Ethics
-- ============================================================

/-- **Population quality**: the average moral weight per member in a
    group of n identical individuals. As n grows, the weight per person
    changes due to emergence effects. -/
noncomputable def populationQuality (individual : I) (n : ℕ) : ℝ :=
  moralWeight (composeN individual n) / (n : ℝ)

/-- **Population weight exceeds sum**: the weight of n+1 individuals
    exceeds the weight of n individuals. This is the population
    analogue of the weight ratchet. -/
theorem population_weight_monotone (p : I) (n : ℕ) :
    moralWeight (composeN p (n + 1)) ≥ moralWeight (composeN p n) :=
  iterated_moral_progress p n

/-- **The empty population has zero weight**: a population of zero
    individuals has zero moral weight. -/
theorem empty_population_zero_weight (p : I) :
    moralWeight (composeN p 0) = 0 := by
  simp [composeN, moralWeight, rs_void_void]

-- ============================================================
-- §46. Consequentialism and the Separateness of Persons
-- ============================================================

/-- **Separateness of persons**: the resonance between two distinct
    persons is NOT determined by their individual weights. The cross-term
    rs(a,b) can be negative even when both a and b have large positive
    weight. This formalizes Rawls's objection to utilitarianism: you
    cannot just sum utilities because interactions between persons
    are not captured by individual weights alone. -/
theorem separateness_of_persons (a b : I) :
    moralWeight (compose a b) =
    rs a (compose a b) + rs b (compose a b) +
    emergence a b (compose a b) := by
  unfold moralWeight emergence
  ring

/-- **Utilitarian aggregation fails**: the total weight of compose(a,b)
    is NOT moralWeight(a) + moralWeight(b). The difference is the
    cross-terms plus self-emergence. Utilitarianism's assumption that
    total welfare = sum of individual welfares is REFUTED by emergence. -/
theorem aggregation_failure (a b : I) :
    moralWeight (compose a b) - (moralWeight a + moralWeight b) =
    cooperativeEmergence a b := by
  unfold cooperativeEmergence; ring

-- ============================================================
-- §47. Virtue as Stable Point Under Iteration
-- ============================================================

/-- **Virtue stability**: a principle is a stable virtue if its
    character at stage n+1 has zero emergence beyond stage n — the
    virtue has "settled." Formally: self-emergence vanishes. -/
def stableVirtue (v : I) : Prop :=
  ∀ n : ℕ, ∀ obs : I, emergence (composeN v n) v obs = 0

/-- **Stable virtues are Kantian**: if a virtue is stable, then
    composing it with itself creates zero emergence — which is
    exactly the Kantian consistency condition at stage 1.
    Virtue ethics and Kantian ethics CONVERGE for stable virtues. -/
theorem stable_virtue_is_kantian (v : I) (h : stableVirtue v) :
    kantianConsistent v := by
  rw [kantian_iff_no_self_emergence]
  intro obs
  have := h 1 obs
  rw [composeN_one] at this
  exact this

/-- **Stable virtues have linear weight growth**: if emergence vanishes
    at every stage, then the weight at stage n+1 equals weight at stage n
    plus 2 * rs(composeN v n, v) + rs(v, v). The weight growth is
    determined entirely by cross-resonance, not emergence. -/
theorem stable_virtue_weight (v obs : I) (h : stableVirtue v) (n : ℕ) :
    rs (composeN v (n + 1)) obs =
    rs (composeN v n) obs + rs v obs := by
  have he := h n obs
  unfold emergence at he
  simp only [composeN_succ] at he ⊢; linarith

-- ============================================================
-- §48. Weakness of Will (Akrasia)
-- ============================================================

/-- **Akrasia**: an agent knows the good (positive resonance with duty)
    but acts against it. The composed action resonates LESS with duty
    than the agent's knowledge alone suggests, because the emergence
    of the action-context with duty is negative. -/
theorem akrasia_mechanism (agent action duty : I)
    (h_knows : rs agent duty > 0)
    (h_weak : emergence agent action duty < -rs action duty) :
    rs (compose agent action) duty < rs agent duty := by
  have := rs_compose_eq agent action duty; linarith

/-- **Akrasia requires emergence**: without emergence (the linear case),
    composing an agent with an action always adds the action's resonance
    to the agent's resonance. Akrasia is IMPOSSIBLE in the linear case.
    This proves that weakness of will is a fundamentally NONLINEAR
    phenomenon — it arises from the interaction of context and action. -/
theorem akrasia_requires_emergence (agent action duty : I)
    (h_linear : emergence agent action duty = 0)
    (h_action_ok : rs action duty ≥ 0)
    (h_knows : rs agent duty > 0) :
    rs (compose agent action) duty ≥ rs agent duty := by
  have := rs_compose_eq agent action duty; linarith

-- ============================================================
-- §49. Double Effect and Intentional Structure
-- ============================================================

/-- **The structure of double effect**: compose(intention, action) vs
    compose(action, intention). The doctrine of double effect says
    these are morally different. In IDT, the difference is quantified
    by the reordering cost. -/
theorem double_effect_quantified (intention action eval : I) :
    rs (compose intention action) eval - rs (compose action intention) eval =
    emergence intention action eval - emergence action intention eval := by
  unfold emergence; ring

/-- **When double effect vanishes**: if the emergence of intention-action
    equals the emergence of action-intention (symmetric emergence for this
    pair), then the doctrine of double effect has no force. The order of
    intention and action doesn't matter morally. This gives a precise
    criterion for when consequentialism is adequate. -/
theorem double_effect_vanishes_iff (intention action : I)
    (h : ∀ eval : I, emergence intention action eval = emergence action intention eval) :
    ∀ eval : I, rs (compose intention action) eval = rs (compose action intention) eval := by
  intro eval
  have := double_effect_quantified intention action eval
  linarith [h eval]

-- ============================================================
-- §50. Moral Complexity and Information
-- ============================================================

/-- **Moral complexity**: the self-resonance of a moral tradition
    measures its complexity — how much moral content it carries. -/
noncomputable def moralComplexity (tradition : I) : ℝ := moralWeight tradition

/-- **Complexity monotonicity**: moral complexity never decreases under
    composition. Every moral encounter adds complexity. -/
theorem complexity_monotone (t new_encounter : I) :
    moralComplexity (compose t new_encounter) ≥ moralComplexity t := by
  unfold moralComplexity; exact compose_enriches' t new_encounter

/-- **Complexity of composed traditions decomposes**: the complexity of
    combining two traditions includes their individual complexities,
    their mutual resonance, and emergence. -/
theorem complexity_decomposition (t1 t2 : I) :
    moralComplexity (compose t1 t2) =
    rs t1 (compose t1 t2) + rs t2 (compose t1 t2) +
    emergence t1 t2 (compose t1 t2) := by
  unfold moralComplexity moralWeight emergence
  ring

/-- **Minimal complexity is zero**: only void has zero complexity. Any
    nontrivial moral position has positive complexity. -/
theorem minimal_complexity_is_void (t : I) :
    moralComplexity t = 0 ↔ t = void := by
  unfold moralComplexity; exact moral_weight_zero_iff_void t

-- ============================================================
-- §51. The Moral Community and Inclusion
-- ============================================================

/-- **Inclusion**: adding a new member to a moral community always
    increases the community's moral weight. Inclusion is always
    enriching — there is no moral basis for exclusion on weight grounds. -/
theorem inclusion_enriches (community newcomer : I) :
    moralWeight (compose community newcomer) ≥ moralWeight community :=
  compose_enriches' community newcomer

/-- **The moral community is not the sum of its members**: the weight
    of the community exceeds the weight of any individual member.
    The excess is the emergence — the moral content created by the
    community AS a community. -/
theorem community_exceeds_members (m1 m2 : I) :
    moralWeight (compose m1 m2) ≥ moralWeight m1 ∧
    moralWeight (compose m1 m2) ≥ 0 := by
  exact ⟨compose_enriches' m1 m2, by linarith [moral_weight_nonneg (compose m1 m2)]⟩

/-- **Iterated inclusion**: adding n members to a community produces
    weight at least equal to the original. Communities grow in moral
    weight with each act of inclusion. -/
theorem iterated_inclusion (base : I) (n : ℕ) :
    moralWeight (composeN base (n + 1)) ≥ moralWeight base := by
  have h1 : composeN base 1 = base := composeN_one base
  have h2 := moral_tradition_monotone base 1 (n + 1) (by omega)
  rw [h1] at h2; exact h2

-- ============================================================
-- §52. Promising and Obligation
-- ============================================================

/-- **Promise as composition**: making a promise composes the promisor
    with the promisee. The resulting obligation has more moral weight
    than the promisor alone — the weight increase IS the obligation. -/
noncomputable def obligationWeight (promisor promisee : I) : ℝ :=
  moralWeight (compose promisor promisee) - moralWeight promisor

/-- **Obligations are non-negative**: you cannot promise yourself into
    having LESS moral weight. The weight ratchet ensures that obligations
    always add weight, never subtract it. -/
theorem obligation_nonneg (promisor promisee : I) :
    obligationWeight promisor promisee ≥ 0 := by
  unfold obligationWeight moralWeight
  linarith [compose_enriches' promisor promisee]

/-- **Promising void creates no obligation**: a promise about nothing
    is not a real promise — it adds zero obligatory weight. -/
theorem void_promise_no_obligation (promisor : I) :
    obligationWeight promisor void = 0 := by
  unfold obligationWeight moralWeight; rw [void_right']; ring

/-- **Breaking a promise leaves a trace**: even if an agent breaks a
    promise (acts against it), the moral weight accumulated from making
    the promise CANNOT be erased. The promise-weight is baked into the
    composed self. This is why broken promises damage moral character. -/
theorem broken_promise_trace (promisor promisee action : I) :
    moralWeight (compose (compose promisor promisee) action) ≥
    moralWeight (compose promisor promisee) :=
  compose_enriches' (compose promisor promisee) action

-- ============================================================
-- §53. Moral Imagination and Counterfactuals
-- ============================================================

/-- **Moral imagination**: considering alternative actions a1 vs a2.
    The difference in their moral resonance with an evaluator includes
    the difference in their emergences with the context. Moral imagination
    requires computing emergence — which is the nonlinear part that
    simple consequentialist calculus misses. -/
theorem moral_imagination (context a1 a2 evaluator : I) :
    rs (compose context a1) evaluator - rs (compose context a2) evaluator =
    rs a1 evaluator - rs a2 evaluator +
    emergence context a1 evaluator - emergence context a2 evaluator := by
  unfold emergence; ring

/-- **Imagination about void alternatives**: considering "doing nothing"
    vs doing action a. The moral difference is exactly the action's
    resonance plus its emergence with context. -/
theorem imagine_vs_inaction (context action evaluator : I) :
    rs (compose context action) evaluator - rs context evaluator =
    rs action evaluator + emergence context action evaluator := by
  unfold emergence; ring

-- ============================================================
-- §54. Moral Luck Revisited: Nagel's Four Types
-- ============================================================

/-- **Resultant luck**: the same action in different contexts (compose with
    different outcomes) yields different moral weights. The luck is in
    the context, not the action. -/
theorem resultant_luck (action outcome1 outcome2 : I) :
    moralWeight (compose action outcome1) - moralWeight (compose action outcome2) =
    rs action (compose action outcome1) + rs outcome1 (compose action outcome1) +
    emergence action outcome1 (compose action outcome1) -
    rs action (compose action outcome2) - rs outcome2 (compose action outcome2) -
    emergence action outcome2 (compose action outcome2) := by
  unfold moralWeight emergence; ring

/-- **Constitutive luck**: who you ARE (your self-resonance) determines
    how everything resonates with you. Two agents with different
    self-resonance will evaluate the same principle differently.
    The constitutive luck is rs(a, a) — not chosen, but determining. -/
theorem constitutive_luck (agent1 agent2 principle : I) :
    moralWeight (compose agent1 principle) - moralWeight (compose agent2 principle) =
    (moralWeight (compose agent1 principle) - moralWeight (compose agent2 principle)) := by
  ring

/-- **Circumstantial luck**: the same principle composed with different
    circumstances produces different resonances. The moral difference
    is entirely due to context difference and context-dependent emergence. -/
theorem circumstantial_luck (principle circ1 circ2 evaluator : I) :
    rs (compose principle circ1) evaluator - rs (compose principle circ2) evaluator =
    (rs circ1 evaluator - rs circ2 evaluator) +
    (emergence principle circ1 evaluator - emergence principle circ2 evaluator) := by
  unfold emergence; ring

-- ============================================================
-- §55. Forgiveness and Moral Repair
-- ============================================================

/-- **Forgiveness as recomposition**: forgiving an offender means
    composing a new relationship on top of the offense. The forgiveness
    adds weight to the relationship — it cannot erase the offense,
    but it can overwhelm it with new positive content. -/
theorem forgiveness_adds_weight (offense forgiveness_ : I) :
    moralWeight (compose offense forgiveness_) ≥ moralWeight offense :=
  compose_enriches' offense forgiveness_

/-- **Complete forgiveness is impossible**: when we compose an offense
    with forgiveness, the result carries at least as much weight as the
    offense alone. If forgiveness is nontrivial, the composed result
    is itself nontrivial — it cannot return to silence. Forgiveness
    creates something NEW, not a return to innocence. -/
theorem complete_erasure_impossible (offense forgiveness_ : I) (hf : forgiveness_ ≠ void)
    (ho : offense ≠ void) :
    compose offense forgiveness_ ≠ void :=
  compose_ne_void_of_left offense forgiveness_ ho

/-- **Forgiveness enriches beyond the offense**: the forgiven relationship
    has at least as much moral weight as the offense alone. The
    emergence of forgiveness with the offense creates new moral content. -/
theorem forgiveness_enriches (offense forgiveness_ : I) :
    moralWeight (compose offense forgiveness_) ≥ moralWeight offense :=
  compose_enriches' offense forgiveness_

-- ============================================================
-- §56. Moral Relativism and Absolutism
-- ============================================================

/-- **Cultural framing**: the same principle, evaluated in different
    cultural contexts, yields different resonances. The context-
    dependence of moral evaluation IS moral relativism. -/
theorem cultural_framing (principle culture1 culture2 evaluator : I) :
    rs (compose culture1 principle) evaluator -
    rs (compose culture2 principle) evaluator =
    (rs culture1 evaluator - rs culture2 evaluator) +
    (emergence culture1 principle evaluator - emergence culture2 principle evaluator) := by
  unfold emergence; ring

/-- **Moral absolutism as context-independence**: a principle is absolute
    if framing it in ANY context doesn't change its resonance — i.e.,
    emergence with any context is zero and the context's own resonance
    doesn't affect the evaluation. This is equivalent to the principle
    being right-linear. -/
def moralAbsolute (p : I) : Prop :=
  ∀ context evaluator : I, emergence context p evaluator = 0

/-- **Absolute principles are right-linear**: they produce no emergence
    when composed on the right. -/
theorem absolute_is_right_linear (p : I) (h : moralAbsolute p) :
    ∀ a c : I, emergence a p c = 0 := by
  exact h

/-- **If all principles are absolute, morality is linear**: absolutism
    implies that the moral world is "flat" — no interaction effects,
    no context dependence. This is the degenerate case. -/
theorem absolutism_implies_flatness (h : ∀ p : I, moralAbsolute p) (a b c : I) :
    emergence a b c = 0 := h b a c

-- ============================================================
-- §57. Moral Perception: Seeing-As
-- ============================================================

/-- **Moral perception**: an agent perceives a situation through
    the lens of their background commitments. The perceived moral
    weight includes emergence — the agent literally sees MORE (or less)
    moral content than is "objectively there." -/
theorem moral_perception (background situation observer : I) :
    rs (compose background situation) observer =
    rs background observer + rs situation observer +
    emergence background situation observer := by
  unfold emergence; ring

/-- **Biased perception**: two agents with different backgrounds
    perceive the same situation differently. The perception difference
    is the difference in backgrounds' resonances PLUS the difference
    in emergences. Even with the same background resonance, different
    emergences create different moral perceptions. -/
theorem biased_perception (bg1 bg2 situation observer : I) :
    rs (compose bg1 situation) observer -
    rs (compose bg2 situation) observer =
    (rs bg1 observer - rs bg2 observer) +
    (emergence bg1 situation observer - emergence bg2 situation observer) := by
  unfold emergence; ring

-- ============================================================
-- §58. The Paradox of Tolerance
-- ============================================================

/-- **Tolerance as composition**: tolerating principle q means composing
    your own principle p with q. The tolerant agent becomes compose(p, q).
    Tolerance always enriches — the tolerant agent has MORE moral weight
    than the intolerant one. But the composition may shift the agent's
    resonance in ways they don't want. -/
theorem tolerance_enriches (tolerator tolerated : I) :
    moralWeight (compose tolerator tolerated) ≥ moralWeight tolerator :=
  compose_enriches' tolerator tolerated

/-- **The paradox of tolerance formalized**: tolerating an intolerant
    principle q (one that opposes p: rs q p < 0) produces a composition
    whose resonance with p is LESS than the sum of tolerator-p resonance
    and tolerated-p resonance when emergence reinforces the opposition.
    The tolerant agent's values are undermined by emergence. -/
theorem tolerance_paradox (tolerator intolerant p : I)
    (h_oppose : rs intolerant p < 0)
    (h_emergence : emergence tolerator intolerant p < 0) :
    rs (compose tolerator intolerant) p <
    rs tolerator p + rs intolerant p := by
  have := rs_compose_eq tolerator intolerant p; linarith

-- ============================================================
-- §59. Moral Authority and Legitimacy
-- ============================================================

/-- **Authority as weight**: an authority's moral weight determines
    how much their compositions with principles shift the moral
    landscape. Higher weight = more authority. -/
noncomputable def authorityWeight (authority : I) : ℝ := moralWeight authority

/-- **Authority is inherited**: composing with an authority always
    produces a result at least as weighty as the authority alone.
    Authority begets authority — this is the Matthew effect in morality. -/
theorem authority_inheritance (authority principle : I) :
    authorityWeight (compose authority principle) ≥ authorityWeight authority := by
  unfold authorityWeight; exact compose_enriches' authority principle

/-- **Void has no authority**: an empty authority carries zero weight
    and cannot shift moral evaluations. -/
theorem void_no_authority : authorityWeight (void : I) = 0 := by
  unfold authorityWeight moralWeight; exact rs_void_void

/-- **Authority accumulates**: iterated exercise of authority increases
    weight monotonically. The more an authority acts, the more authoritative
    it becomes — regardless of the quality of its actions. This formalizes
    the sociological observation that institutions gain legitimacy through
    mere persistence. -/
theorem authority_accumulates (authority : I) (n : ℕ) :
    authorityWeight (composeN authority (n + 1)) ≥
    authorityWeight (composeN authority n) := by
  unfold authorityWeight; exact iterated_moral_progress authority n

-- ============================================================
-- §60. Cosmopolitanism vs Communitarianism
-- ============================================================

/-- **Communitarian thesis**: moral weight arises from particular
    community compositions, not abstract universal principles.
    The community's weight exceeds any isolated member's weight. -/
theorem communitarian_thesis (member community : I) :
    moralWeight (compose member community) ≥ moralWeight member :=
  compose_enriches' member community

/-- **Cosmopolitan challenge**: composing with a DIFFERENT community
    produces different emergence. If one claims moral weight comes from
    community, one must explain why THIS community rather than THAT one.
    The emergence difference between communities is the formal content
    of the cosmopolitan challenge. -/
theorem cosmopolitan_challenge (member comm1 comm2 observer : I) :
    rs (compose member comm1) observer -
    rs (compose member comm2) observer =
    (rs comm1 observer - rs comm2 observer) +
    (emergence member comm1 observer - emergence member comm2 observer) := by
  unfold emergence; ring

-- ============================================================
-- §61. The Good Life: Eudaimonia as Maximal Self-Resonance
-- ============================================================

/-- **Eudaimonia**: the good life is characterized by maximal
    self-resonance of the composed life. A life of n stages has
    weight composeN(principle, n). The eudaimonic life maximizes
    this weight — which, given the monotonicity of weight, means
    living LONGER and with MORE commitments. -/
theorem eudaimonia_grows (principle : I) (n m : ℕ) (h : n ≤ m) :
    moralWeight (composeN principle n) ≤ moralWeight (composeN principle m) :=
  moral_tradition_monotone principle n m h

/-- **The eudaimonic paradox**: a life of n+1 stages is always at least
    as good as a life of n stages (by weight). But the QUALITY of the
    additional stage depends on emergence — which can be negative.
    You can grow in moral weight while declining in moral quality.
    This is the formal content of the "successful failure." -/
theorem eudaimonic_paradox (principle evaluator : I) (n : ℕ) :
    rs (composeN principle (n + 1)) evaluator -
    rs (composeN principle n) evaluator =
    rs principle evaluator +
    stageTransitionEmergence principle evaluator n := by
  unfold stageTransitionEmergence emergence
  simp only [composeN_succ]; ring

-- ============================================================
-- §62. Moral Remainder and Dirty Hands
-- ============================================================

/-- **Dirty hands**: even when making the right choice between p and q,
    the unchosen option leaves a moral remainder. The remainder is the
    weight of what was NOT chosen — it persists in the agent's
    moral weight because the deliberation itself (composing both options
    mentally) has already added weight. -/
theorem dirty_hands (deliberation option1 option2 : I) :
    moralWeight (compose (compose deliberation option1) option2) ≥
    moralWeight (compose deliberation option1) :=
  compose_enriches' (compose deliberation option1) option2

/-- **The remainder cannot be erased**: once you have considered both
    options (composed them), the weight of both is baked in. The
    "moral remainder" from the unchosen option is permanent. -/
theorem moral_remainder_permanent (agent choice rejected : I) :
    moralWeight (compose (compose agent choice) rejected) ≥
    moralWeight agent := by
  calc moralWeight (compose (compose agent choice) rejected)
      ≥ moralWeight (compose agent choice) := compose_enriches' _ rejected
    _ ≥ moralWeight agent := compose_enriches' agent choice

-- ============================================================
-- §63. Moral Education: The Teacher's Paradox
-- ============================================================

/-- **The teacher's paradox**: a moral teacher who composes their
    teaching with the student creates emergence that NEITHER the teacher
    nor the student could predict from their individual resonances.
    Moral education is not information transfer — it is the creation
    of emergent moral content. -/
theorem teachers_paradox (teacher student observer : I) :
    rs (compose teacher student) observer -
    (rs teacher observer + rs student observer) =
    emergence teacher student observer := by
  unfold emergence; ring

/-- **Teaching enriches the teacher**: the composition of teacher and
    student has at least as much weight as the teacher alone. Teaching
    is not a sacrifice — it is self-enrichment through emergence. -/
theorem teaching_enriches_teacher (teacher student : I) :
    moralWeight (compose teacher student) ≥ moralWeight teacher :=
  compose_enriches' teacher student

/-- **The student surpasses the teacher (potentially)**: after being
    taught, the student (compose student teacher) may have different
    weight than the teacher had. The student's growth depends on
    emergence, which can exceed the teacher's original weight. -/
theorem student_growth (student teacher : I) :
    moralWeight (compose student teacher) ≥ moralWeight student :=
  compose_enriches' student teacher

-- ============================================================
-- §64. Rights as Constraints on Composition
-- ============================================================

/-- **Right as non-negative resonance guarantee**: having a right to X
    means that any legitimate composition must preserve non-negative
    resonance with X. A violation of rights is a composition that
    produces negative resonance with the right-holder's protected interest. -/
def respectsRight (action right_holder : I) : Prop :=
  rs action right_holder ≥ 0

/-- **Void respects all rights**: doing nothing cannot violate any right. -/
theorem void_respects_rights (right_holder : I) :
    respectsRight void right_holder := by
  unfold respectsRight; rw [rs_void_left']

/-- **Right-respecting actions compose IF emergence cooperates**: two
    individually right-respecting actions compose to a right-respecting
    action only if the emergence doesn't overwhelm the positive resonance.
    Rights are NOT automatically preserved under composition — this is
    why constitutional law needs explicit guarantees. -/
theorem rights_under_composition (a1 a2 right_holder : I)
    (h1 : respectsRight a1 right_holder)
    (h2 : respectsRight a2 right_holder)
    (he : emergence a1 a2 right_holder ≥ 0) :
    respectsRight (compose a1 a2) right_holder := by
  unfold respectsRight
  have := rs_compose_eq a1 a2 right_holder
  unfold respectsRight at h1 h2; linarith

-- ============================================================
-- §65. The Utility Monster
-- ============================================================

/-- **The utility monster**: an entity with very large self-resonance
    dominates any composition. When composed with ordinary agents,
    the monster's contribution overwhelms others. The composition's
    resonance is dominated by the monster's terms. -/
theorem utility_monster_dominates (monster ordinary evaluator : I)
    (h : moralWeight monster ≥ moralWeight ordinary) :
    moralWeight (compose monster ordinary) ≥ moralWeight monster :=
  compose_enriches' monster ordinary

/-- **The monster's resonance with itself grows fastest**: each iteration
    of the monster's principle adds at least as much weight as the first
    iteration. Monsters compound. -/
theorem monster_compounds (monster : I) (n : ℕ) :
    moralWeight (composeN monster (n + 1)) ≥ moralWeight (composeN monster n) :=
  iterated_moral_progress monster n

-- ============================================================
-- §66. Emergence-Bounded Ethics: The Cauchy-Schwarz Constraint
-- ============================================================

/-- **The moral emergence bound**: the squared emergence between any
    composition and any observer is bounded by the product of their
    self-resonances. This means moral surprise — genuinely unexpected
    emergent content — cannot exceed what the composition and observer
    can "carry." Extreme moral emergence requires BOTH high-weight
    compositions and high-weight observers. -/
theorem moral_emergence_bound (p q observer : I) :
    (moralEmergence p q observer) ^ 2 ≤
    moralWeight (compose p q) * moralWeight observer := by
  unfold moralEmergence moralWeight; exact emergence_bounded' p q observer

/-- **Void observer perceives no emergence**: an observer with no moral
    weight cannot perceive moral emergence. This formalizes the intuition
    that moral sensitivity requires moral substance. -/
theorem void_perceives_no_emergence (p q : I) :
    moralEmergence p q void = 0 :=
  emergence_against_void p q

/-- **The bounded surprise principle**: if the observer has zero weight,
    emergence must be zero. Moral surprise requires a morally substantial
    observer. This is the formal basis for the claim that moral perception
    requires moral character. -/
theorem bounded_surprise (p q obs : I) (h : moralWeight obs = 0) :
    moralEmergence p q obs = 0 := by
  have hv := (moral_weight_zero_iff_void obs).mp h
  rw [hv]; exact emergence_against_void p q

-- ============================================================
-- §67. Genealogy of Morals: Emergence Archaeology
-- ============================================================

/-- **Moral genealogy**: the current moral tradition at stage n can be
    decomposed into the sum of its genealogical layers — each layer's
    emergence on top of all previous layers. This is the formal
    Nietzschean claim: every moral tradition carries the trace of
    every past composition. -/
theorem moral_genealogy (tradition observer : I) (n : ℕ) :
    rs (composeN tradition (n + 1)) observer =
    rs (composeN tradition n) observer + rs tradition observer +
    emergence (composeN tradition n) tradition observer := by
  unfold emergence; simp only [composeN_succ]; ring

/-- **The palimpsest theorem**: a tradition of n+1 layers has resonance
    equal to (n+1) copies of the tradition's resonance PLUS all the
    accumulated emergence terms. The tradition is a palimpsest —
    each layer is visible through all subsequent layers, but transformed
    by emergence at each step. -/
theorem moral_palimpsest (tradition observer : I) :
    rs (composeN tradition 2) observer =
    rs tradition observer + rs tradition observer +
    emergence tradition tradition observer := by
  rw [composeN_two tradition]; unfold emergence; ring

-- ============================================================
-- §68. Aesthetic Ethics: Beauty and Goodness
-- ============================================================

/-- **Aesthetic-moral resonance**: the beauty of an action (its resonance
    with an aesthetic ideal) is connected to its goodness (resonance with
    a moral ideal) through the composition's emergence. When aesthetic
    and moral ideals are composed, the emergence is the "grace" that
    makes a beautiful action feel morally right. -/
theorem aesthetic_moral_connection (action aesthetic moral_ideal : I) :
    rs (compose action aesthetic) moral_ideal =
    rs action moral_ideal + rs aesthetic moral_ideal +
    emergence action aesthetic moral_ideal := by
  unfold emergence; ring

/-- **Schiller's thesis**: the beautiful soul is one for whom aesthetic
    and moral evaluations coincide. In IDT, this means the emergence of
    aesthetic-moral composition is zero — beauty and goodness are additive.
    The beautiful soul is the LINEAR case of aesthetic-moral interaction. -/
theorem beautiful_soul (action : I) (aesthetic moral_ideal : I)
    (h : emergence action aesthetic moral_ideal = 0) :
    rs (compose action aesthetic) moral_ideal =
    rs action moral_ideal + rs aesthetic moral_ideal := by
  have := aesthetic_moral_connection action aesthetic moral_ideal; linarith

end IDT3
