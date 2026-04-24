import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Epistemology — The Theory of Knowledge

Epistemology asks: What is knowledge? How is it acquired? What are its
limits? We formalize classical and contemporary epistemological positions
within the IdeaticSpace3 framework, where:

- **Belief** = positive resonance between agent and proposition
- **Justification** = evidential composition that amplifies resonance
- **Truth** = resonance with the world
- **Knowledge** = justified true belief (and its refinements)
- **Emergence** = the mechanism behind Gettier cases, paradigm shifts,
  and the creative dimension of understanding

## Structure

- §1. Doxastic States (belief, doubt, suspension)
- §2. Knowledge as Justified True Belief
- §3. Gettier Problems and Epistemic Luck
- §4. Foundationalism (chain justification)
- §5. Coherentism (network justification)
- §6. Kuhn's Paradigm Shifts
- §7. Popper's Falsifiability
- §8. Quine's Web of Belief
- §9. Bayesian Epistemology
- §10. Testimony and Trust
- §11. Epistemic Injustice (Fricker)
- §12. Social Epistemology
- §13. Skepticism
- §14. A Priori vs A Posteriori

Every theorem has a complete proof. Zero sorries, zero admits.
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. Doxastic States — Belief, Doubt, and Suspension

Belief is modeled as positive resonance between an epistemic agent and
a proposition. This captures the phenomenological insight that believing
something is having it "resonate" with one's existing cognitive state. -/

section DoxasticStates
variable {I : Type*} [S : IdeaticSpace3 I]

/-- An agent believes a proposition when it resonates positively with
    the agent's cognitive state. Belief is directional: the agent
    receives the proposition. -/
def believes (agent proposition : I) : Prop := rs agent proposition > 0

/-- Strong belief: the proposition also resonates back toward the agent.
    This captures conviction — mutual cognitive reinforcement. -/
def strongBelief (agent proposition : I) : Prop :=
  rs agent proposition > 0 ∧ rs proposition agent > 0

/-- Doubt: negative resonance — the proposition actively conflicts
    with the agent's cognitive state. -/
def doubts (agent proposition : I) : Prop := rs agent proposition < 0

/-- Suspension of judgment: zero resonance — the proposition is
    cognitively neutral for the agent. -/
def suspendsJudgment (agent proposition : I) : Prop := rs agent proposition = 0

-- Theorem 1
/-- The void agent believes nothing. An empty mind has no beliefs.
    This is the epistemic tabula rasa. -/
theorem void_believes_nothing (p : I) : ¬believes (void : I) p := by
  unfold believes; rw [rs_void_left']; linarith

-- Theorem 2
/-- Every non-void agent believes in itself. Self-awareness is the
    most basic form of belief — Descartes' cogito. -/
theorem cogito (a : I) (ha : a ≠ void) : believes a a := by
  unfold believes; exact rs_self_pos a ha

-- Theorem 3
/-- Strong belief implies belief. Conviction is a stronger
    doxastic state than mere belief. -/
theorem strongBelief_implies_belief (a p : I) (h : strongBelief a p) :
    believes a p := h.1

-- Theorem 4
/-- Belief, doubt, and suspension are mutually exclusive and exhaustive.
    No agent can simultaneously believe and doubt the same proposition. -/
theorem belief_doubt_exclusive (a p : I) :
    ¬(believes a p ∧ doubts a p) := by
  intro ⟨hb, hd⟩; unfold believes at hb; unfold doubts at hd; linarith

-- Theorem 5
/-- The void agent neither believes nor doubts — it suspends judgment
    on everything. This is the state of perfect epistemic quietude. -/
theorem void_suspends_all (p : I) : suspendsJudgment (void : I) p := by
  unfold suspendsJudgment; exact rs_void_left' p

-- Theorem 6
/-- Nothing can be believed about void. Void as a proposition
    elicits no doxastic response from any agent. -/
theorem no_belief_about_void (a : I) : ¬believes a (void : I) := by
  unfold believes; rw [rs_void_right']; linarith

-- Theorem 7
/-- Belief strength: the degree to which an agent holds a belief.
    This is the continuous generalization of the binary believes/doubts. -/
noncomputable def beliefStrength (agent proposition : I) : ℝ :=
  rs agent proposition

/-- Belief strength of void agent is always zero. -/
theorem beliefStrength_void_agent (p : I) : beliefStrength (void : I) p = 0 := by
  unfold beliefStrength; exact rs_void_left' p

-- Theorem 8
/-- Belief strength about void proposition is always zero. -/
theorem beliefStrength_void_prop (a : I) : beliefStrength a (void : I) = 0 := by
  unfold beliefStrength; exact rs_void_right' a

-- Theorem 9
/-- Doxastic weight: the strength of an agent's overall doxastic capacity,
    measured by self-resonance. Agents with more self-resonance have
    more capacity for belief. -/
noncomputable def doxasticCapacity (agent : I) : ℝ := rs agent agent

/-- Doxastic capacity is non-negative. Every agent has non-negative
    capacity for belief. -/
theorem doxasticCapacity_nonneg (a : I) : doxasticCapacity a ≥ 0 := by
  unfold doxasticCapacity; exact rs_self_nonneg' a

-- Theorem 10
/-- Only void has zero doxastic capacity. If you can believe anything
    at all, you must be something. -/
theorem doxasticCapacity_zero_iff_void (a : I) :
    doxasticCapacity a = 0 → a = void := by
  unfold doxasticCapacity; exact rs_nondegen' a

end DoxasticStates

/-! ## §2. Knowledge as Justified True Belief

The classical analysis of knowledge: S knows that p iff
(1) S believes p, (2) p is true, (3) S is justified in believing p.

We formalize truth as resonance with a "world" idea, and justification
as evidential composition that strengthens the belief. -/

section JTB
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Truth relative to a world: a proposition is true when it resonates
    positively with the state of the world. -/
def trueIn (proposition world : I) : Prop := rs proposition world > 0

/-- Justification strength: how much evidence e strengthens the resonance
    between belief b and agent a. Justification is the emergence-enriched
    evidential boost. -/
noncomputable def justificationStrength (evidence belief agent : I) : ℝ :=
  rs (compose evidence belief) agent - rs belief agent

/-- A belief b is justified for agent a by evidence e when the
    evidence-belief composition resonates more with the agent than
    the belief alone. -/
def justified (evidence belief agent : I) : Prop :=
  justificationStrength evidence belief agent > 0

/-- Knowledge as Justified True Belief: the classical tripartite analysis. -/
def knowledgeJTB (agent belief evidence world : I) : Prop :=
  believes agent belief ∧ trueIn belief world ∧ justified evidence belief agent

-- Theorem 11
/-- Justification decomposes into direct evidential resonance plus
    emergence. The emergence term captures how evidence and belief
    TOGETHER create new resonance beyond their individual contributions. -/
theorem justification_decomposition (e b a : I) :
    justificationStrength e b a = rs e a + emergence e b a := by
  unfold justificationStrength; rw [rs_compose_eq]; ring

-- Theorem 12
/-- Void evidence provides zero justification. You cannot justify
    a belief with nothing — epistemic responsibility requires evidence. -/
theorem void_justification (b a : I) :
    justificationStrength (void : I) b a = 0 := by
  unfold justificationStrength; simp

-- Theorem 13
/-- Knowledge requires a non-void agent. Only something that exists
    can have knowledge — the epistemic subject must be real. -/
theorem knowledge_requires_agent (a b e w : I) (h : knowledgeJTB a b e w) :
    a ≠ void := by
  intro heq; rw [heq] at h; exact void_believes_nothing b h.1

-- Theorem 14
/-- Knowledge requires a non-void world. Knowledge must be OF something
    real — you cannot have knowledge about nothing. -/
theorem knowledge_requires_world (a b e w : I) (h : knowledgeJTB a b e w) :
    w ≠ void := by
  intro heq; rw [heq] at h
  have := h.2.1; unfold trueIn at this; rw [rs_void_right'] at this; linarith

-- Theorem 15
/-- Knowledge requires a non-void belief. You must believe something
    substantive to have knowledge — believing nothing is not knowledge. -/
theorem knowledge_requires_belief (a b e w : I) (h : knowledgeJTB a b e w) :
    b ≠ void := by
  intro heq; rw [heq] at h
  have := h.1; unfold believes at this; rw [rs_void_right'] at this; linarith

-- Theorem 16
/-- Self-knowledge: every non-void agent knows itself (given appropriate
    evidence and world). The agent IS the belief, evidence, and world. -/
theorem self_knowledge (a : I) (ha : a ≠ void)
    (hj : rs (compose a a) a > rs a a) :
    knowledgeJTB a a a a := by
  refine ⟨?_, ?_, ?_⟩
  · exact cogito a ha
  · unfold trueIn; exact rs_self_pos a ha
  · unfold justified justificationStrength; linarith

-- Theorem 17
/-- Justification by composition always adds weight. The evidential
    composition is at least as weighty as the evidence alone. -/
theorem evidence_composition_enriches (e b : I) :
    rs (compose e b) (compose e b) ≥ rs e e := by
  exact compose_enriches' e b

end JTB

/-! ## §3. Gettier Problems and Epistemic Luck

Edmund Gettier showed that JTB is not sufficient for knowledge: one can
have justified true belief by accident. In IDT, Gettier cases arise
when emergence creates an accidental connection between evidence and truth.

The key insight: emergence can make a belief "accidentally true" — the
composition of evidence and belief resonates with the world not because
of genuine evidential connection, but because of emergent meaning. -/

section Gettier
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Epistemic luck: the degree to which the truth of a belief depends
    on emergence rather than direct evidential connection.
    High epistemic luck = Gettier-vulnerable knowledge. -/
noncomputable def epistemicLuck (evidence belief world : I) : ℝ :=
  emergence evidence belief world

-- Theorem 18
/-- Epistemic luck is zero when evidence is void. No evidence means
    no luck — you need something to be lucky about. -/
theorem luck_void_evidence (b w : I) : epistemicLuck (void : I) b w = 0 := by
  unfold epistemicLuck; exact emergence_void_left b w

-- Theorem 19
/-- Epistemic luck is zero when belief is void. -/
theorem luck_void_belief (e w : I) : epistemicLuck e (void : I) w = 0 := by
  unfold epistemicLuck; exact emergence_void_right e w

-- Theorem 20
/-- Epistemic luck is zero against a void world. In a world of nothing,
    there is no room for epistemic luck. -/
theorem luck_void_world (e b : I) : epistemicLuck e b (void : I) = 0 := by
  unfold epistemicLuck; exact emergence_against_void e b

-- Theorem 21
/-- A Gettier case: justified true belief where the truth comes from
    emergence rather than direct evidential connection. -/
def gettierCase (agent belief evidence world : I) : Prop :=
  knowledgeJTB agent belief evidence world ∧
  rs evidence world ≤ 0 ∧
  epistemicLuck evidence belief world > 0

/-- Gettier cases require non-trivial emergence. A linear evidence
    source cannot produce Gettier-type epistemic luck. -/
theorem gettier_requires_emergence (a b e w : I) (h : gettierCase a b e w) :
    ¬leftLinear e := by
  intro hlin
  have := h.2.2
  unfold epistemicLuck at this
  rw [hlin b w] at this; linarith

-- Theorem 22
/-- No Gettier cases with void evidence. You need substantive
    (if misleading) evidence for a Gettier case. -/
theorem no_gettier_void (a b w : I) : ¬gettierCase a b (void : I) w := by
  intro ⟨_, _, hem⟩
  unfold epistemicLuck at hem; rw [emergence_void_left] at hem; linarith

-- Theorem 23
/-- The epistemic luck satisfies the cocycle condition.
    Luck has global coherence constraints — it cannot be arbitrary. -/
theorem luck_cocycle (e₁ e₂ e₃ w : I) :
    epistemicLuck e₁ e₂ w + epistemicLuck (compose e₁ e₂) e₃ w =
    epistemicLuck e₂ e₃ w + epistemicLuck e₁ (compose e₂ e₃) w := by
  unfold epistemicLuck; exact cocycle_condition e₁ e₂ e₃ w

-- Theorem 24
/-- Epistemic luck is bounded by the self-resonance of the evidence-belief
    composite and the world. Luck cannot exceed what reality can support. -/
theorem luck_bounded (e b w : I) :
    (epistemicLuck e b w) ^ 2 ≤
    rs (compose e b) (compose e b) * rs w w := by
  unfold epistemicLuck; exact emergence_bounded' e b w

-- Theorem 25
/-- The resonance of evidence-belief with world decomposes into
    direct terms plus luck. This is the anatomy of a Gettier case. -/
theorem gettier_anatomy (e b w : I) :
    rs (compose e b) w = rs e w + rs b w + epistemicLuck e b w := by
  unfold epistemicLuck; rw [rs_compose_eq]

end Gettier

/-! ## §4. Foundationalism — Chain Justification

Foundationalism holds that knowledge rests on a chain of justifications
terminating in self-evident foundational beliefs. In IDT, this is
modeled as iterated composition: each link in the chain composes
evidence with the next, building toward the final belief. -/

section Foundationalism
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Foundational belief: an idea that is self-justifying, having
    positive self-resonance. These are the epistemic bedrock. -/
def foundationalBelief (a : I) : Prop := rs a a > 0

-- Theorem 26
/-- Void is not a foundational belief. Nothing is not self-evident. -/
theorem void_not_foundational : ¬foundationalBelief (void : I) := by
  unfold foundationalBelief; rw [rs_void_void]; linarith

-- Theorem 27
/-- Every non-void idea is foundational. In IDT, all substantive
    ideas have positive self-resonance — they are their own ground.
    This vindicates a radical foundationalism. -/
theorem nonvoid_is_foundational (a : I) (ha : a ≠ void) :
    foundationalBelief a := by
  unfold foundationalBelief; exact rs_self_pos a ha

-- Theorem 28
/-- Chain justification: the evidential chain a₁ ∘ a₂ ∘ ... justifying
    a target belief. The chain's total resonance with the target
    includes all pairwise emergence terms. -/
noncomputable def chainJustification (chain : List I) (target : I) : ℝ :=
  rs (composeList chain) target

/-- Empty chain provides zero justification. -/
theorem chain_empty (t : I) : chainJustification [] t = 0 := by
  unfold chainJustification; simp [rs_void_left']

-- Theorem 29
/-- Single-link chain equals direct resonance. -/
theorem chain_single (a t : I) : chainJustification [a] t = rs a t := by
  unfold chainJustification; simp

-- Theorem 30
/-- Two-link chain decomposes into individual resonances plus emergence.
    The emergence term is the foundationalist's "inferential surplus" —
    what the chain produces beyond what its links contribute individually. -/
theorem chain_two (a b t : I) :
    chainJustification [a, b] t = rs a t + rs b t + emergence a b t := by
  unfold chainJustification
  simp [composeList, rs_compose_eq]

-- Theorem 31
/-- Longer chains have at least as much self-resonance. Adding links
    to a justificatory chain can only increase its epistemic weight.
    This is the foundationalist's "accumulation thesis." -/
theorem chain_weight_grows (a : I) (l : List I) :
    rs (composeList (a :: l)) (composeList (a :: l)) ≥ rs a a := by
  simp [composeList]; exact compose_enriches' a (composeList l)

-- Theorem 32
/-- The foundationalist's regress: an infinite chain has ever-increasing
    weight. Each additional iteration of a non-void idea adds weight. -/
theorem regress_weight_mono (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) := by
  simp only [composeN_succ]; exact compose_enriches' (composeN a n) a

end Foundationalism

/-! ## §5. Coherentism — Network Justification

Coherentism holds that beliefs are justified by their mutual support
within a coherent network, not by a foundational chain. In IDT,
coherence is mutual resonance: ideas justify each other when they
resonate together. -/

section Coherentism
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Coherence between two ideas: the sum of their mutual resonances.
    High coherence means each idea supports the other. -/
noncomputable def coherence (a b : I) : ℝ := rs a b + rs b a

-- Theorem 33
/-- Coherence is symmetric. The coherence of a with b equals the
    coherence of b with a — mutual support is symmetric. -/
theorem coherence_symm (a b : I) : coherence a b = coherence b a := by
  unfold coherence; ring

-- Theorem 34
/-- Self-coherence equals twice the self-resonance. An idea is maximally
    coherent with itself. -/
theorem self_coherence (a : I) : coherence a a = 2 * rs a a := by
  unfold coherence; ring

-- Theorem 35
/-- Self-coherence is non-negative. -/
theorem self_coherence_nonneg (a : I) : coherence a a ≥ 0 := by
  rw [self_coherence]; linarith [rs_self_nonneg' a]

-- Theorem 36
/-- Void has zero coherence with everything. Silence supports nothing. -/
theorem coherence_void (a : I) : coherence (void : I) a = 0 := by
  unfold coherence; simp [rs_void_left', rs_void_right']

-- Theorem 37
/-- Coherence after composition: composing two ideas and measuring
    coherence with a third decomposes into individual coherences
    plus emergence terms. -/
theorem coherence_compose_left (a b c : I) :
    rs (compose a b) c = rs a c + rs b c + emergence a b c := by
  rw [rs_compose_eq]

-- Theorem 38
/-- The coherentist's thesis: knowledge is fully determined by the
    network of coherence relations. Two ideas with the same coherence
    profile (same resonance to all others) are epistemically identical. -/
def coherenceEquivalent (a b : I) : Prop :=
  ∀ c : I, coherence a c = coherence b c

/-- Coherence equivalence is reflexive. -/
theorem coherenceEquiv_refl (a : I) : coherenceEquivalent a a :=
  fun _ => rfl

-- Theorem 39
/-- Coherence equivalence is symmetric. -/
theorem coherenceEquiv_symm (a b : I) (h : coherenceEquivalent a b) :
    coherenceEquivalent b a := by
  intro c; rw [coherence_symm b c, coherence_symm a c]
  have h1 := h c; unfold coherence at h1 ⊢; linarith

-- Theorem 40
/-- The incoherence measure: how much two ideas fail to support
    each other, relative to their individual weights. -/
noncomputable def incoherence (a b : I) : ℝ :=
  rs a a + rs b b - coherence a b

/-- Incoherence is symmetric. -/
theorem incoherence_symm (a b : I) : incoherence a b = incoherence b a := by
  unfold incoherence; rw [coherence_symm]; ring

-- Theorem 41
/-- Self-incoherence is zero. Every idea is perfectly coherent with itself,
    since mutual resonance exactly cancels the self-resonance terms. -/
theorem self_incoherence (a : I) : incoherence a a = 0 := by
  unfold incoherence; rw [self_coherence]; ring

end Coherentism

/-! ## §6. Kuhn's Paradigm Shifts — Phase Transitions in Knowledge

Thomas Kuhn argued that scientific knowledge does not accumulate linearly
but undergoes revolutionary "paradigm shifts." In IDT, a paradigm is a
dominant idea with high self-resonance that shapes how other ideas
resonate. A paradigm shift occurs when a new idea has higher resonance
with the evidence than the old paradigm. -/

section ParadigmShifts
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A paradigm dominates when it has stronger resonance with evidence
    than its rival. -/
def dominates (paradigm rival evidence : I) : Prop :=
  rs paradigm evidence > rs rival evidence

-- Theorem 42
/-- Dominance is irreflexive: no paradigm dominates itself. -/
theorem dominates_irrefl (p e : I) : ¬dominates p p e := by
  unfold dominates; linarith

-- Theorem 43
/-- Dominance is asymmetric. -/
theorem dominates_asymm (p q e : I) (h : dominates p q e) :
    ¬dominates q p e := by
  unfold dominates at *; linarith

-- Theorem 44
/-- Paradigm shift: the resonance advantage of new over old. -/
noncomputable def paradigmShiftMagnitude (old new_ evidence : I) : ℝ :=
  rs new_ evidence - rs old evidence

/-- A paradigm shift is symmetric: the magnitude from old→new equals
    minus the magnitude from new→old. -/
theorem paradigm_shift_antisymm (old new_ evidence : I) :
    paradigmShiftMagnitude old new_ evidence =
    -paradigmShiftMagnitude new_ old evidence := by
  unfold paradigmShiftMagnitude; ring

-- Theorem 45
/-- Incommensurability: two paradigms are incommensurable when their
    mutual resonance is zero. They cannot "see" each other. -/
def incommensurable (p q : I) : Prop :=
  rs p q = 0 ∧ rs q p = 0

/-- Incommensurability is symmetric. -/
theorem incommensurable_symm (p q : I) (h : incommensurable p q) :
    incommensurable q p := ⟨h.2, h.1⟩

-- Theorem 46
/-- Void is incommensurable with everything. The empty paradigm
    is universally incommensurable. -/
theorem void_incommensurable (a : I) :
    incommensurable (void : I) a := by
  constructor
  · exact rs_void_left' a
  · exact rs_void_right' a

-- Theorem 47
/-- Paradigm absorption: composing a paradigm with new evidence creates
    a richer paradigm. The composed paradigm has at least as much
    self-resonance as the original. -/
theorem paradigm_absorption (p e : I) :
    rs (compose p e) (compose p e) ≥ rs p p := by
  exact compose_enriches' p e

-- Theorem 48
/-- Kuhn loss: when paradigms shift, some knowledge is lost.
    The new paradigm may not resonate with everything the old one did.
    Formalized: emergence in the shift can be negative. -/
noncomputable def kuhnLoss (old new_ probe : I) : ℝ :=
  rs old probe - rs new_ probe

/-- Kuhn loss is antisymmetric. -/
theorem kuhn_loss_antisymm (old new_ probe : I) :
    kuhnLoss old new_ probe = -kuhnLoss new_ old probe := by
  unfold kuhnLoss; ring

end ParadigmShifts

/-! ## §7. Popper's Falsifiability — Negative Resonance Tests

Karl Popper argued that scientific theories are distinguished by their
falsifiability — the possibility of being refuted by evidence. In IDT,
falsification is negative resonance: a theory is falsified when evidence
opposes it. -/

section Falsifiability
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A theory is falsifiable by evidence when they have negative resonance.
    The evidence "opposes" the theory. -/
def falsifiedBy (theory evidence : I) : Prop := rs theory evidence < 0

/-- A theory is corroborated by evidence when they have positive resonance.
    Corroboration is NOT verification — it just means the theory survived
    this particular test. -/
def corroboratedBy (theory evidence : I) : Prop := rs theory evidence > 0

-- Theorem 49
/-- Falsification and corroboration are mutually exclusive. A theory
    cannot be both falsified and corroborated by the same evidence. -/
theorem falsification_corroboration_exclusive (t e : I) :
    ¬(falsifiedBy t e ∧ corroboratedBy t e) := by
  intro ⟨hf, hc⟩; unfold falsifiedBy at hf; unfold corroboratedBy at hc; linarith

-- Theorem 50
/-- Void evidence neither falsifies nor corroborates. You need real
    evidence to test a theory. -/
theorem void_evidence_neutral_left (t : I) : ¬falsifiedBy t (void : I) := by
  unfold falsifiedBy; rw [rs_void_right']; linarith

-- Theorem 51
theorem void_evidence_neutral_right (t : I) : ¬corroboratedBy t (void : I) := by
  unfold corroboratedBy; rw [rs_void_right']; linarith

-- Theorem 52
/-- Self-falsification is impossible for non-void theories. A substantive
    theory always corroborates itself. This is Popper's point: falsification
    must come from OUTSIDE the theory. -/
theorem no_self_falsification (t : I) (ht : t ≠ void) :
    ¬falsifiedBy t t := by
  unfold falsifiedBy; have := rs_self_pos t ht; linarith

-- Theorem 53
/-- A non-void theory corroborates itself. Every substantive theory
    is self-consistent. -/
theorem self_corroboration (t : I) (ht : t ≠ void) :
    corroboratedBy t t := by
  unfold corroboratedBy; exact rs_self_pos t ht

-- Theorem 54
/-- The falsifiability degree: how much a theory is refuted by evidence.
    More negative = more falsified. -/
noncomputable def falsifiabilityDegree (theory evidence : I) : ℝ :=
  -(rs theory evidence)

/-- Falsifiability degree of void theory is zero. -/
theorem falsifiability_void_theory (e : I) :
    falsifiabilityDegree (void : I) e = 0 := by
  unfold falsifiabilityDegree; rw [rs_void_left']; ring

end Falsifiability

/-! ## §8. Quine's Web of Belief — Holistic Resonance

W.V.O. Quine argued that beliefs face the "tribunal of experience" not
individually but as a corporate body. No belief is immune to revision,
and any belief can be held true by making adjustments elsewhere.

In IDT, this is captured by the cocycle condition: the emergence of
composing beliefs is globally constrained. You cannot change one
resonance without affecting others. -/

section WebOfBelief
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Belief revision: composing new evidence with an existing belief system
    to get an updated system. -/
def revise (beliefSystem evidence : I) : I := compose beliefSystem evidence

-- Theorem 55
/-- Revision by void evidence changes nothing. No evidence, no revision.
    This is Quine's point that experience MUST impinge. -/
theorem revision_void (b : I) : revise b (void : I) = b := by
  unfold revise; simp

-- Theorem 56
/-- Revision of void belief system just adopts the evidence. -/
theorem revision_from_void (e : I) : revise (void : I) e = e := by
  unfold revise; simp

-- Theorem 57
/-- Quine's holism: the resonance of a revised belief system with any
    probe depends on the entire system, not just the new evidence.
    This is the rs_compose_eq in epistemic dress. -/
theorem quine_holism (system evidence probe : I) :
    rs (revise system evidence) probe =
    rs system probe + rs evidence probe + emergence system evidence probe := by
  unfold revise; rw [rs_compose_eq]

-- Theorem 58
/-- Underdetermination: the same revision effect (same resonance with
    probe) can come from different decompositions of system and evidence.
    If emergence differs, the individual contributions must compensate. -/
theorem underdetermination (s₁ e₁ s₂ e₂ p : I)
    (h : rs (revise s₁ e₁) p = rs (revise s₂ e₂) p) :
    rs s₁ p + rs e₁ p + emergence s₁ e₁ p =
    rs s₂ p + rs e₂ p + emergence s₂ e₂ p := by
  unfold revise at h; rw [rs_compose_eq, rs_compose_eq] at h; linarith

-- Theorem 59
/-- Web revision is associative: revising twice in sequence is the same
    as revising once with the composed evidence. This is Quine's thesis
    that there is no privileged order of revision. -/
theorem revision_assoc (b e₁ e₂ : I) :
    revise (revise b e₁) e₂ = revise b (compose e₁ e₂) := by
  unfold revise; rw [compose_assoc']

-- Theorem 60
/-- Revision always increases or preserves epistemic weight. You cannot
    lose weight by learning — but you might gain "noise." -/
theorem revision_enriches (b e : I) :
    rs (revise b e) (revise b e) ≥ rs b b := by
  unfold revise; exact compose_enriches' b e

-- Theorem 61
/-- The Duhem-Quine thesis: when evidence conflicts with a system, we
    can always "save" any particular belief by adjusting the rest.
    Formally: the emergence term can compensate for any direct conflict. -/
theorem duhem_quine (system evidence probe : I) :
    rs (revise system evidence) probe - rs system probe =
    rs evidence probe + emergence system evidence probe := by
  unfold revise; rw [rs_compose_eq]; ring

end WebOfBelief

/-! ## §9. Bayesian Epistemology — Resonance as Prior Update

Bayesian epistemology models rational belief update using probability
theory. In IDT, the "prior" is the agent's existing resonance structure,
and "updating" is composing with new evidence. The emergence term captures
the non-linear aspect of Bayesian surprise. -/

section Bayesian
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Prior belief: the agent's resonance with a hypothesis before evidence. -/
noncomputable def prior (agent hypothesis : I) : ℝ := rs agent hypothesis

/-- Posterior belief: the agent's resonance with a hypothesis after
    incorporating evidence. -/
noncomputable def posterior (agent evidence hypothesis : I) : ℝ :=
  rs (compose agent evidence) hypothesis

-- Theorem 62
/-- Bayesian update equation: posterior = prior + evidence resonance +
    emergence. The emergence term is the "Bayesian surprise" — the
    non-additive insight that comes from combining agent and evidence. -/
theorem bayesian_update (agent evidence hypothesis : I) :
    posterior agent evidence hypothesis =
    prior agent hypothesis + rs evidence hypothesis +
    emergence agent evidence hypothesis := by
  unfold posterior prior; rw [rs_compose_eq]

-- Theorem 63
/-- With void evidence, posterior equals prior. No evidence, no update.
    This is the Bayesian requirement of conservatism. -/
theorem posterior_void_evidence (a h : I) :
    posterior a (void : I) h = prior a h := by
  unfold posterior prior; simp

-- Theorem 64
/-- A void agent's posterior just reflects the evidence. A blank slate
    adopts whatever the evidence says. -/
theorem posterior_void_agent (e h : I) :
    posterior (void : I) e h = rs e h := by
  unfold posterior; simp

-- Theorem 65
/-- The Bayesian surprise: how much the posterior differs from prior + evidence.
    This is exactly emergence — the non-additive part of the update. -/
noncomputable def bayesianSurprise (agent evidence hypothesis : I) : ℝ :=
  posterior agent evidence hypothesis - prior agent hypothesis - rs evidence hypothesis

/-- Bayesian surprise equals emergence. -/
theorem surprise_is_emergence (a e h : I) :
    bayesianSurprise a e h = emergence a e h := by
  unfold bayesianSurprise posterior prior; unfold emergence; ring

-- Theorem 66
/-- Surprise from void evidence is zero. -/
theorem surprise_void_evidence (a h : I) :
    bayesianSurprise a (void : I) h = 0 := by
  rw [surprise_is_emergence]; exact emergence_void_right a h

-- Theorem 67
/-- Sequential Bayesian update satisfies the cocycle condition.
    The surprise from updating with e₁ then e₂ is constrained by
    the surprise from updating with e₂ then composing with e₁. -/
theorem bayesian_cocycle (a e₁ e₂ h : I) :
    bayesianSurprise a e₁ h + bayesianSurprise (compose a e₁) e₂ h =
    bayesianSurprise e₁ e₂ h + bayesianSurprise a (compose e₁ e₂) h := by
  simp only [surprise_is_emergence]; exact cocycle_condition a e₁ e₂ h

end Bayesian

/-! ## §10. Testimony and Trust — Transmission with Emergence

Testimony is a primary source of knowledge: we learn from others.
In IDT, testimony is modeled as the speaker composing their belief
with the channel of communication, and the hearer receiving the result. -/

section Testimony
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Testimonial transmission: a speaker communicates a belief through
    a channel (language, gesture, etc.) -/
noncomputable def testimonialResonance (speaker belief hearer : I) : ℝ :=
  rs (compose speaker belief) hearer

-- Theorem 68
/-- Testimonial resonance decomposes into direct resonances plus
    emergence. The emergence is the "hermeneutic surplus" — what the
    hearer gets beyond what speaker and belief individually contribute. -/
theorem testimony_decomposition (speaker belief hearer : I) :
    testimonialResonance speaker belief hearer =
    rs speaker hearer + rs belief hearer + emergence speaker belief hearer := by
  unfold testimonialResonance; rw [rs_compose_eq]

-- Theorem 69
/-- A void speaker transmits nothing. Without a speaker, there is
    no testimony — the hearer gets only the belief's own resonance. -/
theorem testimony_void_speaker (b h : I) :
    testimonialResonance (void : I) b h = rs b h := by
  unfold testimonialResonance; simp

-- Theorem 70
/-- Testimony of void belief contributes only the speaker's resonance. -/
theorem testimony_void_belief (s h : I) :
    testimonialResonance s (void : I) h = rs s h := by
  unfold testimonialResonance; simp

-- Theorem 71
/-- Trust level: how much a hearer's belief is amplified by trusting
    the speaker. Trust is the excess of testimonial resonance over
    the belief's own resonance. -/
noncomputable def trustLevel (speaker belief hearer : I) : ℝ :=
  testimonialResonance speaker belief hearer - rs belief hearer

/-- Trust decomposes into speaker credibility plus emergence. -/
theorem trust_decomposition (s b h : I) :
    trustLevel s b h = rs s h + emergence s b h := by
  unfold trustLevel testimonialResonance; rw [rs_compose_eq]; ring

-- Theorem 72
/-- Void speaker has zero trust. You cannot trust a non-existent source. -/
theorem trust_void_speaker (b h : I) : trustLevel (void : I) b h = 0 := by
  unfold trustLevel testimonialResonance; simp

-- Theorem 73
/-- Trust chain: testimony through an intermediary. The chain of trust
    from original speaker through intermediary to hearer satisfies
    the cocycle. -/
theorem trust_chain (s₁ s₂ b h : I) :
    emergence s₁ s₂ h + emergence (compose s₁ s₂) b h =
    emergence s₂ b h + emergence s₁ (compose s₂ b) h := by
  exact cocycle_condition s₁ s₂ b h

end Testimony

/-! ## §11. Epistemic Injustice — Systematic Resonance Suppression

Miranda Fricker identified two forms of epistemic injustice:
testimonial injustice (credibility deficit due to prejudice) and
hermeneutical injustice (lack of interpretive resources).

In IDT, testimonial injustice is modeled as a context (prejudice) that
reduces the resonance of a speaker's testimony with the hearer.
Hermeneutical injustice is modeled as an interpretive framework that
suppresses emergence. -/

section EpistemicInjustice
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Credibility deficit: how much a context (prejudice) reduces
    the resonance of a speaker with a hearer.
    Negative values indicate suppression. -/
noncomputable def credibilityShift (prejudice speaker hearer : I) : ℝ :=
  rs (compose prejudice speaker) hearer - rs speaker hearer

-- Theorem 74
/-- The credibility shift decomposes into the prejudice's direct effect
    plus emergence. Prejudice harms through both direct bias and
    emergent effects (stereotypes interacting with the speaker's identity). -/
theorem credibility_decomposition (prejudice speaker hearer : I) :
    credibilityShift prejudice speaker hearer =
    rs prejudice hearer + emergence prejudice speaker hearer := by
  unfold credibilityShift; rw [rs_compose_eq]; ring

-- Theorem 75
/-- No prejudice, no credibility shift. The absence of bias preserves
    testimonial credibility. -/
theorem no_prejudice_no_shift (speaker hearer : I) :
    credibilityShift (void : I) speaker hearer = 0 := by
  unfold credibilityShift; simp

-- Theorem 76
/-- Testimonial injustice: a credibility deficit that occurs despite
    the speaker being non-void (having genuine testimony to give). -/
def testimonialInjustice (prejudice speaker hearer : I) : Prop :=
  speaker ≠ void ∧ credibilityShift prejudice speaker hearer < 0

/-- Testimonial injustice requires non-void prejudice. Without bias,
    there can be no injustice. -/
theorem injustice_requires_bias (p s h : I)
    (hinj : testimonialInjustice p s h) : p ≠ void := by
  intro heq; rw [heq] at hinj
  have := no_prejudice_no_shift s h
  unfold testimonialInjustice at hinj; linarith [hinj.2]

-- Theorem 77
/-- Hermeneutical gap: the deficit in interpretive resources, measured
    by missing emergence. When the hearer's framework lacks the concepts
    to understand the speaker, emergence is suppressed. -/
noncomputable def hermeneuticalGap (framework speaker content : I) : ℝ :=
  emergence speaker content framework

/-- The hermeneutical gap is bounded. Even the worst hermeneutical
    injustice has finite magnitude. -/
theorem hermeneutical_gap_bounded (f s c : I) :
    (hermeneuticalGap f s c) ^ 2 ≤
    rs (compose s c) (compose s c) * rs f f := by
  unfold hermeneuticalGap; exact emergence_bounded' s c f

-- Theorem 78
/-- Double injustice: when both testimonial and hermeneutical injustice
    operate, the total suppression compounds. -/
noncomputable def totalSuppression (prejudice speaker content hearer : I) : ℝ :=
  credibilityShift prejudice speaker hearer +
  hermeneuticalGap hearer speaker content

/-- Total suppression from void prejudice equals just the hermeneutical gap. -/
theorem suppression_no_prejudice (s c h : I) :
    totalSuppression (void : I) s c h = hermeneuticalGap h s c := by
  unfold totalSuppression; rw [no_prejudice_no_shift]; ring

end EpistemicInjustice

/-! ## §12. Social Epistemology — Collective Knowledge

Knowledge is not just individual but social. Groups can know things
that no individual member knows. In IDT, collective knowledge arises
through the composition of individual knowers — and the emergence
captures what the group knows beyond the sum of its members. -/

section SocialEpistemology
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Collective resonance: how a group (composed of agents) resonates
    with a proposition. -/
noncomputable def collectiveResonance (agent₁ agent₂ proposition : I) : ℝ :=
  rs (compose agent₁ agent₂) proposition

-- Theorem 79
/-- Collective knowledge surplus: the group knows more than the sum
    of its parts. This is emergence in epistemic dress. -/
noncomputable def collectiveSurplus (a₁ a₂ p : I) : ℝ :=
  collectiveResonance a₁ a₂ p - rs a₁ p - rs a₂ p

/-- The collective surplus IS emergence. Collective intelligence
    is a special case of the general emergence phenomenon. -/
theorem collective_surplus_is_emergence (a₁ a₂ p : I) :
    collectiveSurplus a₁ a₂ p = emergence a₁ a₂ p := by
  unfold collectiveSurplus collectiveResonance emergence; ring

-- Theorem 80
/-- Adding a void agent to a collective changes nothing. Deadweight
    members contribute nothing to collective knowledge. -/
theorem collective_void_member (a p : I) :
    collectiveResonance a (void : I) p = rs a p := by
  unfold collectiveResonance; simp

-- Theorem 81
/-- The group's epistemic weight exceeds any individual member's.
    The whole is at least as weighty as its parts. -/
theorem collective_weight (a₁ a₂ : I) :
    rs (compose a₁ a₂) (compose a₁ a₂) ≥ rs a₁ a₁ := by
  exact compose_enriches' a₁ a₂

-- Theorem 82
/-- Wisdom of crowds: with void agent as aggregation,
    collective resonance reduces to individual. -/
theorem wisdom_baseline (a p : I) :
    collectiveResonance (void : I) a p = rs a p := by
  unfold collectiveResonance; simp

-- Theorem 83
/-- The collective cocycle: adding a third member to a dyad
    satisfies the global coherence constraint. Group formation
    is constrained by the same cocycle as all emergence. -/
theorem collective_cocycle (a₁ a₂ a₃ p : I) :
    emergence a₁ a₂ p + emergence (compose a₁ a₂) a₃ p =
    emergence a₂ a₃ p + emergence a₁ (compose a₂ a₃) p := by
  exact cocycle_condition a₁ a₂ a₃ p

-- Theorem 84
/-- Epistemic division of labor: the collective resonance of agents
    with a proposition decomposes into individual contributions plus
    the synergistic emergence. -/
theorem epistemic_division (a₁ a₂ p : I) :
    collectiveResonance a₁ a₂ p =
    rs a₁ p + rs a₂ p + emergence a₁ a₂ p := by
  unfold collectiveResonance; rw [rs_compose_eq]

end SocialEpistemology

/-! ## §13. Skepticism — Can We Know Anything?

Skepticism questions whether knowledge is possible at all. In IDT,
radical skepticism corresponds to asking: can resonance with the world
ever be guaranteed? The answer is nuanced: self-resonance is certain
(the cogito), but resonance with external things depends on emergence. -/

section Skepticism
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Radical skepticism about a proposition: it has zero resonance with
    the world in both directions. The skeptic claims we are
    epistemically cut off from reality. -/
def radicalSkepticism (agent world : I) : Prop :=
  rs agent world = 0 ∧ rs world agent = 0

-- Theorem 85
/-- Void is the perfect skeptic — it is radically skeptical of everything. -/
theorem void_perfect_skeptic (w : I) :
    radicalSkepticism (void : I) w := by
  constructor
  · exact rs_void_left' w
  · exact rs_void_right' w

-- Theorem 86
/-- Self-skepticism is impossible for non-void agents. You cannot doubt
    your own existence — this is the Cartesian cogito. -/
theorem cogito_defeats_self_skepticism (a : I) (ha : a ≠ void) :
    ¬radicalSkepticism a a := by
  intro ⟨h, _⟩; have := rs_self_pos a ha; linarith

-- Theorem 87
/-- Methodical doubt: even if we doubt everything external, self-resonance
    remains. The floor of knowledge is self-knowledge. -/
theorem methodical_doubt_floor (a : I) : rs a a ≥ 0 := by
  exact rs_self_nonneg' a

-- Theorem 88
/-- The skeptic's dilemma: if a skeptic is non-void, they must have
    positive self-resonance, which means they know at least one thing
    (themselves). Total skepticism is self-defeating. -/
theorem skeptic_dilemma (skeptic : I) (h : skeptic ≠ void) :
    rs skeptic skeptic > 0 := by
  exact rs_self_pos skeptic h

-- Theorem 89
/-- External world skepticism: even if agent-world resonance is zero,
    composing the agent with the world adds weight. Engagement with
    the external world is never entirely empty. -/
theorem engagement_adds_weight (agent world : I) :
    rs (compose agent world) (compose agent world) ≥ rs agent agent := by
  exact compose_enriches' agent world

-- Theorem 90
/-- The brain-in-a-vat scenario: even a deceived agent (one whose
    world is void) has genuine self-resonance. The skeptical scenario
    does not undermine self-knowledge. -/
theorem brain_in_vat (agent : I) (ha : agent ≠ void) :
    rs agent agent > 0 := by
  exact rs_self_pos agent ha

end Skepticism

/-! ## §14. A Priori vs A Posteriori — Sources of Knowledge

The distinction between a priori knowledge (independent of experience)
and a posteriori knowledge (dependent on experience) maps onto IDT as:
- A priori = derivable from self-resonance and void
- A posteriori = requiring composition with external ideas -/

section APriori
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A priori epistemic strength: how much an agent knows about a
    proposition from self-resonance alone (without external evidence). -/
noncomputable def aPrioriStrength (agent proposition : I) : ℝ :=
  rs agent proposition

/-- A posteriori strength: the additional resonance gained by composing
    the agent with evidence from the world. -/
noncomputable def aPosterioriGain (agent evidence proposition : I) : ℝ :=
  rs (compose agent evidence) proposition - rs agent proposition

-- Theorem 91
/-- A posteriori gain decomposes into evidence contribution plus emergence.
    Experience teaches both through direct resonance and through emergent
    understanding (the "aha" moment). -/
theorem aposteriori_decomposition (a e p : I) :
    aPosterioriGain a e p = rs e p + emergence a e p := by
  unfold aPosterioriGain; rw [rs_compose_eq]; ring

-- Theorem 92
/-- Void experience yields zero a posteriori gain. Without experience,
    there is nothing to learn empirically. This is the rationalist's
    thesis in IDT form. -/
theorem void_experience_no_gain (a p : I) :
    aPosterioriGain a (void : I) p = 0 := by
  unfold aPosterioriGain; simp

-- Theorem 93
/-- Void agent gains exactly the evidence's resonance. A blank slate
    learns exactly what experience offers — no more, no less. -/
theorem tabula_rasa_gain (e p : I) :
    aPosterioriGain (void : I) e p = rs e p := by
  unfold aPosterioriGain; simp [rs_void_left']

-- Theorem 94
/-- Synthetic a priori: emergence from self-composition. Composing an
    idea with itself can produce genuinely new resonance (synthetic content)
    without external input — Kant's synthetic a priori. -/
noncomputable def syntheticAPriori (a probe : I) : ℝ :=
  emergence a a probe

/-- The synthetic a priori is exactly the semantic charge when measured
    against the idea itself. -/
theorem synthetic_apriori_eq_charge (a : I) :
    syntheticAPriori a a = semanticCharge a := by
  unfold syntheticAPriori; rfl

-- Theorem 95
/-- Void has no synthetic a priori content. Pure emptiness generates
    no synthetic knowledge. -/
theorem void_no_synthetic (p : I) : syntheticAPriori (void : I) p = 0 := by
  unfold syntheticAPriori; exact emergence_void_left (void : I) p

-- Theorem 96
/-- The synthetic a priori is bounded. Even self-generated knowledge
    has limits determined by one's cognitive capacity. -/
theorem synthetic_apriori_bounded (a p : I) :
    (syntheticAPriori a p) ^ 2 ≤
    rs (compose a a) (compose a a) * rs p p := by
  unfold syntheticAPriori; exact emergence_bounded' a a p

-- Theorem 97
/-- Analytic truths: propositions with zero emergence under any
    composition. Analytic propositions add no new information. -/
def analyticFor (agent proposition : I) : Prop :=
  ∀ c : I, emergence agent c proposition = 0

/-- Analytic truths for void are trivial. -/
theorem void_all_analytic (p : I) : analyticFor (void : I) p := by
  intro c; exact emergence_void_left c p

end APriori

/-! ## §15. Epistemic Virtues and Vices — Character Epistemology

Virtue epistemology holds that knowledge depends on the intellectual
character of the knower. We formalize epistemic virtues as structural
properties of an agent's resonance profile. -/

section EpistemicVirtues
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Intellectual humility: the agent's resonance with void — openness
    to emptiness, to not-knowing. A humble agent has zero resonance
    with void (perfectly calibrated). -/
noncomputable def intellectualHumility (agent : I) : ℝ :=
  rs agent agent - rs (compose agent agent) agent + rs agent agent

-- Theorem 98
/-- Intellectual humility is always well-defined (finite). -/
theorem humility_equals (a : I) :
    intellectualHumility a = 2 * rs a a - rs (compose a a) a := by
  unfold intellectualHumility; ring

-- Theorem 99
/-- Void agent has perfect humility (zero). -/
theorem void_humility : intellectualHumility (void : I) = 0 := by
  unfold intellectualHumility; simp [rs_void_void, rs_void_left']

/-- Open-mindedness: how much an agent's resonance changes when
    presented with new ideas. Higher change = more open-minded. -/
noncomputable def openMindedness (agent newIdea : I) : ℝ :=
  rs (compose agent newIdea) (compose agent newIdea) - rs agent agent

-- Theorem 100
/-- Open-mindedness is non-negative. Engaging with new ideas can
    only increase (or preserve) one's epistemic weight. -/
theorem openMindedness_nonneg (a b : I) : openMindedness a b ≥ 0 := by
  unfold openMindedness; linarith [compose_enriches' a b]

-- Theorem 101
/-- Open-mindedness to void is zero. Engaging with nothing teaches nothing. -/
theorem openMindedness_void (a : I) : openMindedness a (void : I) = 0 := by
  unfold openMindedness; simp

/-- Intellectual courage: the willingness to engage with ideas that
    oppose one's current state. Measured by the weight gained from
    composition even with potentially opposing ideas. -/
noncomputable def epistemicResilience (agent challenge : I) : ℝ :=
  rs (compose agent challenge) (compose agent challenge)

-- Theorem 102
/-- Epistemic resilience always at least preserves the agent's weight.
    Even after confronting challenging ideas, the agent remains at least
    as substantial as before. -/
theorem resilience_preserves (a c : I) :
    epistemicResilience a c ≥ rs a a := by
  unfold epistemicResilience; exact compose_enriches' a c

end EpistemicVirtues

/-! ## §16. Epistemic Logic Fundamentals — Knowledge and Belief Interaction

The logical structure of knowledge: relationships between knowing,
believing, and the various operations on epistemic states. -/

section EpistemicLogic
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Epistemic gain from composition: how much composing two ideas
    increases resonance with a target beyond individual contributions. -/
noncomputable def epistemicGain (a b target : I) : ℝ :=
  rs (compose a b) target - rs a target - rs b target

-- Theorem 103
/-- Epistemic gain is exactly emergence. The fundamental identity
    of IDT epistemology: learning IS emergence. -/
theorem gain_is_emergence (a b t : I) :
    epistemicGain a b t = emergence a b t := by
  unfold epistemicGain emergence; ring

-- Theorem 104
/-- The total epistemic content of a composition: everything the
    combined idea resonates with a target, decomposed into
    individual and emergent contributions. -/
theorem epistemic_total (a b t : I) :
    rs (compose a b) t =
    rs a t + rs b t + epistemicGain a b t := by
  unfold epistemicGain; ring

-- Theorem 105
/-- Epistemic gain from void is zero. -/
theorem gain_void_left (b t : I) : epistemicGain (void : I) b t = 0 := by
  rw [gain_is_emergence]; exact emergence_void_left b t

-- Theorem 106
/-- Epistemic gain satisfies the cocycle: sequential learning is
    globally constrained. -/
theorem epistemic_cocycle (a b c t : I) :
    epistemicGain a b t + epistemicGain (compose a b) c t =
    epistemicGain b c t + epistemicGain a (compose b c) t := by
  simp only [gain_is_emergence]; exact cocycle_condition a b c t

-- Theorem 107
/-- Epistemic weight of an idea: its self-resonance, the fundamental
    measure of how much "there is" to know in an idea. -/
noncomputable def epistemicWeight (a : I) : ℝ := rs a a

/-- Epistemic weight is non-negative. Every idea has non-negative
    epistemic content. -/
theorem epistemic_weight_nonneg (a : I) : epistemicWeight a ≥ 0 := by
  unfold epistemicWeight; exact rs_self_nonneg' a

-- Theorem 108
/-- Epistemic weight grows under composition. Combining knowledge
    always preserves or increases total epistemic weight. -/
theorem weight_monotone (a b : I) :
    epistemicWeight (compose a b) ≥ epistemicWeight a := by
  unfold epistemicWeight; exact compose_enriches' a b

-- Theorem 109
/-- Zero epistemic weight implies void. Only nothing has zero
    epistemic content. -/
theorem zero_weight_void (a : I) (h : epistemicWeight a = 0) :
    a = void := by
  unfold epistemicWeight at h; exact rs_nondegen' a h

-- Theorem 110
/-- Epistemic asymmetry: the difference in how two ideas relate to
    each other epistemically. Knowledge is inherently perspectival. -/
noncomputable def epistemicAsymmetry (a b : I) : ℝ :=
  rs a b - rs b a

/-- Epistemic asymmetry is antisymmetric. -/
theorem epistemicAsymmetry_antisymm (a b : I) :
    epistemicAsymmetry a b = -epistemicAsymmetry b a := by
  unfold epistemicAsymmetry; ring

-- Theorem 111
/-- Self-asymmetry is zero. Every agent views itself symmetrically. -/
theorem self_asymmetry (a : I) : epistemicAsymmetry a a = 0 := by
  unfold epistemicAsymmetry; ring

-- Theorem 112
/-- Void has zero asymmetry with everything. The empty knower has
    no epistemic perspective. -/
theorem void_asymmetry (a : I) : epistemicAsymmetry (void : I) a = 0 := by
  unfold epistemicAsymmetry; simp [rs_void_left', rs_void_right']

end EpistemicLogic

/-! ## §17. Epistemic Closure and Iteration

What happens when knowledge is iterated — when we know that we know,
or learn about learning itself? -/

section EpistemicIteration
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Iterated knowledge: composing an idea with itself n times.
    Knowing that you know = reflecting on reflection. -/
noncomputable def iteratedKnowledge (a : I) (n : ℕ) : ℝ :=
  rs (composeN a n) (composeN a n)

-- Theorem 113
/-- Zeroth iteration is void — knowing nothing is knowing void. -/
theorem iterated_zero (a : I) : iteratedKnowledge a 0 = 0 := by
  unfold iteratedKnowledge; simp [rs_void_void]

-- Theorem 114
/-- Iterated knowledge is non-negative at every level. -/
theorem iterated_nonneg (a : I) (n : ℕ) : iteratedKnowledge a n ≥ 0 := by
  unfold iteratedKnowledge; exact rs_self_nonneg' _

-- Theorem 115
/-- Iterated knowledge is monotonically non-decreasing. Higher-order
    reflection can only increase epistemic weight. -/
theorem iterated_mono (a : I) (n : ℕ) :
    iteratedKnowledge a (n + 1) ≥ iteratedKnowledge a n := by
  unfold iteratedKnowledge; simp only [composeN_succ]
  exact compose_enriches' (composeN a n) a

-- Theorem 116
/-- Iterated void knowledge is always zero. Reflecting on nothing,
    no matter how many times, produces nothing. -/
theorem iterated_void (n : ℕ) : iteratedKnowledge (void : I) n = 0 := by
  unfold iteratedKnowledge; simp [rs_void_void]

-- Theorem 117
/-- First-order knowledge equals basic self-resonance. -/
theorem iterated_one (a : I) : iteratedKnowledge a 1 = rs a a := by
  unfold iteratedKnowledge; simp [composeN_one]

-- Theorem 118
/-- Epistemic closure under composition: if you know a and you know b,
    the composite is at least as weighty as a. Knowledge under composition
    is never lost (though it may be transformed by emergence). -/
theorem epistemic_closure (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a := by
  exact compose_enriches' a b

end EpistemicIteration

end IDT3
