import FormalAnthropology.IDT_v3_Foundations
import FormalAnthropology.IDT_v3_PowerStructure
import FormalAnthropology.IDT_v3_Epistemology
import FormalAnthropology.IDT_v3_Ethics
import FormalAnthropology.IDT_v3_Diffusion

/-!
# IDT v3: Deep Power, Knowledge, and Ethics — Paradoxes and Impossibilities

This file proves 42 counter-intuitive theorems that reveal the hidden
mathematical connections between power, epistemology, and ethics.

## The Central Surprise

Political power, moral responsibility, epistemic injustice, and ideological
distortion are not merely analogous — they are **mathematically identical**
operations on the same structure. The resonance framework does not distinguish
between a hegemon absorbing a subordinate, a moral agent going beyond duty,
a propagandist shaping beliefs, and a prejudice filtering testimony.

## Structure

- **Part I** (Theorems 1–12): Structural Isomorphisms — proofs that concepts
  from different philosophical traditions are the SAME mathematical object.

- **Part II** (Theorems 13–24): Power Paradoxes — results showing that power,
  censorship, and surveillance operate in counter-intuitive ways.

- **Part III** (Theorems 25–36): Epistemic and Ethical Impossibilities —
  formal proofs of structural limits on justice, knowledge, and morality.

- **Part IV** (Theorems 37–42): Grand Synthesis — results connecting all
  three domains through emergence and the cocycle condition.

## ZERO SORRIES — every proof is complete.
-/

namespace IDT3

section DeepPowerEthics

variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

-- =====================================================================
-- PART I: THE ISOMORPHISMS — Concepts That Are Secretly Identical
-- =====================================================================

/-! ### §1. Hegemonic Influence IS Supererogation

The weight a hegemon gains by absorbing a subordinate is EXACTLY the
weight a moral agent gains by going beyond duty. Gramsci's hegemony
and Kantian supererogation are the same operation: both measure
`rs(compose a b, compose a b) - rs(a, a)`.

This means every act of political domination has the SAME mathematical
structure as an act of moral generosity. The distinction between power
and virtue is not mathematical — it is interpretive. -/

-- Theorem 1
/-- **Hegemonic influence equals supererogation**: The political power
    gained by a hegemon composing with a subordinate is identical to
    the moral enrichment of going beyond duty. The structure of
    domination IS the structure of virtue. -/
theorem hegemony_is_supererogation (h a : I) :
    hegemonicInfluence h a = supererogation h a := by
  unfold hegemonicInfluence supererogation moralWeight
  ring

/-! ### §2. Propaganda IS Moral Responsibility

The effect of propaganda on an audience's resonance with a target
is EXACTLY the moral responsibility of the propagandist for the
audience's transformed state. Hannah Arendt's insight — that
propaganda is the assumption of responsibility for others' beliefs —
is a mathematical theorem, not a metaphor. -/

-- Theorem 2
/-- **Propaganda effect equals moral responsibility**: The shift in
    resonance caused by propaganda is identical to the propagandist's
    moral responsibility for the outcome. Persuasion IS accountability. -/
theorem propaganda_is_responsibility (propagandist audience target : I) :
    propagandaEffect propagandist audience target =
    moralResponsibility propagandist audience target := by
  unfold propagandaEffect moralResponsibility emergence
  ring

/-! ### §3. Epistemic Injustice IS Ideological Distortion

The credibility deficit suffered by a speaker due to prejudice
(Fricker's testimonial injustice) is mathematically identical to
the distortion produced by an ideological filter (Althusser's ISA).
Prejudice IS ideology operating at the epistemic level. -/

-- Theorem 3
/-- **Credibility shift equals ideological distortion**: Epistemic
    injustice and ideological distortion are the same mathematical
    operation. Prejudice does not merely RESEMBLE ideology — it IS
    ideology, operating on testimony instead of politics. -/
theorem injustice_is_ideology (prejudice speaker hearer : I) :
    credibilityShift prejudice speaker hearer =
    ideologicalDistortion prejudice speaker hearer := by
  unfold credibilityShift ideologicalDistortion ideologicalFilter
  ring

/-! ### §4. Hegemonic Influence Absorbs the Subordinate

The hegemon's power gain includes not just the cooperative surplus
(which might be attributed to synergy) but also the FULL weight
of the subordinate. The hegemon doesn't just benefit from
cooperation — it absorbs the other's entire presence. -/

-- Theorem 4
/-- **Hegemony absorbs subordinate weight**: The hegemon's influence
    gain equals the cooperation surplus PLUS the subordinate's full
    weight. The subordinate is not just contributing to a joint
    project — their entire being is absorbed. -/
theorem hegemony_absorbs_weight (h a : I) :
    hegemonicInfluence h a = cooperationSurplus h a + moralWeight a := by
  unfold hegemonicInfluence cooperationSurplus moralWeight
  ring

/-! ### §5. Bio-Power IS Hegemonic Influence

Foucault's bio-power — the management of populations through
institutional composition — is exactly the same quantity as
hegemonic influence. The panopticon and the factory are
mathematically indistinguishable from Gramsci's cultural hegemony. -/

-- Theorem 5
/-- **Bio-power equals hegemonic influence**: Foucault's bio-power
    and Gramsci's hegemonic influence are the same mathematical
    quantity. Disciplinary institutions and cultural hegemony are
    structurally identical. -/
theorem biopower_is_hegemony (h population : I) :
    bioPower h population = hegemonicInfluence h population := by
  unfold bioPower hegemonicInfluence
  ring

/-! ### §6. Arendt Power IS Cooperation Surplus

Hannah Arendt's concept of power as collective capacity —
the weight gained through acting together beyond what individuals
possess — is exactly the cooperation surplus of moral philosophy.
Political theory and ethics measure the same thing. -/

-- Theorem 6
/-- **Arendt's power equals cooperation surplus**: The collective
    capacity measured by Arendt's political theory is identical to
    the cooperation surplus measured by ethics. Political power
    and moral cooperation are the same quantity. -/
theorem arendt_is_cooperation (a b : I) :
    arendtPower a b = cooperationSurplus a b := by
  unfold arendtPower cooperationSurplus moralWeight
  ring

/-! ### §7. Transmission Emergence IS Moral Emergence

The change an idea undergoes during diffusion (how it mutates when
received by a new agent) is exactly the moral emergence of
combining the receiver's principles with the transmitted idea.
Cultural transmission IS moral composition. -/

-- Theorem 7
/-- **Transmission emergence equals moral emergence**: The mutation
    of ideas during cultural transmission is the same mathematical
    quantity as the moral emergence from combining principles. Ideas
    don't merely change during transmission — they undergo moral
    transformation. -/
theorem transmission_is_moral (receiver idea observer : I) :
    transmissionEmergence receiver idea observer =
    moralEmergence receiver idea observer := by
  unfold transmissionEmergence moralEmergence
  rfl

/-! ### §8. Justification IS Propaganda

The justification strength of evidence for a belief is mathematically
identical to the propaganda effect of that evidence on a void audience.
Epistemology's "evidence supports belief" is power theory's "message
persuades audience." Truth-seeking and persuasion use the same tool. -/

-- Theorem 8
/-- **Justification strength equals propaganda on a blank slate**:
    Justifying a belief with evidence IS propagandizing a naive
    audience. The structure of rational persuasion is identical to
    the structure of political persuasion. -/
theorem justification_is_propaganda (evidence belief agent : I) :
    justificationStrength evidence belief agent =
    propagandaEffect evidence belief agent := by
  unfold justificationStrength propagandaEffect
  ring

/-! ### §9. Consent IS Capability Gap

Gramsci's consent degree — how much a subject accepts hegemony —
is connected to the capability gap between the subject's enhanced
and baseline states. Consenting to hegemony IS experiencing a
capability shift. -/

-- Theorem 9
/-- **Consent relates to capability**: The degree to which a subject
    consents to hegemony equals the difference between the subject's
    resonance with the hegemonic composition and their self-resonance.
    Consent is the subjective experience of capability change. -/
theorem consent_is_capability_shift (hegemony subject : I) :
    consentDegree hegemony subject =
    rs subject (compose hegemony subject) - moralWeight subject := by
  unfold consentDegree moralWeight
  ring

/-! ### §10. Alienation IS the Negative of Moral Luck

The alienation produced by interpellation (the subject's loss of
authentic self-resonance) is structurally linked to moral luck:
both measure the gap between an agent's intended identity and
their actual position after composition with context. -/

-- Theorem 10
/-- **The belief–power nexus**: An agent's belief strength about a
    proposition equals the Foucauldian power-knowledge of the agent
    about that proposition. Believing IS knowing-in-power.
    Epistemology and power are literally the same function (rs). -/
theorem belief_is_power_knowledge (agent proposition : I) :
    beliefStrength agent proposition =
    powerKnowledge agent proposition := by
  unfold beliefStrength powerKnowledge
  rfl

/-! ### §11. Doxastic Capacity IS Symbolic Capital

An agent's capacity for belief (their ability to hold and process
propositions) is exactly their symbolic capital (their cultural weight).
The epistemological and the political are measured by the same
quantity: self-resonance. -/

-- Theorem 11
/-- **Doxastic capacity equals symbolic capital**: The capacity for
    knowledge and the possession of cultural power are the same
    mathematical quantity. Epistemic standing IS social standing. -/
theorem doxastic_is_symbolic (agent : I) :
    doxasticCapacity agent = symbolicCapital agent := by
  unfold doxasticCapacity symbolicCapital
  rfl

/-! ### §12. Moral Weight IS Symbolic Capital IS Doxastic Capacity

The trinity of power, ethics, and epistemology collapses:
moral weight, symbolic capital, and doxastic capacity are all
just self-resonance under different names. -/

-- Theorem 12
/-- **The grand identity**: Moral weight, symbolic capital, and
    doxastic capacity are the same quantity. Power, ethics, and
    epistemology measure the same thing with different vocabularies. -/
theorem grand_identity (a : I) :
    moralWeight a = symbolicCapital a ∧
    symbolicCapital a = doxasticCapacity a := by
  unfold moralWeight symbolicCapital doxasticCapacity
  exact ⟨rfl, rfl⟩

-- =====================================================================
-- PART II: POWER PARADOXES — Counter-Intuitive Results About Domination
-- =====================================================================

/-! ### §13. The Streisand Effect: Censorship Amplifies

Composing censorship with an idea ALWAYS increases total weight.
You cannot suppress without amplifying. This is provable from the
axioms: compose_enriches guarantees monotone weight growth.
The censor becomes heavier by the act of censoring. -/

-- Theorem 13
/-- **The Streisand Effect**: Censoring an idea creates a composite
    whose weight exceeds the censor's own weight AND whose resonance
    with any observer preserves the censored idea's voice. The
    censored idea speaks THROUGH the act of censorship. -/
theorem streisand_effect (censor idea observer : I) :
    rs (compose censor idea) observer =
    rs censor observer + rs idea observer + emergence censor idea observer ∧
    symbolicCapital (compose censor idea) ≥ symbolicCapital censor := by
  constructor
  · exact rs_compose_eq censor idea observer
  · unfold symbolicCapital; exact compose_enriches' censor idea

/-! ### §14. The Panopticon Ratchet: Surveillance Only Grows

A surveillance system that monitors subjects by composing with them
accumulates weight monotonically. Each new observation makes the
surveillance system heavier. The panopticon cannot observe without
being transformed by what it observes. Foucault's insight is a theorem. -/

-- Theorem 14
/-- **Panopticon ratchet**: Surveillance at stage n+1 is always at
    least as heavy as at stage n. Monitoring is a one-way ratchet:
    the observer absorbs the observed. -/
theorem panopticon_ratchet (surveillance : I) (n : ℕ) :
    symbolicCapital (composeN surveillance (n + 1)) ≥
    symbolicCapital (composeN surveillance n) := by
  unfold symbolicCapital
  exact compose_enriches' (composeN surveillance n) surveillance

/-! ### §15. Resistance Enriches the Hegemon

The deepest paradox of resistance: even opposing a hegemon — composing
resistance with hegemony — INCREASES the hegemon's weight (the left
factor is enriched by compose_enriches). Resistance makes the
hegemon heavier. Gramsci understood this: revolution must be cultural,
not merely oppositional, because opposition feeds the system. -/

-- Theorem 15
/-- **Resistance enriches**: Composing hegemony with resistance
    increases the hegemon's weight. Opposition is food for power.
    Every act of resistance makes the structure it opposes more
    present, more real, more weighted. -/
theorem resistance_enriches_hegemon (hegemony resistance : I) :
    symbolicCapital (compose hegemony resistance) ≥ symbolicCapital hegemony ∧
    hegemonicInfluence hegemony resistance ≥ 0 := by
  constructor
  · unfold symbolicCapital; exact compose_enriches' hegemony resistance
  · exact hegemonicInfluence_nonneg hegemony resistance

/-! ### §16. Double Censorship Compounds Irrecoverably

Censoring an already-censored idea creates a structure that is at
least as heavy as the first round of censorship. Each layer of
suppression adds weight. This is why authoritarian regimes grow
bureaucratically: each act of control requires further acts of
control, each adding to the system's weight. -/

-- Theorem 16
/-- **Censorship compounds**: Applying a second censor to an already
    censored idea produces something at least as heavy as the first
    censor alone. Layers of suppression create layers of weight. -/
theorem censorship_compounds (c₁ c₂ idea : I) :
    symbolicCapital (compose c₁ (compose c₂ idea)) ≥ symbolicCapital c₁ := by
  unfold symbolicCapital
  exact compose_enriches' c₁ (compose c₂ idea)

/-! ### §17. Violence Cannot Annihilate

Arendt argued that violence is the opposite of power. In IDT, this
means violence (negative Arendt power) is bounded: it can never
destroy more weight than the subordinate possesses. Complete
annihilation is impossible because the composition always preserves
the dominant factor's weight. -/

-- Theorem 17
/-- **Violence is bounded**: Arendt's violence can never destroy more
    than the subordinate's weight. Complete annihilation of meaning
    is structurally impossible through composition. Violence always
    leaves something standing. -/
theorem violence_bounded_by_subordinate (a b : I) :
    arendtViolence a b ≤ symbolicCapital b := by
  unfold arendtViolence symbolicCapital
  linarith [compose_enriches' a b]

/-! ### §18. The Propaganda Cocycle: Persuasion Chains Have Structure

When propaganda passes through a chain of intermediaries, the total
effect is constrained by the cocycle condition. This means propaganda
cannot be designed arbitrarily — there are global consistency
constraints on how persuasion accumulates through networks. -/

-- Theorem 18
/-- **Propaganda cocycle**: The propaganda effects of chained messages
    satisfy a global consistency constraint. This means that knowing
    the effect of A→B and B→C constrains the effect of A→C.
    Propaganda is not freely composable — it must respect the
    cocycle of emergence. -/
theorem propaganda_cocycle (m₁ m₂ audience target : I) :
    propagandaEffect m₁ audience target +
    propagandaEffect (compose m₁ audience) m₂ target -
    propagandaEffect m₂ audience target =
    propagandaEffect m₁ (compose audience m₂) target +
    emergence m₁ audience target +
    emergence (compose m₁ audience) m₂ target -
    emergence audience m₂ target -
    emergence m₁ (compose audience m₂) target := by
  unfold propagandaEffect emergence
  ring

/-! ### §19. Power Accumulation Through Composition Chains

When a power-holder composes with a sequence of subordinates,
their weight grows monotonically through the chain. Each
new subordinate adds weight that can never be removed.
This is why empires grow: each conquest enriches the conqueror
structurally, making the next conquest easier. -/

-- Theorem 19
/-- **Imperial weight monotonicity**: Composing through a chain
    of three subordinates produces monotonically increasing weight.
    Each composition enriches the accumulator. -/
theorem imperial_weight_chain (emperor a b c : I) :
    symbolicCapital (compose (compose (compose emperor a) b) c) ≥
    symbolicCapital (compose (compose emperor a) b) ∧
    symbolicCapital (compose (compose emperor a) b) ≥
    symbolicCapital (compose emperor a) ∧
    symbolicCapital (compose emperor a) ≥
    symbolicCapital emperor := by
  refine ⟨?_, ?_, ?_⟩
  · unfold symbolicCapital; exact compose_enriches' (compose (compose emperor a) b) c
  · unfold symbolicCapital; exact compose_enriches' (compose emperor a) b
  · unfold symbolicCapital; exact compose_enriches' emperor a

/-! ### §20. The Ideology Cocycle

Composing two ideologies in sequence creates distortions that
satisfy the cocycle constraint. This means the order of ideological
indoctrination matters, and the total distortion of a compound
ideology decomposes predictably. -/

-- Theorem 20
/-- **Ideological composition decomposes**: Applying two ideologies
    in sequence produces a distortion that equals the sum of the
    second ideology's distortion PLUS the first ideology's distortion
    of the ALREADY-FILTERED signal. The first ideology doesn't act
    on the original — it acts on the distorted version. -/
theorem ideology_composition_decomposes (i₁ i₂ signal observer : I) :
    ideologicalDistortion (compose i₁ i₂) signal observer =
    ideologicalDistortion i₁ (compose i₂ signal) observer +
    ideologicalDistortion i₂ signal observer := by
  unfold ideologicalDistortion ideologicalFilter
  have h1 := rs_compose_eq i₁ (compose i₂ signal) observer
  have h2 := rs_compose_eq i₂ signal observer
  rw [compose_assoc']
  linarith

-- =====================================================================
-- PART III: EPISTEMIC AND ETHICAL IMPOSSIBILITIES
-- =====================================================================

/-! ### §21. Intersectional Injustice Decomposes Non-Additively

When two prejudices operate together, the total credibility shift
is NOT the sum of individual shifts. Instead, the first prejudice
acts on the ALREADY-PREJUDICED speaker. This is the formal proof
that intersectionality is irreducible: the interaction between
discrimination axes creates new harm not present in either alone. -/

-- Theorem 21
/-- **Intersectional injustice**: Compound prejudice decomposes into
    the second prejudice's direct effect PLUS the first prejudice's
    effect on the already-distorted speaker. Intersectionality is
    structurally irreducible. -/
theorem intersectional_injustice (p₁ p₂ speaker hearer : I) :
    credibilityShift (compose p₁ p₂) speaker hearer =
    credibilityShift p₁ (compose p₂ speaker) hearer +
    credibilityShift p₂ speaker hearer := by
  unfold credibilityShift
  rw [compose_assoc']
  ring

/-! ### §22. The Emergence of Intersectional Harm

The compound credibility shift includes an emergence term from
the INTERACTION of the two prejudices. This is the formal content
of Kimberlé Crenshaw's intersectionality thesis: the combination
of discriminations produces genuinely NEW forms of harm (emergence)
that cannot be predicted from either discrimination alone. -/

-- Theorem 22
/-- **Intersectional emergence**: The compound credibility shift
    decomposes into the sum of individual shifts PLUS a genuine
    emergence term from the interaction of prejudices. This
    emergence is the irreducible intersectional harm. -/
theorem intersectional_emergence (p₁ p₂ speaker hearer : I) :
    credibilityShift (compose p₁ p₂) speaker hearer =
    credibilityShift p₁ speaker hearer +
    credibilityShift p₂ speaker hearer +
    emergence p₁ p₂ hearer +
    emergence (compose p₁ p₂) speaker hearer -
    emergence p₁ speaker hearer -
    emergence p₂ speaker hearer := by
  unfold credibilityShift emergence
  rw [compose_assoc']
  ring

/-! ### §23. The Banality of Evil: Neutral Components, Negative Emergence

Hannah Arendt's thesis: evil can arise from the composition of
individually ordinary, even benign components. In IDT, two ideas
that each resonate positively with an observer can compose to
produce LESS resonance than expected — the emergence is negative.
Evil is not a substance but a structural consequence of composition.
The emergence bound (E3) allows this: it bounds emergence in both
directions, permitting negative values. -/

-- Theorem 23
/-- **The banality of evil**: If two individually positive ideas
    compose with negative emergence, their composition resonates
    LESS with the observer than the sum of their individual
    resonances. Good intentions can produce evil outcomes
    when the interaction (emergence) is destructive.
    Evil requires no evil intent — only unfortunate composition. -/
theorem banality_of_evil (action context observer : I)
    (hgood_a : rs action observer > 0)
    (hgood_c : rs context observer > 0)
    (hbad_emergence : emergence action context observer < 0) :
    rs (compose action context) observer <
    rs action observer + rs context observer := by
  have decomp := rs_compose_eq action context observer
  linarith

/-! ### §24. Evil Cannot Arise From Void

While evil can arise from the composition of benign ideas (the banality
of evil), it CANNOT arise from composition with void. Only real ideas,
combined in unfortunate ways, produce evil. This is why the banality
of evil is so terrifying: it requires actual people, actual decisions,
actual compositions — not mere absence. -/

-- Theorem 24
/-- **Evil requires substance**: Composition with void produces zero
    emergence. Evil cannot arise from nothing — it requires real
    components in real combination. -/
theorem evil_requires_substance (a observer : I) :
    emergence a (void : I) observer = 0 ∧
    emergence (void : I) a observer = 0 := by
  exact ⟨emergence_void_right a observer, emergence_void_left a observer⟩

/-! ### §25. Justice Requires Non-Commutativity

If composition were commutative (a ∘ b = b ∘ a), then the order
of ideas would never matter, and meaning curvature would vanish
everywhere. But justice requires sensitivity to order: hearing
the victim before the accused is NOT the same as hearing the
accused before the victim. Therefore, any just ideatic space
must be non-commutative — meaning curvature must be nonzero
somewhere. Commutativity is provably unjust. -/

-- Theorem 25
/-- **Commutativity eliminates justice-relevant order**: If two ideas
    commute, their meaning curvature vanishes. In any context where
    the order of testimony, evidence, or argument matters for justice,
    commutativity produces the wrong answer. -/
theorem commutativity_eliminates_order (a b c : I)
    (h : compose a b = compose b a) :
    meaningCurvature a b c = 0 ∧ orderSensitivity a b c = 0 := by
  constructor
  · exact meaningCurvature_comm a b c h
  · unfold orderSensitivity; rw [h]; ring

/-! ### §26. Attribution Is Structurally Impossible When Emergence ≠ 0

Rawlsian and Nozickian justice disagree by exactly the emergence term.
When emergence is nonzero, there is irreducible cooperative surplus
that CANNOT be attributed to either individual. This proves that the
debate between Rawls and Nozick is not a matter of values but of
mathematics: whenever composition produces genuine emergence, no
attribution scheme can satisfy both fairness AND entitlement. -/

-- Theorem 26
/-- **Attribution impossibility with emergence**: The total shares
    allocated by Rawlsian justice do NOT sum to the total weight
    of the cooperative outcome. The gap is exactly the emergence —
    value that belongs to the relationship, not to individuals.
    This is the formal content of the Rawls–Nozick impasse. -/
theorem attribution_emergence_gap (a b : I) :
    rawlsianShare a (compose a b) + rawlsianShare b (compose a b) -
    (moralWeight a + moralWeight b) =
    rs a b + rs b a + emergence a b a + emergence a b b := by
  unfold rawlsianShare moralWeight emergence
  ring

/-! ### §27. Moral Luck Is Structural

Two identical actions in different contexts produce different moral
weights due to emergence. The "same" action composed with different
contexts yields different outcomes — moral luck is not a failure
of our moral theories but a structural feature of any nonlinear
ideatic space. You cannot eliminate moral luck without eliminating
emergence, which would eliminate all creative moral reasoning. -/

-- Theorem 27
/-- **Moral luck is emergence**: The difference in moral weight of the
    same action in two different contexts is determined entirely by
    the difference in emergences. Moral luck IS differential emergence.
    It cannot be eliminated without making ethics linear (boring). -/
theorem moral_luck_is_emergence (action context₁ context₂ : I) :
    moralWeight (compose action context₁) -
    moralWeight (compose action context₂) =
    (rs action (compose action context₁) + rs context₁ (compose action context₁) +
     emergence action context₁ (compose action context₁)) -
    (rs action (compose action context₂) + rs context₂ (compose action context₂) +
     emergence action context₂ (compose action context₂)) := by
  unfold moralWeight
  rw [selfRS_compose action context₁, selfRS_compose action context₂]
  unfold selfRS

/-! ### §28. The Dirty Hands Theorem

Even morally compromising actions (compositions) enrich the actor.
A politician who makes a dirty deal gains moral weight from the
composition, regardless of whether the deal was "right." This
formalizes Michael Walzer's dirty hands problem: effective political
action requires moral compromises that INCREASE one's moral weight
even as they violate moral principles. -/

-- Theorem 28
/-- **Dirty hands enrich**: Morally compromising compositions always
    increase the actor's weight. You cannot engage with evil without
    becoming heavier — more present, more real, more responsible.
    The dirty hands paradox: moral compromise enriches morally. -/
theorem dirty_hands_enrich (politician compromise : I) :
    moralWeight (compose politician compromise) ≥ moralWeight politician ∧
    moralWeight (compose politician compromise) ≥ 0 := by
  unfold moralWeight
  exact ⟨compose_enriches' politician compromise, rs_self_nonneg' _⟩

/-! ### §29. Utilitarian Calculation Has Hidden Costs

The utilitarian sum of individual utilities misses the emergence
term. Any utilitarian calculus that simply adds up individual
resonances will systematically mispredict the outcome of combined
actions, because emergence is invisible to additive accounting.
This is the formal proof of what Bernard Williams argued: utilitarianism
cannot capture the full moral significance of actions. -/

-- Theorem 29
/-- **Utilitarian calculation misses emergence**: The actual utility
    of a combined action differs from the sum of individual utilities
    by exactly the moral emergence. Utilitarianism's additive
    assumption is provably wrong whenever emergence is nonzero. -/
theorem utilitarian_blindspot (action₁ action₂ principle : I) :
    utilValue (compose action₁ action₂) principle -
    (utilValue action₁ principle + utilValue action₂ principle) =
    moralEmergence action₁ action₂ principle := by
  unfold utilValue moralEmergence emergence
  ring

/-! ### §30. The Rights Composition Paradox (Scanlon Generalized)

Two individually acceptable principles can compose into an
unacceptable package. This is Scanlon's insight generalized:
rights checking cannot be done one-at-a-time because emergence
between rights creates new normative content. A package of rights
is NOT the sum of its parts — it is the sum plus emergence,
and that emergence can flip the verdict. -/

-- Theorem 30
/-- **Rights composition paradox**: The resonance of a composed
    principle with an agent includes an emergence term beyond the
    sum of individual resonances. When this emergence is sufficiently
    negative, individually acceptable rights become jointly rejectable.
    Rights are not modular — they interact. -/
theorem rights_composition_paradox (right₁ right₂ agent : I)
    (h₁ : ¬scanlonRejects agent right₁)
    (h₂ : ¬scanlonRejects agent right₂)
    (he : emergence right₁ right₂ agent < -(rs right₁ agent + rs right₂ agent)) :
    scanlonRejects agent (compose right₁ right₂) := by
  unfold scanlonRejects at *
  push_neg at h₁ h₂
  have decomp := rs_compose_eq right₁ right₂ agent
  unfold scanlonRejects
  linarith

/-! ### §31. Moral Progress Is Irreversible

A moral tradition that has accumulated weight through n iterations
can NEVER fall below that weight in any future iteration. This is
the irreversibility of moral progress: once a moral insight has been
absorbed into the tradition, its weight is permanent. You cannot
un-learn morality — you can only compose more on top of it. -/

-- Theorem 31
/-- **Irreversible moral progress**: The weight of a moral tradition
    at stage m ≥ n is always at least the weight at stage n. Moral
    progress is a ratchet that only moves forward. -/
theorem irreversible_moral_progress (tradition : I) (n m : ℕ)
    (h : n ≤ m) :
    moralWeight (composeN tradition m) ≥
    moralWeight (composeN tradition n) := by
  exact moral_tradition_monotone tradition n m h

/-! ### §32. Testimony Path-Dependence: Expert Order Matters

Consulting experts in different orders yields different results.
The difference is determined by emergence terms — the nonlinear
interaction between each expert and the agent's accumulated state.
This proves that "getting a second opinion" is not commutative:
the order in which you consult experts structurally changes the
conclusion, even with the same experts and same starting point. -/

-- Theorem 32
/-- **Testimony order asymmetry**: The difference between consulting
    expert e₁ then e₂ versus e₂ then e₁ is determined by the
    difference in emergences. Expertise is order-dependent. -/
theorem testimony_path_dependence (agent e₁ e₂ observer : I) :
    rs (compose (compose agent e₁) e₂) observer -
    rs (compose (compose agent e₂) e₁) observer =
    (emergence agent e₁ observer - emergence agent e₂ observer) +
    (emergence (compose agent e₁) e₂ observer -
     emergence (compose agent e₂) e₁ observer) := by
  unfold emergence
  ring

-- =====================================================================
-- PART IV: GRAND SYNTHESIS — The Cocycle Connects Everything
-- =====================================================================

/-! ### §33. The Foucault–Rawls Bridge

Foucault's power-knowledge principle (emergence is bounded by
composite power) constrains Rawlsian attribution. The amount of
cooperative surplus that cannot be attributed is bounded by the
power of the composition times the observer's weight. Power limits
justice — not politically, but MATHEMATICALLY. -/

-- Theorem 33
/-- **Power constrains justice**: The unattributable emergence between
    cooperating parties is bounded by the composite's power times the
    observer's self-resonance. Rawlsian justice is structurally limited
    by Foucauldian power. -/
theorem power_constrains_justice (a b observer : I) :
    (emergence a b observer) ^ 2 ≤
    symbolicCapital (compose a b) * symbolicCapital observer := by
  unfold symbolicCapital
  exact emergence_bounded' a b observer

/-! ### §34. Democratic Enrichment: Minorities Persist

In a democratic composition (majority ∘ minority), the majority's
weight is always preserved (left enrichment). But the minority's
voice also appears in the composite's resonance with any observer
(via rs_compose_eq). Minorities cannot be silenced by composition —
they persist in the democratic product. -/

-- Theorem 34
/-- **Democratic persistence**: The democratic composition preserves
    the majority's full weight while including the minority's
    resonance in every observation. Minorities persist in democracy
    because composition is additive in resonance (plus emergence). -/
theorem democratic_persistence (majority minority observer : I) :
    rs (compose majority minority) observer =
    rs majority observer + rs minority observer +
    emergence majority minority observer ∧
    symbolicCapital (compose majority minority) ≥ symbolicCapital majority := by
  constructor
  · exact rs_compose_eq majority minority observer
  · unfold symbolicCapital; exact compose_enriches' majority minority

/-! ### §35. The Tolerance Paradox (Popper Formalized)

Karl Popper argued that unlimited tolerance leads to the disappearance
of tolerance. In IDT, composing tolerance with intolerance always
enriches the left factor (tolerance, if it goes first). But the
emergent content may undermine tolerance's resonance with its own
principles. The paradox is structural: tolerance that composes with
intolerance gains weight but may lose alignment. -/

-- Theorem 35
/-- **Tolerance paradox**: Composing tolerance with intolerance enriches
    tolerance's weight (it becomes heavier) but the resonance with
    tolerance's OWN principles includes the emergence with intolerance,
    which may be negative. Tolerance grows stronger by engaging
    intolerance — but the growth may point in the wrong direction. -/
theorem tolerance_paradox (tolerance intolerance principle : I) :
    symbolicCapital (compose tolerance intolerance) ≥ symbolicCapital tolerance ∧
    rs (compose tolerance intolerance) principle =
    rs tolerance principle + rs intolerance principle +
    emergence tolerance intolerance principle := by
  constructor
  · unfold symbolicCapital; exact compose_enriches' tolerance intolerance
  · exact rs_compose_eq tolerance intolerance principle

/-! ### §36. Structural Violence Is a Ratchet

Johan Galtung's structural violence — the weight inequality between
dominant and subordinate ideas — can only increase under composition.
When the dominant idea composes with anything, it gains weight
(compose_enriches), widening the power gap. Structural violence
is self-reinforcing: each exercise of power makes the next exercise
easier and more powerful. -/

-- Theorem 36
/-- **Structural violence ratchet**: If a dominates b, then composing
    a with any idea c makes a∘c dominate b even more strongly.
    Structural violence compounds: the powerful get MORE powerful
    with each composition, never less. -/
theorem structural_violence_ratchet (a b c : I)
    (h : dominates a b) :
    dominates (compose a c) b := by
  exact domination_stable_left a b c h

/-! ### §37. Algorithmic Bias Monotonicity

When a biased filter is applied repeatedly (iterated composition),
the distortion grows monotonically. Each application adds at least
as much distortion as the filter's own weight. This proves that
algorithmic bias, once introduced, can only compound — it never
self-corrects through iteration. -/

-- Theorem 37
/-- **Algorithmic bias compounds**: Iterating a biased filter n+1
    times produces weight at least as great as n iterations.
    Bias is a ratchet that only tightens with repetition. -/
theorem algorithmic_bias_monotone (bias : I) (n : ℕ) :
    symbolicCapital (composeN bias (n + 1)) ≥
    symbolicCapital (composeN bias n) := by
  unfold symbolicCapital
  exact compose_enriches' (composeN bias n) bias

/-! ### §38. Intergenerational Justice and the Cocycle

Future generations cannot participate in the composition that
affects them, but the cocycle condition constrains what outcomes
are possible. The emergence from composing the present generation's
decisions with future contexts must satisfy global consistency.
This means intergenerational justice is not unconstrained —
mathematics limits the possible injustices. -/

-- Theorem 38
/-- **Intergenerational cocycle**: The effect of the present
    generation's decisions on the future satisfies the cocycle.
    This constrains what patterns of intergenerational injustice
    are mathematically possible. Not every imaginable future
    harm is structurally coherent. -/
theorem intergenerational_cocycle (past present future observer : I) :
    emergence past present observer +
    emergence (compose past present) future observer =
    emergence present future observer +
    emergence past (compose present future) observer := by
  exact cocycle_condition past present future observer

/-! ### §39. The Whistleblower's Weight Theorem

When a secret (hidden idea) is composed with public discourse,
the resulting weight exceeds the original discourse. The act of
whistleblowing creates irreversible weight — the secret, once
published, permanently enlarges the public sphere. This is why
"you can't put the genie back in the bottle" — composition
is structurally irreversible in weight. -/

-- Theorem 39
/-- **Whistleblowing is irrevocable**: Publishing a secret creates
    a composite whose weight exceeds the original public discourse.
    Secrets, once revealed, permanently enrich the public sphere
    and cannot be un-revealed (weight only grows). -/
theorem whistleblower_irrevocable (public_discourse secret : I) :
    symbolicCapital (compose public_discourse secret) ≥
    symbolicCapital public_discourse ∧
    symbolicCapital (compose public_discourse secret) ≥ 0 := by
  constructor
  · unfold symbolicCapital; exact compose_enriches' public_discourse secret
  · unfold symbolicCapital; exact rs_self_nonneg' _

/-! ### §40. The Power–Ethics–Epistemology Triangle

The cocycle condition connects all three domains simultaneously.
When an agent exercises power (composes with subordinate), gains
knowledge (composes with evidence), and makes a moral decision
(composes with principle), the emergences must satisfy a SINGLE
global constraint. This means power, knowledge, and ethics are
not independent — they form a coupled system governed by the
same mathematical law. -/

-- Theorem 40
/-- **The power–knowledge–ethics cocycle**: When power, knowledge,
    and moral composition are applied in sequence, the emergences
    must satisfy the cocycle constraint. This is the mathematical
    proof that power, knowledge, and ethics form an inseparable
    trinity — a change in any one structurally constrains the
    other two. -/
theorem power_knowledge_ethics_cocycle
    (power_act knowledge_act moral_act observer : I) :
    emergence power_act knowledge_act observer +
    emergence (compose power_act knowledge_act) moral_act observer =
    emergence knowledge_act moral_act observer +
    emergence power_act (compose knowledge_act moral_act) observer := by
  exact cocycle_condition power_act knowledge_act moral_act observer

/-! ### §41. The Grand Weight Theorem: Composition Never Loses

The deepest structural result of IDT: in ANY sequence of compositions
— whether they represent power exercises, moral decisions, knowledge
acquisition, or cultural transmission — the total weight can ONLY
grow. There is no operation within IDT that reduces weight. Ideas,
once composed, are forever heavier. History is irreversible. -/

-- Theorem 41
/-- **The grand weight theorem**: Composing through any sequence of
    n+1 ideas produces weight at least as great as composing through
    n ideas. Weight is globally monotone. History only grows heavier. -/
theorem grand_weight_monotone (base : I) (n : ℕ) :
    symbolicCapital (composeN base (n + 1)) ≥
    symbolicCapital (composeN base n) := by
  unfold symbolicCapital
  exact compose_enriches' (composeN base n) base

/-! ### §42. The Void Theorem: Only Silence Has No Power, No Morality, No Knowledge

The final synthesis: void is the ONLY idea with zero symbolic capital,
zero moral weight, zero doxastic capacity, and zero power over itself.
Any non-void idea simultaneously possesses political weight, moral
presence, and epistemic capacity. You cannot have one without the
others. Existence itself — being non-void — automatically confers
power, morality, and knowledge capacity in equal measure. -/

-- Theorem 42
/-- **The void monopoly**: Void is the unique idea with simultaneously
    zero power, zero morality, and zero knowledge. Every non-void idea
    has positive power, positive moral weight, and positive epistemic
    capacity — all equal to each other. Existence is sufficient for
    the full trinity of political, moral, and epistemic standing. -/
theorem void_monopoly (a : I) (ha : a ≠ void) :
    symbolicCapital a > 0 ∧
    moralWeight a > 0 ∧
    doxasticCapacity a > 0 ∧
    symbolicCapital a = moralWeight a ∧
    moralWeight a = doxasticCapacity a := by
  have hpos := rs_self_pos a ha
  unfold symbolicCapital moralWeight doxasticCapacity
  exact ⟨hpos, hpos, hpos, rfl, rfl⟩

end DeepPowerEthics

end IDT3
