import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Power Structure — Domination, Hegemony, Ideology

Formalizes political and social power through resonance and emergence.
Power is weight differential; hegemony is universal resonance alignment;
ideology is an interpretive filter; propaganda is strategic composition;
resistance is counter-composition. Draws on Gramsci, Foucault, Althusser.

## ZERO SORRIES — every proof is complete.
-/

namespace IDT3

section PowerStructure
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-! ## §1. Power as Weight Differential -/

/-- Power of a over b: the difference in self-resonance (weight).
    More "present" ideas have more power — they command more attention,
    carry more cultural weight, resonate more with themselves. -/
noncomputable def power (a b : I) : ℝ := rs a a - rs b b

/-- Power is antisymmetric: power of a over b = -(power of b over a). -/
theorem power_antisymm (a b : I) : power a b = -power b a := by
  unfold power; ring

/-- An idea has zero power over itself. -/
theorem power_self (a : I) : power a a = 0 := by
  unfold power; ring

/-- Power of void over anything is non-positive (void is weakest). -/
theorem void_powerless (a : I) : power (void : I) a ≤ 0 := by
  unfold power; simp [rs_void_void]; linarith [rs_self_nonneg' a]

/-- Void has zero power against itself. -/
theorem power_void_void : power (void : I) (void : I) = 0 := by
  unfold power; ring

/-- Power transitivity: if a dominates b and b dominates c,
    then a dominates c. Power difference is transitive. -/
theorem power_transitive (a b c : I)
    (hab : power a b ≥ 0) (hbc : power b c ≥ 0) :
    power a c ≥ 0 := by
  unfold power at *; linarith

/-! ## §2. Domination and Subordination -/

/-- a dominates b if a has strictly greater weight. -/
def dominates (a b : I) : Prop := rs a a > rs b b

/-- Domination is transitive. -/
theorem dominates_trans (a b c : I)
    (hab : dominates a b) (hbc : dominates b c) :
    dominates a c := by
  unfold dominates at *; linarith

/-- Domination is irreflexive — nothing dominates itself. -/
theorem dominates_irrefl (a : I) : ¬dominates a a := by
  unfold dominates; linarith

/-- Domination is asymmetric. -/
theorem dominates_asymm (a b : I) (h : dominates a b) : ¬dominates b a := by
  unfold dominates at *; linarith

/-- Non-void ideas dominate void. -/
theorem nonvoid_dominates_void (a : I) (h : a ≠ void) :
    dominates a void := by
  unfold dominates; simp [rs_void_void]; exact rs_self_pos a h

/-- If a dominates b, then a has positive weight. -/
theorem dominates_pos_weight (a b : I) (h : dominates a b) :
    rs a a > 0 := by
  unfold dominates at h; linarith [rs_self_nonneg' b]

/-- Subordination: a is subordinate to b if b dominates a. -/
def subordinate (a b : I) : Prop := dominates b a

/-- Subordination is the reverse of domination. -/
theorem subordinate_iff (a b : I) :
    subordinate a b ↔ dominates b a := Iff.rfl

/-- Composing always produces something that dominates or equals
    the left component. -/
theorem compose_dominates_or_eq_left (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- A domination chain a > b > c implies a > c. -/
theorem domination_chain (a b c : I)
    (h1 : dominates a b) (h2 : dominates b c) :
    dominates a c :=
  dominates_trans a b c h1 h2

/-- If a dominates b, then a ∘ anything still dominates b. -/
theorem domination_stable_left (a b c : I) (h : dominates a b) :
    dominates (compose a c) b := by
  unfold dominates at *; linarith [compose_enriches' a c]

/-- Non-void ideas form a domination hierarchy over void. -/
theorem void_at_bottom (a : I) (h : a ≠ void) :
    dominates a void :=
  nonvoid_dominates_void a h

/-! ## §3. Symbolic Capital (Bourdieu) -/

/-- Symbolic capital: the weight an idea commands.
    Every non-void idea has positive symbolic capital. -/
noncomputable def symbolicCapital (a : I) : ℝ := rs a a

/-- Symbolic capital is non-negative. -/
theorem symbolicCapital_nonneg (a : I) : symbolicCapital a ≥ 0 := by
  unfold symbolicCapital; exact rs_self_nonneg' a

/-- Symbolic capital of void is zero. -/
theorem symbolicCapital_void : symbolicCapital (void : I) = 0 := by
  unfold symbolicCapital; exact rs_void_void

/-- Non-void ideas have positive symbolic capital. -/
theorem symbolicCapital_pos (a : I) (h : a ≠ void) :
    symbolicCapital a > 0 := by
  unfold symbolicCapital; exact rs_self_pos a h

/-- Composition never decreases symbolic capital of the left factor. -/
theorem symbolicCapital_compose_left (a b : I) :
    symbolicCapital (compose a b) ≥ symbolicCapital a := by
  unfold symbolicCapital; exact compose_enriches' a b

/-- The only idea with zero symbolic capital is void. -/
theorem zero_capital_is_void (a : I) (h : symbolicCapital a = 0) :
    a = void := by
  unfold symbolicCapital at h; exact rs_nondegen' a h

/-- Power is the difference in symbolic capital. -/
theorem power_eq_capital_diff (a b : I) :
    power a b = symbolicCapital a - symbolicCapital b := by
  unfold power symbolicCapital; ring

/-! ## §4. Hegemony as Universal Resonance Alignment -/

/-- An idea h is hegemonic if composing with ANY other idea
    always increases h's own weight. The hegemonic idea benefits
    from every interaction — it's the cultural "default." -/
def hegemonic (h : I) : Prop :=
  ∀ a : I, rs (compose h a) (compose h a) ≥ rs h h

/-- Every idea is hegemonic (this is just compose_enriches!).
    In IDT, ALL ideas are "hegemonic" in this basic sense —
    composition always enriches. The real question is DEGREE. -/
theorem all_hegemonic (h : I) : hegemonic h :=
  fun a => compose_enriches' h a

/-- Hegemonic influence: how much h amplifies its weight
    by composing with a. Measures how much a "serves" h. -/
noncomputable def hegemonicInfluence (h a : I) : ℝ :=
  rs (compose h a) (compose h a) - rs h h

/-- Hegemonic influence is always non-negative (by compose_enriches). -/
theorem hegemonicInfluence_nonneg (h a : I) :
    hegemonicInfluence h a ≥ 0 := by
  unfold hegemonicInfluence; linarith [compose_enriches' h a]

/-- Hegemonic influence of void is exactly the subordinate's weight.
    Void starts with no weight, so ALL weight in the composition
    comes from the subordinate. -/
theorem hegemonicInfluence_void_left (a : I) :
    hegemonicInfluence (void : I) a = rs a a := by
  unfold hegemonicInfluence; simp [rs_void_void]

/-- Hegemonic influence on void is zero. -/
theorem hegemonicInfluence_void_right (h : I) :
    hegemonicInfluence h (void : I) = 0 := by
  unfold hegemonicInfluence; simp

/-- Strong hegemony: h has more weight than a, so h benefits
    disproportionately from their composition. -/
def stronglyHegemonic (h a : I) : Prop :=
  power h a ≥ 0

/-- Strong hegemony is equivalent to weight dominance. -/
theorem stronglyHegemonic_iff_weight (h a : I) :
    stronglyHegemonic h a ↔ rs h h ≥ rs a a := by
  unfold stronglyHegemonic power; constructor <;> intro h1 <;> linarith

/-! ## §5. Ideology as Interpretation Filter -/

/-- An ideology acts as an interpretation filter.
    When you compose ideology i with signal s, you get the
    "ideologically filtered" version of s. -/
noncomputable def ideologicalFilter (ideology signal : I) : I :=
  compose ideology signal

/-- The ideological distortion: how much the ideology changes
    the resonance of a signal with an observer. -/
noncomputable def ideologicalDistortion (ideology signal observer : I) : ℝ :=
  rs (ideologicalFilter ideology signal) observer - rs signal observer

/-- Ideological distortion decomposes into resonance of the ideology
    with the observer, plus emergence. -/
theorem ideologicalDistortion_eq (i s o : I) :
    ideologicalDistortion i s o = rs i o + emergence i s o := by
  unfold ideologicalDistortion ideologicalFilter
  have := rs_compose_eq i s o; linarith

/-- A "transparent" ideology creates no emergence —
    it only adds its own resonance, never creates new meaning. -/
def transparentIdeology (i : I) : Prop := leftLinear i

/-- For transparent ideologies, distortion is just the ideology's
    own resonance — no hidden meaning creation. -/
theorem transparent_distortion (i s o : I) (h : transparentIdeology i) :
    ideologicalDistortion i s o = rs i o := by
  rw [ideologicalDistortion_eq]; have := h s o; linarith

/-- Void is a transparent ideology (the "no ideology" ideology). -/
theorem void_transparent : transparentIdeology (void : I) := void_leftLinear

/-- The void ideology creates zero distortion. -/
theorem void_no_distortion (s o : I) :
    ideologicalDistortion (void : I) s o = 0 := by
  unfold ideologicalDistortion ideologicalFilter; simp [rs_void_left']

/-- Composing two ideologies is itself an ideology. The composition
    produces a new filter whose distortion relates to both. -/
theorem composed_ideology_distortion (i₁ i₂ s o : I) :
    ideologicalDistortion (compose i₁ i₂) s o =
    ideologicalDistortion i₁ (compose i₂ s) o +
    ideologicalDistortion i₂ s o := by
  unfold ideologicalDistortion ideologicalFilter
  have h1 := rs_compose_eq i₁ (compose i₂ s) o
  have h2 := rs_compose_eq i₂ s o
  rw [compose_assoc']; linarith

/-! ## §6. Propaganda as Strategic Composition -/

/-- Propaganda effectiveness: how much composing message m with
    audience a shifts a's resonance toward target idea t.
    Propaganda succeeds when it makes the audience resonate more
    with the target. -/
noncomputable def propagandaEffect (message audience target : I) : ℝ :=
  rs (compose message audience) target - rs audience target

/-- Propaganda effect decomposes into the message's own resonance
    with the target plus emergence. -/
theorem propagandaEffect_eq (m a t : I) :
    propagandaEffect m a t = rs m t + emergence m a t := by
  unfold propagandaEffect; have := rs_compose_eq m a t; linarith

/-- Void propaganda has no effect — silence doesn't persuade. -/
theorem void_propaganda (a t : I) :
    propagandaEffect (void : I) a t = 0 := by
  unfold propagandaEffect; simp [rs_void_left']

/-- Propaganda against void has no target to shift toward. -/
theorem propaganda_void_target (m a : I) :
    propagandaEffect m a (void : I) = 0 := by
  unfold propagandaEffect; simp [rs_void_right']

/-- Propaganda on void audience is just the message's resonance. -/
theorem propaganda_void_audience (m t : I) :
    propagandaEffect m (void : I) t = rs m t := by
  unfold propagandaEffect; simp [rs_void_left']

/-- For linear messages, propaganda is purely additive — no synergy. -/
theorem linear_propaganda (m a t : I) (h : leftLinear m) :
    propagandaEffect m a t = rs m t := by
  rw [propagandaEffect_eq]; have := h a t; linarith

/-- Propaganda accumulation: n repetitions of message m composed
    with audience a. Uses composeN for the message repetition. -/
noncomputable def propagandaAccumulation (m : I) (n : ℕ) (a : I) : I :=
  compose (composeN m n) a

/-- Zero repetitions = just the audience. -/
theorem propaganda_zero (m a : I) :
    propagandaAccumulation m 0 a = a := by
  unfold propagandaAccumulation; simp

/-- One repetition = single message. -/
theorem propaganda_one (m a : I) :
    propagandaAccumulation m 1 a = compose m a := by
  unfold propagandaAccumulation; simp [composeN_one]

/-- Each propagandized audience has weight at least the message weight. -/
theorem propaganda_weight_bound (m a : I) (n : ℕ) :
    rs (propagandaAccumulation m n a) (propagandaAccumulation m n a) ≥
    rs (composeN m n) (composeN m n) := by
  unfold propagandaAccumulation; exact compose_enriches' (composeN m n) a

/-! ## §7. Resistance as Counter-Composition -/

/-- Resistance strength: how much composing resistance r with
    hegemony h REDUCES h's resonance with target t.
    Positive = effective resistance. -/
noncomputable def resistanceStrength (resistance hegemony target : I) : ℝ :=
  rs hegemony target - rs (compose hegemony resistance) target

/-- Resistance decomposes into negative resonance and anti-emergence. -/
theorem resistanceStrength_eq (r h t : I) :
    resistanceStrength r h t = -(rs r t + emergence h r t) := by
  unfold resistanceStrength; have := rs_compose_eq h r t; linarith

/-- Void resistance is ineffective — silence doesn't resist. -/
theorem void_resistance (h t : I) :
    resistanceStrength (void : I) h t = 0 := by
  unfold resistanceStrength; simp

/-- Perfect resistance: r exactly cancels h's resonance with t. -/
def perfectResistance (r h t : I) : Prop :=
  rs (compose h r) t = 0

/-- If r perfectly resists h w.r.t. t, the resistance strength
    equals h's full resonance with t. -/
theorem perfect_resistance_strength (r h t : I)
    (hp : perfectResistance r h t) :
    resistanceStrength r h t = rs h t := by
  unfold resistanceStrength perfectResistance at *; linarith

/-- An idea resists hegemony when it is orthogonal to it —
    it operates in a completely different resonance space. -/
def resistsViaOrthogonality (r h : I) : Prop := orthogonal r h

/-- Void resists everything trivially (by being nothing). -/
theorem void_resists_all (h : I) : resistsViaOrthogonality (void : I) h :=
  rs_void_left' h

/-- Everything resists void. -/
theorem all_resist_void (r : I) : resistsViaOrthogonality r (void : I) :=
  rs_void_right' r

/-! ## §8. Gramscian Hegemony: Consent and Coercion -/

/-- Gramsci: hegemony operates through consent, not just coercion.
    Cultural hegemony means composing the hegemonic idea with
    anything produces something that resonates back with the hegemon. -/
def culturalHegemony (h : I) : Prop :=
  ∀ a : I, rs h (compose h a) ≥ 0

/-- Consent degree: how much a "consents" to h's hegemony.
    Measured by how much a's resonance with h∘a exceeds its self-resonance. -/
noncomputable def consentDegree (h a : I) : ℝ :=
  rs a (compose h a) - rs a a

/-- Consent degree when h is void is zero — no hegemony, no consent. -/
theorem consent_void (a : I) : consentDegree (void : I) a = 0 := by
  unfold consentDegree; simp

/-- Consent degree when a is void. -/
theorem consent_void_subject (h : I) : consentDegree h (void : I) = 0 := by
  unfold consentDegree; simp [rs_void_left', rs_void_void]

/-- Coercion: the hegemon composes with the subject even when
    the subject doesn't resonate with the hegemon. -/
def coercive (h a : I) : Prop :=
  rs a h ≤ 0 ∧ rs (compose h a) (compose h a) > rs a a

/-- Non-void hegemons can always coerce through composition
    (enrichment guarantees weight increase). -/
theorem coercive_potential (h a : I) (_hne : h ≠ void) :
    rs (compose h a) (compose h a) ≥ rs h h := by
  exact compose_enriches' h a

/-- Consent: the subject resonates positively with the hegemon. -/
def consents (a h : I) : Prop := rs a h > 0

/-- Mutual consent: positive resonance in both directions. -/
def mutualConsent (a h : I) : Prop :=
  rs a h > 0 ∧ rs h a > 0

/-! ## §9. Foucauldian Power/Knowledge -/

/-- Foucault: power and knowledge are inseparable (pouvoir/savoir).
    In IDT: power IS the resonance structure. Knowledge of a about b
    is rs(a, b). Power is weight = rs(a, a). They are literally the
    same mathematical object — the resonance function. -/
noncomputable def powerKnowledge (a b : I) : ℝ := rs a b

/-- The Foucault principle: power (self-resonance) of the composition
    constrains knowledge (emergence) about any observer.
    You cannot learn more than your combined weight allows. -/
theorem foucault_principle (a b c : I) :
    (emergence a b c) ^ 2 ≤ rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- Power constrains knowledge: emergence is bounded by power. -/
theorem power_constrains_knowledge (a b c : I) :
    (rs (compose a b) c - rs a c - rs b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- Knowledge of void is zero — you can't know nothing. -/
theorem knowledge_of_void (a : I) : powerKnowledge a (void : I) = 0 := by
  unfold powerKnowledge; exact rs_void_right' a

/-- Void knows nothing. -/
theorem void_knows_nothing (a : I) : powerKnowledge (void : I) a = 0 := by
  unfold powerKnowledge; exact rs_void_left' a

/-- Disciplinary power: h exercises discipline over a when
    composing a with h yields less surplus than h with a. -/
def disciplinary (h a : I) : Prop :=
  rs (compose a h) (compose a h) - rs a a ≤
  rs (compose h a) (compose h a) - rs h h

/-- Void exercises discipline trivially. Both compose(void,a) and
    compose(a,void) equal a, so surplus is the same. -/
theorem void_disciplinary (a : I) :
    disciplinary (void : I) a := by
  unfold disciplinary; simp [rs_void_void]; linarith [rs_self_nonneg' a, compose_enriches' a (void : I)]

/-- Bio-power: h exercises bio-power over a population by
    increasing the system's total weight. Always non-negative. -/
noncomputable def bioPower (h population : I) : ℝ :=
  rs (compose h population) (compose h population) - rs h h

/-- Bio-power is non-negative (enrichment). -/
theorem bioPower_nonneg (h p : I) : bioPower h p ≥ 0 := by
  unfold bioPower; linarith [compose_enriches' h p]

/-- Bio-power of void is the population's weight —
    void starts with nothing, so all weight comes from the population. -/
theorem bioPower_void (p : I) : bioPower (void : I) p = rs p p := by
  unfold bioPower; simp [rs_void_void]

/-- Bio-power on void population is zero — silence adds nothing. -/
theorem bioPower_void_pop (h : I) : bioPower h (void : I) = 0 := by
  unfold bioPower; simp

/-! ## §10. Information Control and Censorship -/

/-- Censorship: removing idea c from circulation. The resonance loss
    measures what is lost by censorship. -/
noncomputable def censorshipLoss (censored context observer : I) : ℝ :=
  rs (compose context censored) observer - rs context observer

/-- Censorship loss equals the censored idea's resonance
    with the observer plus emergence. -/
theorem censorshipLoss_eq (c ctx o : I) :
    censorshipLoss c ctx o = rs c o + emergence ctx c o := by
  unfold censorshipLoss; have := rs_compose_eq ctx c o; linarith

/-- Censoring void loses nothing — you can't censor silence. -/
theorem censor_void (ctx o : I) :
    censorshipLoss (void : I) ctx o = 0 := by
  unfold censorshipLoss; simp

/-- Information control: choosing which compositions are available.
    Measured by the resonance difference between full and restricted. -/
noncomputable def informationControl (controller restricted full observer : I) : ℝ :=
  rs (compose controller full) observer -
  rs (compose controller restricted) observer

/-- Information control decomposes via emergence. -/
theorem informationControl_eq (ctrl r f o : I) :
    informationControl ctrl r f o =
    rs f o - rs r o + emergence ctrl f o - emergence ctrl r o := by
  unfold informationControl
  have h1 := rs_compose_eq ctrl f o
  have h2 := rs_compose_eq ctrl r o; linarith

/-- Controlling void vs controlling something: the gain from
    introducing new information. -/
theorem control_vs_void (ctrl f o : I) :
    informationControl ctrl (void : I) f o =
    rs f o + emergence ctrl f o := by
  unfold informationControl
  have h1 := rs_compose_eq ctrl f o
  simp [rs_void_left', rs_void_right', emergence_void_right]; linarith

/-! ## §11. Ideological State Apparatus (Althusser) -/

/-- An ideological state apparatus "interpellates" — transforms
    subjects by composing them with the state ideology. -/
noncomputable def interpellate (stateIdeology subject : I) : I :=
  compose stateIdeology subject

/-- Interpellation by void leaves the subject unchanged. -/
theorem interpellate_void (s : I) :
    interpellate (void : I) s = s := by
  unfold interpellate; simp

/-- Interpellation always enriches the ideology's weight. -/
theorem interpellation_enriches (ideology subject : I) :
    rs (interpellate ideology subject) (interpellate ideology subject) ≥
    rs ideology ideology := by
  unfold interpellate; exact compose_enriches' ideology subject

/-- Double interpellation compounds ideological effect. -/
theorem double_interpellation (i s : I) :
    interpellate i (interpellate i s) =
    compose i (compose i s) := by
  unfold interpellate; rfl

/-- The alienation effect: difference between the subject's
    self-resonance and how the interpellated subject resonates
    with the original subject. -/
noncomputable def alienation (ideology subject : I) : ℝ :=
  rs subject subject - rs (interpellate ideology subject) subject

/-- Alienation from void ideology is zero. -/
theorem alienation_void (s : I) : alienation (void : I) s = 0 := by
  unfold alienation interpellate; simp

/-- Alienation of void subject is zero. -/
theorem alienation_void_subject (i : I) : alienation i (void : I) = 0 := by
  unfold alienation interpellate
  simp [rs_void_void, rs_void_left', rs_void_right']

/-- The compliance measure: how much the subject's own resonance
    contributes to the interpellated whole. -/
noncomputable def compliance (ideology subject : I) : ℝ :=
  rs subject (interpellate ideology subject)

/-- Compliance of void subject is zero. -/
theorem compliance_void_subject (i : I) :
    compliance i (void : I) = 0 := by
  unfold compliance interpellate; simp [rs_void_left']

/-- Compliance with void ideology is self-resonance. -/
theorem compliance_void_ideology (s : I) :
    compliance (void : I) s = rs s s := by
  unfold compliance interpellate; simp

/-! ## §12. Liberation Dynamics -/

/-- Liberation potential: how much weight a subordinate gains
    by composing with a liberating idea. -/
noncomputable def liberationPotential (subordinateIdea liberator : I) : ℝ :=
  rs (compose subordinateIdea liberator) (compose subordinateIdea liberator) -
  rs subordinateIdea subordinateIdea

/-- Liberation potential is always non-negative (compose enriches). -/
theorem liberation_nonneg (s l : I) :
    liberationPotential s l ≥ 0 := by
  unfold liberationPotential; linarith [compose_enriches' s l]

/-- Void liberation does nothing — silence doesn't liberate. -/
theorem void_liberation (s : I) :
    liberationPotential s (void : I) = 0 := by
  unfold liberationPotential; simp

/-- Liberation of void gains the liberator's weight. -/
theorem liberation_from_void (l : I) :
    liberationPotential (void : I) l = rs l l := by
  unfold liberationPotential; simp [rs_void_void]

/-- Effective liberation: after composing with l, the subordinate
    is no longer dominated by h. -/
def effectiveLiberation (sub hegemon liberator : I) : Prop :=
  dominates hegemon sub ∧
  ¬dominates hegemon (compose sub liberator)

/-- Revolutionary potential: the weight gain from composing
    a subordinate idea with a revolutionary idea. -/
noncomputable def revolutionaryPotential (revolution subordinateIdea : I) : ℝ :=
  rs (compose subordinateIdea revolution) (compose subordinateIdea revolution) -
  rs subordinateIdea subordinateIdea

/-- Revolutionary potential is always non-negative. -/
theorem revolutionaryPotential_nonneg (r s : I) :
    revolutionaryPotential r s ≥ 0 := by
  unfold revolutionaryPotential; linarith [compose_enriches' s r]

/-- Void revolution does nothing. -/
theorem void_revolution (s : I) :
    revolutionaryPotential (void : I) s = 0 := by
  unfold revolutionaryPotential; simp

/-! ## §13. Counter-Hegemony and Subaltern Voice -/

/-- Counter-hegemonic strength: how much a counter-narrative c
    competes with hegemon h for observer o's attention. -/
noncomputable def counterHegemonicStrength (counter hegemon observer : I) : ℝ :=
  rs counter observer - rs hegemon observer

/-- Counter-hegemonic strength is antisymmetric. -/
theorem counterHegemonic_antisymm (c h o : I) :
    counterHegemonicStrength c h o = -counterHegemonicStrength h c o := by
  unfold counterHegemonicStrength; ring

/-- Counter-hegemonic strength with void counter is negative. -/
theorem counterHegemonic_void_counter (h o : I) :
    counterHegemonicStrength (void : I) h o = -rs h o := by
  unfold counterHegemonicStrength; simp [rs_void_left']

/-- Subaltern voice: the weight contribution of a subordinate idea
    when composed with a dominant one. -/
noncomputable def subalternVoice (subaltern dominant : I) : ℝ :=
  rs (compose dominant subaltern) (compose dominant subaltern) -
  rs dominant dominant

/-- Subaltern voice is always non-negative (the subaltern adds weight). -/
theorem subalternVoice_nonneg (s d : I) : subalternVoice s d ≥ 0 := by
  unfold subalternVoice; linarith [compose_enriches' d s]

/-- Subaltern voice of void is zero — void can't speak. -/
theorem subalternVoice_void (d : I) : subalternVoice (void : I) d = 0 := by
  unfold subalternVoice; simp

/-! ## §14. Symbolic Annihilation -/

/-- Symbolic annihilation: composing with a dominant idea makes the
    subordinate idea's contribution vanish. "The subaltern cannot speak." -/
def symbolicallyAnnihilated (dominant sub observer : I) : Prop :=
  rs sub observer ≠ 0 ∧
  rs (compose dominant sub) observer = rs dominant observer

/-- Symbolic annihilation means emergence exactly cancels the sub's voice. -/
theorem annihilation_means_absorption (d s o : I)
    (h : symbolicallyAnnihilated d s o) :
    rs s o + emergence d s o = 0 := by
  unfold symbolicallyAnnihilated at h
  have h2 := rs_compose_eq d s o; linarith [h.2]

/-- If the subordinate is symbolically annihilated, its emergence with
    the dominant idea is exactly the negation of its direct resonance. -/
theorem annihilation_emergence (d s o : I)
    (h : symbolicallyAnnihilated d s o) :
    emergence d s o = -rs s o := by
  have := annihilation_means_absorption d s o h; linarith

/-! ## §15. Structural Violence -/

/-- Structural violence: how the composition structure systematically
    affects the weight of an idea. -/
noncomputable def structuralViolence (structure_ victim : I) : ℝ :=
  rs structure_ structure_ - rs victim victim

/-- Structural violence is just the power differential. -/
theorem structuralViolence_eq_power (s v : I) :
    structuralViolence s v = power s v := by
  unfold structuralViolence power; ring

/-- Structural violence against void. -/
theorem structuralViolence_void (s : I) :
    structuralViolence s (void : I) = rs s s := by
  unfold structuralViolence; simp [rs_void_void]

/-- No structural violence when there's no power differential. -/
theorem no_structuralViolence_self (a : I) :
    structuralViolence a a = 0 := by
  unfold structuralViolence; ring

/-! ## §16. Discourse Control -/

/-- The discourse field: the total resonance landscape an idea creates. -/
noncomputable def discourseWeight (a reference : I) : ℝ :=
  rs a a + rs a reference

/-- Void has zero discourse weight. -/
theorem discourseWeight_void (r : I) :
    discourseWeight (void : I) r = 0 := by
  unfold discourseWeight; simp [rs_void_void, rs_void_left']

/-- Discourse weight against void is just self-resonance. -/
theorem discourseWeight_void_ref (a : I) :
    discourseWeight a (void : I) = rs a a := by
  unfold discourseWeight; simp [rs_void_right']

/-- The marginalization effect: how much composing with h shifts
    idea a's discourse relative to reference r. -/
noncomputable def marginalization (hegemon victim reference : I) : ℝ :=
  discourseWeight victim reference -
  rs victim (compose hegemon victim)

/-- Marginalization of void victim is zero. -/
theorem marginalization_void_victim (h r : I) :
    marginalization h (void : I) r = 0 := by
  unfold marginalization discourseWeight
  simp [rs_void_void, rs_void_left']

/-! ## §17. Resonance Alignment -/

/-- Two ideas are resonance-aligned w.r.t. an observer when they
    both resonate positively with the observer. -/
def resonanceAligned (a b observer : I) : Prop :=
  rs a observer > 0 ∧ rs b observer > 0

/-- Resonance opposition: a and b resonate oppositely with o. -/
def resonanceOpposed (a b observer : I) : Prop :=
  rs a observer > 0 ∧ rs b observer < 0

/-- Void is never positively aligned with anything. -/
theorem void_not_aligned (a o : I) : ¬resonanceAligned (void : I) a o := by
  unfold resonanceAligned; intro ⟨h, _⟩; simp [rs_void_left'] at h

/-- Ideological alignment: composing with i preserves or increases
    resonance with all observers. -/
def ideologicallyAligned (a ideology : I) : Prop :=
  ∀ o : I, rs (compose ideology a) o ≥ rs a o

/-! ## §18. Hegemonic Reproduction -/

/-- Each iteration of hegemonic reproduction preserves or increases weight. -/
theorem hegemonic_reproduction_mono (h : I) (n : ℕ) :
    rs (composeN h (n + 1)) (composeN h (n + 1)) ≥
    rs (composeN h n) (composeN h n) :=
  rs_composeN_mono h n

/-- Ideological reproduction: ideology reproduces through repeated
    interpellation. Each cycle compounds the effect. -/
theorem ideological_reproduction (i : I) (n : ℕ) :
    rs (composeN i (n + 1)) (composeN i (n + 1)) ≥ rs i i := by
  induction n with
  | zero => simp [composeN_one]
  | succ n ih => linarith [rs_composeN_mono i (n + 1)]

/-- Hegemonic reproduction starting from non-void always yields non-void. -/
theorem hegemonic_reproduction_nonvoid (h : I) (hne : h ≠ void) (n : ℕ) :
    composeN h (n + 1) ≠ void := by
  intro heq
  have h1 : rs (composeN h (n + 1)) (composeN h (n + 1)) ≥ rs h h :=
    ideological_reproduction h n
  rw [heq, rs_void_void] at h1
  linarith [rs_self_pos h hne]

/-- Hegemonic stability: how much weight a hegemon gains from
    self-composition. Always non-negative. -/
noncomputable def hegemonicStability (h : I) : ℝ :=
  rs (compose h h) (compose h h) - rs h h

/-- Hegemonic stability is non-negative. -/
theorem hegemonicStability_nonneg (h : I) :
    hegemonicStability h ≥ 0 := by
  unfold hegemonicStability; linarith [compose_enriches' h h]

/-- Void has zero hegemonic stability. -/
theorem hegemonicStability_void :
    hegemonicStability (void : I) = 0 := by
  unfold hegemonicStability; simp [rs_void_void]

/-! ## §19. Emergence as Power Coupling -/

/-- Emergence is bounded by the power (weight) of the composition
    and the observer. -/
theorem emergence_power_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- When the observer is void, emergence must vanish —
    powerless observers see no emergence. -/
theorem emergence_powerless_observer (a b : I) :
    emergence a b (void : I) = 0 :=
  emergence_against_void a b

/-- When both source ideas are void, emergence vanishes. -/
theorem emergence_void_composition (c : I) :
    emergence (void : I) (void : I) c = 0 :=
  emergence_void_left (void : I) c

/-- Emergence is constrained but possible: this is the mathematical
    expression that revolution is possible but bounded. -/
theorem revolution_constrained (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-! ## §20. Reciprocity and Asymmetry of Power -/

/-- Power asymmetry: how a "sees" b vs how b "sees" a. -/
noncomputable def powerAsymmetry (a b : I) : ℝ :=
  rs a b - rs b a

/-- Power asymmetry is antisymmetric. -/
theorem powerAsymmetry_antisymm (a b : I) :
    powerAsymmetry a b = -powerAsymmetry b a := by
  unfold powerAsymmetry; ring

/-- Power asymmetry with self is zero. -/
theorem powerAsymmetry_self (a : I) :
    powerAsymmetry a a = 0 := by
  unfold powerAsymmetry; ring

/-- Power asymmetry with void is zero. -/
theorem powerAsymmetry_void (a : I) :
    powerAsymmetry (void : I) a = 0 := by
  unfold powerAsymmetry; simp [rs_void_left', rs_void_right']

/-- Power asymmetry of void on the right. -/
theorem powerAsymmetry_void_right (a : I) :
    powerAsymmetry a (void : I) = 0 := by
  unfold powerAsymmetry; simp [rs_void_left', rs_void_right']

/-! ## §21. Collective Power -/

/-- Collective power gain: how much weight a coalition gains. -/
noncomputable def collectivePowerGain (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a

/-- Collective power gain is non-negative. -/
theorem collectivePowerGain_nonneg (a b : I) :
    collectivePowerGain a b ≥ 0 := by
  unfold collectivePowerGain; linarith [compose_enriches' a b]

/-- Collective power gain from void is zero. -/
theorem collectivePowerGain_void (a : I) :
    collectivePowerGain a (void : I) = 0 := by
  unfold collectivePowerGain; simp

/-- Collective power gain of void equals partner's weight. -/
theorem collectivePowerGain_void_left (b : I) :
    collectivePowerGain (void : I) b = rs b b := by
  unfold collectivePowerGain; simp [rs_void_void]

/-! ## §22. Weight Preservation Laws -/

/-- Composition never loses the left component's weight. -/
theorem weight_preservation_left (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- Weight is preserved under re-association. -/
theorem weight_reassociation (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) =
    rs (compose a (compose b c)) (compose a (compose b c)) := by
  rw [compose_assoc']

/-- Double composition increases weight over the original. -/
theorem double_compose_weight (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥ rs a a := by
  linarith [compose_enriches' a b, compose_enriches' (compose a b) c]

/-- Composition with void preserves weight exactly. -/
theorem power_compose_void (a : I) :
    power (compose a (void : I)) a = 0 := by
  unfold power; simp

/-! ## §23. Power Accumulation -/

/-- Power accumulates under iterated composition. -/
theorem power_composeN_mono (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) :=
  rs_composeN_mono a n

/-- Cultural capital accumulates through composition. -/
theorem capital_accumulation (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) :=
  rs_composeN_mono a n

/-- Starting from nothing, first composition yields exactly a's weight. -/
theorem capital_from_nothing (a : I) :
    rs (composeN a 1) (composeN a 1) = rs a a := by
  simp [composeN_one]

/-- Power of a ∘ b over void. -/
theorem compose_power_over_void (a b : I) :
    power (compose a b) (void : I) = rs (compose a b) (compose a b) := by
  unfold power; simp [rs_void_void]

/-! ## §24. Micro-Power (Foucault) -/

/-- Micro-power: power operates at every level, not just top-down.
    Even the smallest composition creates enrichment. -/
theorem micro_power (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- Power is everywhere: any non-void idea has power over void. -/
theorem power_everywhere (a : I) (h : a ≠ void) :
    power a void > 0 := by
  unfold power; simp [rs_void_void]; exact rs_self_pos a h

/-- The capillary nature of power: even composing with void
    doesn't reduce power. Power is preserved at minimum. -/
theorem capillary_power (a : I) :
    rs (compose a (void : I)) (compose a (void : I)) = rs a a := by simp

/-! ## §25. Power Topology: Strata -/

/-- Two ideas are in the same power stratum if they have the
    same symbolic capital (self-resonance). -/
def sameStratum (a b : I) : Prop := rs a a = rs b b

/-- Being in the same stratum is reflexive. -/
theorem sameStratum_refl (a : I) : sameStratum a a := rfl

/-- Being in the same stratum is symmetric. -/
theorem sameStratum_symm (a b : I) (h : sameStratum a b) :
    sameStratum b a := h.symm

/-- Being in the same stratum is transitive. -/
theorem sameStratum_trans (a b c : I)
    (h1 : sameStratum a b) (h2 : sameStratum b c) :
    sameStratum a c := h1.trans h2

/-- Same stratum means zero power differential. -/
theorem sameStratum_zero_power (a b : I) (h : sameStratum a b) :
    power a b = 0 := by
  unfold power sameStratum at *; linarith

/-- Void is only in the same stratum as itself. -/
theorem void_stratum_unique (a : I) (h : sameStratum (void : I) a) :
    a = void := by
  unfold sameStratum at h; simp [rs_void_void] at h
  exact rs_nondegen' a h.symm

/-! ## §26. Void Paradox -/

/-- Void represents both total liberation (freedom from all ideology)
    and total powerlessness (no voice, no weight). The paradox of nihilism. -/
theorem void_paradox :
    power (void : I) (void : I) = 0 ∧ symbolicCapital (void : I) = 0 :=
  ⟨power_void_void, symbolicCapital_void⟩

/-- Against void, no revolution occurs — you need substance. -/
theorem no_revolution_against_void (a b : I) :
    emergence a b (void : I) = 0 :=
  emergence_against_void a b

/-! ## §27. Propaganda via Cocycle -/

/-- The cocycle condition constrains propaganda: the effect of
    sequential propaganda messages satisfies a consistency relation.
    You can't freely manipulate emergence. -/
theorem propaganda_cocycle (m₁ m₂ audience target : I) :
    emergence m₁ m₂ target + emergence (compose m₁ m₂) audience target =
    emergence m₂ audience target + emergence m₁ (compose m₂ audience) target :=
  cocycle_condition m₁ m₂ audience target

/-- Sequential vs simultaneous propaganda: the difference in effect
    between delivering messages sequentially vs as a composition. -/
noncomputable def propagandaSequenceGap (m₁ m₂ a t : I) : ℝ :=
  propagandaEffect m₁ (compose m₂ a) t - propagandaEffect (compose m₁ m₂) a t

/-- The propaganda sequence gap simplifies by associativity:
    the gap between sequential and simultaneous delivery
    equals minus the standalone effect of the second message. -/
theorem propagandaSequenceGap_eq (m₁ m₂ a t : I) :
    propagandaSequenceGap m₁ m₂ a t =
    -(propagandaEffect m₂ a t) := by
  unfold propagandaSequenceGap propagandaEffect
  have h4 : compose m₁ (compose m₂ a) = compose (compose m₁ m₂) a := by
    rw [compose_assoc']
  rw [h4]; ring

/-! ## §28. Influence and Soft Power -/

/-- Soft power: the ability to attract and co-opt rather than coerce.
    Measured by cross-resonance (how much others resonate with you). -/
noncomputable def softPower (a b : I) : ℝ := rs b a

/-- Soft power of void is zero — nothing is attracted to void. -/
theorem softPower_void (b : I) : softPower (void : I) b = 0 := by
  unfold softPower; exact rs_void_right' b

/-- Soft power from void is zero — void attracts nothing. -/
theorem softPower_from_void (a : I) : softPower a (void : I) = 0 := by
  unfold softPower; exact rs_void_left' a

/-- Hard power: the self-resonance (weight) component of power. -/
noncomputable def hardPower (a : I) : ℝ := rs a a

/-- Hard power is non-negative. -/
theorem hardPower_nonneg (a : I) : hardPower a ≥ 0 := by
  unfold hardPower; exact rs_self_nonneg' a

/-- Hard power of void is zero. -/
theorem hardPower_void : hardPower (void : I) = 0 := by
  unfold hardPower; exact rs_void_void

/-- Total influence: hard power plus soft power. -/
noncomputable def totalInfluence (a b : I) : ℝ :=
  hardPower a + softPower a b

/-- Total influence with void target. -/
theorem totalInfluence_void_target (a : I) :
    totalInfluence a (void : I) = rs a a := by
  unfold totalInfluence hardPower softPower; simp [rs_void_left']

/-! ## §29. Ideological Superstructure -/

/-- The superstructure is built on the base through composition.
    Base ideas gain new meaning when filtered through ideology. -/
noncomputable def superstructureEffect (ideology base observer : I) : ℝ :=
  emergence ideology base observer

/-- Void ideology has no superstructure effect. -/
theorem no_superstructure_void_ideology (base observer : I) :
    superstructureEffect (void : I) base observer = 0 :=
  emergence_void_left base observer

/-- Void base has no superstructure effect. -/
theorem no_superstructure_void_base (ideology observer : I) :
    superstructureEffect ideology (void : I) observer = 0 :=
  emergence_void_right ideology observer

/-- Superstructure effect is bounded by power. -/
theorem superstructure_bounded (i b o : I) :
    (superstructureEffect i b o) ^ 2 ≤
    rs (compose i b) (compose i b) * rs o o := by
  unfold superstructureEffect; exact emergence_bounded' i b o

/-! ## §30. Dialectics of Power -/

/-- Dialectical tension between thesis and antithesis. -/
noncomputable def powerDialectic (thesis antithesis : I) : ℝ :=
  emergence thesis antithesis (compose thesis antithesis)

/-- Dialectical tension with void is zero — no synthesis from nothing. -/
theorem dialectic_void_right (a : I) :
    powerDialectic a (void : I) = 0 := by
  unfold powerDialectic
  have := emergence_void_right a (compose a (void : I))
  simp at this ⊢; exact this

/-- Dialectical tension with void thesis. -/
theorem dialectic_void_left (b : I) :
    powerDialectic (void : I) b = 0 := by
  unfold powerDialectic; simp [emergence_void_left]

/-- The synthesis (compose thesis antithesis) always has at least
    as much weight as the thesis alone. -/
theorem synthesis_enriches (thesis antithesis : I) :
    rs (compose thesis antithesis) (compose thesis antithesis) ≥
    rs thesis thesis :=
  compose_enriches' thesis antithesis

/-! ## §31. Normalization and Naturalization -/

/-- Normalization: an idea is "normalized" if composing it with
    any other idea is indistinguishable in resonance from just adding
    its weight — i.e., it creates no emergence. This is the idea
    that is so hegemonic it's invisible. -/
def normalized (h : I) : Prop := leftLinear h

/-- Void is normalized — silence is the ultimate normalization. -/
theorem void_normalized : normalized (void : I) := void_leftLinear

/-- A normalized idea's composition resonance is purely additive. -/
theorem normalized_additive (h : I) (hn : normalized h) (a c : I) :
    rs (compose h a) c = rs h c + rs a c := by
  exact leftLinear_additive h hn a c

/-- Naturalization: the process by which an idea becomes normalized.
    Measured by how close its emergence is to zero. -/
noncomputable def naturalizationGap (h a c : I) : ℝ :=
  emergence h a c

/-- Void has zero naturalization gap. -/
theorem void_naturalized (a c : I) :
    naturalizationGap (void : I) a c = 0 :=
  emergence_void_left a c

/-! ## §32. Power and Emergence Coupling -/

/-- The fundamental power-emergence inequality: emergence (the creative/
    revolutionary force) is bounded by the weights (power) of the
    composition and observer. -/
theorem power_emergence_coupling (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

/-- Emergence against a powerless (void-weight) observer vanishes. -/
theorem emergence_against_powerless (a b c : I) (h : rs c c = 0) :
    emergence a b c = 0 := by
  have hv := rs_nondegen' c h; rw [hv]; exact emergence_against_void a b

/-- Emergence squared is bounded by composition weight times observer weight. -/
theorem emergence_sq_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤
    (rs a a + hegemonicInfluence a b) * rs c c := by
  have h1 := emergence_bounded' a b c
  unfold hegemonicInfluence
  have h2 := compose_enriches' a b
  have : rs (compose a b) (compose a b) ≤ rs a a + (rs (compose a b) (compose a b) - rs a a) := by linarith
  linarith

/-! ## §33. Ideology Composition Laws -/

/-- Composing two ideologies produces a third; the composition is
    associative (inherited from the monoid structure). -/
theorem ideology_composition_assoc (i₁ i₂ i₃ s : I) :
    ideologicalFilter (compose i₁ i₂) (compose i₃ s) =
    ideologicalFilter i₁ (ideologicalFilter i₂ (compose i₃ s)) := by
  unfold ideologicalFilter; rw [compose_assoc']

/-- The void filter is a left identity for ideology composition. -/
theorem void_filter_left (s : I) :
    ideologicalFilter (void : I) s = s := by
  unfold ideologicalFilter; simp

/-- The void filter is a right identity for ideology composition. -/
theorem void_filter_right (i : I) :
    ideologicalFilter i (void : I) = i := by
  unfold ideologicalFilter; simp

/-! ## §34. Hegemonic Weight Bounds -/

/-- For a linear hegemon, cross-resonance is bounded. -/
theorem linear_hegemon_bound (h : I) (hn : leftLinear h) (a c : I) :
    rs (compose h a) c = rs h c + rs a c :=
  leftLinear_additive h hn a c

/-- Composition weight is at least the left factor's weight. -/
theorem hegemon_minimum_weight (h a : I) :
    rs (compose h a) (compose h a) ≥ rs h h :=
  compose_enriches' h a

/-- The weight of h∘a is non-negative. -/
theorem hegemon_composition_nonneg (h a : I) :
    rs (compose h a) (compose h a) ≥ 0 :=
  rs_self_nonneg' (compose h a)

/-! ## §35. Liberation Algebra -/

/-- Liberation is additive: composing two liberators compounds
    the liberation potential (at least for the left factor). -/
theorem liberation_compounds (s l₁ l₂ : I) :
    rs (compose s (compose l₁ l₂)) (compose s (compose l₁ l₂)) ≥
    rs (compose s l₁) (compose s l₁) := by
  rw [← compose_assoc']
  exact compose_enriches' (compose s l₁) l₂

/-- Self-liberation (composing with yourself) always enriches. -/
theorem self_liberation (a : I) :
    liberationPotential a a ≥ 0 := by
  exact liberation_nonneg a a

/-- Liberation from void equals the liberator's own weight. -/
theorem liberation_from_nothing (l : I) :
    liberationPotential (void : I) l = rs l l :=
  liberation_from_void l

/-! ## §36. Ideology and False Consciousness -/

/-- False consciousness: the ideology makes the subject resonate
    MORE with the hegemon than with itself. Measured by the
    difference between compliance and self-resonance. -/
noncomputable def falseConsciousness (ideology subject : I) : ℝ :=
  rs subject (interpellate ideology subject) - rs subject subject

/-- False consciousness under void ideology is zero. -/
theorem falseConsciousness_void (s : I) :
    falseConsciousness (void : I) s = 0 := by
  unfold falseConsciousness interpellate; simp

/-- False consciousness of void subject is zero. -/
theorem falseConsciousness_void_subject (i : I) :
    falseConsciousness i (void : I) = 0 := by
  unfold falseConsciousness interpellate
  simp [rs_void_left', rs_void_void]

/-- False consciousness equals consent degree (definitionally). -/
theorem falseConsciousness_eq_consent (i s : I) :
    falseConsciousness i s = consentDegree i s := by
  unfold falseConsciousness consentDegree interpellate; ring

/-! ## §37. Ideological Spectrum -/

/-- The ideological spectrum position: how much an idea resonates
    with a reference "left" vs "right" idea. -/
noncomputable def spectrumPosition (idea left right : I) : ℝ :=
  rs idea left - rs idea right

/-- Void has no position on the spectrum. -/
theorem void_no_position (l r : I) :
    spectrumPosition (void : I) l r = 0 := by
  unfold spectrumPosition; simp [rs_void_left']

/-- The spectrum position is antisymmetric in left/right. -/
theorem spectrum_antisymm (a l r : I) :
    spectrumPosition a l r = -spectrumPosition a r l := by
  unfold spectrumPosition; ring

/-- Composing with an ideology shifts spectrum position. -/
theorem ideology_shifts_spectrum (i a l r : I) :
    spectrumPosition (compose i a) l r =
    spectrumPosition a l r + rs i l - rs i r +
    emergence i a l - emergence i a r := by
  unfold spectrumPosition
  have h1 := rs_compose_eq i a l
  have h2 := rs_compose_eq i a r; linarith

end PowerStructure

end IDT3
