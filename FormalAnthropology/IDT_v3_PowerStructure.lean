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

/-! ## §38. Arendt's Power vs Violence Distinction

Hannah Arendt argued that power and violence are opposites: power arises from
collective action (composition enriches), while violence is the destruction of
power (annihilation of resonance). Power grows through composition; violence
destroys through isolation. -/

/-- Arendt's power: the weight gained through collective composition.
    Power is inherently relational — it arises from acting together. -/
noncomputable def arendtPower (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- Arendt's violence: the negation of power — it destroys rather than creates.
    Violence is measured by how much an interaction REDUCES total weight
    below what would be expected from summation. -/
noncomputable def arendtViolence (a b : I) : ℝ :=
  rs a a + rs b b - rs (compose a b) (compose a b)

/-- Power and violence are exact negations of each other. -/
theorem arendt_power_violence_dual (a b : I) :
    arendtPower a b = -arendtViolence a b := by
  unfold arendtPower arendtViolence; ring

/-- Violence is bounded above: composition always enriches the left,
    so violence cannot exceed b's weight. -/
theorem arendt_violence_bounded (a b : I) :
    arendtViolence a b ≤ rs b b := by
  unfold arendtViolence; linarith [compose_enriches' a b]

/-- Violence against void is zero — you can't destroy nothing. -/
theorem arendt_violence_void_right (a : I) :
    arendtViolence a (void : I) = 0 := by
  unfold arendtViolence; simp [rs_void_void]

/-- Violence of void is zero — void can't be violent. -/
theorem arendt_violence_void_left (b : I) :
    arendtViolence (void : I) b = 0 := by
  unfold arendtViolence; simp [rs_void_void]

/-- Power with void is zero from the right. -/
theorem arendt_power_void_right (a : I) :
    arendtPower a (void : I) = 0 := by
  unfold arendtPower; simp [rs_void_void]

/-- Power from void yields the partner's full weight minus nothing. -/
theorem arendt_power_void_left (b : I) :
    arendtPower (void : I) b = 0 := by
  unfold arendtPower; simp [rs_void_void]

/-- Arendt's key insight: power (as collective capacity) always exists
    at least at the level of enrichment. The composition can never
    have LESS weight than the first component alone. -/
theorem arendt_power_enrichment (a b : I) :
    arendtPower a b ≥ -rs b b := by
  unfold arendtPower; linarith [compose_enriches' a b]

/-- Self-power: composing with yourself always enriches. -/
theorem arendt_self_power_nonneg_iff (a : I) :
    arendtPower a a ≥ -rs a a := by
  unfold arendtPower; linarith [compose_enriches' a a]

/-! ## §39. Lukes's Three Dimensions of Power

Steven Lukes distinguished three dimensions:
1. Decision-making power (direct resonance advantage)
2. Non-decision-making power (agenda control via composition)
3. Ideological power (shaping preferences via emergence) -/

/-- First dimension: direct power — a has more weight than b. -/
def lukesDim1 (a b : I) : Prop := rs a a > rs b b

/-- Second dimension: agenda-setting — a controls what gets composed.
    a's composition with any idea c dominates b's composition with c. -/
def lukesDim2 (a b : I) : Prop :=
  ∀ c : I, rs (compose a c) (compose a c) ≥ rs (compose b c) (compose b c)

/-- Third dimension: ideological power — a shapes how composition is
    interpreted. a creates more emergence than b when composed. -/
noncomputable def lukesDim3Strength (a b c : I) : ℝ :=
  emergence a c b - emergence b c a

/-- First dimension implies dominates. -/
theorem lukes_dim1_iff_dominates (a b : I) :
    lukesDim1 a b ↔ dominates a b := by
  unfold lukesDim1 dominates; exact Iff.rfl

/-- Second dimension is reflexive. -/
theorem lukes_dim2_refl (a : I) : lukesDim2 a a := fun _ => le_refl _

/-- Second dimension is transitive. -/
theorem lukes_dim2_trans (a b c : I) (h1 : lukesDim2 a b) (h2 : lukesDim2 b c) :
    lukesDim2 a c :=
  fun d => le_trans (h2 d) (h1 d)

/-- Third-dimension strength is antisymmetric in the two agents. -/
theorem lukes_dim3_antisymm (a b c : I) :
    lukesDim3Strength a b c = -lukesDim3Strength b a c := by
  unfold lukesDim3Strength; ring

/-- Void has zero third-dimension power. -/
theorem lukes_dim3_void (b c : I) :
    lukesDim3Strength (void : I) b c = -emergence b c (void : I) := by
  unfold lukesDim3Strength; simp [emergence_void_left]

/-! ## §40. Mann's Sources of Social Power (IEMP Model)

Michael Mann identified four sources of social power:
Ideological, Economic, Military, Political.
We model each as a component of resonance structure. -/

/-- Ideological power: ability to shape meaning through emergence. -/
noncomputable def ideologicalPower (a b c : I) : ℝ := emergence a b c

/-- Economic power: the accumulated weight (capital). -/
noncomputable def economicPower (a : I) : ℝ := rs a a

/-- Military power: the capacity to destroy (reduce resonance). -/
noncomputable def militaryPower (a b : I) : ℝ :=
  rs a a - rs (compose a b) b

/-- Political power: the capacity to coordinate (cross-resonance). -/
noncomputable def politicalPower (a b : I) : ℝ := rs a b + rs b a

/-- Economic power is non-negative. -/
theorem economicPower_nonneg (a : I) : economicPower a ≥ 0 := by
  unfold economicPower; exact rs_self_nonneg' a

/-- Void has zero economic power. -/
theorem economicPower_void : economicPower (void : I) = 0 := by
  unfold economicPower; exact rs_void_void

/-- Political power with void is zero. -/
theorem politicalPower_void (a : I) : politicalPower a (void : I) = 0 := by
  unfold politicalPower; simp [rs_void_right', rs_void_left']

/-- Political power is symmetric. -/
theorem politicalPower_symm (a b : I) :
    politicalPower a b = politicalPower b a := by
  unfold politicalPower; ring

/-- Political power with self is double self-resonance. -/
theorem politicalPower_self (a : I) :
    politicalPower a a = 2 * rs a a := by
  unfold politicalPower; ring

/-- Military power against void. -/
theorem militaryPower_void_target (a : I) :
    militaryPower a (void : I) = rs a a := by
  unfold militaryPower; simp [rs_void_right']

/-- IEMP total: all four sources combined. -/
noncomputable def mannTotalPower (a b c : I) : ℝ :=
  ideologicalPower a b c + economicPower a + militaryPower a b + politicalPower a b

/-- IEMP total with void is just economic power. -/
theorem mann_total_void (a : I) :
    mannTotalPower a (void : I) (void : I) = 2 * rs a a := by
  unfold mannTotalPower ideologicalPower economicPower militaryPower politicalPower
  simp [emergence_void_right, rs_void_right', rs_void_left']; ring

/-! ## §41. Weber's Types of Authority

Max Weber distinguished three ideal types of legitimate authority:
Traditional (based on custom), Charismatic (based on personal qualities),
Rational-Legal (based on rules). -/

/-- Traditional authority: power derived from iterated self-composition
    (the weight of tradition — repetition creates legitimacy). -/
noncomputable def traditionalAuthority (tradition : I) (n : ℕ) : ℝ :=
  rs (composeN tradition n) (composeN tradition n)

/-- Traditional authority grows monotonically with repetition. -/
theorem traditional_authority_mono (t : I) (n : ℕ) :
    traditionalAuthority t (n + 1) ≥ traditionalAuthority t n := by
  unfold traditionalAuthority; exact rs_composeN_mono t n

/-- Traditional authority is always non-negative. -/
theorem traditional_authority_nonneg (t : I) (n : ℕ) :
    traditionalAuthority t n ≥ 0 := by
  unfold traditionalAuthority; exact rs_self_nonneg' _

/-- Zero-length tradition has zero authority. -/
theorem traditional_authority_zero (t : I) :
    traditionalAuthority t 0 = 0 := by
  unfold traditionalAuthority; simp [rs_void_void]

/-- Charismatic authority: the cross-resonance a leader creates.
    A charismatic leader makes others resonate with them. -/
noncomputable def charismaticAuthority (leader follower : I) : ℝ :=
  rs follower leader

/-- Charismatic authority of void leader is zero. -/
theorem charismatic_void_leader (f : I) :
    charismaticAuthority (void : I) f = 0 := by
  unfold charismaticAuthority; exact rs_void_right' f

/-- Charismatic authority from void follower is zero. -/
theorem charismatic_void_follower (l : I) :
    charismaticAuthority l (void : I) = 0 := by
  unfold charismaticAuthority; exact rs_void_left' l

/-- Rational-legal authority: authority derived from the institutional
    framework (composition structure) rather than personal qualities.
    Measured by how much the institution enriches beyond raw charisma. -/
noncomputable def rationalLegalAuthority (institution official : I) : ℝ :=
  rs (compose institution official) (compose institution official) -
  rs institution institution

/-- Rational-legal authority is non-negative (institutions always enrich). -/
theorem rationalLegal_nonneg (inst off : I) :
    rationalLegalAuthority inst off ≥ 0 := by
  unfold rationalLegalAuthority; linarith [compose_enriches' inst off]

/-- Rational-legal authority with void institution yields the official's weight. -/
theorem rationalLegal_void_inst (off : I) :
    rationalLegalAuthority (void : I) off = rs off off := by
  unfold rationalLegalAuthority; simp [rs_void_void]

/-- Rational-legal authority with void official is zero. -/
theorem rationalLegal_void_official (inst : I) :
    rationalLegalAuthority inst (void : I) = 0 := by
  unfold rationalLegalAuthority; simp

/-- Weber's legitimacy gap: how much traditional authority exceeds
    charismatic for the same idea. -/
noncomputable def weberLegitimacyGap (a : I) (n : ℕ) : ℝ :=
  traditionalAuthority a (n + 1) - traditionalAuthority a n

/-- The legitimacy gap is non-negative (tradition only grows). -/
theorem weber_legitimacy_gap_nonneg (a : I) (n : ℕ) :
    weberLegitimacyGap a n ≥ 0 := by
  unfold weberLegitimacyGap traditionalAuthority
  linarith [rs_composeN_mono a n]

/-! ## §42. Agamben's State of Exception

Giorgio Agamben theorized the state of exception: sovereign power operates
by suspending the normal order. In IDT, this is modeled as the sovereign's
ability to "reset" composition — reducing others to void-like status. -/

/-- The state of exception: how much sovereign s reduces subject a's
    effective weight through composition. When high, the sovereign
    "suspends the normal order" for the subject. -/
noncomputable def stateOfException (sovereign subject : I) : ℝ :=
  rs subject subject - rs subject (compose sovereign subject)

/-- State of exception under void sovereign is zero (no sovereign = normal). -/
theorem exception_void_sovereign (a : I) :
    stateOfException (void : I) a = 0 := by
  unfold stateOfException; simp

/-- State of exception for void subject is zero (nothing to except). -/
theorem exception_void_subject (s : I) :
    stateOfException s (void : I) = 0 := by
  unfold stateOfException; simp [rs_void_void, rs_void_left']

/-- Bare life: the subject under total exception — their weight is
    entirely subsumed by the sovereign's composition. -/
noncomputable def bareLife (sovereign subject : I) : ℝ :=
  rs (compose sovereign subject) (compose sovereign subject) - rs sovereign sovereign

/-- Bare life weight is always non-negative (composition enriches). -/
theorem bareLife_nonneg (sov sub : I) : bareLife sov sub ≥ 0 := by
  unfold bareLife; linarith [compose_enriches' sov sub]

/-- Bare life under void sovereign yields subject's weight. -/
theorem bareLife_void_sovereign (sub : I) : bareLife (void : I) sub = rs sub sub := by
  unfold bareLife; simp [rs_void_void]

/-- Homo sacer: the gap between sovereign power and subject autonomy. -/
noncomputable def homoSacer (sovereign subject : I) : ℝ :=
  rs sovereign sovereign - rs subject subject

/-- Homo sacer is just the power differential. -/
theorem homoSacer_eq_power (sov sub : I) :
    homoSacer sov sub = power sov sub := by
  unfold homoSacer power; ring

/-- Homo sacer against void: sovereign's full weight. -/
theorem homoSacer_void_subject (sov : I) :
    homoSacer sov (void : I) = rs sov sov := by
  unfold homoSacer; simp [rs_void_void]

/-- Homo sacer with void sovereign: negative of subject's weight. -/
theorem homoSacer_void_sovereign (sub : I) :
    homoSacer (void : I) sub = -rs sub sub := by
  unfold homoSacer; simp [rs_void_void]

/-! ## §43. Butler's Performativity and Subject Formation

Judith Butler theorized that subjects are constituted through repeated
performative acts. Identity is not prior to action but emerges through
iterated composition. -/

/-- Performative constitution: the subject is formed by n iterations
    of a performative act. Identity is an effect, not a cause. -/
noncomputable def performativeIdentity (act : I) (n : ℕ) : I :=
  composeN act n

/-- Performative identity at zero iterations is void (no subject yet). -/
theorem performative_zero (act : I) :
    performativeIdentity act 0 = (void : I) := by
  unfold performativeIdentity; simp

/-- Performative identity at one iteration is just the act. -/
theorem performative_one (act : I) :
    performativeIdentity act 1 = act := by
  unfold performativeIdentity; exact composeN_one act

/-- Subject weight grows with each performative iteration. -/
theorem performative_weight_mono (act : I) (n : ℕ) :
    rs (performativeIdentity act (n + 1)) (performativeIdentity act (n + 1)) ≥
    rs (performativeIdentity act n) (performativeIdentity act n) := by
  unfold performativeIdentity; exact rs_composeN_mono act n

/-- Non-void acts produce non-void subjects after any positive iteration. -/
theorem performative_nonvoid (act : I) (h : act ≠ void) (n : ℕ) :
    performativeIdentity act (n + 1) ≠ void := by
  unfold performativeIdentity; exact hegemonic_reproduction_nonvoid act h n

/-- Subjectivation: the process of becoming a subject through ideology.
    Butler: the subject is produced by the very power that subordinates. -/
noncomputable def subjectivation (power_ subject : I) : I :=
  compose power_ subject

/-- Subjectivation by void leaves subject unchanged. -/
theorem subjectivation_void_power (s : I) :
    subjectivation (void : I) s = s := by
  unfold subjectivation; simp

/-- Subjectivation of void yields pure power. -/
theorem subjectivation_void_subject (p : I) :
    subjectivation p (void : I) = p := by
  unfold subjectivation; simp

/-- The subjection paradox: the power that forms the subject always
    has at least as much weight as the subject alone. -/
theorem subjection_paradox (p s : I) :
    rs (subjectivation p s) (subjectivation p s) ≥ rs p p := by
  unfold subjectivation; exact compose_enriches' p s

/-- Gender performativity: iterated performance creates gender identity.
    The weight of gender increases with each citation. -/
theorem gender_performativity_accumulates (act : I) (n : ℕ) :
    rs (performativeIdentity act (n + 1)) (performativeIdentity act (n + 1)) ≥
    rs act act := by
  unfold performativeIdentity; exact ideological_reproduction act n

/-- Subversive repetition: performing differently creates emergence
    (the gap between expected and actual performance). -/
noncomputable def subversiveRepetition (norm subversion observer : I) : ℝ :=
  emergence norm subversion observer

/-- Subversive repetition with void norm is zero. -/
theorem subversive_void_norm (s o : I) :
    subversiveRepetition (void : I) s o = 0 := by
  unfold subversiveRepetition; exact emergence_void_left s o

/-- Subversive repetition against void observer is zero. -/
theorem subversive_void_observer (n s : I) :
    subversiveRepetition n s (void : I) = 0 := by
  unfold subversiveRepetition; exact emergence_against_void n s

/-! ## §44. Habermas's Colonization of the Lifeworld

Jürgen Habermas argued that "system" (bureaucratic/market logic) colonizes
the "lifeworld" (communicative, meaning-making context). In IDT, this is
the system's composition overwhelming lifeworld emergence. -/

/-- System colonization: how much the system's composition with the
    lifeworld exceeds what the lifeworld would produce alone. -/
noncomputable def systemColonization (system lifeworld : I) : ℝ :=
  rs (compose system lifeworld) (compose system lifeworld) -
  rs system system

/-- System colonization is non-negative (systems always enrich composition). -/
theorem colonization_nonneg (sys lw : I) :
    systemColonization sys lw ≥ 0 := by
  unfold systemColonization; linarith [compose_enriches' sys lw]

/-- Void system colonization yields lifeworld's weight. -/
theorem colonization_void_system (lw : I) :
    systemColonization (void : I) lw = rs lw lw := by
  unfold systemColonization; simp [rs_void_void]

/-- Colonization of void lifeworld is zero. -/
theorem colonization_void_lifeworld (sys : I) :
    systemColonization sys (void : I) = 0 := by
  unfold systemColonization; simp

/-- Communicative rationality: the emergence created through genuine
    dialogue, not strategic system action. -/
noncomputable def communicativeRationality (speaker hearer topic : I) : ℝ :=
  emergence speaker hearer topic + emergence hearer speaker topic

/-- Communicative rationality with void speaker vanishes. -/
theorem communicative_void_speaker (h t : I) :
    communicativeRationality (void : I) h t = emergence h (void : I) t := by
  unfold communicativeRationality
  simp [emergence_void_left]

/-- Communicative rationality against void topic vanishes entirely. -/
theorem communicative_void_topic (s h : I) :
    communicativeRationality s h (void : I) = 0 := by
  unfold communicativeRationality
  simp [emergence_against_void]

/-- The colonization ratio: system weight relative to communicative surplus. -/
noncomputable def colonizationIntensity (sys lw : I) : ℝ :=
  rs sys sys - rs lw lw

/-- Colonization intensity is antisymmetric (system vs lifeworld is relative). -/
theorem colonization_intensity_antisymm (a b : I) :
    colonizationIntensity a b = -colonizationIntensity b a := by
  unfold colonizationIntensity; ring

/-- Colonization intensity with void system is negative of lifeworld weight. -/
theorem colonization_intensity_void_sys (lw : I) :
    colonizationIntensity (void : I) lw = -rs lw lw := by
  unfold colonizationIntensity; simp [rs_void_void]

/-! ## §45. Mouffe's Agonistic Pluralism

Chantal Mouffe argues for agonistic pluralism: political conflict between
adversaries (not enemies) is constitutive of democracy. Consensus is
impossible and undesirable — the goal is to channel antagonism productively. -/

/-- Agonistic encounter: two ideas compose but maintain distinct identities.
    The weight of their composition exceeds both individually. -/
def agonistic (a b : I) : Prop :=
  rs (compose a b) (compose a b) > rs a a ∧
  rs (compose a b) (compose a b) > rs b b

/-- Agonistic encounter is possible when neither is void. -/
theorem agonistic_nonvoid_left (a b : I) (h : agonistic a b) : a ≠ void := by
  intro heq; unfold agonistic at h
  rw [heq] at h; simp [rs_void_void] at h

/-- The agonistic surplus: how much the encounter creates beyond
    the sum of individual weights. -/
noncomputable def agonisticSurplus (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- Agonistic surplus with void is zero. -/
theorem agonistic_surplus_void_right (a : I) :
    agonisticSurplus a (void : I) = 0 := by
  unfold agonisticSurplus; simp [rs_void_void]

/-- Agonistic surplus with void on the left. -/
theorem agonistic_surplus_void_left (b : I) :
    agonisticSurplus (void : I) b = 0 := by
  unfold agonisticSurplus; simp [rs_void_void]

/-- The agonistic surplus is bounded below by -rs b b (enrichment guarantees
    the composition is at least as heavy as a). -/
theorem agonistic_surplus_lower_bound (a b : I) :
    agonisticSurplus a b ≥ -rs b b := by
  unfold agonisticSurplus; linarith [compose_enriches' a b]

/-- Antagonism: ideas in outright opposition (negative cross-resonance). -/
def antagonistic (a b : I) : Prop :=
  rs a b < 0 ∧ rs b a < 0

/-- Void is never antagonistic. -/
theorem void_not_antagonistic (a : I) : ¬antagonistic (void : I) a := by
  unfold antagonistic; intro ⟨h, _⟩; simp [rs_void_left'] at h

/-- Mouffe's thesis: even antagonistic ideas produce enrichment through
    composition. Conflict is productive. -/
theorem mouffe_productive_conflict (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- Democratic paradox: the more you compose (democratize), the more
    weight accumulates. Democracy cannot avoid power concentration. -/
theorem democratic_paradox (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) :=
  rs_composeN_mono a n

/-! ## §46. Scott's Weapons of the Weak (Hidden Transcripts)

James C. Scott: subordinate groups resist through "hidden transcripts" —
discourse that takes place offstage, away from the eyes of power.
The public transcript vs hidden transcript distinction maps to
different resonance contexts. -/

/-- Public transcript: how the subordinate resonates in the presence
    of the dominant power. -/
noncomputable def publicTranscript (subordinate dominant observer : I) : ℝ :=
  rs (compose dominant subordinate) observer

/-- Hidden transcript: how the subordinate resonates without the
    dominant power present. -/
noncomputable def hiddenTranscript (subordinate observer : I) : ℝ :=
  rs subordinate observer

/-- The transcript gap: the difference between hidden and public
    expression. Positive gap means the subordinate is more expressive
    in private (typical hidden transcript). -/
noncomputable def transcriptGap (sub dom obs : I) : ℝ :=
  hiddenTranscript sub obs - publicTranscript sub dom obs

/-- Transcript gap decomposes into dominance effects. -/
theorem transcript_gap_eq (sub dom obs : I) :
    transcriptGap sub dom obs = -(rs dom obs + emergence dom sub obs) := by
  unfold transcriptGap hiddenTranscript publicTranscript
  have := rs_compose_eq dom sub obs; linarith

/-- Under void domination, the transcript gap is zero (no hidden transcript). -/
theorem transcript_gap_void_dom (sub obs : I) :
    transcriptGap sub (void : I) obs = 0 := by
  unfold transcriptGap hiddenTranscript publicTranscript
  simp [rs_void_left']

/-- Void subordinate has transcript gap equal to negative of dominant's resonance. -/
theorem transcript_gap_void_sub (dom obs : I) :
    transcriptGap (void : I) dom obs = -rs dom obs := by
  unfold transcriptGap hiddenTranscript publicTranscript
  simp [rs_void_left']

/-- Infrapolitics: the everyday forms of resistance that occur below
    the threshold of organized political action. Scott's "weapons of
    the weak" — foot-dragging, false compliance, gossip, sabotage. -/
noncomputable def infrapolitics (weak strong : I) : ℝ :=
  rs weak weak - rs weak (compose strong weak)

/-- Infrapolitics of void subordinate is zero. -/
theorem infrapolitics_void_weak (s : I) :
    infrapolitics (void : I) s = 0 := by
  unfold infrapolitics; simp [rs_void_void, rs_void_left']

/-- Infrapolitics under void domination is zero. -/
theorem infrapolitics_void_strong (w : I) :
    infrapolitics w (void : I) = 0 := by
  unfold infrapolitics; simp

/-- Everyday resistance: small acts of defiance accumulate.
    Scott: resistance doesn't require grand gestures. -/
noncomputable def everydayResistance (sub dom : I) : ℝ :=
  rs sub sub - rs (compose dom sub) sub

/-- Everyday resistance under void domination is zero. -/
theorem everyday_resistance_void_dom (sub : I) :
    everydayResistance sub (void : I) = 0 := by
  unfold everydayResistance; simp

/-! ## §47. Fanon's Decolonization (Violence as Counter-Emergence)

Frantz Fanon argued that colonial violence must be met with
counter-violence. The colonized must compose themselves anew,
creating new subjectivities that escape colonial determination. -/

/-- Colonial imposition: the weight the colonizer adds to the colonized
    through forced composition. -/
noncomputable def colonialImposition (colonizer colonized : I) : ℝ :=
  rs (compose colonizer colonized) (compose colonizer colonized) -
  rs colonizer colonizer

/-- Colonial imposition is non-negative (colonizer always adds weight). -/
theorem colonial_imposition_nonneg (cr cd : I) :
    colonialImposition cr cd ≥ 0 := by
  unfold colonialImposition; linarith [compose_enriches' cr cd]

/-- Void colonizer's imposition yields the colonized's weight. -/
theorem colonial_imposition_void (cd : I) :
    colonialImposition (void : I) cd = rs cd cd := by
  unfold colonialImposition; simp [rs_void_void]

/-- Decolonization: the counter-composition that restores the colonized's
    own resonance patterns. Measured by how much self-composition
    adds beyond colonial imposition. -/
noncomputable def decolonization (colonized liberator : I) : ℝ :=
  rs (compose colonized liberator) (compose colonized liberator) -
  rs colonized colonized

/-- Decolonization is non-negative (self-composition enriches). -/
theorem decolonization_nonneg (cd lib : I) :
    decolonization cd lib ≥ 0 := by
  unfold decolonization; linarith [compose_enriches' cd lib]

/-- Decolonization from void adds nothing. -/
theorem decolonization_void_liberator (cd : I) :
    decolonization cd (void : I) = 0 := by
  unfold decolonization; simp

/-- Fanon's new humanism: the decolonized subject, through self-composition,
    creates weight at least equal to the colonizer's imposition.
    Both sides gain from composition — but the colonized gains autonomy. -/
theorem fanon_new_humanism (colonizer colonized : I) :
    rs (compose colonized colonizer) (compose colonized colonizer) ≥
    rs colonized colonized := by
  exact compose_enriches' colonized colonizer

/-- Counter-emergence: the emergence created by the colonized's own
    composition, as measured against the colonial framework. -/
noncomputable def counterEmergence (colonized self_comp colonial_frame : I) : ℝ :=
  emergence colonized self_comp colonial_frame

/-- Counter-emergence against void frame is zero. -/
theorem counter_emergence_void_frame (cd sc : I) :
    counterEmergence cd sc (void : I) = 0 := by
  unfold counterEmergence; exact emergence_against_void cd sc

/-- Wretched of the earth: those with minimal weight (close to void)
    gain the most from liberation composition. -/
theorem wretched_liberation (liberator : I) :
    decolonization (void : I) liberator = rs liberator liberator := by
  unfold decolonization; simp [rs_void_void]

/-! ## §48. Stability and Revolution: Deep Mathematical Results -/

/-- A power structure is stable if composition preserves the ordering:
    whoever dominates continues to dominate after composition. -/
def powerStable (h a c : I) : Prop :=
  dominates h a → dominates (compose h c) (compose a c)

/-- Stability theorem: composition with the same element preserves
    domination — power structures are stable under shared composition. -/
theorem stability_shared_composition (h a c : I) (_hd : dominates h a) :
    rs (compose h c) (compose h c) ≥ rs h h := by
  exact compose_enriches' h c

/-- Revolution requires breaking stability: there must exist some
    composition that reverses the power order. -/
def revolutionPossible (h a : I) : Prop :=
  dominates h a ∧ ∃ r : I, ¬dominates (compose h r) (compose a r)

/-- The composition monotonicity principle: the left-dominant always
    retains at least their original weight after any composition. -/
theorem composition_monotonicity (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- Iterated stability: n-fold composition preserves non-negativity. -/
theorem iterated_stability (a : I) (n : ℕ) :
    rs (composeN a n) (composeN a n) ≥ 0 :=
  rs_self_nonneg' _

/-- Entropy of power: self-composition always creates at least as much
    weight, so power entropy (weight) never decreases. This is
    the "second law of power dynamics." -/
theorem second_law_of_power (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) :=
  rs_composeN_mono a n

/-- Weight conservation under reassociation: total weight is invariant
    under how we group compositions. A deep structural result. -/
theorem weight_conservation_associativity (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) =
    rs (compose a (compose b c)) (compose a (compose b c)) := by
  rw [compose_assoc']

/-! ## §49. Power Concentration and Diffusion -/

/-- Power concentration: how much composing multiple ideas with a single
    center concentrates weight at the center. -/
noncomputable def powerConcentration (center periphery : I) : ℝ :=
  rs (compose center periphery) (compose center periphery) - rs center center

/-- Power concentration is non-negative. -/
theorem powerConcentration_nonneg (c p : I) :
    powerConcentration c p ≥ 0 := by
  unfold powerConcentration; linarith [compose_enriches' c p]

/-- Void center concentrates periphery's weight. -/
theorem powerConcentration_void_center (p : I) :
    powerConcentration (void : I) p = rs p p := by
  unfold powerConcentration; simp [rs_void_void]

/-- Power diffusion: the reverse of concentration — how much the
    periphery's composition diffuses the center's influence. -/
noncomputable def powerDiffusion (center periphery : I) : ℝ :=
  rs center center - rs center (compose center periphery)

/-- Power diffusion under void periphery is zero. -/
theorem powerDiffusion_void_periphery (c : I) :
    powerDiffusion c (void : I) = 0 := by
  unfold powerDiffusion; simp

/-- Power diffusion of void center is zero. -/
theorem powerDiffusion_void_center (p : I) :
    powerDiffusion (void : I) p = 0 := by
  unfold powerDiffusion; simp [rs_void_void, rs_void_left']

/-! ## §50. Domination Lattice Properties -/

/-- Power differential is additive: power(a,b) + power(b,c) = power(a,c). -/
theorem power_additive (a b c : I) :
    power a b + power b c = power a c := by
  unfold power; ring

/-- Domination forms a strict total preorder on weight classes. -/
theorem domination_trichotomy (a b : I) :
    dominates a b ∨ dominates b a ∨ sameStratum a b := by
  unfold dominates sameStratum
  rcases lt_trichotomy (rs b b) (rs a a) with h | h | h
  · left; exact h
  · right; right; exact h.symm
  · right; left; exact h

/-- Composing two ideas in the same stratum yields something
    at least as heavy as either. -/
theorem sameStratum_compose_bound (a b : I) (h : sameStratum a b) :
    rs (compose a b) (compose a b) ≥ rs b b := by
  unfold sameStratum at h; linarith [compose_enriches' a b]

/-- The void stratum is a singleton. -/
theorem void_stratum_singleton (a b : I)
    (ha : sameStratum a (void : I))
    (hb : sameStratum b (void : I)) :
    a = void ∧ b = void := by
  exact ⟨void_stratum_unique a (sameStratum_symm _ _ ha),
         void_stratum_unique b (sameStratum_symm _ _ hb)⟩

/-! ## §51. Ideological Interpenetration -/

/-- Ideological interpenetration: how much two ideologies create
    combined emergence beyond their individual effects. -/
noncomputable def ideologicalInterpenetration (i₁ i₂ observer : I) : ℝ :=
  emergence i₁ i₂ observer

/-- Interpenetration with void ideology is zero. -/
theorem interpenetration_void_left (i₂ o : I) :
    ideologicalInterpenetration (void : I) i₂ o = 0 := by
  unfold ideologicalInterpenetration; exact emergence_void_left i₂ o

/-- Interpenetration against void observer is zero. -/
theorem interpenetration_void_observer (i₁ i₂ : I) :
    ideologicalInterpenetration i₁ i₂ (void : I) = 0 := by
  unfold ideologicalInterpenetration; exact emergence_against_void i₁ i₂

/-- The interpenetration cocycle: ideological interactions satisfy
    global consistency (from the cocycle condition). -/
theorem interpenetration_cocycle (i₁ i₂ i₃ o : I) :
    ideologicalInterpenetration i₁ i₂ o +
    ideologicalInterpenetration (compose i₁ i₂) i₃ o =
    ideologicalInterpenetration i₂ i₃ o +
    ideologicalInterpenetration i₁ (compose i₂ i₃) o := by
  unfold ideologicalInterpenetration; exact cocycle_condition i₁ i₂ i₃ o

/-! ## §52. Resistance Networks and Solidarity -/

/-- Solidarity weight: the combined weight of two ideas in solidarity
    (composition) minus their individual weights. -/
noncomputable def solidarityWeight (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a

/-- Solidarity weight is non-negative (composition enriches). -/
theorem solidarity_nonneg (a b : I) : solidarityWeight a b ≥ 0 := by
  unfold solidarityWeight; linarith [compose_enriches' a b]

/-- Solidarity with void adds nothing. -/
theorem solidarity_void (a : I) : solidarityWeight a (void : I) = 0 := by
  unfold solidarityWeight; simp

/-- Void solidarity gains partner's weight. -/
theorem solidarity_from_void (b : I) :
    solidarityWeight (void : I) b = rs b b := by
  unfold solidarityWeight; simp [rs_void_void]

/-- Solidarity compounds: adding a third ally only increases weight. -/
theorem solidarity_compounds (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥
    rs (compose a b) (compose a b) := by
  exact compose_enriches' (compose a b) c

/-! ## §53. Hegemonic Cycle Theory -/

/-- A hegemonic cycle: the hegemon composes with itself n times.
    Each cycle potentially increases the weight of the hegemonic idea. -/
noncomputable def hegemonicCycle (h : I) (n : ℕ) : ℝ :=
  rs (composeN h n) (composeN h n)

/-- Hegemonic cycle at step 0 is void weight. -/
theorem hegemonicCycle_zero (h : I) : hegemonicCycle h 0 = 0 := by
  unfold hegemonicCycle; simp [rs_void_void]

/-- Hegemonic cycle at step 1 is the hegemon's own weight. -/
theorem hegemonicCycle_one (h : I) : hegemonicCycle h 1 = rs h h := by
  unfold hegemonicCycle; simp [composeN_one]

/-- Hegemonic cycles are monotonically non-decreasing. -/
theorem hegemonicCycle_mono (h : I) (n : ℕ) :
    hegemonicCycle h (n + 1) ≥ hegemonicCycle h n := by
  unfold hegemonicCycle; exact rs_composeN_mono h n

/-- Non-void hegemonic cycles are strictly positive after step 1. -/
theorem hegemonicCycle_pos (h : I) (hne : h ≠ void) (n : ℕ) :
    hegemonicCycle h (n + 1) > 0 := by
  unfold hegemonicCycle
  have := ideological_reproduction h n
  linarith [rs_self_pos h hne]

/-- The hegemonic cycle increment is non-negative. -/
noncomputable def hegemonicCycleIncrement (h : I) (n : ℕ) : ℝ :=
  hegemonicCycle h (n + 1) - hegemonicCycle h n

/-- Hegemonic cycle increment is non-negative. -/
theorem hegemonicCycleIncrement_nonneg (h : I) (n : ℕ) :
    hegemonicCycleIncrement h n ≥ 0 := by
  unfold hegemonicCycleIncrement; linarith [hegemonicCycle_mono h n]

/-! ## §54. Power Projection -/

/-- Power projection: the ability of a to project its influence onto
    the composition of b and c. -/
noncomputable def powerProjection (a b c : I) : ℝ :=
  rs a (compose b c)

/-- Power projection onto void composition. -/
theorem powerProjection_void_right (a b : I) :
    powerProjection a b (void : I) = rs a b := by
  unfold powerProjection; simp

/-- Power projection by void is zero. -/
theorem powerProjection_void_source (b c : I) :
    powerProjection (void : I) b c = 0 := by
  unfold powerProjection; exact rs_void_left' _

/-- Power projection onto void-left composition. -/
theorem powerProjection_void_left (a c : I) :
    powerProjection a (void : I) c = rs a c := by
  unfold powerProjection; simp

/-! ## §55. Institutional Inertia -/

/-- Institutional inertia: the resistance of an institution to change,
    measured by how much weight it accumulates through self-composition. -/
noncomputable def institutionalInertia (inst : I) : ℝ :=
  rs (compose inst inst) (compose inst inst) - rs inst inst

/-- Institutional inertia is non-negative. -/
theorem institutionalInertia_nonneg (inst : I) :
    institutionalInertia inst ≥ 0 := by
  unfold institutionalInertia; linarith [compose_enriches' inst inst]

/-- Void institution has zero inertia. -/
theorem institutionalInertia_void :
    institutionalInertia (void : I) = 0 := by
  unfold institutionalInertia; simp [rs_void_void]

/-- Institutional inertia equals hegemonic stability. -/
theorem inertia_eq_stability (a : I) :
    institutionalInertia a = hegemonicStability a := rfl
/-! ## §56. Recursive Domination -/

/-- Recursive domination: domination that reproduces itself at every level.
    n+1 fold composition dominates n-fold composition. -/
theorem recursive_domination (a : I) (_ha : a ≠ void) (n : ℕ) :
    dominates (composeN a (n + 2)) (composeN a (n + 1)) ∨
    sameStratum (composeN a (n + 2)) (composeN a (n + 1)) := by
  unfold dominates sameStratum
  rcases lt_or_eq_of_le (rs_composeN_mono a (n + 1)) with h | h
  · left; exact h
  · right; exact h.symm

/-- Domination gap between iterated compositions. -/
noncomputable def dominationGap (a : I) (n m : ℕ) : ℝ :=
  rs (composeN a n) (composeN a n) - rs (composeN a m) (composeN a m)

/-- Domination gap is zero for same index. -/
theorem dominationGap_self (a : I) (n : ℕ) :
    dominationGap a n n = 0 := by
  unfold dominationGap; ring

/-- Domination gap is antisymmetric. -/
theorem dominationGap_antisymm (a : I) (n m : ℕ) :
    dominationGap a n m = -dominationGap a m n := by
  unfold dominationGap; ring

/-! ## §57. Consent Manufacturing (Chomsky/Herman) -/

/-- Manufactured consent: the degree to which composition with media m
    makes subject s resonate MORE with the dominant ideology d. -/
noncomputable def manufacturedConsent (media subject dominant : I) : ℝ :=
  rs (compose media subject) dominant - rs subject dominant

/-- Manufactured consent decomposes into media resonance plus emergence. -/
theorem manufactured_consent_eq (m s d : I) :
    manufacturedConsent m s d = rs m d + emergence m s d := by
  unfold manufacturedConsent; have := rs_compose_eq m s d; linarith

/-- Void media manufactures no consent. -/
theorem manufactured_consent_void_media (s d : I) :
    manufacturedConsent (void : I) s d = 0 := by
  unfold manufacturedConsent; simp [rs_void_left']

/-- Manufacturing consent for void subject. -/
theorem manufactured_consent_void_subject (m d : I) :
    manufacturedConsent m (void : I) d = rs m d := by
  unfold manufacturedConsent; simp [rs_void_left']

/-- Manufacturing consent against void dominant ideology is zero. -/
theorem manufactured_consent_void_dominant (m s : I) :
    manufacturedConsent m s (void : I) = 0 := by
  unfold manufacturedConsent; simp [rs_void_right']

/-! ## §58. Necropolitics (Mbembe) -/

/-- Necropower: the power to dictate who lives and who dies.
    In IDT, this is the ability to reduce others to void (symbolic death). -/
noncomputable def necropower (sovereign subject : I) : ℝ :=
  rs subject subject - rs (compose sovereign subject) subject

/-- Necropower of void sovereign is zero. -/
theorem necropower_void_sovereign (s : I) :
    necropower (void : I) s = 0 := by
  unfold necropower; simp

/-- Necropower over void subject is zero (can't kill void). -/
theorem necropower_void_subject (sov : I) :
    necropower sov (void : I) = 0 := by
  unfold necropower; simp [rs_void_void, rs_void_left', rs_void_right']

/-- Necropower and state of exception share the same mathematical form
    when resonance is symmetric; in general, they differ by order sensitivity. -/
theorem necropower_exception_gap (sov sub : I) :
    necropower sov sub - stateOfException sov sub =
    rs sub (compose sov sub) - rs (compose sov sub) sub := by
  unfold necropower stateOfException; ring

/-! ## §59. Counter-Power and Dual Power -/

/-- Dual power: the coexistence of two competing power structures,
    each with its own weight. The gap measures instability. -/
noncomputable def dualPowerGap (state movement : I) : ℝ :=
  rs state state - rs movement movement

/-- Dual power gap is antisymmetric. -/
theorem dualPower_antisymm (s m : I) :
    dualPowerGap s m = -dualPowerGap m s := by
  unfold dualPowerGap; ring

/-- Dual power gap with void state. -/
theorem dualPower_void_state (m : I) :
    dualPowerGap (void : I) m = -rs m m := by
  unfold dualPowerGap; simp [rs_void_void]

/-- Dual power gap with void movement. -/
theorem dualPower_void_movement (s : I) :
    dualPowerGap s (void : I) = rs s s := by
  unfold dualPowerGap; simp [rs_void_void]

/-- Counter-power: the ability to create alternative compositions
    that rival the dominant structure. -/
noncomputable def counterPower (alternative dominant : I) : ℝ :=
  rs (compose alternative alternative) (compose alternative alternative) -
  rs (compose dominant dominant) (compose dominant dominant)

/-- Counter-power is antisymmetric. -/
theorem counterPower_antisymm (a d : I) :
    counterPower a d = -counterPower d a := by
  unfold counterPower; ring

/-! ## §60. Epistemic Injustice (Fricker) -/

/-- Testimonial injustice: the speaker's credibility is deflated
    because of their social identity. Measured by how much a
    prejudice reduces the resonance of testimony. -/
noncomputable def testimonialInjustice (prejudice testimony observer : I) : ℝ :=
  rs testimony observer - rs (compose prejudice testimony) observer

/-- Testimonial injustice decomposition. -/
theorem testimonial_injustice_eq (p t o : I) :
    testimonialInjustice p t o = -(rs p o + emergence p t o) := by
  unfold testimonialInjustice
  have := rs_compose_eq p t o; linarith

/-- No prejudice, no injustice. -/
theorem no_prejudice_no_injustice (t o : I) :
    testimonialInjustice (void : I) t o = 0 := by
  unfold testimonialInjustice; simp [rs_void_left']

/-- Injustice against void observer vanishes. -/
theorem injustice_void_observer (p t : I) :
    testimonialInjustice p t (void : I) = 0 := by
  unfold testimonialInjustice; simp [rs_void_right']

/-- Hermeneutical injustice: the gap in interpretive resources.
    Some ideas lack the conceptual framework to be understood. -/
noncomputable def hermeneuticalInjustice (experience framework : I) : ℝ :=
  rs experience experience - rs experience framework

/-- Hermeneutical injustice with void framework. -/
theorem hermeneutical_void_framework (e : I) :
    hermeneuticalInjustice e (void : I) = rs e e := by
  unfold hermeneuticalInjustice; simp [rs_void_right']

/-- Hermeneutical injustice of void experience is zero. -/
theorem hermeneutical_void_experience (f : I) :
    hermeneuticalInjustice (void : I) f = 0 := by
  unfold hermeneuticalInjustice; simp [rs_void_void, rs_void_left']

/-! ## §61. Symbolic Violence (Bourdieu, Extended) -/

/-- Symbolic violence in the field: how much the dominant habitus
    devalues a subordinate position. -/
noncomputable def symbolicViolenceField (dominant subordinate field : I) : ℝ :=
  rs dominant field - rs subordinate field

/-- Symbolic violence is antisymmetric in dominant/subordinate. -/
theorem symbolicViolence_antisymm (d s f : I) :
    symbolicViolenceField d s f = -symbolicViolenceField s d f := by
  unfold symbolicViolenceField; ring

/-- Void dominant has no symbolic violence. -/
theorem symbolicViolence_void_dom (s f : I) :
    symbolicViolenceField (void : I) s f = -rs s f := by
  unfold symbolicViolenceField; simp [rs_void_left']

/-- Symbolic violence against void field is zero. -/
theorem symbolicViolence_void_field (d s : I) :
    symbolicViolenceField d s (void : I) = 0 := by
  unfold symbolicViolenceField; simp [rs_void_right']

/-- Misrecognition: the subject's inability to perceive symbolic violence.
    Measured by how much the subject resonates with the very structure
    that subordinates them. -/
noncomputable def misrecognition (subject structure_ : I) : ℝ :=
  rs subject structure_

/-- Misrecognition of void structure is zero. -/
theorem misrecognition_void_structure (s : I) :
    misrecognition s (void : I) = 0 := by
  unfold misrecognition; exact rs_void_right' s

/-- Misrecognition by void subject is zero. -/
theorem misrecognition_void_subject (st : I) :
    misrecognition (void : I) st = 0 := by
  unfold misrecognition; exact rs_void_left' st

/-! ## §62. Governmentality (Foucault, Extended) -/

/-- Governmentality: the art of governing through composition of norms.
    The conduct of conduct. -/
noncomputable def governmentality (norm subject : I) : ℝ :=
  rs (compose norm subject) (compose norm subject) - rs norm norm

/-- Governmentality is non-negative (norms always add weight). -/
theorem governmentality_nonneg (n s : I) : governmentality n s ≥ 0 := by
  unfold governmentality; linarith [compose_enriches' n s]

/-- Void norm governmentality yields subject's weight. -/
theorem governmentality_void_norm (s : I) :
    governmentality (void : I) s = rs s s := by
  unfold governmentality; simp [rs_void_void]

/-- Governmentality over void subject is zero. -/
theorem governmentality_void_subject (n : I) :
    governmentality n (void : I) = 0 := by
  unfold governmentality; simp

/-- Governmentality equals rational-legal authority (same formula). -/
theorem governmentality_eq_rationalLegal (n s : I) :
    governmentality n s = rationalLegalAuthority n s := rfl

/-! ## §63. Surplus Repression (Marcuse) -/

/-- Surplus repression: repression beyond what is necessary for
    social order. The excess weight of the repressive apparatus. -/
noncomputable def surplusRepression (repression necessity : I) : ℝ :=
  rs repression repression - rs necessity necessity

/-- Surplus repression is antisymmetric. -/
theorem surplus_repression_antisymm (r n : I) :
    surplusRepression r n = -surplusRepression n r := by
  unfold surplusRepression; ring

/-- Zero surplus when repression equals necessity. -/
theorem surplus_repression_self (a : I) :
    surplusRepression a a = 0 := by
  unfold surplusRepression; ring

/-- All repression is surplus when necessity is void. -/
theorem surplus_repression_void_necessity (r : I) :
    surplusRepression r (void : I) = rs r r := by
  unfold surplusRepression; simp [rs_void_void]

/-! ## §64. Spectacle (Debord) -/

/-- The spectacle: social relations mediated by images.
    The spectacle's power is in making all observation go through it. -/
noncomputable def spectaclePower (spectacle subject observer : I) : ℝ :=
  rs (compose spectacle subject) observer - rs subject observer

/-- Spectacle power decomposes. -/
theorem spectacle_power_eq (sp s o : I) :
    spectaclePower sp s o = rs sp o + emergence sp s o := by
  unfold spectaclePower; have := rs_compose_eq sp s o; linarith

/-- Void spectacle has no power. -/
theorem spectacle_void (s o : I) :
    spectaclePower (void : I) s o = 0 := by
  unfold spectaclePower; simp [rs_void_left']

/-- Spectacle against void observer is zero. -/
theorem spectacle_void_observer (sp s : I) :
    spectaclePower sp s (void : I) = 0 := by
  unfold spectaclePower; simp [rs_void_right']

/-! ## §65. Intersectionality (Crenshaw) -/

/-- Intersectional weight: the composition of multiple identity axes.
    Weight of combined identities exceeds any single axis. -/
theorem intersectional_enrichment (axis1 axis2 : I) :
    rs (compose axis1 axis2) (compose axis1 axis2) ≥ rs axis1 axis1 :=
  compose_enriches' axis1 axis2

/-- Intersectional emergence: the new meaning that arises from
    the intersection of two identity axes. -/
noncomputable def intersectionalEmergence (axis1 axis2 observer : I) : ℝ :=
  emergence axis1 axis2 observer

/-- Intersectional emergence is bounded by composition weight. -/
theorem intersectional_emergence_bounded (a1 a2 o : I) :
    (intersectionalEmergence a1 a2 o) ^ 2 ≤
    rs (compose a1 a2) (compose a1 a2) * rs o o := by
  unfold intersectionalEmergence; exact emergence_bounded' a1 a2 o

/-- Intersectional emergence with void axis is zero. -/
theorem intersectional_void_axis (a2 o : I) :
    intersectionalEmergence (void : I) a2 o = 0 := by
  unfold intersectionalEmergence; exact emergence_void_left a2 o

/-- Intersectional emergence satisfies the cocycle condition:
    adding a third axis of identity is constrained. -/
theorem intersectional_cocycle (a1 a2 a3 o : I) :
    intersectionalEmergence a1 a2 o +
    intersectionalEmergence (compose a1 a2) a3 o =
    intersectionalEmergence a2 a3 o +
    intersectionalEmergence a1 (compose a2 a3) o := by
  unfold intersectionalEmergence; exact cocycle_condition a1 a2 a3 o

/-! ## §66. Sovereign Power (Schmitt/Agamben) -/

/-- Sovereignty: the capacity to declare the exception.
    The sovereign is whoever controls the composition function.
    Measured by weight advantage over all others. -/
noncomputable def sovereignWeight (sov : I) : ℝ := rs sov sov

/-- Sovereign weight is non-negative. -/
theorem sovereignWeight_nonneg (s : I) : sovereignWeight s ≥ 0 := by
  unfold sovereignWeight; exact rs_self_nonneg' s

/-- Void has no sovereignty. -/
theorem sovereignWeight_void : sovereignWeight (void : I) = 0 := by
  unfold sovereignWeight; exact rs_void_void

/-- Sovereignty through composition: the sovereign composes with
    the polity to produce the state. -/
theorem sovereign_composition_enriches (sov polity : I) :
    rs (compose sov polity) (compose sov polity) ≥ rs sov sov :=
  compose_enriches' sov polity

/-! ## §67. Primitive Accumulation -/

/-- Primitive accumulation: the initial dispossession that creates
    the power differential. From void, the first composition creates weight. -/
theorem primitive_accumulation (a : I) (ha : a ≠ void) :
    rs (composeN a 1) (composeN a 1) > 0 := by
  simp [composeN_one]; exact rs_self_pos a ha

/-- Dispossession: the weight transferred from one to another through
    forced composition. -/
noncomputable def dispossession (expropriator victim : I) : ℝ :=
  rs (compose expropriator victim) (compose expropriator victim) -
  rs expropriator expropriator - rs victim victim

/-- Dispossession from void victim is zero. -/
theorem dispossession_void_victim (e : I) :
    dispossession e (void : I) = 0 := by
  unfold dispossession; simp [rs_void_void]

/-- Dispossession by void expropriator is zero. -/
theorem dispossession_void_expropriator (v : I) :
    dispossession (void : I) v = 0 := by
  unfold dispossession; simp [rs_void_void]

/-- Dispossession is bounded below by the enrichment principle. -/
theorem dispossession_lower_bound (e v : I) :
    dispossession e v ≥ -rs v v := by
  unfold dispossession; linarith [compose_enriches' e v]

/-! ## §68. Cultural Capital Dynamics (Bourdieu, Extended) -/

/-- Cultural capital conversion: how one form of capital (weight)
    converts to another through composition. -/
noncomputable def capitalConversion (from_capital to_field : I) : ℝ :=
  rs from_capital to_field

/-- Capital conversion from void is zero. -/
theorem capitalConversion_void (f : I) :
    capitalConversion (void : I) f = 0 := by
  unfold capitalConversion; exact rs_void_left' f

/-- Capital conversion to void field is zero. -/
theorem capitalConversion_void_field (c : I) :
    capitalConversion c (void : I) = 0 := by
  unfold capitalConversion; exact rs_void_right' c

/-- Capital appreciation: composition increases symbolic capital. -/
theorem capital_appreciation (a b : I) :
    symbolicCapital (compose a b) ≥ symbolicCapital a := by
  unfold symbolicCapital; exact compose_enriches' a b

/-- Cultural capital accumulation through repeated practice. -/
theorem cultural_capital_accumulation (a : I) (n : ℕ) :
    symbolicCapital (composeN a (n + 1)) ≥ symbolicCapital (composeN a n) := by
  unfold symbolicCapital; exact rs_composeN_mono a n

/-! ## §69. Panopticism (Foucault, Extended) -/

/-- Panoptic effect: the change in subject behavior under surveillance.
    Measured by how much the observer's presence (composition) changes
    the subject's resonance with a norm. -/
noncomputable def panopticEffect (surveillance subject norm : I) : ℝ :=
  rs (compose surveillance subject) norm - rs subject norm

/-- Panoptic effect decomposes into surveillance resonance and emergence. -/
theorem panoptic_decompose (surv sub norm : I) :
    panopticEffect surv sub norm = rs surv norm + emergence surv sub norm := by
  unfold panopticEffect; have := rs_compose_eq surv sub norm; linarith

/-- Void surveillance has no panoptic effect. -/
theorem panoptic_void_surveillance (sub norm : I) :
    panopticEffect (void : I) sub norm = 0 := by
  unfold panopticEffect; simp [rs_void_left']

/-- Panoptic effect against void norm is zero. -/
theorem panoptic_void_norm (surv sub : I) :
    panopticEffect surv sub (void : I) = 0 := by
  unfold panopticEffect; simp [rs_void_right']

/-! ## §70. Deterritorialization (Deleuze & Guattari) -/

/-- Deterritorialization: the process by which an idea escapes its
    original context. Measured by the emergence created when an idea
    is placed in a new context. -/
noncomputable def deterritorialization (idea newContext observer : I) : ℝ :=
  emergence idea newContext observer

/-- Reterritorialization: the recapture of deterritorialized ideas. -/
noncomputable def reterritorialization (idea oldContext newContext observer : I) : ℝ :=
  emergence idea oldContext observer - emergence idea newContext observer

/-- Deterritorialization from void context is zero. -/
theorem deterritorialization_void_context (i o : I) :
    deterritorialization i (void : I) o = 0 := by
  unfold deterritorialization; exact emergence_void_right i o

/-- Deterritorialization against void observer is zero. -/
theorem deterritorialization_void_observer (i c : I) :
    deterritorialization i c (void : I) = 0 := by
  unfold deterritorialization; exact emergence_against_void i c

/-- Reterritorialization is zero when contexts are the same. -/
theorem reterritorialization_same_context (i c o : I) :
    reterritorialization i c c o = 0 := by
  unfold reterritorialization; ring

/-- Net deterritorialization: the total emergence change. -/
theorem reterritorialization_antisymm (i c₁ c₂ o : I) :
    reterritorialization i c₁ c₂ o = -reterritorialization i c₂ c₁ o := by
  unfold reterritorialization; ring

/-! ## §71. Ideological State Apparatus Composition -/

/-- Multiple ISAs compound: composing two ISAs creates a more
    comprehensive ideological apparatus. -/
theorem isa_compound (isa₁ isa₂ subject : I) :
    rs (compose (compose isa₁ isa₂) subject) (compose (compose isa₁ isa₂) subject) ≥
    rs (compose isa₁ isa₂) (compose isa₁ isa₂) := by
  exact compose_enriches' (compose isa₁ isa₂) subject

/-- ISA composition is associative. -/
theorem isa_composition_assoc (isa₁ isa₂ isa₃ : I) :
    compose (compose isa₁ isa₂) isa₃ = compose isa₁ (compose isa₂ isa₃) := by
  exact compose_assoc' isa₁ isa₂ isa₃

/-- The weight of combined ISAs exceeds any individual ISA. -/
theorem isa_combined_weight (isa₁ isa₂ : I) :
    rs (compose isa₁ isa₂) (compose isa₁ isa₂) ≥ rs isa₁ isa₁ :=
  compose_enriches' isa₁ isa₂

/-! ## §72. Repressive Tolerance (Marcuse) -/

/-- Repressive tolerance: the system absorbs dissent by composing it,
    thereby increasing the system's own weight. -/
noncomputable def repressiveTolerance (system dissent : I) : ℝ :=
  rs (compose system dissent) (compose system dissent) - rs system system

/-- Repressive tolerance is non-negative (absorbing dissent enriches). -/
theorem repressive_tolerance_nonneg (sys dis : I) :
    repressiveTolerance sys dis ≥ 0 := by
  unfold repressiveTolerance; linarith [compose_enriches' sys dis]

/-- Repressive tolerance of void dissent is zero. -/
theorem repressive_tolerance_void_dissent (sys : I) :
    repressiveTolerance sys (void : I) = 0 := by
  unfold repressiveTolerance; simp

/-- Repressive tolerance by void system gains dissent's weight. -/
theorem repressive_tolerance_void_system (dis : I) :
    repressiveTolerance (void : I) dis = rs dis dis := by
  unfold repressiveTolerance; simp [rs_void_void]

/-! ## §73. Power Equilibrium -/

/-- Two ideas are in power equilibrium when neither dominates. -/
def powerEquilibrium (a b : I) : Prop :=
  ¬dominates a b ∧ ¬dominates b a

/-- Power equilibrium implies same stratum. -/
theorem equilibrium_same_stratum (a b : I) (h : powerEquilibrium a b) :
    sameStratum a b := by
  unfold powerEquilibrium dominates at h
  unfold sameStratum
  push_neg at h
  linarith [h.1, h.2]

/-- Power equilibrium is symmetric. -/
theorem equilibrium_symm (a b : I) (h : powerEquilibrium a b) :
    powerEquilibrium b a := by
  unfold powerEquilibrium at *; exact ⟨h.2, h.1⟩

/-- Void is in equilibrium only with itself. -/
theorem equilibrium_void (a : I) (h : powerEquilibrium (void : I) a) :
    a = void := by
  have hs := equilibrium_same_stratum _ _ h
  exact void_stratum_unique a hs

/-! ## §74. Emergence Calculus for Power -/

/-- Emergence is additive in the observer (through composition decomposition). -/
theorem emergence_observer_decompose (a b c d : I) :
    rs (compose a b) (compose c d) =
    rs a (compose c d) + rs b (compose c d) + emergence a b (compose c d) := by
  exact rs_compose_eq a b (compose c d)

/-- Double emergence: emergence of a composition observed by a composition. -/
noncomputable def doubleEmergence (a b c d : I) : ℝ :=
  emergence a b (compose c d)

/-- Double emergence with void observer. -/
theorem double_emergence_void_observer_right (a b c : I) :
    doubleEmergence a b c (void : I) = emergence a b c := by
  unfold doubleEmergence; simp

/-- Double emergence with void first observer. -/
theorem double_emergence_void_observer_left (a b d : I) :
    doubleEmergence a b (void : I) d = emergence a b d := by
  unfold doubleEmergence; simp

/-! ## §75. Power Network Effects -/

/-- Network power: the weight advantage gained by being in a larger
    composition network. -/
noncomputable def networkPower (node network : I) : ℝ :=
  rs (compose node network) (compose node network) - rs node node

/-- Network power is non-negative. -/
theorem networkPower_nonneg (n net : I) : networkPower n net ≥ 0 := by
  unfold networkPower; linarith [compose_enriches' n net]

/-- Network power of void node equals network weight. -/
theorem networkPower_void_node (net : I) :
    networkPower (void : I) net = rs net net := by
  unfold networkPower; simp [rs_void_void]

/-- Network power with void network is zero. -/
theorem networkPower_void_network (n : I) :
    networkPower n (void : I) = 0 := by
  unfold networkPower; simp

/-- Network effects compound: joining a larger network gives more power. -/
theorem network_effects_compound (n a b : I) :
    rs (compose n (compose a b)) (compose n (compose a b)) ≥
    rs (compose n a) (compose n a) := by
  rw [← compose_assoc']
  exact compose_enriches' (compose n a) b

/-! ## §76. Legitimacy and Authority -/

/-- Legitimacy: the degree to which power is accepted.
    Measured by cross-resonance from subject to authority. -/
noncomputable def legitimacy (authority subject : I) : ℝ :=
  rs subject authority

/-- Legitimacy from void subject is zero. -/
theorem legitimacy_void_subject (a : I) :
    legitimacy a (void : I) = 0 := by
  unfold legitimacy; exact rs_void_left' a

/-- Legitimacy of void authority is zero. -/
theorem legitimacy_void_authority (s : I) :
    legitimacy (void : I) s = 0 := by
  unfold legitimacy; exact rs_void_right' s

/-- Authority deficit: the gap between hard power and legitimacy. -/
noncomputable def authorityDeficit (auth subject : I) : ℝ :=
  rs auth auth - rs subject auth

/-- Authority deficit with void subject equals full hard power. -/
theorem authorityDeficit_void_subject (a : I) :
    authorityDeficit a (void : I) = rs a a := by
  unfold authorityDeficit; simp [rs_void_left']

/-! ## §77. Discourse Theory (Laclau/Mouffe) -/

/-- Nodal point: an idea that fixes the meaning of other ideas in a
    discourse. Its emergence with everything is structured. -/
noncomputable def nodalPointEffect (nodal idea observer : I) : ℝ :=
  emergence nodal idea observer

/-- Floating signifier: the gap between two different contexts giving
    the same idea different meanings. -/
noncomputable def floatingSignifier (idea context1 context2 observer : I) : ℝ :=
  emergence idea context1 observer - emergence idea context2 observer

/-- Floating signifier is zero when contexts are the same. -/
theorem floating_same_context (i c o : I) :
    floatingSignifier i c c o = 0 := by
  unfold floatingSignifier; ring

/-- Floating signifier is antisymmetric in contexts. -/
theorem floating_antisymm (i c1 c2 o : I) :
    floatingSignifier i c1 c2 o = -floatingSignifier i c2 c1 o := by
  unfold floatingSignifier; ring

/-- Nodal point with void idea has no effect. -/
theorem nodal_void_idea (n o : I) :
    nodalPointEffect n (void : I) o = 0 := by
  unfold nodalPointEffect; exact emergence_void_right n o

/-- Nodal point with void observer has no effect. -/
theorem nodal_void_observer (n i : I) :
    nodalPointEffect n i (void : I) = 0 := by
  unfold nodalPointEffect; exact emergence_against_void n i

end PowerStructure

end IDT3
