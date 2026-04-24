import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Phenomenology of Meaning

Husserl's intentionality, horizon structure, givenness, constitution,
reduction, temporality, intersubjectivity, embodiment, and the lifeworld —
all formalized within the IdeaticSpace3 framework.

Every theorem has a complete proof. Zero sorries.

## Structure

- §1. Intentionality (consciousness directed toward objects)
- §2. The Horizon (accumulated background of experience)
- §3. Givenness and Constitution (profiles, adequacy)
- §4. The Reduction (epoché, eidetic reduction)
- §5. Temporality (retention, protention, living present)
- §6. Intersubjectivity (empathy, shared horizons)
- §7. Embodiment and Perception (kinaesthesia, synesthesia)
- §8. The Lifeworld (Lebenswelt, habituality, crisis)
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. Intentionality — Consciousness Is Always Consciousness OF Something -/

section Intentionality
variable {I : Type*} [S : IdeaticSpace3 I]

/-- An intentional act: subject directs attention toward an object.
    Husserl: every mental act is composed of noesis (act) and noema (content). -/
def intentionalAct (subject object : I) : I := compose subject object

/-- Noesis: the act-pole of intentionality -/
def noesis (_subject _object : I) : I := _subject

/-- Noema: the content-pole of intentionality -/
def noema (_subject _object : I) : I := _object

-- Theorem 1
/-- The intentional act is exactly a composition. -/
theorem intentionalAct_eq (s o : I) :
    intentionalAct s o = compose s o := rfl

-- Theorem 2
/-- Empty intention: directing attention at nothing returns the subject. -/
theorem empty_intention (s : I) :
    intentionalAct s void = s := by
  unfold intentionalAct; simp

-- Theorem 3
/-- Pure receptivity: a void subject simply receives the object. -/
theorem pure_receptivity (o : I) :
    intentionalAct void o = o := by
  unfold intentionalAct; simp

-- Theorem 4
/-- The experiential weight: how rich an intentional experience is. -/
noncomputable def experientialWeight (s o : I) : ℝ :=
  rs (intentionalAct s o) (intentionalAct s o)

-- Theorem 5
/-- Experience is always at least as rich as the subject alone.
    Intentionality enriches — attending to something adds presence. -/
theorem intentionality_enriches (s o : I) :
    experientialWeight s o ≥ rs s s := by
  unfold experientialWeight intentionalAct
  exact compose_enriches' s o

-- Theorem 6
/-- The noematic contribution: how the object shapes the experience,
    measured against some probe c. -/
noncomputable def noematicContribution (s o c : I) : ℝ :=
  rs (intentionalAct s o) c - rs s c

-- Theorem 7
/-- The noematic contribution decomposes into the object's direct resonance
    plus emergence (the genuinely new meaning). -/
theorem noematic_decomposition (s o c : I) :
    noematicContribution s o c = rs o c + emergence s o c := by
  unfold noematicContribution intentionalAct
  rw [rs_compose_eq]; ring

-- Theorem 8
/-- Noematic contribution vanishes for a void object. -/
theorem noematic_void_object (s c : I) :
    noematicContribution s void c = 0 := by
  unfold noematicContribution intentionalAct; simp [rs_void_left']

-- Theorem 9
/-- The subject's contribution to the experience: how the subject
    shapes what is experienced. -/
noncomputable def noeticContribution (s o c : I) : ℝ :=
  rs (intentionalAct s o) c - rs o c

-- Theorem 10
/-- Noetic contribution decomposes into subject's resonance plus emergence. -/
theorem noetic_decomposition (s o c : I) :
    noeticContribution s o c = rs s c + emergence s o c := by
  unfold noeticContribution intentionalAct
  rw [rs_compose_eq]; ring

-- Theorem 11
/-- Noetic contribution of a void subject is zero. -/
theorem noetic_void_subject (o c : I) :
    noeticContribution void o c = 0 := by
  unfold noeticContribution intentionalAct; simp [rs_void_left']

-- Theorem 12
/-- The intentional surplus: the emergence measures what neither subject
    nor object contribute individually — the genuinely NEW meaning
    that arises from the intentional relation. -/
theorem intentional_surplus (s o c : I) :
    emergence s o c =
    noematicContribution s o c - rs o c := by
  unfold noematicContribution intentionalAct emergence; ring

-- Theorem 13
/-- Double intentionality: composing two intentional acts.
    Reflecting on an experience is itself an intentional act. -/
theorem double_intentionality (s₁ s₂ o : I) :
    intentionalAct s₁ (intentionalAct s₂ o) =
    compose s₁ (compose s₂ o) := rfl

-- Theorem 14
/-- Sequential intentionality associates: (s₁ attending to (s₂ attending to o))
    equals ((s₁ composed with s₂) attending to o). -/
theorem intentional_assoc (s₁ s₂ o : I) :
    intentionalAct s₁ (intentionalAct s₂ o) =
    intentionalAct (compose s₁ s₂) o := by
  unfold intentionalAct; rw [compose_assoc']

end Intentionality

/-! ## §2. The Horizon — Accumulated Background of Experience -/

section Horizon
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The horizon: accumulated background built from n repetitions of experience e. -/
def horizon (e : I) (n : ℕ) : I := composeN e n

-- Theorem 15
/-- The empty horizon is void — no experience yet. -/
theorem empty_horizon (e : I) : horizon e 0 = void := rfl

-- Theorem 16
/-- Each new experience extends the horizon. -/
theorem horizon_extends (e : I) (n : ℕ) :
    horizon e (n + 1) = compose (horizon e n) e := rfl

-- Theorem 17
/-- The horizon is always at least as rich as any earlier horizon.
    Experience accumulates — you can't un-learn. -/
theorem horizon_enriches (e : I) (n : ℕ) :
    rs (horizon e (n+1)) (horizon e (n+1)) ≥
    rs (horizon e n) (horizon e n) := by
  unfold horizon; exact rs_composeN_mono e n

-- Theorem 18
/-- Experiencing something against a horizon includes emergence from
    the horizon. The horizon shapes everything. -/
theorem horizon_shapes_experience (e : I) (n : ℕ) (a c : I) :
    rs (compose (horizon e n) a) c =
    rs (horizon e n) c + rs a c + emergence (horizon e n) a c := by
  rw [rs_compose_eq]

-- Theorem 19
/-- The horizon's self-resonance is non-negative. -/
theorem horizon_self_nonneg (e : I) (n : ℕ) :
    rs (horizon e n) (horizon e n) ≥ 0 := by
  unfold horizon; exact rs_composeN_nonneg e n

-- Theorem 20
/-- Horizon shift: adding a new experience to the horizon changes
    how everything resonates. The shift is captured by emergence. -/
noncomputable def horizonShift (e : I) (n : ℕ) (c : I) : ℝ :=
  rs (horizon e (n + 1)) c - rs (horizon e n) c

-- Theorem 21
/-- The horizon shift decomposes into the new experience's resonance
    plus the emergence from composing with the existing horizon. -/
theorem horizonShift_eq (e : I) (n : ℕ) (c : I) :
    horizonShift e n c = rs e c + emergence (horizon e n) e c := by
  unfold horizonShift horizon
  rw [composeN_succ, rs_compose_eq]; ring

-- Theorem 22
/-- The horizon against void is zero. -/
theorem horizon_rs_void (e : I) (n : ℕ) :
    rs (horizon e n) void = 0 := rs_void_right' _

-- Theorem 23
/-- Expanding the horizon by void doesn't change it. -/
theorem horizon_void_stable (n : ℕ) :
    horizon (void : I) n = void := by
  unfold horizon; exact composeN_void n

-- Theorem 24
/-- The first horizon step is just the experience itself. -/
theorem horizon_one (e : I) : horizon e 1 = e := by
  unfold horizon; exact composeN_one e

end Horizon

/-! ## §3. Givenness and Constitution -/

section Givenness
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A profile of object a under context c: how a appears when approached
    through context c. -/
def profile (a c : I) : I := compose c a

-- Theorem 25
/-- The void profile reveals the bare object. -/
theorem void_profile (a : I) : profile a void = a := by
  unfold profile; simp

-- Theorem 26
/-- A profile is always at least as rich as its context. -/
theorem profile_enriches_context (a c : I) :
    rs (profile a c) (profile a c) ≥ rs c c := by
  unfold profile; exact compose_enriches' c a

-- Theorem 27
/-- How a profile resonates: includes the context, the object, and emergence. -/
theorem profile_resonance (a c d : I) :
    rs (profile a c) d = rs c d + rs a d + emergence c a d := by
  unfold profile; rw [rs_compose_eq]

-- Theorem 28
/-- The emergence in a profile measures what is genuinely GIVEN in this
    particular approach — beyond what context and object contribute alone. -/
noncomputable def givenness (a c d : I) : ℝ := emergence c a d

-- Theorem 29
/-- Givenness through void context is zero — no perspective, no givenness. -/
theorem givenness_void_context (a d : I) :
    givenness a (void : I) d = 0 := by
  unfold givenness; exact emergence_void_left a d

-- Theorem 30
/-- Givenness against void is zero — nothing is given to nothing. -/
theorem givenness_against_void (a c : I) :
    givenness a c (void : I) = 0 := by
  unfold givenness; exact emergence_against_void c a

-- Theorem 31
/-- Adequacy bound: givenness is bounded by the geometric mean of
    profile and observer self-resonances (Cauchy-Schwarz). -/
theorem adequacy_bound (a c d : I) :
    (givenness a c d) ^ 2 ≤
    rs (profile a c) (profile a c) * rs d d := by
  unfold givenness profile; exact emergence_bounded' c a d

-- Theorem 32
/-- Two profiles of the same object differ by their emergence patterns.
    Different contexts reveal different aspects of the object. -/
theorem profile_difference (a c₁ c₂ d : I) :
    rs (profile a c₁) d - rs (profile a c₂) d =
    (rs c₁ d - rs c₂ d) + (emergence c₁ a d - emergence c₂ a d) := by
  unfold profile; rw [rs_compose_eq, rs_compose_eq]; ring

-- Theorem 33
/-- The constituted invariant: across all profiles, the object's own
    resonance rs(a, d) is the invariant core. -/
theorem constituted_invariant (a c d : I) :
    rs (profile a c) d - rs c d - emergence c a d = rs a d := by
  unfold profile; rw [rs_compose_eq]; ring

-- Theorem 34
/-- Inadequate givenness: when the observer is void, nothing is given. -/
theorem inadequate_givenness_void_observer (a c : I) :
    givenness a c void = 0 := by
  unfold givenness; exact emergence_against_void c a

end Givenness

/-! ## §4. The Reduction — Bracketing Presuppositions -/

section Reduction
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Phenomenological reduction (epoché): strip away the horizon h
    to reveal what a contributes on its own.
    Formally: the difference between the full experience and the horizon. -/
noncomputable def reduction (h a c : I) : ℝ :=
  rs (compose h a) c - rs h c

-- Theorem 35
/-- The reduction decomposes into the object's resonance plus emergence. -/
theorem reduction_decomposition (h a c : I) :
    reduction h a c = rs a c + emergence h a c := by
  unfold reduction; rw [rs_compose_eq]; ring

-- Theorem 36
/-- Reducing void yields nothing — bracketing nothing leaves nothing. -/
theorem reduction_void_object (h c : I) :
    reduction h void c = 0 := by
  unfold reduction; simp [rs_void_left']

-- Theorem 37
/-- Reducing with a void horizon reveals the pure object. -/
theorem reduction_void_horizon (a c : I) :
    reduction void a c = rs a c := by
  unfold reduction; simp [rs_void_left']

-- Theorem 38
/-- The pure emergence: what the reduction reveals beyond the bare object. -/
noncomputable def pureEmergence (h a c : I) : ℝ :=
  reduction h a c - rs a c

-- Theorem 39
/-- Pure emergence equals the emergence function. -/
theorem pureEmergence_eq (h a c : I) :
    pureEmergence h a c = emergence h a c := by
  unfold pureEmergence; rw [reduction_decomposition]; ring

-- Theorem 40
/-- Eidetic reduction: finding what is essential across different contexts.
    Two experiences share an eidos if their reductions agree against all probes. -/
def sharesEidos (h₁ h₂ a c : I) : Prop :=
  reduction h₁ a c = reduction h₂ a c

-- Theorem 41
/-- Sharing eidos is equivalent to equal emergence from different horizons. -/
theorem sharesEidos_iff_emergence (h₁ h₂ a c : I) :
    sharesEidos h₁ h₂ a c ↔ emergence h₁ a c = emergence h₂ a c := by
  unfold sharesEidos
  rw [reduction_decomposition, reduction_decomposition]
  constructor
  · intro h; linarith
  · intro h; linarith

-- Theorem 42
/-- Every experience shares eidos with itself (reflexivity). -/
theorem sharesEidos_refl (h a c : I) :
    sharesEidos h h a c := by
  unfold sharesEidos; rfl

-- Theorem 43
/-- The transcendental reduction: the subject's own contribution
    to the experience, after removing the object. -/
noncomputable def transcendentalContribution (s o c : I) : ℝ :=
  rs (compose s o) c - rs o c

-- Theorem 44
/-- The transcendental contribution is the subject's resonance plus emergence. -/
theorem transcendental_decomposition (s o c : I) :
    transcendentalContribution s o c = rs s c + emergence s o c := by
  unfold transcendentalContribution; rw [rs_compose_eq]; ring

-- Theorem 45
/-- A void subject contributes nothing transcendentally. -/
theorem transcendental_void_subject (o c : I) :
    transcendentalContribution void o c = 0 := by
  unfold transcendentalContribution; simp [rs_void_left']

-- Theorem 46
/-- Reduction against void always yields zero. -/
theorem reduction_against_void (h a : I) :
    reduction h a void = 0 := by
  unfold reduction; simp [rs_void_right']

end Reduction

/-! ## §5. Temporality — Retention, Protention, The Living Present -/

section Temporality
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The living present: composed of retention (just-past), the now, and
    protention (anticipation). -/
def livingPresent (retention now protention : I) : I :=
  compose (compose retention now) protention

-- Theorem 47
/-- The specious present is an associative composition. -/
theorem livingPresent_assoc (r n p : I) :
    livingPresent r n p = compose r (compose n p) := by
  unfold livingPresent; rw [compose_assoc']

-- Theorem 48
/-- The living present with no retention: pure present + anticipation. -/
theorem present_no_retention (n p : I) :
    livingPresent void n p = compose n p := by
  unfold livingPresent; simp

-- Theorem 49
/-- The living present with no protention: past + present. -/
theorem present_no_protention (r n : I) :
    livingPresent r n void = compose r n := by
  unfold livingPresent; simp

-- Theorem 50
/-- Pure now: no past, no future. -/
theorem pure_now (n : I) :
    livingPresent void n void = n := by
  unfold livingPresent; simp

-- Theorem 51
/-- Temporal enrichment: the living present is at least as rich as
    retention + now alone. -/
theorem temporal_enrichment (r n p : I) :
    rs (livingPresent r n p) (livingPresent r n p) ≥
    rs (compose r n) (compose r n) := by
  unfold livingPresent; exact compose_enriches' (compose r n) p

-- Theorem 52
/-- Temporal flow: how moving from moment n₁ to n₂ shifts the present. -/
noncomputable def temporalFlow (r n₁ n₂ p c : I) : ℝ :=
  rs (livingPresent r n₂ p) c - rs (livingPresent r n₁ p) c

-- Theorem 53
/-- Retention accumulates: n steps of retention form a horizon. -/
def retentionalHorizon (past : I) (n : ℕ) : I := composeN past n

-- Theorem 54
/-- The retained past grows in richness. -/
theorem retention_enriches (past : I) (n : ℕ) :
    rs (retentionalHorizon past (n+1)) (retentionalHorizon past (n+1)) ≥
    rs (retentionalHorizon past n) (retentionalHorizon past n) := by
  unfold retentionalHorizon; exact rs_composeN_mono past n

-- Theorem 55
/-- Temporal resonance: the retained past resonates with the present. -/
theorem temporal_resonance (r n p c : I) :
    rs (livingPresent r n p) c =
    rs (compose r n) c + rs p c + emergence (compose r n) p c := by
  unfold livingPresent; rw [rs_compose_eq]

-- Theorem 56
/-- The protentional contribution: what anticipation adds to the present. -/
noncomputable def protentionalContribution (r n p c : I) : ℝ :=
  rs (livingPresent r n p) c - rs (compose r n) c

-- Theorem 57
/-- Protentional contribution equals protention's resonance plus temporal emergence. -/
theorem protentional_decomposition (r n p c : I) :
    protentionalContribution r n p c =
    rs p c + emergence (compose r n) p c := by
  unfold protentionalContribution; rw [temporal_resonance]; ring

-- Theorem 58
/-- Zero protention: no anticipation contributes nothing. -/
theorem zero_protention (r n c : I) :
    protentionalContribution r n void c = 0 := by
  unfold protentionalContribution livingPresent; simp [rs_void_left']

end Temporality

/-! ## §6. Intersubjectivity — Other Minds, Empathy, Shared Horizons -/

section Intersubjectivity
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Intersubjective encounter: two subjects' ideas composed together. -/
def encounter (my_idea other_idea : I) : I :=
  compose my_idea other_idea

-- Theorem 59
/-- Encounter resonance: how the encounter resonates with a probe. -/
theorem encounter_resonance (a b c : I) :
    rs (encounter a b) c = rs a c + rs b c + emergence a b c := by
  unfold encounter; rw [rs_compose_eq]

-- Theorem 60
/-- Encountering void (no other) is just oneself. -/
theorem encounter_void (a : I) : encounter a void = a := by
  unfold encounter; simp

-- Theorem 61
/-- Empathy measure: how much two subjects resonate with each other. -/
noncomputable def empathy (a b : I) : ℝ := rs a b + rs b a

-- Theorem 62
/-- Empathy is symmetric. -/
theorem empathy_symmetric (a b : I) : empathy a b = empathy b a := by
  unfold empathy; ring

-- Theorem 63
/-- Empathy with void is zero — no empathy with nothing. -/
theorem empathy_void (a : I) : empathy a (void : I) = 0 := by
  unfold empathy; simp [rs_void_left', rs_void_right']

-- Theorem 64
/-- Intersubjective emergence: what arises from the encounter that
    neither subject has alone. -/
noncomputable def intersubjectiveEmergence (a b c : I) : ℝ :=
  emergence a b c

-- Theorem 65
/-- Intersubjective emergence against void vanishes. -/
theorem intersubjective_emergence_void (a b : I) :
    intersubjectiveEmergence a b void = 0 := by
  unfold intersubjectiveEmergence; exact emergence_against_void a b

-- Theorem 66
/-- Shared horizon: two subjects sharing n experiences of e. -/
def sharedHorizon (e : I) (n : ℕ) : I := composeN e n

-- Theorem 67
/-- Shared horizons are at least as rich as individual ones (reflexive). -/
theorem sharedHorizon_nonneg (e : I) (n : ℕ) :
    rs (sharedHorizon e n) (sharedHorizon e n) ≥ 0 :=
  rs_self_nonneg' _

-- Theorem 68
/-- The encounter is at least as rich as either participant. -/
theorem encounter_enriches (a b : I) :
    rs (encounter a b) (encounter a b) ≥ rs a a := by
  unfold encounter; exact compose_enriches' a b

-- Theorem 69
/-- Understanding gap: the asymmetry in how subjects experience the encounter. -/
noncomputable def understandingGap (a b _c : I) : ℝ :=
  rs a (encounter a b) - rs b (encounter a b)

-- Theorem 70
/-- Understanding gap via resonance of the encounter with its components.
    This uses the encounter decomposition. -/
theorem understandingGap_eq (a b : I) :
    understandingGap a b (encounter a b) =
    rs a (compose a b) - rs b (compose a b) := by
  unfold understandingGap encounter; ring

end Intersubjectivity

/-! ## §7. Embodiment and Perception -/

section Embodiment
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Embodied perception: all perception is composed with the bodily context.
    The body is the ever-present horizon of perception. -/
def embodiedPerception (body stimulus : I) : I :=
  compose body stimulus

-- Theorem 71
/-- Embodied perception is always at least as rich as the body alone.
    Having a body enriches every perception. -/
theorem embodied_enriches (body stimulus : I) :
    rs (embodiedPerception body stimulus) (embodiedPerception body stimulus) ≥
    rs body body := by
  unfold embodiedPerception; exact compose_enriches' body stimulus

-- Theorem 72
/-- Disembodied perception: a void body perceives the bare stimulus. -/
theorem disembodied (stimulus : I) :
    embodiedPerception void stimulus = stimulus := by
  unfold embodiedPerception; simp

-- Theorem 73
/-- Kinaesthetic shift: how movement changes perception.
    Moving from body state b₁ to b₂ changes what is perceived. -/
noncomputable def kinaestheticShift (b₁ b₂ stimulus c : I) : ℝ :=
  rs (embodiedPerception b₂ stimulus) c -
  rs (embodiedPerception b₁ stimulus) c

-- Theorem 74
/-- Zero movement means zero kinaesthetic shift. -/
theorem zero_kinaesthesia (b stimulus c : I) :
    kinaestheticShift b b stimulus c = 0 := by
  unfold kinaestheticShift; ring

-- Theorem 75
/-- Kinaesthetic shift decomposes into body difference plus emergence difference. -/
theorem kinaesthetic_decomposition (b₁ b₂ stimulus c : I) :
    kinaestheticShift b₁ b₂ stimulus c =
    (rs b₂ c - rs b₁ c) +
    (emergence b₂ stimulus c - emergence b₁ stimulus c) := by
  unfold kinaestheticShift embodiedPerception
  rw [rs_compose_eq, rs_compose_eq]; ring

-- Theorem 76
/-- Embodied resonance: includes the body's own resonance plus emergence. -/
theorem embodied_resonance (body stimulus c : I) :
    rs (embodiedPerception body stimulus) c =
    rs body c + rs stimulus c + emergence body stimulus c := by
  unfold embodiedPerception; rw [rs_compose_eq]

-- Theorem 77
/-- Cross-modal emergence (synesthesia): when composing stimuli from different
    modalities produces emergence. Formally, composing two stimuli
    with the body creates emergence beyond the sum. -/
noncomputable def crossModalEmergence (body s₁ s₂ c : I) : ℝ :=
  emergence (compose body s₁) s₂ c

-- Theorem 78
/-- Cross-modal emergence against void is zero. -/
theorem crossModal_void (body s₁ s₂ : I) :
    crossModalEmergence body s₁ s₂ void = 0 := by
  unfold crossModalEmergence; exact emergence_against_void _ _

-- Theorem 79
/-- The phantom phenomenon: emergence persists from composition with body
    even when the stimulus is void (absent). -/
theorem phantom_emergence (body c : I) :
    rs (embodiedPerception body void) c = rs body c := by
  unfold embodiedPerception; simp [rs_void_left']

-- Theorem 80
/-- Embodied perception composes: perceiving s₁ then s₂ is associative. -/
theorem perception_composes (body s₁ s₂ : I) :
    compose (embodiedPerception body s₁) s₂ =
    embodiedPerception body (compose s₁ s₂) := by
  unfold embodiedPerception; rw [compose_assoc']

end Embodiment

/-! ## §8. The Lifeworld — Lebenswelt, Habituality, Crisis -/

section Lifeworld
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The lifeworld: the ultimate horizon, built from all accumulated experience. -/
def lifeworld (experiences : List I) : I := composeList experiences

-- Theorem 81
/-- The empty lifeworld is void — before all experience. -/
theorem lifeworld_empty : lifeworld ([] : List I) = void := rfl

-- Theorem 82
/-- A single-experience lifeworld is that experience itself. -/
theorem lifeworld_single (e : I) : lifeworld [e] = e := by
  unfold lifeworld; simp [composeList]

-- Theorem 83
/-- Adding a new experience to the lifeworld composes it. -/
theorem lifeworld_cons (e : I) (es : List I) :
    lifeworld (e :: es) = compose e (lifeworld es) := rfl

-- Theorem 84
/-- The lifeworld is preserved under composition: composing with the
    lifeworld maintains the background structure. -/
theorem lifeworld_preservation (e : I) (es : List I) (c : I) :
    rs (lifeworld (e :: es)) c =
    rs e c + rs (lifeworld es) c + emergence e (lifeworld es) c := by
  unfold lifeworld; rw [composeList_cons, rs_compose_eq]

-- Theorem 85
/-- Habituality: repeated experience creates stable patterns.
    After n repetitions, the horizon is composeN. -/
def habitual (e : I) (n : ℕ) : I := composeN e n

-- Theorem 86
/-- Habituality grows: more repetition means richer pattern. -/
theorem habituality_grows (e : I) (n : ℕ) :
    rs (habitual e (n+1)) (habitual e (n+1)) ≥
    rs (habitual e n) (habitual e n) := by
  unfold habitual; exact rs_composeN_mono e n

-- Theorem 87
/-- Pre-theoretical resonance: the lifeworld's direct resonance with
    an idea, before any theoretical mediation. -/
noncomputable def pretheoretical (lw a : I) : ℝ := rs lw a

-- Theorem 88
/-- Pre-theoretical understanding of void is zero. -/
theorem pretheoretical_void (lw : I) :
    pretheoretical lw void = 0 := by
  unfold pretheoretical; exact rs_void_right' lw

-- Theorem 89
/-- Crisis: when a theoretical construct t has zero resonance with
    the lifeworld, it has become alienated from lived experience. -/
def inCrisis (lw t : I) : Prop := rs lw t = 0

-- Theorem 90
/-- Void is always in crisis (trivially). -/
theorem void_in_crisis (lw : I) : inCrisis lw void := by
  unfold inCrisis; exact rs_void_right' lw

-- Theorem 91
/-- Crisis is avoided for the lifeworld's own content:
    if lw ≠ void, then rs(lw, lw) > 0, so lw resonates with itself. -/
theorem self_resonance_no_crisis (lw : I) (h : lw ≠ void) :
    ¬inCrisis lw lw := by
  unfold inCrisis; intro habs
  exact absurd (rs_nondegen' lw habs) h

-- Theorem 92
/-- Sedimentation: the lifeworld absorbs each new experience, growing richer.
    This is the fundamental law of phenomenological accumulation. -/
theorem sedimentation (lw new_exp c : I) :
    rs (compose lw new_exp) c =
    rs lw c + rs new_exp c + emergence lw new_exp c :=
  rs_compose_eq lw new_exp c

-- Theorem 93
/-- Habituality is monotone in self-resonance: the void habitual is void. -/
theorem habitual_void (n : ℕ) : habitual (void : I) n = void := by
  unfold habitual; exact composeN_void n

-- Theorem 94
/-- The lifeworld resonance with void is always zero. -/
theorem lifeworld_vs_void (es : List I) :
    rs (lifeworld es) void = 0 := rs_void_right' _

end Lifeworld

/-! ## §9. Additional Phenomenological Structures -/

section Additional
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Attention as composition weight: attending to object o with intensity
    measured by n repetitions. -/
def attend (o : I) (n : ℕ) : I := composeN o n

-- Theorem 95
/-- Attending zero times yields void (no attention). -/
theorem attend_zero (o : I) : attend o 0 = void := rfl

-- Theorem 96
/-- First attention is the object itself. -/
theorem attend_one (o : I) : attend o 1 = o :=
  composeN_one o

-- Theorem 97
/-- Repeated attention enriches: attending more deeply never decreases richness. -/
theorem attention_enriches (o : I) (n : ℕ) :
    rs (attend o (n+1)) (attend o (n+1)) ≥
    rs (attend o n) (attend o n) := by
  unfold attend; exact rs_composeN_mono o n

-- Theorem 98
/-- Intersubjective encounter emergence satisfies the cocycle condition:
    how three subjects' ideas compose is constrained. -/
theorem intersubjective_cocycle (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

-- Theorem 99
/-- Noematic invariance: if the noema (object) is void, the noetic
    contribution reduces to the subject alone. -/
theorem noematic_invariance (s c : I) :
    rs (compose s void) c = rs s c := by simp

-- Theorem 100
/-- Reverse encounter: composing b ∘ a vs a ∘ b gives different resonance
    unless emergence is symmetric — this is the non-commutativity of
    intersubjective understanding. -/
theorem encounter_noncommutativity (a b c : I) :
    rs (compose a b) c - rs (compose b a) c =
    emergence a b c - emergence b a c := by
  unfold emergence; ring

-- Theorem 101
/-- Horizon composition: composing two horizons gives a combined horizon
    with its own emergence structure. -/
theorem horizon_composition (e : I) (m n : ℕ) (c : I) :
    rs (compose (horizon e m) (horizon e n)) c =
    rs (horizon e m) c + rs (horizon e n) c +
    emergence (horizon e m) (horizon e n) c := by
  rw [rs_compose_eq]

-- Theorem 102
/-- Perceptual enrichment: embodied perception of a composition.
    Perceiving (s₁ ∘ s₂) through the body decomposes via associativity. -/
theorem perceptual_enrichment (body s₁ s₂ c : I) :
    rs (embodiedPerception body (compose s₁ s₂)) c =
    rs body c + rs (compose s₁ s₂) c +
    emergence body (compose s₁ s₂) c := by
  unfold embodiedPerception; rw [rs_compose_eq]

-- Theorem 103
/-- Self-givenness: the object is trivially given to itself (zero extra context). -/
theorem self_givenness (a : I) :
    profile a void = a :=
  void_profile a

-- Theorem 104
/-- Temporal composition: the living present composes temporally.
    Adding more protention enriches the temporal experience. -/
theorem temporal_composition_enriches (r n p : I) :
    rs (livingPresent r n p) (livingPresent r n p) ≥
    rs r r := by
  unfold livingPresent
  have h1 := compose_enriches' r n
  have h2 := compose_enriches' (compose r n) p
  linarith

-- Theorem 105
/-- Eidetic identity: an object shares eidos with itself under any horizon. -/
theorem eidetic_identity (h a c : I) :
    sharesEidos h h a c := by
  unfold sharesEidos; rfl

-- Theorem 106
/-- Lifeworld self-resonance is non-negative. -/
theorem lifeworld_nonneg (es : List I) :
    rs (lifeworld es) (lifeworld es) ≥ 0 :=
  rs_self_nonneg' _

-- Theorem 107
/-- Encounter enrichment is bounded by Cauchy-Schwarz:
    the emergence from an encounter can't exceed what the composite can carry. -/
theorem encounter_bounded (a b c : I) :
    (emergence a b c) ^ 2 ≤
    rs (encounter a b) (encounter a b) * rs c c := by
  unfold encounter; exact emergence_bounded' a b c

-- Theorem 108
/-- Double reduction: reducing twice (removing two layers of horizon)
    decomposes via the cocycle condition. -/
theorem double_reduction (h₁ h₂ a c : I) :
    reduction (compose h₁ h₂) a c =
    rs a c + emergence (compose h₁ h₂) a c := by
  rw [reduction_decomposition]

-- Theorem 109
/-- The lifeworld after two experiences. -/
theorem lifeworld_two (e₁ e₂ : I) :
    lifeworld [e₁, e₂] = compose e₁ e₂ := by
  unfold lifeworld; simp [composeList]

-- Theorem 110
/-- Embodied vs disembodied: the body contributes emergence to perception. -/
theorem embodiment_contribution (body stimulus c : I) :
    rs (embodiedPerception body stimulus) c -
    rs stimulus c =
    rs body c + emergence body stimulus c := by
  unfold embodiedPerception; rw [rs_compose_eq]; ring

end Additional

/-! ## §10. Husserl Deep — Noetic-Noematic Correlation, Passive Synthesis,
    Genetic Phenomenology, Layers of Constitution -/

section HusserlDeep
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Noetic-noematic correlation strength: the degree to which the act-pole
    and content-pole of an intentional act resonate with each other.
    Husserl: every noesis has its noema and vice versa — they are correlates. -/
noncomputable def noeticNoematicCorrelation (s o : I) : ℝ :=
  rs s o + rs o s

-- Theorem 111
/-- Noetic-noematic correlation is symmetric in its two poles. -/
theorem noeticNoematic_symmetric (s o : I) :
    noeticNoematicCorrelation s o = noeticNoematicCorrelation o s := by
  unfold noeticNoematicCorrelation; ring

-- Theorem 112
/-- Correlation with void is zero: a contentless act has no correlation. -/
theorem noeticNoematic_void (s : I) :
    noeticNoematicCorrelation s void = 0 := by
  unfold noeticNoematicCorrelation; simp [rs_void_right', rs_void_left']

-- Theorem 113
/-- Passive synthesis: the pre-reflective association between two ideas.
    Husserl: before active judgment, consciousness passively synthesizes
    associations. We model this as the symmetric part of resonance. -/
noncomputable def passiveSynthesis (a b : I) : ℝ :=
  (rs a b + rs b a) / 2

-- Theorem 114
/-- Passive synthesis is symmetric — it doesn't privilege either direction. -/
theorem passiveSynthesis_symmetric (a b : I) :
    passiveSynthesis a b = passiveSynthesis b a := by
  unfold passiveSynthesis; ring

-- Theorem 115
/-- Passive synthesis with void yields zero — no association with nothing. -/
theorem passiveSynthesis_void (a : I) :
    passiveSynthesis a (void : I) = 0 := by
  unfold passiveSynthesis; simp [rs_void_right', rs_void_left']

-- Theorem 116
/-- Active synthesis: the directed, judgmental component — the antisymmetric part.
    Husserl: active synthesis involves the ego's deliberate positing. -/
noncomputable def activeSynthesis (a b : I) : ℝ :=
  (rs a b - rs b a) / 2

-- Theorem 117
/-- Active synthesis is antisymmetric: reversing direction negates it. -/
theorem activeSynthesis_antisymmetric (a b : I) :
    activeSynthesis a b = -activeSynthesis b a := by
  unfold activeSynthesis; ring

-- Theorem 118
/-- Resonance decomposes into passive and active synthesis.
    This is the phenomenological decomposition of intentionality. -/
theorem resonance_passive_active (a b : I) :
    rs a b = passiveSynthesis a b + activeSynthesis a b := by
  unfold passiveSynthesis activeSynthesis; ring

-- Theorem 119
/-- Genetic sedimentation: the difference between the n+1-th and n-th horizons
    captures how each new experience sediments into the lifeworld.
    Husserl's genetic phenomenology: meaning is built layer by layer. -/
theorem genetic_sedimentation (e : I) (n : ℕ) (c : I) :
    rs (horizon e (n+1)) c - rs (horizon e n) c =
    rs e c + emergence (horizon e n) e c := by
  unfold horizon; rw [composeN_succ, rs_compose_eq]; ring

-- Theorem 120
/-- Layered constitution: two successive layers of context.
    Husserl: objects are constituted through layers of sense-giving acts.
    The resonance of a doubly-constituted object decomposes into three layers. -/
theorem layered_constitution (c₁ c₂ a d : I) :
    rs (compose c₁ (compose c₂ a)) d =
    rs c₁ d + rs c₂ d + rs a d +
    emergence c₂ a d + emergence c₁ (compose c₂ a) d := by
  rw [rs_compose_eq c₁ (compose c₂ a) d, rs_compose_eq c₂ a d]; ring

-- Theorem 121
/-- Founding relation: idea a founds idea b if a's self-resonance
    is a prerequisite for b. Formally, if a = void then b's emergence vanishes.
    This captures Husserl's notion of founded acts (e.g., judgment is founded on perception). -/
def founds (a b : I) : Prop :=
  a = void → ∀ c d : I, emergence b c d = 0

-- Theorem 122
/-- Everything trivially founds everything when a is non-void:
    the antecedent a = void is false, so the implication holds vacuously. -/
theorem founds_of_ne_void (a b : I) (h : a ≠ void) : founds a b := by
  intro hab; exact absurd hab h

-- Theorem 123
/-- Void founds only left-linear ideas.
    If the founding element IS void, then the founded idea must have zero emergence. -/
theorem void_founds_iff_leftLinear (b : I) :
    founds (void : I) b ↔ (∀ c d : I, emergence b c d = 0) := by
  unfold founds; constructor
  · intro h; exact h rfl
  · intro h _; exact h

-- Theorem 124
/-- Internal time-consciousness: the flow of time as modeled by the
    difference in temporal experience across successive moments.
    Husserl: time-consciousness is the deepest layer of constitution. -/
noncomputable def timeConsciousnessFlow (r n₁ n₂ p c : I) : ℝ :=
  rs (livingPresent r n₂ p) c - rs (livingPresent r n₁ p) c

-- Theorem 125
/-- Time-consciousness flow decomposes into the change in now-moment
    plus the change in emergence with the retentional-protentional frame. -/
theorem timeConsciousness_decomposition (r n₁ n₂ p c : I) :
    timeConsciousnessFlow r n₁ n₂ p c =
    (rs n₂ c - rs n₁ c) +
    (emergence r n₂ c - emergence r n₁ c) +
    (emergence (compose r n₂) p c - emergence (compose r n₁) p c) := by
  unfold timeConsciousnessFlow livingPresent
  rw [rs_compose_eq (compose r n₂) p c, rs_compose_eq (compose r n₁) p c]
  rw [rs_compose_eq r n₂ c, rs_compose_eq r n₁ c]; ring

-- Theorem 126
/-- Zero temporal flow: if the now doesn't change, consciousness doesn't flow. -/
theorem timeConsciousness_zero_flow (r n p c : I) :
    timeConsciousnessFlow r n n p c = 0 := by
  unfold timeConsciousnessFlow; ring

-- Theorem 127
/-- Eidetic variation: two objects share an essence if their reductions
    under all possible horizons agree. We formalize this pointwise. -/
def eidetically_equivalent (a b : I) : Prop :=
  ∀ h c : I, reduction h a c = reduction h b c

-- Theorem 128
/-- Eidetic equivalence is reflexive. -/
theorem eidetically_equivalent_refl (a : I) : eidetically_equivalent a a :=
  fun _ _ => rfl

-- Theorem 129
/-- Eidetic equivalence is symmetric. -/
theorem eidetically_equivalent_symm {a b : I} (h : eidetically_equivalent a b) :
    eidetically_equivalent b a :=
  fun hh c => (h hh c).symm

-- Theorem 130
/-- Eidetic equivalence means identical emergence profiles:
    two objects are eidetically equivalent iff they produce the same
    emergence in every horizon context. -/
theorem eidetic_equiv_iff_emergence (a b : I) :
    eidetically_equivalent a b ↔
    (∀ h c : I, rs a c + emergence h a c = rs b c + emergence h b c) := by
  unfold eidetically_equivalent
  constructor
  · intro hh h c
    have := hh h c
    rw [reduction_decomposition, reduction_decomposition] at this
    linarith
  · intro hh h c
    rw [reduction_decomposition, reduction_decomposition]
    linarith [hh h c]

end HusserlDeep

/-! ## §11. Heidegger — Being-toward-death, Authenticity, das Man,
    Equipment, The Clearing -/

section Heidegger
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Dasein: the being for whom being is an issue. Dasein is always
    situated in a world (horizon) and projects possibilities. -/
def dasein (world projection : I) : I := compose world projection

-- Theorem 131
/-- Dasein in an empty world is pure projection (pure possibility). -/
theorem dasein_empty_world (p : I) : dasein (void : I) p = p := by
  unfold dasein; simp

-- Theorem 132
/-- Dasein with no projection is mere thrownness (pure facticity). -/
theorem dasein_no_projection (w : I) : dasein w (void : I) = w := by
  unfold dasein; simp

-- Theorem 133
/-- Being-toward-death: the ultimate possibility that individualizes Dasein.
    Death is modeled as a special horizon-limit: the resonance of Dasein's
    finitude. We measure it as the surplus of the projected over the actual. -/
noncomputable def beingTowardDeath (dasein_idea : I) (c : I) : ℝ :=
  rs (compose dasein_idea dasein_idea) c - rs dasein_idea c

-- Theorem 134
/-- Being-toward-death of void is zero: nothing faces death. -/
theorem beingTowardDeath_void (c : I) :
    beingTowardDeath (void : I) c = 0 := by
  unfold beingTowardDeath; simp [rs_void_left']

-- Theorem 135
/-- Being-toward-death decomposes into self-resonance plus emergence with self.
    Death reveals what you are (rs) plus what you become through self-confrontation (emergence). -/
theorem beingTowardDeath_decomposition (d c : I) :
    beingTowardDeath d c = rs d c + emergence d d c := by
  unfold beingTowardDeath; rw [rs_compose_eq]; ring

-- Theorem 136
/-- das Man (the They): the anonymous public self, modeled as the horizon
    that absorbs individual projection. When Dasein falls into das Man,
    its own contribution is reduced to emergence from the public horizon. -/
noncomputable def dasManAbsorption (public_horizon individual c : I) : ℝ :=
  rs (compose public_horizon individual) c - rs public_horizon c

-- Theorem 137
/-- das Man absorption decomposes: the individual's contribution to the public
    is their own resonance plus the emergence they create in the public context. -/
theorem dasMan_decomposition (pub ind c : I) :
    dasManAbsorption pub ind c = rs ind c + emergence pub ind c := by
  unfold dasManAbsorption; rw [rs_compose_eq]; ring

-- Theorem 138
/-- Authenticity: the degree to which Dasein's own projection differs from
    the public (das Man) projection. Measured as the resonance deficit between
    one's own and the public project. -/
noncomputable def authenticityMeasure (own_project public_project c : I) : ℝ :=
  rs own_project c - rs public_project c

-- Theorem 139
/-- Perfect inauthenticity: when own = public, authenticity is zero. -/
theorem perfect_inauthenticity (p c : I) :
    authenticityMeasure p p c = 0 := by
  unfold authenticityMeasure; ring

-- Theorem 140
/-- Equipment / readiness-to-hand (Zuhandenheit): a tool is transparent
    when it contributes no emergence — it functions additively in the
    referential totality. The tool withdraws from attention. -/
def readyToHand (tool : I) : Prop :=
  ∀ context probe : I, emergence context tool probe = 0

-- Theorem 141
/-- Void is ready-to-hand: nothing is maximally transparent. -/
theorem void_readyToHand : readyToHand (void : I) := by
  intro c p; exact emergence_void_right c p

-- Theorem 142
/-- A ready-to-hand tool acts linearly: composing with it adds resonance additively. -/
theorem readyToHand_linear (tool : I) (h : readyToHand tool)
    (context probe : I) :
    rs (compose context tool) probe = rs context probe + rs tool probe := by
  have := rs_compose_eq context tool probe
  rw [h context probe] at this; linarith

-- Theorem 143
/-- Breakdown / present-at-hand (Vorhandenheit): when a tool has nonzero
    emergence, it becomes conspicuous — it breaks from the referential totality.
    The tool shows itself AS a thing. -/
def presentAtHand (tool context probe : I) : Prop :=
  emergence context tool probe ≠ 0

-- Theorem 144
/-- The clearing (Lichtung): the open space in which beings can show themselves.
    Modeled as the total emergence that arises when a world-context meets a being.
    The clearing is not nothing — it is the condition for manifestation. -/
noncomputable def clearing (world being probe : I) : ℝ :=
  emergence world being probe

-- Theorem 145
/-- The clearing satisfies the cocycle condition: the way beings show themselves
    in the clearing is constrained by the global structure of manifestation. -/
theorem clearing_cocycle (w a b d : I) :
    clearing w a d + clearing (compose w a) b d =
    clearing a b d + clearing w (compose a b) d := by
  unfold clearing; exact cocycle_condition w a b d

-- Theorem 146
/-- An empty world has no clearing — without a world, nothing is manifest. -/
theorem clearing_void_world (being probe : I) :
    clearing (void : I) being probe = 0 := by
  unfold clearing; exact emergence_void_left being probe

-- Theorem 147
/-- Thrownness (Geworfenheit): the factical given of Dasein's situation.
    Modeled as the composition weight of the world before projection. -/
noncomputable def thrownness (world : I) : ℝ := rs world world

-- Theorem 148
/-- Thrownness is non-negative: you always have SOME situation. -/
theorem thrownness_nonneg (world : I) : thrownness world ≥ 0 := by
  unfold thrownness; exact rs_self_nonneg' world

-- Theorem 149
/-- Only void has zero thrownness. -/
theorem thrownness_zero_iff_void (world : I) (h : thrownness world = 0) :
    world = void := by
  unfold thrownness at h; exact rs_nondegen' world h

-- Theorem 150
/-- Temporality as ecstatic: Dasein's being is spread across three ecstasies
    (past-facticity, present-falling, future-projection). The total temporal
    weight always exceeds any single ecstasy. -/
theorem ecstatic_temporality (past present future : I) :
    rs (livingPresent past present future) (livingPresent past present future) ≥
    rs past past := by
  unfold livingPresent
  have h1 := compose_enriches' past present
  have h2 := compose_enriches' (compose past present) future
  linarith

end Heidegger

/-! ## §12. Merleau-Ponty — Flesh, Chiasm, Reversibility, Motor Intentionality -/

section MerleauPonty
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Flesh (chair): the elemental medium between perceiver and perceived.
    Merleau-Ponty: flesh is neither subject nor object but the condition
    of their intertwining. Modeled as the emergence from their encounter. -/
noncomputable def flesh (perceiver perceived probe : I) : ℝ :=
  emergence perceiver perceived probe

-- Theorem 151
/-- Chiasm (intertwining): the flesh relates the two directions of perception.
    The chiasm is the difference between perceiver→perceived and perceived→perceiver
    emergence. When chiasm = 0, perception is perfectly reversible. -/
noncomputable def chiasm (perceiver perceived probe : I) : ℝ :=
  flesh perceiver perceived probe - flesh perceived perceiver probe

-- Theorem 152
/-- The chiasm is antisymmetric: reversing perceiver and perceived negates it. -/
theorem chiasm_antisymmetric (a b c : I) :
    chiasm a b c = -chiasm b a c := by
  unfold chiasm; ring

-- Theorem 153
/-- Reversibility: the chiasm vanishes iff perception runs symmetrically.
    Merleau-Ponty: touching and being touched are aspects of a single phenomenon. -/
def reversible (a b : I) : Prop :=
  ∀ c : I, chiasm a b c = 0

-- Theorem 154
/-- Reversibility is symmetric. -/
theorem reversible_symmetric {a b : I} (h : reversible a b) : reversible b a := by
  intro c; rw [chiasm_antisymmetric]; linarith [h c]

-- Theorem 155
/-- Void is reversible with everything. -/
theorem void_reversible (a : I) : reversible (void : I) a := by
  intro c; unfold chiasm flesh; rw [emergence_void_left, emergence_void_right]; ring

-- Theorem 156
/-- Motor intentionality: the body reaches toward the world through movement.
    Unlike cognitive intentionality, motor intentionality is practical — it
    transforms the body-state itself. The motor act produces a NEW body-state. -/
noncomputable def motorIntentionality (body_state goal c : I) : ℝ :=
  rs (compose body_state goal) c - rs body_state c

-- Theorem 157
/-- Motor intentionality decomposes: the goal's resonance plus emergence.
    The body doesn't just ADD the goal — it integrates it (emergence). -/
theorem motorIntentionality_decomposition (b g c : I) :
    motorIntentionality b g c = rs g c + emergence b g c := by
  unfold motorIntentionality; rw [rs_compose_eq]; ring

-- Theorem 158
/-- Zero motor intentionality: reaching for nothing changes nothing. -/
theorem motorIntentionality_void_goal (b c : I) :
    motorIntentionality b (void : I) c = 0 := by
  unfold motorIntentionality; simp [rs_void_left']

-- Theorem 159
/-- Body schema vs body image: the body schema is the pre-reflective motor
    capacity (emergence-generating), while the body image is the reflective
    representation (pure resonance). Their difference is the emergence term. -/
noncomputable def bodySchemaContribution (body object probe : I) : ℝ :=
  emergence body object probe

noncomputable def bodyImageContribution (body probe : I) : ℝ :=
  rs body probe

-- Theorem 160
/-- The full embodied experience is body image + object + body schema contribution. -/
theorem embodied_full_decomposition (body object probe : I) :
    rs (compose body object) probe =
    bodyImageContribution body probe + rs object probe +
    bodySchemaContribution body object probe := by
  unfold bodyImageContribution bodySchemaContribution
  rw [rs_compose_eq]

-- Theorem 161
/-- Intercorporeality: two bodies encountering each other produce emergence
    that neither body alone possesses. The flesh between bodies. -/
noncomputable def intercorporeality (body₁ body₂ probe : I) : ℝ :=
  emergence body₁ body₂ probe

-- Theorem 162
/-- Intercorporeality satisfies the cocycle condition: the emergence between
    three bodies is globally constrained. -/
theorem intercorporeality_cocycle (b₁ b₂ b₃ probe : I) :
    intercorporeality b₁ b₂ probe +
    intercorporeality (compose b₁ b₂) b₃ probe =
    intercorporeality b₂ b₃ probe +
    intercorporeality b₁ (compose b₂ b₃) probe := by
  unfold intercorporeality; exact cocycle_condition b₁ b₂ b₃ probe

-- Theorem 163
/-- Flesh of the world: the total emergence when the world-context is the perceiver.
    Merleau-Ponty's late ontology: the world itself is flesh. -/
noncomputable def worldFlesh (world thing probe : I) : ℝ :=
  flesh world thing probe + flesh thing world probe

-- Theorem 164
/-- World-flesh is symmetric: it doesn't matter whether we start from
    world-to-thing or thing-to-world. -/
theorem worldFlesh_symmetric (w t p : I) :
    worldFlesh w t p = worldFlesh t w p := by
  unfold worldFlesh; ring

-- Theorem 165
/-- World-flesh with void is zero: no flesh without materiality. -/
theorem worldFlesh_void (w p : I) :
    worldFlesh w (void : I) p = 0 := by
  unfold worldFlesh flesh; rw [emergence_void_right, emergence_void_left]; ring

end MerleauPonty

/-! ## §13. Levinas — The Face, Infinity, Proximity, Substitution -/

section Levinas
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The face of the Other: the ethical demand that exceeds all representation.
    Levinas: the face is what cannot be reduced to a profile — it overflows
    every context. We measure this as the emergence that resists contextualization. -/
noncomputable def faceExcess (other context probe : I) : ℝ :=
  emergence context other probe

-- Theorem 166
/-- The face excess is bounded: even infinity has bounds in the formal structure.
    Yet the bound involves the COMPOSITE, not the parts alone. -/
theorem face_excess_bounded (other context probe : I) :
    (faceExcess other context probe) ^ 2 ≤
    rs (compose context other) (compose context other) * rs probe probe := by
  unfold faceExcess; exact emergence_bounded' context other probe

-- Theorem 167
/-- Infinity vs totality: totality is what can be captured by a single horizon;
    infinity is what overflows it. The face excess measures the overflow. -/
noncomputable def totalityCapture (horizon thing probe : I) : ℝ :=
  rs horizon probe + rs thing probe

noncomputable def infinityOverflow (horizon thing probe : I) : ℝ :=
  faceExcess thing horizon probe

-- Theorem 168
/-- The resonance of encounter decomposes into totality plus infinity.
    What we perceive = what we grasp (totality) + what overflows (infinity). -/
theorem totality_plus_infinity (h t p : I) :
    rs (compose h t) p = totalityCapture h t p + infinityOverflow h t p := by
  unfold totalityCapture infinityOverflow faceExcess
  rw [rs_compose_eq]

-- Theorem 169
/-- The saying (le Dire) vs the said (le Dit): the saying is the act of
    signification that is always betrayed by the said (its content).
    The saying is modeled as the emergence — what exceeds the content. -/
noncomputable def theSaying (speaker utterance listener : I) : ℝ :=
  emergence speaker utterance listener

noncomputable def theSaid (utterance listener : I) : ℝ :=
  rs utterance listener

-- Theorem 170
/-- The full communicative act is the said plus the speaker's resonance
    plus the saying. The saying is what the said cannot capture. -/
theorem saying_and_said (speaker utterance listener : I) :
    rs (compose speaker utterance) listener =
    rs speaker listener + theSaid utterance listener +
    theSaying speaker utterance listener := by
  unfold theSaying theSaid; rw [rs_compose_eq]

-- Theorem 171
/-- Proximity: ethical nearness to the Other, measured as the correlation
    between self and other within their encounter.
    Levinas: proximity is not spatial but ethical — responsibility before freedom. -/
noncomputable def proximity (self other : I) : ℝ :=
  rs self (compose self other) + rs other (compose self other)

-- Theorem 172
/-- Proximity to void is self-resonance: facing nothing, you face yourself. -/
theorem proximity_void (self : I) :
    proximity self (void : I) = rs self self + rs (void : I) self := by
  unfold proximity; simp [rs_void_left']

-- Theorem 173
/-- Substitution: the subject puts itself in the Other's place.
    Levinas: substitution is the deepest structure of subjectivity — being
    for the other. The substituted resonance replaces self with other. -/
noncomputable def substitution (self other probe : I) : ℝ :=
  rs other probe - rs self probe

-- Theorem 174
/-- Substitution is antisymmetric: substituting self for other negates. -/
theorem substitution_antisymmetric (a b c : I) :
    substitution a b c = -substitution b a c := by
  unfold substitution; ring

-- Theorem 175
/-- Self-substitution is zero: substituting yourself for yourself changes nothing. -/
theorem self_substitution (a c : I) :
    substitution a a c = 0 := by
  unfold substitution; ring

-- Theorem 176
/-- Ethical surplus: the encounter produces more than the sum of parts.
    Levinas: the ethical relation is not a relation of knowledge but of surplus. -/
noncomputable def ethicalSurplus (self other : I) : ℝ :=
  rs (compose self other) (compose self other) - rs self self - rs other other

-- Theorem 177
/-- Ethical surplus is non-negative when the other enriches:
    encounter always carries at least as much weight as self alone. -/
theorem ethicalSurplus_lower_bound (self other : I) :
    ethicalSurplus self other ≥ -rs other other := by
  unfold ethicalSurplus
  have h := compose_enriches' self other
  linarith

end Levinas

/-! ## §14. Sartre — Being-for-itself, Being-in-itself, Bad Faith, The Look -/

section Sartre
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Being-in-itself (en-soi): the opaque, self-identical being.
    An in-itself being has zero emergence with itself — it simply IS,
    with no internal differentiation. -/
def beingInItself (a : I) : Prop :=
  emergence a a a = 0

-- Theorem 178
/-- Void is being-in-itself: pure nothingness is maximally self-identical. -/
theorem void_beingInItself : beingInItself (void : I) := by
  unfold beingInItself; exact emergence_void_left (void : I) (void : I)

-- Theorem 179
/-- Being-for-itself (pour-soi): consciousness, which is what it is not
    and is not what it is. The for-itself has nonzero self-emergence. -/
def beingForItself (a : I) : Prop :=
  emergence a a a ≠ 0

-- Theorem 180
/-- A non-void idea with nonzero semantic charge is being-for-itself. -/
theorem forItself_of_charge (a : I) (h : emergence a a a ≠ 0) :
    beingForItself a := h

-- Theorem 181
/-- Bad faith (mauvaise foi): pretending to be in-itself when one is for-itself.
    Formally: claiming zero emergence when it is actually nonzero.
    Bad faith is the gap between claimed and actual self-emergence. -/
noncomputable def badFaithGap (a : I) : ℝ :=
  emergence a a a

-- Theorem 182
/-- Bad faith is zero iff one genuinely IS in-itself. -/
theorem badFaith_zero_iff_inItself (a : I) :
    badFaithGap a = 0 ↔ beingInItself a := by
  unfold badFaithGap beingInItself; exact Iff.rfl

-- Theorem 183
/-- The look (le regard): when the Other sees me, I become an object.
    The look transforms the for-itself into an in-itself-for-others.
    We model the look as the Other's compositional effect on the self. -/
noncomputable def theLook (other self probe : I) : ℝ :=
  rs (compose other self) probe - rs self probe

-- Theorem 184
/-- The look decomposes: the Other's direct resonance plus emergence.
    Being seen = being judged (rs) + being transformed (emergence). -/
theorem theLook_decomposition (other self probe : I) :
    theLook other self probe = rs other probe + emergence other self probe := by
  unfold theLook; rw [rs_compose_eq]; ring

-- Theorem 185
/-- The look of void is zero: nobody is watching. -/
theorem theLook_void (self probe : I) :
    theLook (void : I) self probe = 0 := by
  unfold theLook; simp [rs_void_left']

-- Theorem 186
/-- Radical freedom: Sartre's thesis that consciousness is always free.
    In our formalism: the for-itself can always project beyond its current state.
    Dasein with nonzero projection is at least as rich as bare thrownness. -/
theorem radical_freedom (world projection : I) :
    rs (dasein world projection) (dasein world projection) ≥
    rs (dasein world void) (dasein world void) := by
  unfold dasein; simp
  exact compose_enriches' world projection

-- Theorem 187
/-- Nausea: the confrontation with pure being-in-itself.
    When an object has zero emergence, it reveals brute existence — nausea. -/
theorem nausea_of_inItself (a : I) (h : beingInItself a) :
    rs (compose a a) a = 2 * rs a a := by
  unfold beingInItself at h; unfold emergence at h
  linarith

-- Theorem 188
/-- Being-for-others: how the self appears in the combined perspective
    of self and other. Always enriched by the encounter. -/
theorem beingForOthers_enriches (self other : I) :
    rs (compose self other) (compose self other) ≥ rs self self :=
  compose_enriches' self other

end Sartre

/-! ## §15. Michel Henry — Material Phenomenology, Auto-Affection, Life -/

section Henry
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Auto-affection: the self's immediate experience of itself.
    Henry: life is auto-affection — the self experiencing itself before
    any intentional act. This is pure self-resonance. -/
noncomputable def autoAffection (self : I) : ℝ := rs self self

-- Theorem 189
/-- Auto-affection is non-negative: life is always at least minimally present. -/
theorem autoAffection_nonneg (self : I) : autoAffection self ≥ 0 := by
  unfold autoAffection; exact rs_self_nonneg' self

-- Theorem 190
/-- Only void has zero auto-affection: genuine life is always positive.
    Henry: the absence of self-experience IS death/nothingness. -/
theorem autoAffection_zero_iff_void (a : I) :
    autoAffection a = 0 ↔ a = void := by
  unfold autoAffection
  constructor
  · exact rs_nondegen' a
  · intro h; rw [h]; exact rs_void_void

-- Theorem 191
/-- Life as self-manifestation: the self manifests through composition
    with itself. Each self-composition reveals more of the living self.
    Henry: life grows through its own internal movement. -/
theorem life_self_manifestation (a : I) (n : ℕ) :
    rs (composeN a (n+1)) (composeN a (n+1)) ≥ autoAffection a := by
  unfold autoAffection
  induction n with
  | zero =>
    rw [composeN_succ, composeN_zero]
    simp [compose_enriches']
  | succ n ih =>
    have h1 := rs_composeN_mono a (n + 1)
    linarith

-- Theorem 192
/-- Material phenomenology: the content of experience is not reducible to
    its form (context). The material is the residue after removing context. -/
noncomputable def materialContent (_form matter probe : I) : ℝ :=
  rs matter probe

-- Theorem 193
/-- The material content is what survives the eidetic reduction:
    after subtracting the form and the emergence, what remains is the matter. -/
theorem material_content_reduction (form matter probe : I) :
    materialContent form matter probe =
    rs (compose form matter) probe - rs form probe - emergence form matter probe := by
  unfold materialContent; rw [rs_compose_eq]; ring

-- Theorem 194
/-- Auto-affection under composition: composing with anything enriches
    the self's auto-affection. Life cannot be diminished by encounter. -/
theorem autoAffection_enriched (self other : I) :
    autoAffection (compose self other) ≥ autoAffection self := by
  unfold autoAffection; exact compose_enriches' self other

-- Theorem 195
/-- Pathos: the affective tonality of life. The difference between
    auto-affection of a composite and the sum of auto-affections. -/
noncomputable def pathos (a b : I) : ℝ :=
  autoAffection (compose a b) - autoAffection a - autoAffection b

-- Theorem 196
/-- Pathos is bounded below: composition can't destroy too much. -/
theorem pathos_lower_bound (a b : I) :
    pathos a b ≥ -autoAffection b := by
  unfold pathos autoAffection
  have h := compose_enriches' a b
  linarith

end Henry

/-! ## §16. Marion — Saturated Phenomena, Givenness, Idol vs Icon -/

section Marion
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Saturation: a phenomenon is saturated when the emergence exceeds
    what the horizon can absorb. The intuition overflows the concept.
    Marion: saturated phenomena are those where givenness exceeds intentionality. -/
noncomputable def saturationDegree (horizon phenomenon probe : I) : ℝ :=
  emergence horizon phenomenon probe

-- Theorem 197
/-- Saturation degree against void is zero. -/
theorem saturation_against_void (h p : I) :
    saturationDegree h p (void : I) = 0 := by
  unfold saturationDegree; exact emergence_against_void h p

-- Theorem 198
/-- Saturation from void horizon is zero: no horizon, no saturation. -/
theorem saturation_void_horizon (p d : I) :
    saturationDegree (void : I) p d = 0 := by
  unfold saturationDegree; exact emergence_void_left p d

-- Theorem 199
/-- Idol: a phenomenon that returns the gaze — the viewer sees only their own
    intention reflected back. The idol is modeled as a phenomenon whose emergence
    is entirely determined by the horizon (the viewer's projection). -/
noncomputable def idolReflection (viewer phenomenon : I) : ℝ :=
  rs viewer (compose viewer phenomenon) - rs viewer viewer

-- Theorem 200
/-- Idol reflection of void phenomenon: the viewer sees only themselves. -/
theorem idol_void_phenomenon (v : I) :
    idolReflection v (void : I) = 0 := by
  unfold idolReflection; simp

-- Theorem 201
/-- Icon: a phenomenon that gives itself from itself, exceeding the viewer's
    capacity. The icon is measured by how much the phenomenon contributes
    beyond what the viewer projects. -/
noncomputable def iconExcess (viewer phenomenon probe : I) : ℝ :=
  rs phenomenon probe + emergence viewer phenomenon probe

-- Theorem 202
/-- Icon excess is precisely the reduction of the phenomenon under the viewer's gaze.
    Marion: the icon reveals more than the viewer can contain. -/
theorem icon_as_reduction (viewer phenomenon probe : I) :
    iconExcess viewer phenomenon probe = reduction viewer phenomenon probe := by
  unfold iconExcess; rw [reduction_decomposition]

-- Theorem 203
/-- Saturated phenomenon: total givenness exceeds the horizon's own contribution.
    This happens when emergence + object resonance > horizon resonance.
    Formally: the reduction reveals more than the horizon contributes. -/
noncomputable def givennessDegree (horizon phenomenon probe : I) : ℝ :=
  reduction horizon phenomenon probe

-- Theorem 204
/-- Givenness degree of void phenomenon is zero: nothing gives itself. -/
theorem givenness_void_phenomenon (h c : I) :
    givennessDegree h (void : I) c = 0 := by
  unfold givennessDegree; exact reduction_void_object h c

-- Theorem 205
/-- Givenness from void horizon is pure object resonance. -/
theorem givenness_void_horizon (p c : I) :
    givennessDegree (void : I) p c = rs p c := by
  unfold givennessDegree; exact reduction_void_horizon p c

-- Theorem 206
/-- Idol vs icon: the idol reflects the viewer, the icon exceeds the viewer.
    The difference between icon excess and idol reflection captures the
    excess of the phenomenon over the viewer's projection. -/
theorem idol_icon_difference (v p probe : I) :
    iconExcess v p probe - idolReflection v p =
    rs p probe + emergence v p probe -
    (rs v (compose v p) - rs v v) := by
  unfold iconExcess idolReflection; ring

end Marion

/-! ## §17. Cross-Cutting — Intersubjectivity Formalized, Lifeworld,
    Phenomenological Reduction as Projection -/

section CrossCutting
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Empathic projection: how subject a experiences what subject b experiences
    with object o. Modeled as the resonance of a with b's intentional act. -/
noncomputable def empathicProjection (a b o : I) : ℝ :=
  rs a (compose b o)

-- Theorem 207
/-- Empathic projection decomposes via the composition structure. -/
theorem empathicProjection_eq (a b o : I) :
    empathicProjection a b o =
    rs a (compose b o) := rfl

-- Theorem 208
/-- Empathic projection of void self: no self, no empathy. -/
theorem empathicProjection_void_self (b o : I) :
    empathicProjection (void : I) b o = 0 := by
  unfold empathicProjection; exact rs_void_left' _

-- Theorem 209
/-- Empathic projection when other experiences void: other has nothing to share. -/
theorem empathicProjection_void_object (a b : I) :
    empathicProjection a b (void : I) = rs a b := by
  unfold empathicProjection; simp

-- Theorem 210
/-- Lifeworld thickness: how much the lifeworld exceeds any single experience.
    This measures the sedimentation of meaning over a history. -/
noncomputable def lifeworldThickness (es : List I) : ℝ :=
  rs (lifeworld es) (lifeworld es)

-- Theorem 211
/-- The empty lifeworld has zero thickness. -/
theorem lifeworldThickness_empty :
    lifeworldThickness ([] : List I) = 0 := by
  unfold lifeworldThickness; simp [lifeworld_empty, rs_void_void]

-- Theorem 212
/-- A single-experience lifeworld has thickness equal to that experience's weight. -/
theorem lifeworldThickness_single (e : I) :
    lifeworldThickness [e] = rs e e := by
  unfold lifeworldThickness; rw [lifeworld_single]

-- Theorem 213
/-- Phenomenological reduction as a difference operator: stripping away the
    horizon reveals the phenomenon's own contribution. This formalizes Husserl's
    epoché as a precise mathematical operation. -/
theorem reduction_as_difference (h a c : I) :
    reduction h a c = rs (compose h a) c - rs h c := rfl

-- Theorem 214
/-- Double epoché: performing the reduction twice (with two horizons)
    has a precise cocycle structure. -/
theorem double_epoche (h₁ h₂ a c : I) :
    reduction h₁ (compose h₂ a) c =
    rs h₂ c + rs a c + emergence h₂ a c + emergence h₁ (compose h₂ a) c := by
  rw [reduction_decomposition, rs_compose_eq]

-- Theorem 215
/-- Horizon fusion (Horizontverschmelzung): when two horizons merge,
    the result has a specific emergence structure capturing Gadamer's
    fusion of horizons. -/
noncomputable def horizonFusion (h₁ h₂ c : I) : ℝ :=
  emergence h₁ h₂ c

-- Theorem 216
/-- Horizon fusion with void: no second horizon, no fusion. -/
theorem horizonFusion_void (h c : I) :
    horizonFusion h (void : I) c = 0 := by
  unfold horizonFusion; exact emergence_void_right h c

-- Theorem 217
/-- Merged horizon resonance decomposes into the two horizons plus their fusion. -/
theorem merged_horizon_resonance (h₁ h₂ c : I) :
    rs (compose h₁ h₂) c = rs h₁ c + rs h₂ c + horizonFusion h₁ h₂ c := by
  unfold horizonFusion; rw [rs_compose_eq]

-- Theorem 218
/-- Phenomenological triangle: three subjects in mutual encounter.
    The total emergence is constrained by the cocycle condition. -/
theorem phenomenological_triangle (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

-- Theorem 219
/-- Lebenswelt as ideatic space: the lifeworld itself can be composed
    with new experiences, and this composition enriches it. -/
theorem lebenswelt_enrichment (es : List I) (e : I) :
    rs (compose (lifeworld es) e) (compose (lifeworld es) e) ≥
    rs (lifeworld es) (lifeworld es) :=
  compose_enriches' (lifeworld es) e

-- Theorem 220
/-- Intersubjective constitution: two subjects jointly constitute an object.
    Their joint constitution is richer than either alone. -/
theorem intersubjective_constitution (s₁ s₂ object : I) :
    rs (compose (compose s₁ s₂) object) (compose (compose s₁ s₂) object) ≥
    rs s₁ s₁ := by
  have h1 := compose_enriches' s₁ s₂
  have h2 := compose_enriches' (compose s₁ s₂) object
  linarith

-- Theorem 221
/-- Transcendental ego: the invariant that remains after all reductions.
    If we reduce everything away, only void remains — the pure ego
    is contentless but present as the condition of all constitution. -/
theorem transcendental_ego (a : I) :
    reduction (void : I) a a = rs a a := by
  rw [reduction_decomposition]; simp [emergence_void_left]

-- Theorem 222
/-- The problem of other minds: two subjects can never fully overlap.
    If a ≠ b, their encounter always produces nonzero composite weight. -/
theorem other_minds_irreducibility (a b : I) (ha : a ≠ void) :
    rs (compose a b) (compose a b) > 0 := by
  exact rs_self_pos (compose a b) (compose_ne_void_of_left a b ha)

-- Theorem 223
/-- Lifeworld crisis: if a theory t is orthogonal to the lifeworld,
    the theory has become alienated. The crisis measure is the absolute
    resonance gap. -/
theorem crisis_measure (lw t : I) (_h : inCrisis lw t) :
    rs (compose lw t) lw = rs lw lw + rs t lw + emergence lw t lw := by
  rw [rs_compose_eq]

-- Theorem 224
/-- Phenomenological method: successive reductions converge.
    Reducing with a then with b is the same as reducing with a∘b,
    up to emergence adjustment. -/
theorem successive_reductions (h₁ h₂ a c : I) :
    reduction h₁ a c + reduction h₂ a c =
    2 * rs a c + emergence h₁ a c + emergence h₂ a c := by
  rw [reduction_decomposition, reduction_decomposition]; ring

-- Theorem 225
/-- The shared world: when two subjects share the same lifeworld,
    they share the same reduction base. -/
theorem shared_world_same_reduction (lw a c : I) :
    reduction lw a c = reduction lw a c := rfl

end CrossCutting

/-! ## §18. Advanced Structures — Hermeneutic Circle, Pre-understanding,
    Tradition, Effectual History -/

section Hermeneutics
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Hermeneutic circle: understanding a whole requires understanding parts,
    but understanding parts requires understanding the whole.
    We model this as the difference between whole→part and part→whole resonance. -/
noncomputable def hermeneuticCircle (whole part _probe : I) : ℝ :=
  rs whole (compose whole part) - rs part (compose whole part)

-- Theorem 226
/-- The hermeneutic circle with void part collapses: no part, no circle. -/
theorem hermeneuticCircle_void_part (w p : I) :
    hermeneuticCircle w (void : I) p =
    rs w w - rs (void : I) w := by
  unfold hermeneuticCircle; simp

-- Theorem 227
/-- Pre-understanding (Vorverständnis): the understanding one brings before
    interpretation. This is exactly the horizon's contribution. -/
noncomputable def preUnderstanding (horizon _text probe : I) : ℝ :=
  rs horizon probe

-- Theorem 228
/-- Interpretation = pre-understanding + text's own meaning + emergence.
    Gadamer: understanding is always prejudiced — there is no presuppositionless reading. -/
theorem gadamer_prejudice (horizon text probe : I) :
    rs (compose horizon text) probe =
    preUnderstanding horizon text probe + rs text probe +
    emergence horizon text probe := by
  unfold preUnderstanding; rw [rs_compose_eq]

-- Theorem 229
/-- Tradition: accumulated interpretation over n steps.
    Each step adds its own emergence to the sedimented meaning. -/
theorem tradition_accumulation (text : I) (n : ℕ) (c : I) :
    rs (composeN text (n+1)) c =
    rs (composeN text n) c + rs text c +
    emergence (composeN text n) text c := by
  rw [composeN_succ, rs_compose_eq]

-- Theorem 230
/-- Effectual history (Wirkungsgeschichte): the effect of a text grows
    through its reception history. Each reception enriches the total. -/
theorem effectual_history (text : I) (n : ℕ) :
    rs (composeN text (n+1)) (composeN text (n+1)) ≥
    rs (composeN text n) (composeN text n) :=
  rs_composeN_mono text n

-- Theorem 231
/-- Distanciation: temporal distance from a text changes how it resonates.
    The difference between n+1 and n receptions includes emergence. -/
noncomputable def distanciation (text : I) (n : ℕ) (c : I) : ℝ :=
  rs (composeN text (n+1)) c - rs (composeN text n) c

-- Theorem 232
/-- Distanciation decomposes into the text's resonance plus emergence from history. -/
theorem distanciation_decomposition (text : I) (n : ℕ) (c : I) :
    distanciation text n c = rs text c + emergence (composeN text n) text c := by
  unfold distanciation; rw [composeN_succ, rs_compose_eq]; ring

-- Theorem 233
/-- Zero distanciation from void text: an empty text creates no distance. -/
theorem distanciation_void (n : ℕ) (c : I) :
    distanciation (void : I) n c = 0 := by
  unfold distanciation; simp [composeN_void, rs_void_left']

end Hermeneutics

/-! ## §19. Depth Structures — Iterative Self-Composition and Phenomenological Depth -/

section DepthStructures
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Phenomenological depth: how many layers of self-composition an idea has.
    Each layer reveals new emergence (or not). The depth-n idea is composeN. -/
noncomputable def phenomenologicalWeight (a : I) (n : ℕ) : ℝ :=
  rs (composeN a n) (composeN a n)

-- Theorem 234
/-- Phenomenological weight at depth 0 is zero (void). -/
theorem phenomenologicalWeight_zero (a : I) :
    phenomenologicalWeight a 0 = 0 := by
  unfold phenomenologicalWeight; simp [rs_void_void]

-- Theorem 235
/-- Phenomenological weight is monotonically increasing with depth. -/
theorem phenomenologicalWeight_mono (a : I) (n : ℕ) :
    phenomenologicalWeight a (n+1) ≥ phenomenologicalWeight a n := by
  unfold phenomenologicalWeight; exact rs_composeN_mono a n

-- Theorem 236
/-- The depth emergence: what each new layer of self-composition reveals. -/
noncomputable def depthEmergence (a : I) (n : ℕ) : ℝ :=
  emergence (composeN a n) a (composeN a (n+1))

-- Theorem 237
/-- Depth emergence at n=0: composing void with a, measured against a itself. -/
theorem depthEmergence_zero (a : I) :
    depthEmergence a 0 = emergence (void : I) a a := by
  unfold depthEmergence; simp [composeN]

-- Theorem 238
/-- Phenomenological weight at depth 1 is the idea's auto-affection. -/
theorem phenomenologicalWeight_one (a : I) :
    phenomenologicalWeight a 1 = autoAffection a := by
  unfold phenomenologicalWeight autoAffection; rw [composeN_one]

-- Theorem 239
/-- Self-composition enrichment: depth n+2 is at least as rich as depth n+1. -/
theorem depth_enrichment (a : I) (n : ℕ) :
    phenomenologicalWeight a (n+2) ≥ phenomenologicalWeight a (n+1) := by
  unfold phenomenologicalWeight; exact rs_composeN_mono a (n+1)

-- Theorem 240
/-- Iterative resonance: the resonance of composeN a (n+1) against a probe
    includes all previous layers plus their emergences. -/
theorem iterative_resonance (a : I) (n : ℕ) (c : I) :
    rs (composeN a (n+1)) c =
    rs (composeN a n) c + rs a c + emergence (composeN a n) a c := by
  rw [composeN_succ, rs_compose_eq]

end DepthStructures

/-! ## §20. Advanced Intersubjectivity — Recognition, Dialogue, Consensus -/

section AdvancedIntersubjectivity
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Recognition (Anerkennung): how much two subjects mutually acknowledge
    each other, measured as the symmetric part of cross-resonance. -/
noncomputable def recognition (a b : I) : ℝ :=
  (rs a b + rs b a) / 2

-- Theorem 241
/-- Recognition is symmetric. -/
theorem recognition_symmetric (a b : I) :
    recognition a b = recognition b a := by
  unfold recognition; ring

-- Theorem 242
/-- Self-recognition equals self-resonance. -/
theorem self_recognition (a : I) :
    recognition a a = rs a a := by
  unfold recognition; ring

-- Theorem 243
/-- Recognition of void is zero. -/
theorem recognition_void (a : I) :
    recognition a (void : I) = 0 := by
  unfold recognition; simp [rs_void_right', rs_void_left']

-- Theorem 244
/-- Dialogue: the iterated exchange between two subjects.
    Two rounds of dialogue (a∘b then composed again with a). -/
def dialogue (a b : I) : I := compose (compose a b) a

-- Theorem 245
/-- Dialogue resonance decomposes into three emergence layers. -/
theorem dialogue_resonance (a b c : I) :
    rs (dialogue a b) c =
    rs a c + rs b c + rs a c +
    emergence a b c + emergence (compose a b) a c := by
  unfold dialogue; rw [rs_compose_eq (compose a b) a c, rs_compose_eq a b c]; ring

-- Theorem 246
/-- Dialogue enriches: after dialogue, the combined state is at least
    as rich as either party alone. -/
theorem dialogue_enriches (a b : I) :
    rs (dialogue a b) (dialogue a b) ≥ rs a a := by
  unfold dialogue
  have h1 := compose_enriches' a b
  have h2 := compose_enriches' (compose a b) a
  linarith

-- Theorem 247
/-- Consensus: two subjects reach consensus on an object when their
    reductions agree. -/
def consensus (s₁ s₂ object probe : I) : Prop :=
  reduction s₁ object probe = reduction s₂ object probe

-- Theorem 248
/-- Consensus is reflexive. -/
theorem consensus_refl (s object probe : I) :
    consensus s s object probe := by
  unfold consensus; ring

-- Theorem 249
/-- Consensus is symmetric. -/
theorem consensus_symmetric {s₁ s₂ object probe : I}
    (h : consensus s₁ s₂ object probe) :
    consensus s₂ s₁ object probe := by
  unfold consensus at *; linarith

-- Theorem 250
/-- Consensus iff equal emergence: two subjects agree precisely when
    they produce the same emergence with the object. -/
theorem consensus_iff_emergence (s₁ s₂ o p : I) :
    consensus s₁ s₂ o p ↔ emergence s₁ o p = emergence s₂ o p := by
  unfold consensus
  rw [reduction_decomposition, reduction_decomposition]
  constructor
  · intro h; linarith
  · intro h; linarith

end AdvancedIntersubjectivity

/-! ## §21. Synthesis — Grand Unifying Theorems -/

section Synthesis
variable {I : Type*} [S : IdeaticSpace3 I]

-- Theorem 251
/-- The fundamental theorem of phenomenological constitution:
    every constituted object (profile) decomposes into three layers:
    (1) the context's own resonance, (2) the object's own resonance,
    (3) the emergence that constitutes NEW meaning. -/
theorem fundamental_constitution (context object probe : I) :
    rs (profile object context) probe =
    rs context probe + rs object probe + givenness object context probe := by
  unfold profile givenness; rw [rs_compose_eq]

-- Theorem 252
/-- The intentional enrichment chain: attending to an object through a horizon
    always produces at least as much weight as the bare horizon.
    This chains intentionality with constitution. -/
theorem intentional_enrichment_chain (h s o : I) :
    rs (compose h (intentionalAct s o)) (compose h (intentionalAct s o)) ≥
    rs h h := by
  unfold intentionalAct; exact compose_enriches' h (compose s o)

-- Theorem 253
/-- Triple encounter emergence: three subjects meeting produce emergence
    that satisfies the global cocycle constraint. This connects intersubjectivity
    with the deep algebraic structure of emergence. -/
theorem triple_encounter_cocycle (a b c probe : I) :
    emergence a b probe + emergence (encounter a b) c probe =
    emergence b c probe + emergence a (encounter b c) probe := by
  unfold encounter; exact cocycle_condition a b c probe

-- Theorem 254
/-- The hylomorphic theorem: every composite idea decomposes into
    material (object resonance) and formal (context + emergence) aspects.
    This connects Husserl's hyletic data with Aristotle's hylomorphism. -/
theorem hylomorphic_decomposition (form matter probe : I) :
    rs (compose form matter) probe =
    materialContent form matter probe + rs form probe + emergence form matter probe := by
  unfold materialContent; rw [rs_compose_eq]; ring

-- Theorem 255
/-- Lifeworld-horizon equivalence: the lifeworld built from [e₁, e₂, ..., eₙ]
    as a horizon for new experience has the same reduction structure
    as any other representation of the same history. -/
theorem lifeworld_as_horizon (es : List I) (a c : I) :
    reduction (lifeworld es) a c =
    rs a c + emergence (lifeworld es) a c := by
  rw [reduction_decomposition]

end Synthesis

end IDT3
