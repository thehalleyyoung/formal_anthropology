import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Phenomenology of Reading

Husserl's intentionality, Heidegger's Dasein, and Merleau-Ponty's embodied
perception, formalized within the quantitative resonance framework of IDT v2.

Key formalizations:
- **Intentionality**: consciousness is always directed — every mental act is a
  composition of subject and object (Husserl).
- **Horizon**: perception occurs against a background of pre-understanding;
  each perception enriches the horizon (Gadamer).
- **Lifeworld** (Lebenswelt): accumulated experience as iterated composition.
- **Epoché**: phenomenological reduction — the object is invariant under
  change of subject.
- **Dasein**: being-in-the-world — the subject is always already situated
  (Heidegger). Care (Sorge) as resonance with possibilities.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Phenomenology

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2 IDT2

/-! ## §1. Intentionality — Consciousness Directed Toward Objects -/

/-- Intentional act: consciousness directed toward an object.
    Every mental act is a composition of subject and object (Husserl). -/
def intentionalAct (subject object : I) : I := compose subject object

/-- Noetic-noematic correlation: the experience is the composed subject+object.
    Noesis (act of thinking) + noema (thought-content) = experience. -/
def experience (noesis noema : I) : I := compose noesis noema

/-- Experiential weight: the intensity/richness of an experience.
    Measured by the self-resonance of the composed intentional act. -/
noncomputable def experientialWeight (subject object : I) : ℝ :=
  resonanceStrength (intentionalAct subject object) (intentionalAct subject object)

/-- Attentiveness: how much the subject resonates with the object.
    Higher attentiveness = deeper engagement with the phenomenon. -/
noncomputable def attentiveness (subject object : I) : ℝ :=
  resonanceStrength subject object

/-- Lifeworld (Lebenswelt): the total accumulated experience.
    Modeled as iterated composition of all experiences. -/
def lifeworld : List I → I
  | [] => void
  | e :: rest => compose e (lifeworld rest)

/-- Theorem 1: Intentionality toward void = bare subject.
    Without an object, consciousness collapses to the subject alone. -/
theorem intentional_act_void_object (s : I) :
    intentionalAct s (void : I) = s := by
  unfold intentionalAct; exact IdeaticSpace2.void_right s

/-- Theorem 2: Void subject sees the object as it is.
    Without a subject, only the object remains — pure objectivity. -/
theorem intentional_act_void_subject (o : I) :
    intentionalAct (void : I) o = o := by
  unfold intentionalAct; exact IdeaticSpace2.void_left o

/-- Theorem 3: Experience enriches beyond bare subjectivity.
    Experiential weight ≥ subject's self-resonance.
    Engaging with any object can only enrich, never diminish. -/
theorem experientialWeight_ge_subject (s o : I) :
    experientialWeight s o ≥ resonanceStrength s s := by
  unfold experientialWeight intentionalAct
  exact rs_compose_self_right s o

/-- Theorem 4: Experience preserves the object's weight.
    Experiential weight ≥ object's self-resonance.
    The object is never lost in the experience. -/
theorem experientialWeight_ge_object (s o : I) :
    experientialWeight s o ≥ resonanceStrength o o := by
  unfold experientialWeight intentionalAct
  exact rs_compose_self_left o s

/-- Theorem 5: All experience is strictly positive.
    No genuine experience is empty — even minimal engagement has weight. -/
theorem experientialWeight_pos (s o : I) :
    experientialWeight s o > 0 := by
  unfold experientialWeight; exact rs_self_pos' _

/-- Theorem 6: Experiential weight is at least 1 (calibration).
    The void baseline provides a lower bound on all experience. -/
theorem experientialWeight_ge_one (s o : I) :
    experientialWeight s o ≥ 1 := by
  unfold experientialWeight; exact rs_self_ge_one _

/-- Theorem 7: Attentiveness is symmetric.
    If the subject resonates with the object, the object resonates with the subject.
    The phenomenon "speaks back" to consciousness (Merleau-Ponty). -/
theorem attentiveness_symm (s o : I) :
    attentiveness s o = attentiveness o s := by
  unfold attentiveness; exact IdeaticSpace2.rs_symm s o

/-- Theorem 8: Self-attentiveness is always positive.
    Consciousness is always aware of itself (Husserl's inner time-consciousness). -/
theorem self_attentiveness_pos (s : I) :
    attentiveness s s > 0 := rs_self_pos' s

/-- Theorem 9: Attentiveness is non-negative.
    Even unfamiliar phenomena elicit non-negative resonance. -/
theorem attentiveness_nonneg (s o : I) :
    attentiveness s o ≥ 0 := by
  unfold attentiveness; exact IdeaticSpace2.rs_nonneg s o

/-- Theorem 10: Attentiveness satisfies Cauchy-Schwarz.
    No object can be attended to more strongly than self-awareness allows. -/
theorem attentiveness_cauchy_schwarz (s o : I) :
    attentiveness s o * attentiveness s o ≤
    attentiveness s s * attentiveness o o := by
  unfold attentiveness; exact IdeaticSpace2.rs_cauchy_schwarz s o

/-! ## §2. Horizons — The Background of Perception -/

/-- Perception: composing the horizon with the percept.
    Every perception occurs against a background of pre-understanding. -/
def perceive (horizon percept : I) : I := compose horizon percept

/-- Horizon shift: perception changes the horizon.
    After perceiving, the new horizon IS the composed result (Gadamer). -/
def horizonShift (horizon percept : I) : I := perceive horizon percept

/-- Theorem 11: Perception enriches the horizon.
    The shifted horizon resonates at least as strongly as the original.
    Each perception makes the subject "weightier." -/
theorem perception_enriches_horizon (h p : I) :
    resonanceStrength (horizonShift h p) (horizonShift h p) ≥
    resonanceStrength h h := by
  unfold horizonShift perceive
  exact rs_compose_self_right h p

/-- Theorem 12: Perception preserves the percept's weight.
    The shifted horizon retains at least the percept's own richness.
    What is perceived is not lost in the absorption. -/
theorem perception_preserves_percept (h p : I) :
    resonanceStrength (horizonShift h p) (horizonShift h p) ≥
    resonanceStrength p p := by
  unfold horizonShift perceive
  exact rs_compose_self_left p h

/-- Theorem 13: Sequential perception is associative.
    Perceiving p₁ then p₂ = perceiving their composition.
    Formalizes the temporal structure of perception (Husserl's retention). -/
theorem sequential_perception (h p1 p2 : I) :
    perceive (perceive h p1) p2 = perceive h (compose p1 p2) := by
  unfold perceive; exact IDT2.compose_assoc h p1 p2

/-- Theorem 14: Void horizon is transparent.
    Without preconceptions, you see the thing itself —
    Husserl's "zu den Sachen selbst!" -/
theorem void_horizon_transparent (p : I) :
    perceive (void : I) p = p := by
  unfold perceive; exact IdeaticSpace2.void_left p

/-- Theorem 15: Depth grows with perception.
    Horizon complexity increases with each perception, bounded by the sum. -/
theorem horizon_depth_grows (h p : I) :
    depth (horizonShift h p) ≤ depth h + depth p := by
  unfold horizonShift perceive
  exact IdeaticSpace2.depth_subadditive h p

/-- Theorem 16: Perceiving nothing doesn't change you.
    The null percept leaves the horizon unchanged. -/
theorem horizonShift_void (h : I) :
    horizonShift h (void : I) = h := by
  unfold horizonShift perceive; exact IdeaticSpace2.void_right h

/-- Theorem 17: Two observers of the same percept grow closer.
    Shared perception increases mutual resonance — the basis of
    intersubjectivity (Merleau-Ponty's intercorporeality). -/
theorem shared_perception_increases_resonance (h1 h2 p : I) :
    resonanceStrength (perceive h1 p) (perceive h2 p) ≥
    resonanceStrength h1 h2 := by
  unfold perceive; exact rs_compose_both_mono h1 h2 p

/-! ## §3. Lifeworld (Lebenswelt) — Accumulated Experience -/

/-- Total depth: sum of depths of a list of experiences. -/
def totalDepth : List I → ℕ
  | [] => 0
  | e :: rest => depth e + totalDepth rest

/-- Theorem 18: No experience = empty subject.
    The lifeworld of no experiences is void. -/
theorem lifeworld_nil : lifeworld ([] : List I) = (void : I) := rfl

/-- Theorem 19: A single experience IS the experience.
    One experience defines the entire lifeworld. -/
theorem lifeworld_singleton (e : I) : lifeworld [e] = e := by
  show compose e (void : I) = e
  exact IdeaticSpace2.void_right e

/-- Theorem 20: Recursive structure of the lifeworld.
    Each new experience composes with the accumulated past. -/
theorem lifeworld_cons (e : I) (rest : List I) :
    lifeworld (e :: rest) = compose e (lifeworld rest) := rfl

/-- Theorem 21: Lifeworld distributes over concatenation.
    Combining two life-phases = composing their lifeworlds (monoidal). -/
theorem lifeworld_append (es1 es2 : List I) :
    lifeworld (es1 ++ es2) = compose (lifeworld es1) (lifeworld es2) := by
  induction es1 with
  | nil =>
    show lifeworld es2 = compose (void : I) (lifeworld es2)
    rw [IdeaticSpace2.void_left]
  | cons e rest ih =>
    show compose e (lifeworld (rest ++ es2)) =
         compose (compose e (lifeworld rest)) (lifeworld es2)
    rw [ih, IdeaticSpace2.compose_assoc]

/-- Theorem 22: The lifeworld grows with each experience.
    Self-resonance never decreases as experiences accumulate. -/
theorem lifeworld_weight_mono (e : I) (rest : List I) :
    resonanceStrength (lifeworld (e :: rest)) (lifeworld (e :: rest)) ≥
    resonanceStrength (lifeworld rest) (lifeworld rest) := by
  show resonanceStrength (compose e (lifeworld rest)) (compose e (lifeworld rest)) ≥ _
  exact IdeaticSpace2.rs_compose_left_mono _ _ e

/-- Theorem 23: Lifeworld self-resonance is always positive. -/
theorem lifeworld_weight_pos (es : List I) :
    resonanceStrength (lifeworld es) (lifeworld es) > 0 :=
  rs_self_pos' _

/-- Theorem 24: Lifeworld self-resonance is at least 1.
    The void calibration guarantees a baseline. -/
theorem lifeworld_weight_ge_one (es : List I) :
    resonanceStrength (lifeworld es) (lifeworld es) ≥ 1 :=
  rs_self_ge_one _

/-- Theorem 25: Lifeworld depth is bounded by the sum of experience depths. -/
theorem lifeworld_depth_bound : ∀ (es : List I),
    depth (lifeworld es) ≤ totalDepth es
  | [] => by
    show depth (void : I) ≤ 0
    rw [IdeaticSpace2.depth_void]
  | e :: rest => by
    show depth (compose e (lifeworld rest)) ≤ depth e + totalDepth rest
    have h := IdeaticSpace2.depth_subadditive e (lifeworld rest)
    have ih := lifeworld_depth_bound rest
    omega

/-- Theorem 26: Empty lifeworld has unit self-resonance.
    The weight of no experience is exactly 1 — the void baseline. -/
theorem lifeworld_nil_weight :
    resonanceStrength (lifeworld ([] : List I)) (lifeworld ([] : List I)) = 1 := by
  show resonanceStrength (void : I) (void : I) = 1
  exact IdeaticSpace2.rs_void_self

/-! ## §4. Epoché — Phenomenological Reduction -/

/-- The bracketed experience: examining the object freed from the subject.
    Epoché strips away the subjective contribution, leaving the pure object. -/
def bracketedExperience (_subject object : I) : I := object

/-- Subjective excess: how much the full experience exceeds the pure object.
    Measures the subject's contribution to the richness of experience. -/
noncomputable def subjectiveExcess (subject object : I) : ℝ :=
  resonanceStrength (experience subject object) (experience subject object) -
  resonanceStrength object object

/-- Theorem 27: Bracketing is independent of the subject.
    THE phenomenological insight: the object is invariant under change of subject.
    No matter who performs the reduction, the same object is revealed. -/
theorem bracketing_independent_of_subject (s1 s2 o : I) :
    bracketedExperience s1 o = bracketedExperience s2 o := rfl

/-- Theorem 28: The subjective excess is non-negative.
    The subject can only add to the experience, never diminish it.
    Husserl: consciousness constitutes but does not destroy. -/
theorem subjective_excess_nonneg (s o : I) :
    subjectiveExcess s o ≥ 0 := by
  unfold subjectiveExcess experience
  linarith [rs_compose_self_left (I := I) o s]

/-- Theorem 29: Void subject contributes nothing.
    When the subject is void, the experience IS the object — zero excess. -/
theorem subjective_excess_void_subject (o : I) :
    subjectiveExcess (void : I) o = 0 := by
  show resonanceStrength (compose (void : I) o) (compose (void : I) o) -
       resonanceStrength o o = 0
  rw [IdeaticSpace2.void_left]; ring

/-- Theorem 30: Bracketing void gives void.
    Epoché applied to an experience with no object yields nothing. -/
theorem bracketed_void_object (s : I) :
    bracketedExperience s (void : I) = (void : I) := rfl

/-- Theorem 31: The full experience is at least as rich as the bracketed.
    Subjective engagement enriches — it never impoverishes the phenomenon. -/
theorem experience_exceeds_bracketed (s o : I) :
    resonanceStrength (experience s o) (experience s o) ≥
    resonanceStrength (bracketedExperience s o) (bracketedExperience s o) := by
  unfold experience bracketedExperience
  exact rs_compose_self_left o s

/-- Theorem 32: The full experience also exceeds the subject alone.
    The noema adds to the noesis — objects enrich the subject. -/
theorem experience_exceeds_subject (s o : I) :
    resonanceStrength (experience s o) (experience s o) ≥
    resonanceStrength s s := by
  unfold experience; exact rs_compose_self_right s o

/-- Theorem 33: Two subjects bracketing the same object get the same result.
    Epoché produces intersubjectively valid results (Husserl's
    transcendental intersubjectivity). -/
theorem epoche_intersubjective (s1 s2 o : I) :
    resonanceStrength (bracketedExperience s1 o) (bracketedExperience s1 o) =
    resonanceStrength (bracketedExperience s2 o) (bracketedExperience s2 o) := rfl

/-! ## §5. Being-in-the-World (Heidegger) — Dasein and Care -/

/-- Dasein: being-in-the-world.
    The subject is always already situated in a world — never a bare ego. -/
def dasein (self world : I) : I := compose self world

/-- Care (Sorge): Dasein's relationship to its possibilities.
    How much Dasein resonates with a given possibility. -/
noncomputable def care (d possibility : I) : ℝ :=
  resonanceStrength d possibility

/-- Existential weight: the richness of Dasein's being.
    Measured by self-resonance of the situated subject. -/
noncomputable def existentialWeight (self world : I) : ℝ :=
  resonanceStrength (dasein self world) (dasein self world)

/-- Theorem 34: Thrownness enriches the self.
    Being thrown into a world makes you at least as rich as your bare self.
    Geworfenheit: the world gives, not takes. -/
theorem thrownness_enriches_self (self world : I) :
    existentialWeight self world ≥ resonanceStrength self self := by
  unfold existentialWeight dasein
  exact rs_compose_self_right self world

/-- Theorem 35: Dasein absorbs the world's weight.
    The world is part of you — its weight is preserved in Dasein. -/
theorem dasein_absorbs_world (self world : I) :
    existentialWeight self world ≥ resonanceStrength world world := by
  unfold existentialWeight dasein
  exact rs_compose_self_left world self

/-- Theorem 36: Dasein's weight is always positive.
    Being-in-the-world always has positive existential weight. -/
theorem dasein_weight_pos (self world : I) :
    existentialWeight self world > 0 := by
  unfold existentialWeight; exact rs_self_pos' _

/-- Theorem 37: Dasein's weight is at least 1.
    Even minimal Dasein exceeds the void baseline. -/
theorem dasein_weight_ge_one (self world : I) :
    existentialWeight self world ≥ 1 := by
  unfold existentialWeight; exact rs_self_ge_one _

/-- Theorem 38: Care is non-negative.
    Dasein's relationship to any possibility is non-negative. -/
theorem care_nonneg (d possibility : I) :
    care d possibility ≥ 0 := by
  unfold care; exact IdeaticSpace2.rs_nonneg d possibility

/-- Theorem 39: Self-care is positive.
    Dasein always cares about itself — the most primordial care. -/
theorem self_care_pos (d : I) :
    care d d > 0 := rs_self_pos' d

/-- Theorem 40: Mitsein — shared world increases mutual resonance.
    Two beings in the same world resonate at least as strongly as bare selves.
    Formalizes Heidegger's Mitsein (being-with). -/
theorem mitsein_shared_resonance (s1 s2 w : I) :
    resonanceStrength (dasein s1 w) (dasein s2 w) ≥
    resonanceStrength s1 s2 := by
  unfold dasein; exact rs_compose_both_mono s1 s2 w

/-- Theorem 41: Mitsein preserves understanding.
    If two beings resonate positively, sharing a world preserves that.
    Community is possible because shared worlds preserve prior bonds. -/
theorem mitsein_preserves_understanding (s1 s2 w : I)
    (h : resonanceStrength s1 s2 > 0) :
    resonanceStrength (dasein s1 w) (dasein s2 w) > 0 := by
  have hmono := mitsein_shared_resonance (I := I) s1 s2 w
  linarith

/-- Theorem 42: Dasein's depth is bounded.
    The complexity of Dasein ≤ the complexity of self + world. -/
theorem dasein_depth_bound (self world : I) :
    depth (dasein self world) ≤ depth self + depth world := by
  unfold dasein; exact IdeaticSpace2.depth_subadditive self world

/-- Theorem 43: Void world = bare subject.
    Without a world, Dasein collapses to the bare self
    (impossible for Heidegger, but a limit case). -/
theorem dasein_void_world (self : I) :
    dasein self (void : I) = self := by
  unfold dasein; exact IdeaticSpace2.void_right self

/-- Theorem 44: Void self = pure world.
    Without a self, only the world remains — no Dasein, just the given. -/
theorem dasein_void_self (world : I) :
    dasein (void : I) world = world := by
  unfold dasein; exact IdeaticSpace2.void_left world

/-- Theorem 45: Dasein composition is associative.
    Being-in-(world₁-in-world₂) = (being-in-world₁)-in-world₂.
    Nested situations reduce to a single composed situation. -/
theorem dasein_assoc (self w1 w2 : I) :
    dasein (dasein self w1) w2 = dasein self (compose w1 w2) := by
  unfold dasein; exact IDT2.compose_assoc self w1 w2

/-- Theorem 46: Care is symmetric.
    If Dasein cares about X, then X "cares" about Dasein in the resonance sense.
    Formalizes the reciprocity of worldly engagement. -/
theorem care_symm (a b : I) :
    care a b = care b a := by
  unfold care; exact IdeaticSpace2.rs_symm a b

/-- Theorem 47: Engaging with the world grows Dasein's weight.
    Further world-engagement (adding context) never diminishes Dasein. -/
theorem world_engagement_grows (self world ctx : I) :
    resonanceStrength (dasein (dasein self world) ctx)
                      (dasein (dasein self world) ctx) ≥
    resonanceStrength (dasein self world) (dasein self world) := by
  unfold dasein; exact rs_compose_self_right (compose self world) ctx

/-- Theorem 48: Care satisfies Cauchy-Schwarz.
    Care for a possibility is bounded by the geometric mean of self-cares. -/
theorem care_cauchy_schwarz (d p : I) :
    care d p * care d p ≤ care d d * care p p := by
  unfold care; exact IdeaticSpace2.rs_cauchy_schwarz d p

end IDT2.Phenomenology
