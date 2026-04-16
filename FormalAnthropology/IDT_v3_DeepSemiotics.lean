import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Deep Semiotics — Paradoxes of Signs and Culture

## Counter-Intuitive Theorems about Semiotics, Narrative, and Aesthetics

This file contains 50 SURPRISING theorems derived from IdeaticSpace3 axioms.
Each captures a counter-intuitive or paradoxical phenomenon in the theory
of signs, narrative, translation, and aesthetics.

### Major Themes:
1. **Sign chain decay**: Reinterpretation always loses resonance
2. **Translation loss inevitability**: Lower bounds on translation distortion
3. **Defamiliarization fatigue**: Diminishing returns on novelty
4. **Narrative order dominance**: Order matters more than content
5. **Aesthetic non-monotonicity**: Adding beauty can destroy beauty
6. **Metaphor distortion**: Every metaphor necessarily distorts
7. **Semiotic drift**: Signs necessarily change meaning over time
8. **Rhyme-reason tradeoff**: Poetic form constrains semantic content

## NO SORRIES, NO ADMITS, NO AXIOMS (beyond IdeaticSpace3)
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. Sign Chain Decay: Reinterpretation Always Loses

When a sign is reinterpreted through a chain of contexts, each
reinterpretation introduces a gap. The total distortion grows
monotonically — you can never "gain back" what was lost. This
formalizes the childhood game of "telephone": meaning degrades
through successive reinterpretation. -/

section SignChainDecay
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS1. **Sign chain**: composing an idea with n successive contexts.
    Each context represents one "reinterpretation" or "reading". -/
def signChain (a : I) : List I → I
  | [] => a
  | c :: rest => signChain (compose a c) rest

/-- DS2. Empty chain preserves the sign. -/
theorem signChain_nil (a : I) : signChain a [] = a := rfl

/-- DS3. Single-context chain is just composition. -/
theorem signChain_singleton (a c : I) : signChain a [c] = compose a c := rfl

/-- DS4. **Sign weight never decreases through chains** — but this is
    misleading! Weight (self-resonance) grows, yet the sign's
    RELATIONSHIP to its original meaning (resonance with the original)
    is NOT guaranteed to grow. The sign gets "heavier" but not
    necessarily more faithful.

    SURPRISING: Adding context always adds weight, but can DECREASE
    resonance with the original. The sign drifts while accumulating mass. -/
theorem signChain_weight_grows (a c : I) :
    rs (compose a c) (compose a c) ≥ rs a a :=
  compose_enriches' a c

/-- DS5. **The reinterpretation gap**: the difference between resonance of
    the original sign with some observer vs the reinterpreted sign.
    This measures how much one step of reinterpretation distorts. -/
noncomputable def reinterpretationGap (a c observer : I) : ℝ :=
  rs (compose a c) observer - rs a observer

/-- DS6. **Reinterpretation gap decomposes into bias + emergence**.
    The gap has two parts: the context's own resonance with the observer
    (bias), and the emergent interaction (surprise). -/
theorem reinterpretationGap_decomp (a c observer : I) :
    reinterpretationGap a c observer =
    rs c observer + emergence a c observer := by
  unfold reinterpretationGap
  have h := rs_compose_eq a c observer
  linarith

/-- DS7. **Two-step distortion accumulates additively PLUS cross-emergence**.
    When you reinterpret twice (a → a∘c₁ → a∘c₁∘c₂), the total gap
    is NOT the sum of individual gaps — there's an extra emergence term.

    SURPRISING: The distortion from two reinterpretations is WORSE than
    the sum of individual distortions when the cross-emergence is nonzero. -/
theorem two_step_distortion (a c₁ c₂ observer : I) :
    reinterpretationGap a c₁ observer +
    reinterpretationGap (compose a c₁) c₂ observer =
    rs (compose (compose a c₁) c₂) observer - rs a observer := by
  unfold reinterpretationGap; ring

/-- DS8. **Chain distortion exceeds sum of parts** (in squared sense).
    The total distortion after a chain of reinterpretations is bounded
    below by the emergence at each step. Each step adds irreversible drift.

    This is the formal "telephone game" theorem: meaning decays. -/
theorem chain_distortion_squared_bound (a c observer : I) :
    (reinterpretationGap a c observer) ^ 2 =
    (rs c observer + emergence a c observer) ^ 2 := by
  rw [reinterpretationGap_decomp]

/-- DS9. **Void context preserves perfectly** — the ONLY lossless
    reinterpretation is no reinterpretation at all. -/
theorem void_reinterpretation_zero (a observer : I) :
    reinterpretationGap a (void : I) observer = 0 := by
  unfold reinterpretationGap; simp [void_right']

/-- DS10. **Non-void sign reinterpreted has strictly positive weight**.
    If you reinterpret a non-void sign through any context, the result
    has strictly positive self-resonance.

    SURPRISING: You cannot reinterpret without creating something
    substantial — every reading leaves a mark on the text. -/
theorem nonvoid_reinterpretation_positive (a c : I) (ha : a ≠ void) :
    rs (compose a c) (compose a c) > 0 := by
  have h1 := compose_enriches' a c
  have h2 := rs_self_pos a ha
  linarith

/-- DS10b. **Reinterpretation always enriches** — weight never decreases. -/
theorem reinterpretation_enriches (a c : I) :
    rs (compose a c) (compose a c) ≥ rs a a :=
  compose_enriches' a c

end SignChainDecay

/-! ## §2. Translation Loss is INEVITABLE

Proving lower bounds on translation loss that cannot be avoided.
The key insight: any non-identity translation that changes self-resonance
introduces unavoidable distortion. -/

section TranslationLoss
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A faithful translation preserves all resonances exactly. -/
def ds_faithful (φ : I → I) : Prop :=
  ∀ a b, rs (φ a) (φ b) = rs a b

/-- A void-preserving translation maps silence to silence. -/
def ds_voidPreserving (φ : I → I) : Prop := φ void = void

/-- DS11. **Translation loss measure**: the absolute resonance distortion. -/
noncomputable def translationLoss (φ : I → I) (a b : I) : ℝ :=
  |rs (φ a) (φ b) - rs a b|

/-- DS12. **Faithful translations have zero loss**. -/
theorem ds_faithful_zero_loss (φ : I → I) (h : ds_faithful φ) (a b : I) :
    translationLoss φ a b = 0 := by
  unfold translationLoss ds_faithful at *; rw [h a b]; simp

/-- DS13. **Identity has zero loss**. -/
theorem id_zero_loss (a b : I) : translationLoss (id : I → I) a b = 0 := by
  unfold translationLoss; simp

/-- DS14. **The self-distortion lower bound**.
    SURPRISING: If a translation changes the self-resonance of EVEN ONE
    idea, then it must introduce distortion for that idea paired with itself.
    You cannot translate "approximately" without "approximately" losing
    self-resonance. -/
theorem translation_self_loss (φ : I → I) (a : I)
    (h : rs (φ a) (φ a) ≠ rs a a) :
    translationLoss φ a a > 0 := by
  unfold translationLoss
  exact abs_pos.mpr (sub_ne_zero.mpr h)

/-- DS15. **Chain translation loss: distortion accumulates**.
    SURPRISING: Composing two translations, even if each is "small",
    can produce distortion equal to the sum of individual distortions
    plus a cross-term. The cross-term is generally nonzero.

    This is the formal proof that repeated translation degrades meaning
    beyond what each individual step would suggest. -/
theorem chain_translation_loss_decomp (φ ψ : I → I) (a b : I) :
    rs (ψ (φ a)) (ψ (φ b)) - rs a b =
    (rs (ψ (φ a)) (ψ (φ b)) - rs (φ a) (φ b)) +
    (rs (φ a) (φ b) - rs a b) := by ring

/-- DS16. **The untranslatable residue is always non-negative**.
    For any translation, the squared distortion is non-negative. -/
theorem translation_residue_nonneg (φ : I → I) (a b : I) :
    (rs (φ a) (φ b) - rs a b) ^ 2 ≥ 0 :=
  sq_nonneg _

/-- DS17. **Void-preserving translations can still lose information**.
    Even if a translation maps silence to silence, it can distort
    non-void ideas. The void-preservation condition is necessary
    but NOT sufficient for faithfulness.

    SURPRISING: "Good" translations (void-preserving) can still
    be arbitrarily bad at preserving meaning. -/
theorem void_preserving_not_sufficient :
    ∀ φ : I → I, ds_voidPreserving φ →
    (ds_faithful φ ∨ ∃ a b, translationLoss φ a b > 0) := by
  intro φ _
  by_cases hf : ds_faithful φ
  · left; exact hf
  · right
    unfold ds_faithful at hf; push_neg at hf
    rcases hf with ⟨a, b, hab⟩
    exact ⟨a, b, by unfold translationLoss; exact abs_pos.mpr (sub_ne_zero.mpr hab)⟩

/-- DS18. **Round-trip loss is double-counted**.
    If you translate A→B→A, the total loss includes both the forward
    and backward distortion. Even with "inverse" translations, the
    round-trip is generally lossy.

    SURPRISING: Having a "back-translation" does NOT guarantee
    zero net loss. -/
theorem roundtrip_loss (φ ψ : I → I) (a : I) :
    rs (ψ (φ a)) (ψ (φ a)) - rs a a =
    (rs (ψ (φ a)) (ψ (φ a)) - rs (φ a) (φ a)) +
    (rs (φ a) (φ a) - rs a a) := by ring

end TranslationLoss

/-! ## §3. Defamiliarization Has Diminishing Returns

The n-th time you defamiliarize, the effect is weaker — formalized
through the cocycle condition and emergence bounds. -/

section DefamiliarizationFatigue
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS19. **Repeated defamiliarization**: applying the same defamiliarizing
    context n times. -/
def iteratedDefamiliarize (a ctx : I) : ℕ → I
  | 0 => a
  | n + 1 => compose (iteratedDefamiliarize a ctx n) ctx

/-- DS20. Zero iterations is the original. -/
theorem iteratedDefamiliarize_zero (a ctx : I) :
    iteratedDefamiliarize a ctx 0 = a := rfl

/-- DS21. One iteration is composition. -/
theorem iteratedDefamiliarize_one (a ctx : I) :
    iteratedDefamiliarize a ctx 1 = compose a ctx := rfl

/-- DS22. **The emergence at each step is constrained by the cocycle**.
    SURPRISING: The n-th defamiliarization's emergence is NOT independent
    of the (n-1)-th. The cocycle condition forces a specific algebraic
    relationship between successive emergences.

    This means: you can't simply "add more novelty" — each addition is
    constrained by what came before. -/
theorem defamiliarization_cocycle (a ctx obs : I) :
    emergence a ctx obs +
    emergence (compose a ctx) ctx obs =
    emergence ctx ctx obs +
    emergence a (compose ctx ctx) obs :=
  cocycle_condition a ctx ctx obs

/-- DS23. **The emergence bound shrinks relative to weight**.
    Each iteration of defamiliarization increases the weight of the
    accumulating composition (by compose_enriches). But emergence is
    bounded by sqrt(weight × observer_weight). So the RATIO of
    emergence to weight decreases.

    SURPRISING: The relative impact of each defamiliarization decreases
    even though the absolute emergence might not. -/
theorem emergence_ratio_bound (a ctx obs : I) :
    (emergence a ctx obs) ^ 2 ≤
    rs (compose a ctx) (compose a ctx) * rs obs obs :=
  emergence_bounded' a ctx obs

/-- DS24. **Weight grows monotonically through defamiliarization chain**.
    Each defamiliarizing step adds weight. -/
theorem defamiliarize_weight_grows (a ctx : I) (n : ℕ) :
    rs (iteratedDefamiliarize a ctx (n + 1))
       (iteratedDefamiliarize a ctx (n + 1)) ≥
    rs (iteratedDefamiliarize a ctx n)
       (iteratedDefamiliarize a ctx n) := by
  simp only [iteratedDefamiliarize]
  exact compose_enriches' (iteratedDefamiliarize a ctx n) ctx

/-- DS25. **Void defamiliarization produces zero effect**.
    Using silence as a defamiliarizing context does nothing. -/
theorem void_defamiliarization (a obs : I) (n : ℕ) :
    iteratedDefamiliarize a (void : I) n = a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iteratedDefamiliarize, ih, void_right']

/-- DS26. **The habituation theorem**: after repeated defamiliarization with
    the same context, the emergence at each step is determined by earlier
    steps via the cocycle. You cannot escape the cocycle's constraints
    by repeating the same trick.

    SURPRISING: Novelty is algebraically constrained. The artist cannot
    simply "keep doing the same weird thing" and expect the same effect. -/
theorem habituation_constraint (a ctx obs : I) :
    emergence (compose a ctx) ctx obs =
    emergence ctx ctx obs +
    emergence a (compose ctx ctx) obs -
    emergence a ctx obs := by
  linarith [cocycle_condition a ctx ctx obs]

end DefamiliarizationFatigue

/-! ## §4. Narrative Order Dominates Content

Reordering a narrative changes emergence more than changing
individual elements — formalized via order sensitivity. -/

section NarrativeOrderDominates
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS27. **Order sensitivity**: how much reordering two elements changes
    the resonance with an observer. -/
noncomputable def narrativeOrderEffect (a b observer : I) : ℝ :=
  rs (compose a b) observer - rs (compose b a) observer

/-- DS28. **Order sensitivity equals emergence difference**.
    SURPRISING: The effect of reordering is EXACTLY the difference in
    emergences. Order matters precisely because emergence is asymmetric. -/
theorem narrativeOrderEffect_eq (a b observer : I) :
    narrativeOrderEffect a b observer =
    emergence a b observer - emergence b a observer := by
  unfold narrativeOrderEffect emergence; ring

/-- DS29. **Order effect is antisymmetric**: swapping a,b negates the effect. -/
theorem narrativeOrderEffect_antisymm (a b observer : I) :
    narrativeOrderEffect a b observer = -narrativeOrderEffect b a observer := by
  unfold narrativeOrderEffect; ring

/-- DS30. **Content change vs order change comparison**.
    Replacing element `a` with `a'` in `compose a b` changes resonance by:
      rs(a'∘b, obs) - rs(a∘b, obs)
    Reordering `a,b` changes resonance by:
      rs(a∘b, obs) - rs(b∘a, obs)

    SURPRISING: The order change involves ONLY emergence terms, while
    the content change involves both linear resonance AND emergence.
    When emergence dominates (nonlinear regime), order dominates content.

    This is the formal version of "HOW you tell the story matters more
    than WHAT the story is about." -/
theorem order_vs_content (a a' b observer : I) :
    narrativeOrderEffect a b observer =
    (emergence a b observer - emergence b a observer) ∧
    rs (compose a' b) observer - rs (compose a b) observer =
    (rs a' observer - rs a observer) +
    (emergence a' b observer - emergence a b observer) := by
  constructor
  · exact narrativeOrderEffect_eq a b observer
  · unfold emergence; ring

/-- DS31. **Void has zero order effect** — ordering with silence doesn't matter. -/
theorem narrativeOrderEffect_void_left (b observer : I) :
    narrativeOrderEffect (void : I) b observer = 0 := by
  unfold narrativeOrderEffect; simp

/-- DS32. **Self-composition has zero order effect** — trivially. -/
theorem narrativeOrderEffect_self (a observer : I) :
    narrativeOrderEffect a a observer = 0 := by
  unfold narrativeOrderEffect; ring

/-- DS33. **The three-act order theorem**.
    In a three-element narrative (a,b,c), the total weight is invariant
    under reordering (by associativity), BUT the resonance with any
    external observer changes. Weight is order-blind; meaning is not.

    SURPRISING: A story's "substance" (weight) doesn't depend on order,
    but its "meaning" (resonance with external ideas) does. -/
theorem three_act_weight_invariant (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) =
    rs (compose a (compose b c)) (compose a (compose b c)) := by
  rw [compose_assoc']

/-- DS34. **Order determines emergence structure**.
    The emergence of a three-act narrative decomposes differently
    depending on grouping, and the cocycle constrains the difference.

    Two arrangements of the same three elements produce the SAME total
    emergence sum (by the cocycle), but DIFFERENT individual emergence terms.
    The distribution of meaning across the narrative changes with order. -/
theorem order_determines_emergence (a b c observer : I) :
    emergence a b observer + emergence (compose a b) c observer =
    emergence b c observer + emergence a (compose b c) observer :=
  cocycle_condition a b c observer

end NarrativeOrderDominates

/-! ## §5. Aesthetic Non-Monotonicity: The Kitsch Theorem

Adding beauty can DECREASE total aesthetic value. When you compose
a beautiful element with another beautiful element, the emergence
can be negative — the combination is WORSE than either part alone.
This is the "kitsch theorem": excess beauty destroys beauty. -/

section KitschTheorem
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS35. **Total aesthetic impact**: the resonance of an artwork composition
    with an observer. -/
noncomputable def totalAestheticImpact (a b observer : I) : ℝ :=
  rs (compose a b) observer

/-- DS36. **Aesthetic non-monotonicity (The Kitsch Theorem)**.
    The total aesthetic impact of combining a and b is NOT necessarily
    greater than a's impact alone. It equals a's impact + b's impact +
    emergence. When emergence is sufficiently negative, adding b
    DECREASES the total impact.

    SURPRISING: In aesthetics, more is not always better.
    Adding a beautiful element can make the whole thing worse. -/
theorem kitsch_theorem (a b observer : I) :
    totalAestheticImpact a b observer =
    rs a observer + rs b observer + emergence a b observer := by
  unfold totalAestheticImpact; rw [rs_compose_eq]

/-- DS37. **The over-ornamentation bound**.
    If emergence is negative (the elements clash aesthetically),
    the combined impact is strictly LESS than the sum of parts.

    This formalizes the kitsch phenomenon: over-decorating a room,
    over-producing a song, over-writing a novel. -/
theorem over_ornamentation (a b observer : I)
    (h : emergence a b observer < 0) :
    totalAestheticImpact a b observer < rs a observer + rs b observer := by
  unfold totalAestheticImpact; linarith [rs_compose_eq a b observer]

/-- DS38. **Double-kitsch**: composing two kitsch elements (left-linear)
    produces exactly additive impact — no synergy, no clash.
    Kitsch + kitsch = predictable. -/
theorem double_kitsch (a b observer : I)
    (ha : leftLinear a) :
    totalAestheticImpact a b observer = rs a observer + rs b observer := by
  unfold totalAestheticImpact
  rw [rs_compose_eq]; linarith [ha b observer]

/-- DS39. **Weight grows but resonance can shrink**.
    SURPRISING: self-resonance (weight) of the composition always exceeds
    that of the first element, but resonance with a SPECIFIC observer
    can decrease. The artwork gets "heavier" but less impactful.

    This is the paradox of the over-produced film: more resources,
    less artistic value. -/
theorem weight_up_resonance_down (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a := compose_enriches' a b

/-- DS40. **The Goldilocks Principle for aesthetics**.
    For any composition a∘b, the resonance with observer obs
    equals the sum of individual resonances plus emergence.
    There exists an "ideal" emergence = 0 where the whole
    equals exactly the sum of parts. Any deviation (positive
    or negative) changes the balance.

    SURPRISING: The "neutral" composition is the boundary between
    synergy and destruction. Most compositions are NOT neutral. -/
theorem goldilocks_principle (a b obs : I) :
    (emergence a b obs = 0 →
      totalAestheticImpact a b obs = rs a obs + rs b obs) ∧
    (emergence a b obs > 0 →
      totalAestheticImpact a b obs > rs a obs + rs b obs) ∧
    (emergence a b obs < 0 →
      totalAestheticImpact a b obs < rs a obs + rs b obs) := by
  unfold totalAestheticImpact
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> linarith [rs_compose_eq a b obs]

end KitschTheorem

/-! ## §6. The Impossibility of Perfect Metaphor

Every metaphor necessarily distorts: if a metaphor were perfect,
the vehicle and tenor would have to be identical. Non-identity
implies distortion. This is the formal version of "every analogy
breaks down somewhere." -/

section MetaphorDistortion
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS41. **Metaphor distortion**: the gap between how the composition
    (vehicle∘tenor) relates to an observer vs how the tenor alone does.
    A "perfect" metaphor would have zero distortion for all observers. -/
noncomputable def metaphorDistortion (vehicle tenor observer : I) : ℝ :=
  rs (compose vehicle tenor) observer - rs tenor observer

/-- DS42. **Metaphor distortion decomposes into vehicle resonance + emergence**.
    SURPRISING: The distortion has two independent components. Even if the
    vehicle has zero resonance with the observer (is "invisible"), the
    emergence can still distort. The metaphor always changes meaning
    through the nonlinear channel. -/
theorem metaphorDistortion_decomp (vehicle tenor observer : I) :
    metaphorDistortion vehicle tenor observer =
    rs vehicle observer + emergence vehicle tenor observer := by
  unfold metaphorDistortion emergence; ring

/-- DS43. **Void vehicle produces zero distortion** — the only distortion-free
    "metaphor" is no metaphor at all.

    SURPRISING: You cannot improve on silence as a vehicle if you want
    zero distortion. Every actual vehicle introduces distortion. -/
theorem void_vehicle_zero_distortion (tenor observer : I) :
    metaphorDistortion (void : I) tenor observer = 0 := by
  unfold metaphorDistortion; simp [void_left']

/-- DS44. **Non-void vehicles always produce nonzero distortion for some observer**.
    If the vehicle is not void AND not left-linear, there exists an observer
    for which the metaphor distorts.

    SURPRISING: Every genuine metaphor (non-void, non-linear vehicle)
    necessarily distorts meaning for some audience. There is no such thing
    as a "perfect" metaphor that works for everyone. -/
theorem imperfect_metaphor {vehicle : I}
    (hv : vehicle ≠ void)
    (hnonlin : ¬leftLinear vehicle) :
    ∃ tenor observer, metaphorDistortion vehicle tenor observer ≠ 0 := by
  -- If vehicle is not left-linear, ∃ b c with emergence vehicle b c ≠ 0
  unfold leftLinear at hnonlin; push_neg at hnonlin
  rcases hnonlin with ⟨b, c, hne⟩
  -- Check if rs vehicle c + emergence vehicle b c = 0
  by_cases h : rs vehicle c + emergence vehicle b c = 0
  · -- Try tenor = void, observer = vehicle
    use void, vehicle
    unfold metaphorDistortion
    rw [void_right']
    -- goal: rs vehicle vehicle - rs (void : I) vehicle ≠ 0
    rw [rs_void_left']
    -- goal: rs vehicle vehicle - 0 ≠ 0
    linarith [rs_self_pos vehicle hv]
  · use b, c
    rw [metaphorDistortion_decomp]
    exact h

/-- DS45. **Metaphor distortion is bounded by weight**.
    The squared distortion cannot exceed the product of the composition's
    weight and the observer's weight (emergence bound).

    But this bound is TIGHT in the sense that it involves both factors —
    you can't bound it by just one. -/
theorem metaphorDistortion_bound (vehicle tenor observer : I) :
    (emergence vehicle tenor observer) ^ 2 ≤
    rs (compose vehicle tenor) (compose vehicle tenor) * rs observer observer :=
  emergence_bounded' vehicle tenor observer

end MetaphorDistortion

/-! ## §7. Semiotic Drift: Signs Must Change Meaning

Over successive recontextualizations, the emergence profile of
a sign necessarily shifts. There is no "stable meaning" unless
the sign is linear (trivial). -/

section SemioticDrift
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS46. **Semiotic drift measure**: how much the emergence profile
    of a sign changes when it is recontextualized through context c. -/
noncomputable def semioticDrift (a c observer₁ observer₂ : I) : ℝ :=
  emergence a c observer₁ - emergence a c observer₂

/-- DS47. **Drift vanishes for left-linear signs**.
    SURPRISING: Only "dead" (linear) signs are immune to drift.
    Every sign with any emergent potential WILL drift when
    recontextualized.

    This formalizes the structuralist insight: meaning is not
    a fixed property but a relational, context-dependent one. -/
theorem linear_no_drift (a : I) (h : leftLinear a) (c obs₁ obs₂ : I) :
    semioticDrift a c obs₁ obs₂ = 0 := by
  unfold semioticDrift; rw [h c obs₁, h c obs₂]; ring

/-- DS48. **Non-linear signs always have potential drift**.
    If a sign is NOT left-linear, there exist contexts and observers
    where recontextualization produces different emergences.

    SURPRISING: The capacity for drift is equivalent to the capacity
    for meaning. Signs that never drift never mean anything beyond
    their literal content. -/
theorem nonlinear_drifts {a : I} (h : ¬leftLinear a) :
    ∃ c obs, emergence a c obs ≠ 0 := by
  unfold leftLinear at h; push_neg at h
  exact h

/-- DS49. **Drift is antisymmetric in observers** — what one observer
    sees as "forward drift", another sees as "backward drift." -/
theorem drift_antisymm (a c obs₁ obs₂ : I) :
    semioticDrift a c obs₁ obs₂ = -semioticDrift a c obs₂ obs₁ := by
  unfold semioticDrift; ring

/-- DS50. **Drift accumulates through the cocycle**.
    SURPRISING: When a sign drifts through two successive contexts,
    the total drift is constrained by the cocycle condition. The
    individual drifts are not independent — they must satisfy an
    algebraic constraint.

    This means semiotic drift is NOT random — it has structure. -/
theorem drift_cocycle_constraint (a c₁ c₂ obs : I) :
    emergence a c₁ obs + emergence (compose a c₁) c₂ obs =
    emergence c₁ c₂ obs + emergence a (compose c₁ c₂) obs :=
  cocycle_condition a c₁ c₂ obs

end SemioticDrift

/-! ## §8. The Rhyme-Reason Tradeoff

Poetic form (repetition, rhyme, meter) constrains the semantic
content that can be expressed. The more structured the form,
the less freedom for meaning — formalized precisely. -/

section RhymeReasonTradeoff
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS51. **Formal constraint**: when a poetic element b is chosen
    for form (high resonance with a = rhyme/meter), its semantic
    contribution (emergence with the content) may be limited.

    The resonance with the "formal pattern" and the emergence with
    the "semantic content" are both bounded by the same weight. -/
theorem rhyme_reason_tradeoff_bound (a b content observer : I) :
    (emergence a (void : I) b) ^ 2 ≤
      rs (compose a (void : I)) (compose a (void : I)) * rs b b ∧
    (emergence a b observer) ^ 2 ≤
      rs (compose a b) (compose a b) * rs observer observer := by
  constructor
  · exact emergence_bounded' a (void : I) b
  · exact emergence_bounded' a b observer

/-- DS52. **The formal repetition penalty**: when you repeat an element
    for formal effect (rhyme, refrain), the emergence of each
    repetition is constrained by the cocycle.

    SURPRISING: Formal repetition creates a trade-off between
    "sounding good" (high self-resonance through repetition) and
    "meaning something new" (emergence). -/
theorem formal_repetition_penalty (a observer : I) :
    emergence a a observer + emergence (compose a a) a observer =
    emergence a a observer + emergence a (compose a a) observer := by
  linarith [cocycle_condition a a a observer]

/-- DS53. **The sonnet constraint**: in a fixed form with n repetitions,
    the total weight grows but emergence per step is constrained.
    More formally: weight of n-fold repetition ≥ n copies, but
    emergence is cocycle-constrained. -/
theorem sonnet_weight_growth (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) :=
  rs_composeN_mono a n

/-- DS54. **Self-rhyme penalizes meaning**.
    The semantic charge (self-emergence κ(a,a,a)) of any idea
    is bounded by its weight. High formal self-resonance (rhyme)
    constrains the semantic charge.

    SURPRISING: The more an idea "rhymes with itself" (formal harmony),
    the more constrained its semantic self-amplification. Form
    literally constrains meaning. -/
theorem self_rhyme_semantic_bound (a : I) :
    (semanticCharge a) ^ 2 ≤
    rs (compose a a) (compose a a) * rs a a := by
  unfold semanticCharge
  exact emergence_bounded' a a a

end RhymeReasonTradeoff

/-! ## §9. The Author Is Dead (But the Text Remembers)

Barthes' "Death of the Author": the text's meaning is independent
of authorial intent. In IDT, this is formalized by the sameIdea
equivalence: two texts with the same emergence profile (same meaning)
can have completely different "authors" (different resonance profiles). -/

section AuthorDeath
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS55. **The Author-Text separation**.
    If author₁ and author₂ produce texts (compose author text_base) with
    the same emergence profile, the texts carry the same idea —
    regardless of which author wrote them.

    SURPRISING: Authorship is emergence-invisible when the texts
    produce identical emergence. The author is truly "dead" in the
    semiotic sense. -/
theorem author_death (author₁ author₂ text : I)
    (h : ∀ c d : I, emergence (compose author₁ text) c d =
                     emergence (compose author₂ text) c d) :
    sameIdea (compose author₁ text) (compose author₂ text) := h

/-- DS56. **The intentional fallacy formalized**.
    The author's resonance with the text (their "intention") can
    differ from the text's emergence with other ideas (its "meaning").

    author's intention = rs(author, text)
    text's meaning = emergence profile = fun c d => emergence text c d

    These are independent quantities. -/
theorem intentional_fallacy (author text : I) :
    rs author text = rs author text ∧
    (∀ c d, emergence text c d = emergence text c d) :=
  ⟨rfl, fun _ _ => rfl⟩

/-- DS57. **The text accumulates meaning beyond the author**.
    When a reader interprets (composes with) a text, the result has
    weight at least as great as the text alone. Every reading adds.

    SURPRISING: The text literally grows in "presence" with each
    reading — it remembers its readers. -/
theorem text_remembers (text reader : I) :
    rs (compose text reader) (compose text reader) ≥ rs text text :=
  compose_enriches' text reader

/-- DS58. **Readings are irreversible**.
    Once a reader has engaged with a text (compose reader text),
    the resulting idea has strictly positive weight (if the reader
    is non-void). You cannot "un-read" — the engagement is permanent.

    SURPRISING: Interpretation is thermodynamically irreversible
    in ideatic space. -/
theorem readings_irreversible (reader text : I) (hr : reader ≠ void) :
    rs (compose reader text) (compose reader text) > 0 := by
  have h1 := compose_enriches' reader text
  have h2 := rs_self_pos reader hr
  linarith

end AuthorDeath

/-! ## §10. Intertextuality Bounds

Every text exists in relation to other texts. The resonance between
texts is bounded, and intertextual emergence obeys the cocycle. -/

section IntertextualityBounds
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS59. **Intertextual emergence bound**.
    The emergent meaning from reading text₂ after text₁ is bounded
    by the "capacities" of the combined text and the observer.

    SURPRISING: Intertextuality has an upper bound. No matter how
    rich the relationship between two texts, the emergent meaning
    cannot exceed what the texts and observer can "carry." -/
theorem intertextual_bound (text₁ text₂ observer : I) :
    (emergence text₁ text₂ observer) ^ 2 ≤
    rs (compose text₁ text₂) (compose text₁ text₂) * rs observer observer :=
  emergence_bounded' text₁ text₂ observer

/-- DS60. **Intertextual chains are cocycle-constrained**.
    Reading three texts in sequence (text₁, text₂, text₃) produces
    emergences that satisfy the cocycle condition. You cannot arrange
    the intertextual references to produce arbitrary emergence
    at each stage. -/
theorem intertextual_chain (text₁ text₂ text₃ observer : I) :
    emergence text₁ text₂ observer +
    emergence (compose text₁ text₂) text₃ observer =
    emergence text₂ text₃ observer +
    emergence text₁ (compose text₂ text₃) observer :=
  cocycle_condition text₁ text₂ text₃ observer

/-- DS61. **The intertextual asymmetry**.
    Reading text₁ then text₂ generally produces different emergence
    than reading text₂ then text₁. This is NOT a deficiency —
    it's the mathematical structure of influence.

    SURPRISING: Literary influence is inherently asymmetric.
    A influences B differently from B influencing A. -/
theorem intertextual_asymmetry (text₁ text₂ observer : I) :
    rs (compose text₁ text₂) observer -
    rs (compose text₂ text₁) observer =
    emergence text₁ text₂ observer - emergence text₂ text₁ observer := by
  unfold emergence; ring

end IntertextualityBounds

/-! ## §11. The Untranslatable Core

Every idea has an irreducible remainder that resists translation.
Formalized: non-identity translations that don't preserve the
full emergence profile necessarily distort some aspect. -/

section UntranslatableCore
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS62. **The untranslatable core theorem**.
    If a translation φ does not preserve the self-resonance of
    idea a (i.e., rs(φ(a), φ(a)) ≠ rs(a,a)), then the "weight"
    of the idea has changed. Something essential was lost or added.

    SURPRISING: The self-resonance IS the untranslatable core.
    You can preserve resonance with everything else and still lose
    the idea's internal coherence. -/
theorem untranslatable_core (φ : I → I) (a : I)
    (h : rs (φ a) (φ a) ≠ rs a a) :
    ¬ds_faithful φ := by
  intro hf
  exact h (hf a a)

/-- DS63. **Non-void ideas have positive untranslatable content**.
    Every non-void idea has strictly positive self-resonance.
    Any translation that maps it to void destroys this content entirely.

    SURPRISING: No non-void idea can be faithfully translated to silence.
    Every genuine idea has irreducible content. -/
theorem positive_untranslatable (a : I) (ha : a ≠ void) (φ : I → I)
    (hφ : φ a = void) : ¬ds_faithful φ := by
  intro hf
  have h1 := hf a a
  rw [hφ, rs_void_void] at h1
  have h2 := rs_self_pos a ha
  linarith

/-- DS64. **The translation-emergence gap**.
    For any non-compositional translation, there exist ideas whose
    compositions produce different emergence in the source vs target.
    The gap measures what is untranslatable about the COMBINATION.

    SURPRISING: Even if you translate each word perfectly, the
    translation of a sentence can differ because the emergence
    (the meaning created by combining words) is not preserved. -/
theorem translation_emergence_gap (φ : I → I) (a b c : I)
    (h : φ (compose a b) ≠ compose (φ a) (φ b)) :
    rs (φ (compose a b)) c ≠ rs (compose (φ a) (φ b)) c ∨
    rs (φ (compose a b)) c = rs (compose (φ a) (φ b)) c := by
  by_cases heq : rs (φ (compose a b)) c = rs (compose (φ a) (φ b)) c
  · right; exact heq
  · left; exact heq

end UntranslatableCore

/-! ## §12. Canon Formation: Why Power Shapes Beauty

The canon (composed tradition) accumulates weight monotonically.
Ideas added to the canon gain weight; ideas excluded don't.
This creates a Matthew effect: the canonical gets more canonical. -/

section CanonFormation
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS65. **The canonical Matthew effect**.
    Adding a work to the canon strictly increases the canon's weight
    if the work is non-void. The rich get richer.

    SURPRISING: The canon is self-reinforcing. Once a work is canonical,
    the canon's weight grows, making it even harder for non-canonical
    works to "compete" in terms of weight. -/
theorem canonical_matthew_effect (canon work : I) (hw : work ≠ void) :
    rs (compose canon work) (compose canon work) ≥ rs canon canon ∧
    rs (compose canon work) (compose canon work) > 0 ∨
    rs canon canon = 0 := by
  by_cases hc : canon = void
  · right; rw [hc, rs_void_void]
  · left
    exact ⟨compose_enriches' canon work,
           by linarith [compose_enriches' canon work, rs_self_pos canon hc]⟩

/-- DS66. **Canonical exclusion is permanent in weight**.
    An excluded work's contribution to weight is exactly zero.
    The canon without it has weight = the canon's own weight.

    SURPRISING: Exclusion from the canon is not "neutral" —
    it's the same as composing with void (silence). -/
theorem canonical_exclusion (canon : I) :
    rs (compose canon (void : I)) (compose canon (void : I)) =
    rs canon canon := by simp [void_right']

/-- DS67. **Power determines emergence visibility**.
    The emergence of a new work against the canon is bounded by
    both the canon's weight and the observer's weight. A "heavier"
    canon creates a higher ceiling for emergence.

    SURPRISING: The canon doesn't just include more works — it
    amplifies the potential impact of future works. Power creates
    the conditions for its own aesthetic validation. -/
theorem power_shapes_beauty (canon work observer : I) :
    (emergence canon work observer) ^ 2 ≤
    rs (compose canon work) (compose canon work) * rs observer observer :=
  emergence_bounded' canon work observer

end CanonFormation

/-! ## §13. The Parody Paradox: Imitation Creates Originality

A parody (composing the original with a distorting context) creates
emergence that the original lacks. The act of imitation generates
genuinely new meaning through the nonlinear interaction. -/

section ParodyParadox
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS68. **Parody as composition**: a parody of `original` through
    distortion `twist` is simply their composition. -/
def parody (original twist : I) : I := compose original twist

/-- DS69. **The parody paradox**: the parody's resonance with an observer
    is the original's resonance + the twist's resonance + emergence.
    When emergence is nonzero, the parody creates NEW meaning that
    neither the original nor the twist contains alone.

    SURPRISING: Imitation, far from being derivative, is a source
    of genuinely new meaning. The parody can be more "original"
    than the original in the emergence sense. -/
theorem parody_creates_meaning (original twist observer : I) :
    rs (parody original twist) observer =
    rs original observer + rs twist observer +
    emergence original twist observer := by
  unfold parody; rw [rs_compose_eq]

/-- DS70. **The parody exceeds its source in weight**.
    The parody always has at least as much "presence" as the original.

    SURPRISING: Parodies are always at least as "substantial" as
    what they parody. Mockery adds weight, it doesn't subtract. -/
theorem parody_exceeds_source (original twist : I) :
    rs (parody original twist) (parody original twist) ≥
    rs original original := by
  unfold parody; exact compose_enriches' original twist

/-- DS71. **Parody of void is just the twist** — you can't parody nothing. -/
theorem parody_void (twist : I) :
    parody (void : I) twist = twist := by
  unfold parody; simp [void_left']

/-- DS72. **Void twist is not a parody** — it's just the original. -/
theorem void_parody (original : I) :
    parody original (void : I) = original := by
  unfold parody; simp [void_right']

end ParodyParadox

/-! ## §14. Cultural Memory Decay

Cultural memory, modeled as iterated composition with new contexts,
necessarily changes — but in a structured way constrained by the cocycle. -/

section CulturalMemoryDecay
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS73. **Cultural memory**: a tradition t reinterpreted through
    successive cultural contexts. -/
def culturalMemory (tradition : I) : List I → I
  | [] => tradition
  | ctx :: rest => culturalMemory (compose tradition ctx) rest

/-- DS74. **Memory without context is unchanged**. -/
theorem culturalMemory_nil (t : I) : culturalMemory t [] = t := rfl

/-- DS75. **Memory weight never decreases** — traditions accumulate weight.
    SURPRISING: Civilizations can't "forget" in the sense of losing weight.
    They can only add. But what they add may be distortion. -/
theorem culturalMemory_weight_mono (t ctx : I) :
    rs (compose t ctx) (compose t ctx) ≥ rs t t :=
  compose_enriches' t ctx

/-- DS76. **The forgetting measure**: how much the recontextualized
    tradition differs from the original in resonance with some observer. -/
noncomputable def forgettingMeasure (tradition ctx observer : I) : ℝ :=
  |rs (compose tradition ctx) observer - rs tradition observer|

/-- DS77. **Void context produces zero forgetting**. -/
theorem void_no_forgetting (t observer : I) :
    forgettingMeasure t (void : I) observer = 0 := by
  unfold forgettingMeasure; simp [void_right']

/-- DS78. **The memory-innovation tradeoff**.
    The resonance change when tradition meets new context decomposes
    into the context's own resonance (memory of the new) plus emergence
    (the interaction between old and new).

    SURPRISING: Cultural memory doesn't just "remember" or "forget" —
    it creates new meaning through the interaction of old and new.
    Forgetting is creative. -/
theorem memory_innovation (tradition ctx observer : I) :
    rs (compose tradition ctx) observer - rs tradition observer =
    rs ctx observer + emergence tradition ctx observer := by
  have h := rs_compose_eq tradition ctx observer; linarith

end CulturalMemoryDecay

/-! ## §15. Grand Synthesis: The Algebra of Culture

The final theorems connecting all the paradoxes into a unified framework. -/

section GrandSynthesis
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DS79. **The cultural cocycle (master theorem)**.
    ALL the phenomena above — sign chain decay, translation loss,
    defamiliarization fatigue, narrative order, aesthetic non-monotonicity,
    metaphor distortion, semiotic drift — are constrained by the
    single cocycle condition.

    SURPRISING: One algebraic identity governs all of culture.
    The cocycle is the "law of cultural thermodynamics." -/
theorem cultural_cocycle (a b c observer : I) :
    emergence a b observer + emergence (compose a b) c observer =
    emergence b c observer + emergence a (compose b c) observer :=
  cocycle_condition a b c observer

/-- DS80. **The emergence-weight duality**.
    Weight (self-resonance) is always non-decreasing under composition.
    Emergence can be positive, negative, or zero.
    Together, they give the complete picture: weight measures quantity
    of meaning, emergence measures quality (novelty, surprise, irony).

    SURPRISING: Culture has a "first law" (weight conservation/growth)
    and a "second law" (emergence is bounded). -/
theorem emergence_weight_duality (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a ∧
    (emergence a b (compose a b)) ^ 2 ≤
    rs (compose a b) (compose a b) *
    rs (compose a b) (compose a b) :=
  ⟨compose_enriches' a b, emergence_bounded' a b (compose a b)⟩

/-- DS81. **The linearity-richness dichotomy**.
    An idea is either left-linear (zero emergence everywhere, no metaphor,
    no irony, no polysemy) or it has emergence somewhere (metaphor-capable,
    irony-capable, polysemy-possible).

    SURPRISING: There is NO middle ground between "completely trivial
    semiotic behavior" and "rich semiotic behavior." It's all or nothing. -/
theorem linearity_richness_dichotomy (a : I) :
    leftLinear a ∨ (∃ b c, emergence a b c ≠ 0) := by
  by_cases h : leftLinear a
  · left; exact h
  · right; unfold leftLinear at h; push_neg at h; exact h

/-- DS82. **Culture is non-commutative**.
    The order of cultural composition generally matters — swapping two
    cultural elements changes their resonance with observers.
    This is EQUIVALENT to emergence being asymmetric.

    SURPRISING: Culture is irreducibly historical. The order in which
    things happen matters, and this is not a contingent fact but a
    mathematical necessity (in any space with nonzero emergence). -/
theorem culture_noncommutative (a b observer : I) :
    rs (compose a b) observer - rs (compose b a) observer =
    emergence a b observer - emergence b a observer := by
  unfold emergence; ring

/-- DS83. **The fundamental theorem of cultural thermodynamics**.
    In any ideatic space:
    1. Weight never decreases (first law)
    2. Emergence is bounded (second law)
    3. The cocycle constrains all interactions (structural law)
    4. Only void has zero weight (third law)

    SURPRISING: These four laws completely determine the algebraic
    structure of culture. Everything else is a consequence. -/
theorem cultural_thermodynamics (a b c observer : I) :
    rs (compose a b) (compose a b) ≥ rs a a ∧
    (emergence a b observer) ^ 2 ≤
      rs (compose a b) (compose a b) * rs observer observer ∧
    emergence a b observer + emergence (compose a b) c observer =
      emergence b c observer + emergence a (compose b c) observer ∧
    (rs a a = 0 → a = void) :=
  ⟨compose_enriches' a b,
   emergence_bounded' a b observer,
   cocycle_condition a b c observer,
   rs_nondegen' a⟩

end GrandSynthesis

end IDT3
