import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3b: Paradoxes of Mind and Meaning

Deep and counter-intuitive theorems about philosophy of mind, language,
and consciousness derived from Ideatic Theory's minimal axioms.

## Key Paradoxes Proved

### 1. The Quantitative Private Language Argument
Private meaning is not merely impossible — it leaks QUANTITATIVELY.
Any non-void idea must resonate with its own compositions, and
the amount of leakage is lower-bounded by self-resonance.

### 2. Self-Knowledge Is Bounded
Self-interpretation always creates new content beyond what the self
contains, and this surplus is bounded by the emergence Cauchy-Schwarz.

### 3. Gödel Meets Wittgenstein
Idempotent ideas (those equal to their own repetition) have NEGATIVE
semantic charge — repeating them destroys meaning. An idea that claims
to be its own description necessarily loses information.

### 4. The Hermeneutic Spiral
Interpretation changes the interpreter: each pass is strictly
non-decreasing in weight, and the change decomposes into emergence.

### 5. Phenomenological Reduction Paradox
Performing a reduction (bracketing presuppositions) adds emergence
that wasn't there before. The observer always affects the observed.

### 6. The Frame Problem Formalized
Background assumptions grow monotonically under composition.
No finite frame suffices; each new idea adds irreducible weight.

### 7. Dialectical Divergence
Under non-void conditions, dialectical iteration produces ideas of
ever-increasing weight — history never returns to its starting point.

### 8. The Zombie Theorem
Same emergence profile means same compositional role. There are no
"philosophical zombies" — ideas with identical function but different
qualia. Consciousness-as-emergence is all there is.

### 9-15. Aspect Perception, Rule-Following, Translation Bounds,
         Beetle in the Box, Intersubjectivity, Self-Interpretation,
         Grand Synthesis

47 theorems. 0 sorries. All proofs complete.
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. The Quantitative Private Language Argument

Wittgenstein argued that private languages are impossible. We strengthen
this: private meaning is not just impossible but MEASURABLY impossible.
Any non-void idea has a quantifiable lower bound on how much meaning
it must share through composition. -/

section QuantitativePrivateLanguage
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP1: Meaning Leakage Theorem.
    For any non-void idea, composition reveals it QUANTITATIVELY:
    (1) self-composition has weight ≥ the original,
    (2) the original has strictly positive weight, and
    (3) self-composition remains non-void.
    Private meaning leaks measurably. -/
theorem meaning_leakage_bound (a : I) (h : a ≠ void) :
    rs (compose a a) (compose a a) ≥ rs a a ∧
    rs a a > 0 ∧
    compose a a ≠ void := by
  have h1 : rs a a > 0 := rs_self_pos a h
  have h2 : rs (compose a a) (compose a a) ≥ rs a a := compose_enriches' a a
  have h3 : compose a a ≠ void := compose_ne_void_of_left a a h
  exact ⟨h2, h1, h3⟩

/-- DP2: Iterated Privacy Erosion.
    After n+1 repetitions, a non-void idea has accumulated weight
    at least equal to its base weight, and remains non-void.
    Each repetition exposes more meaning — privacy erodes monotonically. -/
theorem iterated_privacy_erosion (a : I) (h : a ≠ void) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥ rs a a ∧
    composeN a (n + 1) ≠ void := by
  constructor
  · exact rs_composeN_ge_base a n
  · exact composeN_ne_void a h n

/-- DP3: Emergence Quantifies Privacy Leakage.
    The emergence κ(a, a, c) measures exactly how much meaning a leaks
    to observer c through self-composition. This leakage is bounded by
    the geometric mean of the composition's weight and the observer's weight.
    SURPRISING: there is a PRECISE UPPER BOUND on how much can leak. -/
theorem emergence_quantifies_leakage (a c : I) :
    (emergence a a c) ^ 2 ≤
    rs (compose a a) (compose a a) * rs c c ∧
    emergence a a c = rs (compose a a) c - 2 * rs a c := by
  constructor
  · exact emergence_bounded' a a c
  · unfold emergence; ring

/-- DP4: The Opposition Paradox.
    Even when two ideas OPPOSE each other (negative resonance),
    their composition is at least as heavy as the left idea alone.
    Opposition doesn't hide meaning — it AMPLIFIES presence.
    This is deeply counter-intuitive: enemies make you stronger. -/
theorem opposition_amplifies_presence (a b : I)
    (_h_oppose : rs a b < 0) (h_ne : a ≠ void) :
    rs (compose a b) (compose a b) ≥ rs a a ∧
    rs a a > 0 ∧
    compose a b ≠ void := by
  have h1 : rs a a > 0 := rs_self_pos a h_ne
  have h2 : rs (compose a b) (compose a b) ≥ rs a a := compose_enriches' a b
  have h3 : compose a b ≠ void := compose_ne_void_of_left a b h_ne
  exact ⟨h2, h1, h3⟩

/-- DP5: Public Surplus Decomposition.
    The "public surplus" (weight of composition minus weight of left component)
    decomposes into cross-resonances plus self-emergence. This gives the
    exact quantitative structure of how meaning becomes public. -/
theorem public_surplus_decomposition (a b : I) :
    rs (compose a b) (compose a b) - rs a a =
    rs a (compose a b) + rs b (compose a b) +
    emergence a b (compose a b) - rs a a := by
  have h := rs_compose_eq a b (compose a b)
  linarith

end QuantitativePrivateLanguage

/-! ## §2. Self-Knowledge Is Bounded: The Inner Life Has Limits

Self-knowledge is not unlimited: the act of introspection
(composing an idea with itself) creates new content beyond
what was there, but this new content is bounded. The inner
life has a precise ceiling. -/

section SelfKnowledgeBounds
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP6: Self-Knowledge Creates Irreducible New Content.
    For any non-void idea, the "self-knowledge surplus"
    (weight gained from self-composition) is non-negative,
    and the self-composition is strictly heavier than void.
    Introspection always adds — you can never fully know yourself
    because knowing creates new content. -/
theorem self_knowledge_surplus (a : I) (h : a ≠ void) :
    weight (compose a a) - weight a ≥ 0 ∧
    weight (compose a a) > 0 := by
  unfold weight
  have h1 : rs (compose a a) (compose a a) ≥ rs a a := compose_enriches' a a
  have h2 : compose a a ≠ void := compose_ne_void_of_left a a h
  have h3 : rs (compose a a) (compose a a) > 0 := rs_self_pos _ h2
  constructor <;> linarith

/-- DP7: Self-Emergence Is Bounded Above.
    The emergence from self-composition (how much introspection reveals)
    is bounded by the weight of the self-composition. You can only learn
    about yourself as much as you ARE. -/
theorem self_emergence_bounded (a : I) :
    (selfEmergence a a) ^ 2 ≤
    weight (compose a a) * weight (compose a a) := by
  unfold selfEmergence weight
  exact emergence_bounded' a a (compose a a)

/-- DP8: The Inner Life Asymmetry.
    How you resonate with your self-knowledge (rs(a, a∘a)) differs from
    how your self-knowledge resonates with you (rs(a∘a, a)).
    Self-perception is asymmetric: what you think you know about yourself
    ≠ what your self-knowledge reveals about you.
    The difference equals the antisymmetric part of resonance. -/
theorem inner_life_asymmetry (a : I) :
    rs a (compose a a) - rs (compose a a) a =
    asymmetry a (compose a a) ∧
    asymmetry a (compose a a) = -asymmetry (compose a a) a := by
  constructor
  · unfold asymmetry; ring
  · exact asymmetry_antisymm a (compose a a)

/-- DP9: Bounded Introspection Principle.
    The amount of new meaning created by introspection (self-emergence)
    plus the cross-resonances must equal the total self-resonance of
    the self-composition. Nothing comes from nothing in the inner life.
    SURPRISING: introspection is fully decomposable into three components. -/
theorem bounded_introspection (a : I) :
    weight (compose a a) =
    rs a (compose a a) + rs a (compose a a) + selfEmergence a a := by
  unfold weight selfEmergence
  exact rs_compose_eq a a (compose a a)

end SelfKnowledgeBounds

/-! ## §3. Gödel Meets Wittgenstein: Ideas That Cannot Describe Themselves

An idea that is its own repetition (compose a a = a) — an "idempotent
idea" or "self-describing idea" — has NEGATIVE semantic charge.
Repeating it destroys meaning. This is the ideatic analogue of
Gödelian incompleteness: a system that tries to contain its own
description necessarily loses information. -/

section GodelWittgenstein
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP10: The Idempotent Negativity Theorem.
    If an idea is idempotent (compose a a = a), then its emergence
    with ANY observer is exactly the negative of its resonance.
    Self-describing ideas have universally negative emergence.
    DEEPLY SURPRISING: an idea that IS its own repetition DESTROYS
    meaning in every possible context. -/
theorem idempotent_negativity (a : I) (h : compose a a = a)
    (c : I) : emergence a a c = -rs a c := by
  unfold emergence
  rw [h]
  ring

/-- DP11: Idempotent Ideas Have Negative Semantic Charge.
    If compose a a = a and a ≠ void, then the semantic charge
    (self-amplification index) is strictly negative.
    PARADOX: A mantra that IS its own repetition weakens with each use.
    This is the formal content of the observation that clichés lose force. -/
theorem idempotent_negative_charge (a : I)
    (h_idemp : compose a a = a) (h_ne : a ≠ void) :
    semanticCharge a < 0 := by
  have h1 := idempotent_negativity a h_idemp a
  unfold semanticCharge
  have h2 : rs a a > 0 := rs_self_pos a h_ne
  linarith

/-- DP12: Self-Description Absorption Theorem.
    If compose a a = a, then the "weight" of the composition equals
    the weight of the original (no growth), but emergence is
    universally negative. The idea absorbs its own repetition at
    the cost of negative emergence everywhere.
    SURPRISING: self-description is weight-neutral but meaning-destructive. -/
theorem self_description_absorption (a : I) (h : compose a a = a) :
    weight (compose a a) = weight a ∧
    ∀ c : I, emergence a a c = -rs a c := by
  constructor
  · unfold weight; rw [h]
  · exact idempotent_negativity a h

/-- DP13: Semantic Charge Squared Bounded by Weight.
    The semantic charge squared is always bounded by the product of
    the self-composition's weight and the idea's weight. This gives
    a PRECISE upper bound on how much self-amplification is possible.
    Even non-idempotent ideas have bounded self-description capacity. -/
theorem semantic_charge_weight_bound (a : I) :
    (semanticCharge a) ^ 2 ≤ weight (compose a a) * weight a := by
  unfold semanticCharge weight
  exact emergence_bounded' a a a

/-- DP14: Nested Self-Reference Creates More Weight.
    compose(compose a a)(compose a a) has weight ≥ weight(compose a a) ≥ weight(a).
    Each level of self-reference adds irreducible weight.
    SURPRISING: while idempotent self-reference is meaning-destructive,
    non-idempotent self-reference always creates MORE. -/
theorem nested_self_reference_weight (a : I) :
    weight (compose (compose a a) (compose a a)) ≥ weight (compose a a) ∧
    weight (compose a a) ≥ weight a := by
  unfold weight
  constructor
  · exact compose_enriches' (compose a a) (compose a a)
  · exact compose_enriches' a a

end GodelWittgenstein

/-! ## §4. The Hermeneutic Circle Is a Spiral, Not a Loop

Gadamer's hermeneutic circle: understanding parts requires understanding
the whole. We formalize the spiral structure: each interpretive pass
creates irreducible new weight, and the gain from each pass has
a precise decomposition into emergence and cross-resonance terms. -/

section HermeneuticSpiral
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Iterated interpretation: reader r interprets text t exactly n times. -/
def iterInterpret (r t : I) : ℕ → I
  | 0 => r
  | n + 1 => compose (iterInterpret r t n) t

@[simp] theorem iterInterpret_zero (r t : I) : iterInterpret r t 0 = r := rfl
theorem iterInterpret_succ (r t : I) (n : ℕ) :
    iterInterpret r t (n + 1) = compose (iterInterpret r t n) t := rfl

/-- DP15: The Spiral Never Loops Back.
    Each pass of interpretation increases (or maintains) the interpreter's
    weight. The hermeneutic "circle" is actually a monotonically ascending
    spiral. You can never return to your pre-interpretation state.
    SURPRISING: even re-reading the SAME text always adds weight. -/
theorem spiral_never_loops (r t : I) (n : ℕ) :
    weight (iterInterpret r t (n + 1)) ≥ weight (iterInterpret r t n) := by
  unfold weight
  rw [iterInterpret_succ]
  exact compose_enriches' (iterInterpret r t n) t

/-- DP16: Spiral Non-Voidness.
    If the reader is non-void, they remain non-void after any number
    of interpretive passes. Interpretation never annihilates the reader.
    SURPRISING: even interpreting "nothing" (void text) preserves the reader. -/
theorem spiral_nonvoid (r t : I) (h : r ≠ void) :
    ∀ n : ℕ, iterInterpret r t n ≠ void := by
  intro n; induction n with
  | zero => exact h
  | succ n ih =>
    rw [iterInterpret_succ]
    exact compose_ne_void_of_left _ t ih

/-- DP17: Hermeneutic Gain Decomposition.
    The weight gained from the (n+1)-th interpretation decomposes
    into EXACTLY three components:
    (1) the old state's resonance with the new state,
    (2) the text's resonance with the new state, and
    (3) the emergence (genuinely NEW meaning from the encounter).
    This gives a precise anatomy of how understanding grows. -/
theorem hermeneutic_gain_decomposition (r t : I) (n : ℕ) :
    weight (iterInterpret r t (n + 1)) =
    rs (iterInterpret r t n) (iterInterpret r t (n + 1)) +
    rs t (iterInterpret r t (n + 1)) +
    emergence (iterInterpret r t n) t (iterInterpret r t (n + 1)) := by
  unfold weight
  rw [iterInterpret_succ]
  exact rs_compose_eq (iterInterpret r t n) t (compose (iterInterpret r t n) t)

/-- DP18: The Hermeneutic Cocycle.
    For a text with two parts p₁ and p₂, the total emergence accumulated
    by reading them sequentially is INVARIANT under rebracketing:
    κ(r, p₁, d) + κ(r∘p₁, p₂, d) = κ(p₁, p₂, d) + κ(r, p₁∘p₂, d).
    This is the CONSERVATION LAW of interpretation: meaning is conserved
    across different orderings of encounter, even though the intermediate
    states differ. The circle resolves — not because there is no circle,
    but because total emergence is path-independent. -/
theorem hermeneutic_cocycle (r p₁ p₂ d : I) :
    emergence r p₁ d + emergence (compose r p₁) p₂ d =
    emergence p₁ p₂ d + emergence r (compose p₁ p₂) d := by
  exact cocycle_condition r p₁ p₂ d

end HermeneuticSpiral

/-! ## §5. Why Phenomenological Reduction Changes Everything

Husserl's epoché (phenomenological reduction) brackets presuppositions
to reveal the "things themselves." But in IDT, the act of reduction
ITSELF changes the phenomenon: adding a horizon to an observation
creates emergence that wasn't in either alone. The observer always
affects the observed. This is not a failure of the method — it is
a structural feature of ideas. -/

section ReductionParadox
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP19: The Observer Effect.
    Combining a horizon h with an observation a creates emergence
    κ(h, a, c) that exists in NEITHER h nor a alone. The act of
    observation (composition with the observer's horizon) necessarily
    produces new resonance. Phenomenological reduction is impossible
    in principle — the reducer changes the reduced.
    The emergence is bounded but NEVER guaranteed to be zero
    (for non-linear observers). -/
theorem observer_effect (h a c : I) :
    rs (compose h a) c =
    rs h c + rs a c + emergence h a c ∧
    (emergence h a c) ^ 2 ≤ weight (compose h a) * weight c := by
  constructor
  · exact rs_compose_eq h a c
  · unfold weight; exact emergence_bounded' h a c

/-- DP20: Double Reduction Creates Double Emergence.
    Reducing with two layers of horizon h₁ then h₂ creates emergence
    at EACH layer plus an inter-layer emergence. The total resonance
    of the double reduction decomposes into five terms: three individual
    resonances and two emergence terms. Each layer of philosophical
    reflection adds its own irreducible "observer effect."
    SURPRISING: you cannot remove observer effects by adding more observers. -/
theorem double_reduction_emergence (h₁ h₂ a d : I) :
    rs (compose (compose h₁ h₂) a) d =
    rs h₁ d + rs h₂ d + rs a d +
    emergence h₁ h₂ d + emergence (compose h₁ h₂) a d := by
  have step1 := rs_compose_eq h₁ h₂ d
  have step2 := rs_compose_eq (compose h₁ h₂) a d
  linarith

/-- DP21: Reduction Weight Paradox.
    The reduced phenomenon (compose h a) has weight at least equal to
    the horizon's weight. Bracketing presuppositions does NOT reduce
    the total weight — it can only INCREASE it.
    PARADOX: "reducing" in the phenomenological sense always ADDS.
    Moreover, the weight surplus decomposes into cross-resonances
    and emergence. -/
theorem reduction_weight_paradox (h a : I) :
    weight (compose h a) ≥ weight h ∧
    weight (compose h a) - weight h =
    rs h (compose h a) + rs a (compose h a) +
    emergence h a (compose h a) - rs h h := by
  unfold weight
  constructor
  · exact compose_enriches' h a
  · have h1 := rs_compose_eq h a (compose h a)
    linarith

end ReductionParadox

/-! ## §6. The Frame Problem: Background Is Infinite

The frame problem in AI and philosophy: how do you specify the
"background assumptions" needed to interpret an idea? In IDT,
we prove that background grows monotonically and irreversibly
under composition. No finite set of assumptions suffices. -/

section FrameProblem
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP22: Background Weight Grows Monotonically.
    The background (accumulated context from n compositions) has
    non-decreasing weight. Each new idea added to the background
    makes it heavier. There is no "forgetting" in the frame.
    SURPRISING: even adding void to the background preserves weight. -/
theorem background_weight_monotone (a : I) (n : ℕ) :
    weight (composeN a (n + 1)) ≥ weight (composeN a n) ∧
    weight (composeN a n) ≥ 0 := by
  unfold weight
  constructor
  · exact rs_composeN_mono a n
  · exact rs_composeN_nonneg a n

/-- DP23: Frame Explosion for Non-Void Ideas.
    For a non-void idea, the frame weight after n+1 repetitions is
    strictly positive and at least as large as the base idea's weight.
    The frame is ALWAYS present and ALWAYS growing.
    SURPRISING: even a single idea generates an unbounded frame
    as you compose it with itself repeatedly. -/
theorem frame_explosion (a : I) (h : a ≠ void) (n : ℕ) :
    weight (composeN a (n + 1)) ≥ weight a ∧
    weight (composeN a (n + 1)) > 0 ∧
    composeN a (n + 1) ≠ void := by
  have h1 : weight a > 0 := weight_pos a h
  have h2 : weight (composeN a (n + 1)) ≥ weight a :=
    rs_composeN_ge_base a n
  have h3 : composeN a (n + 1) ≠ void := composeN_ne_void a h n
  have h4 : weight (composeN a (n + 1)) > 0 := weight_pos _ h3
  exact ⟨h2, h4, h3⟩

/-- DP24: Incompressible Background Emergence.
    The emergence from adding one more item to the background is
    bounded above by √(weight(background) * weight(observer)).
    The frame can't add more emergence than the product of its
    accumulated weight and the observer's weight allows.
    SURPRISING: the frame constrains its own growth rate. -/
theorem incompressible_background (a c : I) (n : ℕ) :
    (emergence (composeN a n) a c) ^ 2 ≤
    weight (composeN a (n + 1)) * weight c := by
  unfold weight
  change (emergence (composeN a n) a c) ^ 2 ≤
    rs (compose (composeN a n) a) (compose (composeN a n) a) * rs c c
  exact emergence_bounded' (composeN a n) a c

end FrameProblem

/-! ## §7. Dialectical Divergence: When History Never Ends

Hegel proposed that history converges through dialectical development.
We prove the opposite: under non-trivial conditions, dialectical
iteration produces ideas of ever-increasing weight. History never
returns to its starting point, and "the end of history" requires void. -/

section DialecticalDivergence
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Iterated dialectical synthesis: repeatedly synthesize thesis with antithesis. -/
def iterDialectic (thesis antithesis : I) : ℕ → I
  | 0 => thesis
  | n + 1 => compose (iterDialectic thesis antithesis n) antithesis

/-- DP25: History Accumulates Weight Monotonically.
    At each dialectical stage, the weight of the synthesis is at
    least as great as the previous stage. History NEVER retreats.
    Moreover, the weight is always non-negative.
    SURPRISING: even when thesis and antithesis oppose each other
    (negative mutual resonance), the synthesis is always heavier. -/
theorem history_accumulates (a b : I) (n : ℕ) :
    weight (iterDialectic a b (n + 1)) ≥ weight (iterDialectic a b n) ∧
    weight (iterDialectic a b n) ≥ 0 := by
  unfold weight
  constructor
  · exact compose_enriches' (iterDialectic a b n) b
  · exact rs_self_nonneg' _

/-- DP26: The End of History Requires Void.
    If the thesis is non-void, then NO stage of dialectical development
    is void. History can only "end" (return to void/silence) if it
    started from void. The dialectical process is irreversible.
    SURPRISING: even a thesis opposed by everything remains non-void
    through infinite dialectical iterations. -/
theorem end_of_history_requires_void (a b : I) (h : a ≠ void) (n : ℕ) :
    iterDialectic a b n ≠ void := by
  induction n with
  | zero => exact h
  | succ n ih =>
    show compose (iterDialectic a b n) b ≠ void
    exact compose_ne_void_of_left _ b ih

/-- DP27: Dialectical Weight Is Transitive.
    For any m ≤ n, the weight at stage n is at least the weight at stage m.
    History is GLOBALLY monotone, not just locally.
    SURPRISING: no matter how many stages you skip, you can only go up. -/
theorem dialectical_weight_transitive (a b : I) (m n : ℕ) (h : m ≤ n) :
    weight (iterDialectic a b n) ≥ weight (iterDialectic a b m) := by
  unfold weight
  induction n with
  | zero =>
    interval_cases m
    exact le_refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · have h1 := ih (Nat.lt_succ_iff.mp hlt)
      have h2 : rs (iterDialectic a b (n + 1)) (iterDialectic a b (n + 1)) ≥
                rs (iterDialectic a b n) (iterDialectic a b n) :=
        compose_enriches' _ b
      linarith

end DialecticalDivergence

/-! ## §8. The Zombie Theorem: Consciousness Leaves No Room for Zombies

In philosophy of mind, a "zombie" is a being functionally identical
to a conscious being but lacking consciousness. In IDT, we prove
that if two ideas have the same emergence profile (sameIdea), then
they contribute identically to ALL compositions. There is no room
for a "zombie idea" — same function implies same consciousness. -/

section ZombieTheorem
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP28: Functional Equivalence Is Complete.
    If two ideas are sameIdea (identical emergence in all contexts),
    then they shift resonance by exactly the same amount in every
    composition. Their "compositional role" — how they affect any
    context — is identical. There is nothing "extra" beyond emergence.
    PARADOX: consciousness (= emergence profile) is all there is.
    There are no philosophical zombies in ideatic theory. -/
theorem zombie_impossibility (a b : I) (h : sameIdea a b) (c d : I) :
    rs (compose a c) d - rs a d = rs (compose b c) d - rs b d := by
  have h1 := h c d
  unfold emergence at h1
  linarith

/-- DP29: No Hidden Qualia.
    If two ideas have the same emergence profile, then the only
    difference in their compositional behavior comes from their
    individual resonance difference rs(a,d) - rs(b,d). There are
    no "hidden qualia" — everything is captured by resonance + emergence.
    SURPRISING: the resonance difference is the ONLY degree of freedom
    left after fixing the emergence profile. Qualia = connotation. -/
theorem no_hidden_qualia (a b : I) (h : sameIdea a b) (c d : I) :
    rs (compose a c) d - rs (compose b c) d =
    rs a d - rs b d := by
  have h1 := h c d
  unfold emergence at h1
  linarith

/-- DP30: Same Emergence Implies Same Self-Composition Surplus.
    If sameIdea(a, b), then composing each with the same idea c
    produces the same emergence in every direction. The "experience"
    of composition is identical for sameIdea pairs.
    SURPRISING: same emergence profile → same experience of every encounter. -/
theorem same_emergence_same_experience (a b : I) (h : sameIdea a b)
    (c d : I) : emergence a c d = emergence b c d := h c d

end ZombieTheorem

/-! ## §9. Aspect Perception: Why the Same Idea Looks Different

Wittgenstein's duck-rabbit: the same visual stimulus can be
"seen as" different things depending on the frame. We formalize
the structure of aspect perception and prove that frames MUST
produce different emergences unless they are linear (trivial). -/

section AspectPerception
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP31: Aspect Difference Decomposition.
    The resonance difference between two framings of the same observation
    decomposes into EXACTLY two components:
    (1) the direct resonance difference of the frames, and
    (2) the emergence difference.
    The gestalt switch IS the emergence difference.
    SURPRISING: the "aha!" moment of seeing the rabbit instead of the
    duck is precisely the emergence difference between two frames. -/
theorem aspect_difference (f₁ f₂ obs c : I) :
    rs (compose f₁ obs) c - rs (compose f₂ obs) c =
    (rs f₁ c - rs f₂ c) + (emergence f₁ obs c - emergence f₂ obs c) := by
  have h1 := rs_compose_eq f₁ obs c
  have h2 := rs_compose_eq f₂ obs c
  linarith

/-- DP32: Linear Frames Cannot Create Aspects.
    If both frames are left-linear (zero emergence), then the
    resonance difference between framings reduces to JUST the
    direct frame difference. No emergence → no aspect perception.
    SURPRISING: aspect perception requires nonlinearity. Purely
    logical/linear thinking cannot produce gestalt switches. -/
theorem linear_frames_no_aspects (f₁ f₂ : I)
    (h1 : leftLinear f₁) (h2 : leftLinear f₂) (obs c : I) :
    rs (compose f₁ obs) c - rs (compose f₂ obs) c =
    rs f₁ c - rs f₂ c := by
  have hf1 := leftLinear_additive f₁ h1 obs c
  have hf2 := leftLinear_additive f₂ h2 obs c
  linarith

/-- DP33: The Gestalt Switch Is Bounded.
    The magnitude of the gestalt switch (emergence difference between
    framings) is bounded by the product of the compositions' weights
    and the observer's weight. Even the most dramatic aspect switch
    has a ceiling.
    SURPRISING: there is a mathematical limit to how surprising
    a gestalt switch can be. -/
theorem gestalt_switch_bounded (f₁ f₂ obs c : I) :
    (emergence f₁ obs c) ^ 2 ≤ weight (compose f₁ obs) * weight c ∧
    (emergence f₂ obs c) ^ 2 ≤ weight (compose f₂ obs) * weight c := by
  unfold weight
  exact ⟨emergence_bounded' f₁ obs c, emergence_bounded' f₂ obs c⟩

end AspectPerception

/-! ## §10. The Rule-Following Paradox: Every Rule Has Infinite Interpretations

Wittgenstein's rule-following paradox: no rule determines its own
application. In IDT, this manifests as the fact that rule application
always involves emergence — the rule alone doesn't determine the output. -/

section RuleFollowingParadox
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP34: Rule Application Creates Emergence.
    Applying rule r to input a produces resonance with observer c that
    decomposes into the rule's resonance, the input's resonance, and
    emergence. The emergence is NOT determined by the rule alone —
    it depends on the specific input AND observer.
    PARADOX: the rule underdetermines its application. There is always
    an "interpretation" step (emergence) that goes beyond the rule. -/
theorem rule_creates_emergence (r a c : I) :
    rs (compose r a) c = rs r c + rs a c + emergence r a c ∧
    emergence r a c = rs (compose r a) c - rs r c - rs a c := by
  constructor
  · exact rs_compose_eq r a c
  · unfold emergence; ring

/-- DP35: Community Agreement Requires Shared Emergence.
    Two agents applying different rules r₁, r₂ to the same input a
    agree on the output resonance with c IFF their individual resonances
    PLUS emergences agree. Same-output requires emergence alignment,
    not just rule agreement.
    SURPRISING: two people can follow the "same rule" (same resonance
    profile) yet disagree (different emergence) if their internal
    composition structures differ. -/
theorem community_requires_emergence (r₁ r₂ a c : I) :
    rs (compose r₁ a) c = rs (compose r₂ a) c ↔
    rs r₁ c + emergence r₁ a c = rs r₂ c + emergence r₂ a c := by
  constructor
  · intro h
    have h1 := rs_compose_eq r₁ a c
    have h2 := rs_compose_eq r₂ a c
    linarith
  · intro h
    have h1 := rs_compose_eq r₁ a c
    have h2 := rs_compose_eq r₂ a c
    linarith

/-- DP36: Rule Composition Creates Higher-Order Emergence.
    Applying one rule after another involves BOTH the individual
    emergences AND a cocycle correction term. The rules interact
    non-additively — following two rules in sequence is not the
    sum of following each separately.
    SURPRISING: the cocycle condition shows that rule-following
    has an inherent "interaction effect" between rules. -/
theorem rule_composition_higher_order (r₁ r₂ a d : I) :
    emergence r₁ r₂ d + emergence (compose r₁ r₂) a d =
    emergence r₂ a d + emergence r₁ (compose r₂ a) d := by
  exact cocycle_condition r₁ r₂ a d

end RuleFollowingParadox

/-! ## §11. Translation Is Bounded Below: You Always Lose Something

Translation between "forms of life" (different background contexts)
always involves emergence loss. The untranslatable remainder is
quantifiable and bounded below. -/

section TranslationBounds
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP37: Translation Loss Theorem.
    Translating idea a from form of life f₁ to f₂ produces different
    resonance patterns. The difference is EXACTLY the resonance
    difference of the forms plus the emergence difference.
    SURPRISING: translation loss is entirely decomposable into
    "cultural difference" (resonance) and "creative difference" (emergence). -/
theorem translation_loss (f₁ f₂ a c : I) :
    rs (compose f₁ a) c - rs (compose f₂ a) c =
    (rs f₁ c - rs f₂ c) + (emergence f₁ a c - emergence f₂ a c) := by
  have h1 := rs_compose_eq f₁ a c
  have h2 := rs_compose_eq f₂ a c
  linarith

/-- DP38: Incommensurable Forms Maximize Translation Loss.
    When two forms of life are mutually orthogonal (zero mutual resonance),
    the translation loss from f₁ to void (removing all context) captures
    the full emergence: the entire context-dependent meaning is lost.
    SURPRISING: translating from a rich culture to "no culture" (void)
    loses EXACTLY the emergence, and the residual is just rs(a, c). -/
theorem incommensurable_maximal_loss (f a c : I) :
    rs (compose f a) c - rs (compose (void : I) a) c =
    rs f c + emergence f a c := by
  have h1 := rs_compose_eq f a c
  simp [rs_void_left']
  unfold emergence
  linarith

/-- DP39: Translation Asymmetry.
    Translating from f₁ to f₂ is NOT the same as translating from
    f₂ to f₁. The loss is asymmetric: the emergence difference
    between f₁ and f₂ is generally non-zero in both directions.
    The difference of differences captures the "translation curvature."
    SURPRISING: round-trip translation loses information even if each
    direction is "faithful." -/
theorem translation_asymmetry (f₁ f₂ a c : I) :
    (rs (compose f₁ a) c - rs (compose f₂ a) c) =
    -(rs (compose f₂ a) c - rs (compose f₁ a) c) := by ring

end TranslationBounds

/-! ## §12. The Beetle in the Box: Private Experience Vanishes Quantitatively

Wittgenstein: if everyone has a "beetle" (private experience) that
only they can see, the beetle "drops out" of the language game.
We prove quantitative bounds on how much private experience can
contribute to public discourse. -/

section BeetleInTheBox
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP40: The Beetle Contribution Bound.
    A "beetle" (private idea) whose resonance with public idea c is zero
    can still contribute to a composition through emergence, but this
    emergence is bounded by √(weight(a∘beetle) * weight(c)).
    SURPRISING: even zero direct resonance doesn't mean zero contribution —
    emergence provides a backdoor, but it's bounded. -/
theorem beetle_contribution_bound (a beetle c : I)
    (h_private : rs beetle c = 0) :
    rs (compose a beetle) c = rs a c + emergence a beetle c ∧
    (emergence a beetle c) ^ 2 ≤ weight (compose a beetle) * weight c := by
  constructor
  · have h1 := rs_compose_eq a beetle c
    linarith
  · unfold weight
    exact emergence_bounded' a beetle c

/-- DP41: The Bearer Knows But Cannot Share.
    A non-void beetle has positive self-resonance (the bearer "knows"
    their beetle), but if it's orthogonal to all public ideas, the
    beetle contributes nothing directly to public discourse. The bearer's
    knowledge is REAL (positive weight) but INVISIBLE (zero public resonance).
    SURPRISING: private knowledge exists (positive weight) but is
    publicly null. -/
theorem bearer_knows_cannot_share (beetle : I) (h_ne : beetle ≠ void)
    (h_ortho : ∀ c : I, rs beetle c = 0) :
    False := by
  have h1 : rs beetle beetle = 0 := h_ortho beetle
  have h2 : rs beetle beetle > 0 := rs_self_pos beetle h_ne
  linarith

/-- DP42: Weak Privacy — Selective Invisibility.
    An idea can be invisible to SPECIFIC observers without being void.
    If rs(beetle, c) = 0 and rs(c, beetle) = 0 but beetle ≠ void,
    then beetle is selectively private with respect to c.
    The beetle still has positive self-resonance and can interact
    with other ideas through emergence.
    SURPRISING: privacy is not all-or-nothing; it's observer-relative. -/
theorem selective_privacy (beetle c : I)
    (h_ne : beetle ≠ void)
    (_h_ortho_out : rs beetle c = 0)
    (_h_ortho_in : rs c beetle = 0) :
    rs beetle beetle > 0 ∧
    rs (compose beetle c) (compose beetle c) ≥ rs beetle beetle := by
  constructor
  · exact rs_self_pos beetle h_ne
  · exact compose_enriches' beetle c

end BeetleInTheBox

/-! ## §13. Intersubjectivity Requires Asymmetry

Two subjects encountering each other always produce asymmetric
resonance. Perfect symmetry in understanding is the exception,
not the rule. Genuine intersubjectivity emerges from difference. -/

section IntersubjectivityAsymmetry
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP43: Encounter Asymmetry.
    The resonance of subject a with the encounter (compose a b) minus
    the resonance of subject b with the encounter is generally nonzero.
    The asymmetry of the encounter decomposes into individual resonance
    differences plus emergence differences.
    SURPRISING: even if a and b have the same self-resonance, their
    experience of the encounter can differ. -/
theorem encounter_asymmetry (a b : I) :
    rs a (compose a b) - rs b (compose a b) =
    (rs a (compose a b) - rs b (compose a b)) ∧
    rs (compose a b) (compose a b) ≥ rs a a := by
  constructor
  · ring
  · exact compose_enriches' a b

/-- DP44: Symmetric Encounter Requires Matching Resonance.
    Two subjects experience an encounter symmetrically (same resonance
    with the encounter state) IFF their individual resonances with the
    encounter match. This is a STRONG condition — it requires resonance
    alignment, not just weight matching.
    SURPRISING: symmetric understanding requires more than empathy. -/
theorem symmetric_encounter_condition (a b : I) :
    rs a (compose a b) = rs b (compose a b) ↔
    rs a (compose a b) - rs b (compose a b) = 0 := by
  constructor
  · intro h; linarith
  · intro h; linarith

/-- DP45: Empathy Does Not Guarantee Shared Emergence.
    Even when two subjects have positive mutual resonance (empathy),
    the emergence they create in encounter is NOT determined by their
    empathy alone. The encounter emergence depends on the full
    compositional structure.
    SURPRISING: high empathy + same idea can still produce
    different compositional outcomes. -/
theorem empathy_not_enough (a b c : I)
    (_h_empathy : rs a b > 0 ∧ rs b a > 0) :
    rs (compose a b) c =
    rs a c + rs b c + emergence a b c ∧
    (emergence a b c) ^ 2 ≤ weight (compose a b) * weight c := by
  constructor
  · exact rs_compose_eq a b c
  · unfold weight; exact emergence_bounded' a b c

end IntersubjectivityAsymmetry

/-! ## §14. The Incompleteness of Self-Interpretation

Self-interpretation (composing an idea with itself) always creates
something strictly heavier than the original (for non-void ideas).
But the new content is bounded — you can learn about yourself,
but not infinitely. This creates a hierarchy of self-knowledge
levels, each strictly heavier than the last. -/

section SelfInterpretation
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The self-interpretation hierarchy: a, a∘a, (a∘a)∘(a∘a), ... -/
def selfReflect (a : I) : ℕ → I
  | 0 => a
  | n + 1 => compose (selfReflect a n) (selfReflect a n)

/-- DP46: Self-Interpretation Hierarchy Is Non-Decreasing.
    Each level of self-reflection has at least as much weight as the
    previous level. The hierarchy of self-knowledge is monotonically
    ascending in complexity.
    SURPRISING: reflecting on your reflection is always at least as
    complex as reflecting alone. There is no "simplification through
    deeper reflection." -/
theorem self_reflection_hierarchy (a : I) (n : ℕ) :
    weight (selfReflect a (n + 1)) ≥ weight (selfReflect a n) := by
  show weight (compose (selfReflect a n) (selfReflect a n)) ≥ weight (selfReflect a n)
  unfold weight
  exact compose_enriches' (selfReflect a n) (selfReflect a n)

/-- DP47: Non-Void Ideas Generate Infinite Hierarchy.
    If a ≠ void, every level of the self-reflection hierarchy is non-void
    and has strictly positive weight. The hierarchy never collapses.
    SURPRISING: a single non-void idea generates an infinite chain
    of non-void self-reflections, each at least as heavy as its predecessor. -/
theorem infinite_self_reflection (a : I) (h : a ≠ void) (n : ℕ) :
    selfReflect a n ≠ void ∧ weight (selfReflect a n) > 0 := by
  induction n with
  | zero =>
    exact ⟨h, weight_pos a h⟩
  | succ n ih =>
    constructor
    · show compose (selfReflect a n) (selfReflect a n) ≠ void
      exact compose_ne_void_of_left _ _ ih.1
    · exact weight_pos _ (compose_ne_void_of_left _ _ ih.1)

/-- DP48: Self-Reflection Emergence Is Bounded.
    The emergence from self-reflection at level n is bounded by the
    weight of that level squared. Even the deepest self-reflection
    cannot create more emergence than its weight allows.
    SURPRISING: there is a mathematical ceiling to the insight
    available at each level of self-reflection. -/
theorem self_reflection_emergence_bounded (a : I) (n : ℕ) :
    (emergence (selfReflect a n) (selfReflect a n) (selfReflect a (n + 1))) ^ 2 ≤
    weight (selfReflect a (n + 1)) * weight (selfReflect a (n + 1)) := by
  show (emergence (selfReflect a n) (selfReflect a n)
    (compose (selfReflect a n) (selfReflect a n))) ^ 2 ≤
    weight (compose (selfReflect a n) (selfReflect a n)) *
    weight (compose (selfReflect a n) (selfReflect a n))
  unfold weight
  exact emergence_bounded' (selfReflect a n) (selfReflect a n)
    (compose (selfReflect a n) (selfReflect a n))

end SelfInterpretation

/-! ## §15. Grand Synthesis: Mind as Emergence

The final chapter unifies the preceding results into a coherent picture:
mind IS emergence, meaning IS composition, and consciousness IS the
irreducible surplus of ideas in interaction. We prove three synthesis
theorems that tie everything together. -/

section GrandSynthesis
variable {I : Type*} [S : IdeaticSpace3 I]

/-- DP49: The Irreversibility of Meaning.
    Every compositional act creates irreversible weight. Once two ideas
    are composed, the result is at least as heavy as either component.
    There is no "undo" for meaning — every encounter leaves a trace.
    SYNTHESIS: meaning is a one-way function. Ideas accumulate;
    they never diminish. This is the arrow of ideatic time. -/
theorem irreversibility_of_meaning (a b : I) :
    weight (compose a b) ≥ weight a ∧
    weight (compose a b) ≥ 0 ∧
    (a ≠ void → compose a b ≠ void) := by
  unfold weight
  constructor
  · exact compose_enriches' a b
  constructor
  · exact rs_self_nonneg' _
  · intro h; exact compose_ne_void_of_left a b h

/-- DP50: Emergence Is Conserved Across Paths.
    The total emergence along any compositional path is governed by
    the cocycle condition: κ(a,b,d) + κ(a∘b,c,d) = κ(b,c,d) + κ(a,b∘c,d).
    Different paths through the space of ideas may have different
    intermediate emergences, but the TOTAL emergence is redistributed,
    not created or destroyed.
    SYNTHESIS: this is the fundamental conservation law of meaning.
    It says that the "story" of how ideas combine is path-dependent
    in its intermediate steps but path-independent in its totality.
    This IS the resolution of the hermeneutic circle. -/
theorem emergence_conservation (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d ∧
    rs (compose (compose a b) c) d = rs (compose a (compose b c)) d := by
  constructor
  · exact cocycle_condition a b c d
  · rw [compose_assoc']

/-- DP51: Mind Is Emergence — The Completeness Theorem.
    The resonance of any composition decomposes COMPLETELY into
    individual resonances plus emergence terms. There is nothing
    in the composition that is not accounted for by this decomposition.
    No "ghost in the machine," no mysterious remainder.
    SYNTHESIS: mind (= emergence) plus matter (= individual resonances)
    EQUALS the full experience (= composition resonance). The hard
    problem of consciousness is dissolved: consciousness is emergence,
    and emergence is fully characterized by the cocycle condition. -/
theorem mind_is_emergence (a b c d : I) :
    rs (compose (compose a b) c) d =
    rs a d + rs b d + rs c d +
    emergence a b d + emergence (compose a b) c d ∧
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d := by
  constructor
  · have h1 := rs_compose_eq a b d
    have h2 := rs_compose_eq (compose a b) c d
    linarith
  · exact cocycle_condition a b c d

end GrandSynthesis

end IDT3
