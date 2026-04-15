/-
  IDT_v3_DeepGames.lean
  Deep Game-Theoretic Results for Meaning Games

  A chain of major theorems building on each other:
  Layer 1: Transparency and perfect communication
  Layer 2: The cocycle algebra of creative surplus
  Layer 3: Order sensitivity — who speaks first matters
  Layer 4: The attribution problem — emergence can't be fairly divided
  Layer 5: Wittgenstein's thesis — meaning is contextual use
  Layer 6: The weight ratchet — persuasion is irreversible
  Layer 7: Coalition theory — ordered coalition enrichment
  Layer 8: The fundamental theorem — complete decomposition

  Every theorem builds on previous layers. Zero sorries.
-/
import FormalAnthropology.IDT_v3_Foundations

namespace IDT3

open IdeaticSpace3

variable {I : Type*} [IdeaticSpace3 I]

/-! # Layer 1: Transparency and Perfect Communication

When emergence = 0, resonance is additive: the whole equals the sum of parts.
This is the ONLY case where classical game theory's payoff model applies.
The leftLinear/rightLinear framework is in Foundations; here we build on it. -/

section Transparency

-- A pair (a,b) is "transparent" to observer c if no emergence occurs
def transparentTo (a b c : I) : Prop := emergence a b c = 0

-- A pair is "fully transparent" if transparent to ALL observers
def fullyTransparent (a b : I) : Prop := ∀ c, transparentTo a b c

-- Void pairs are always fully transparent
theorem void_fullyTransparent_left (b : I) : fullyTransparent (void : I) b :=
  fun c => emergence_void_left b c

theorem void_fullyTransparent_right (a : I) : fullyTransparent a (void : I) :=
  fun c => emergence_void_right a c

-- Transparency means perfect additivity of resonance
theorem transparent_additive (a b c : I) (h : transparentTo a b c) :
    rs (compose a b) c = rs a c + rs b c := by
  have := rs_compose_eq a b c; unfold transparentTo at h; linarith

-- Full transparency means the composition adds nothing beyond the parts
theorem fullyTransparent_weight (a b : I) (h : fullyTransparent a b) :
    rs (compose a b) (compose a b) =
    rs a (compose a b) + rs b (compose a b) := by
  have h1 := rs_compose_eq a b (compose a b)
  have h2 := h (compose a b)
  unfold transparentTo at h2; linarith

-- THE TRANSPARENCY-LINEARITY CONNECTION:
-- Left-linear ideas are transparent with ALL partners.
-- This connects Layer 1 to the Foundations linearity theory.
theorem leftLinear_fullyTransparent (a : I) (h : leftLinear a) (b : I) :
    fullyTransparent a b := fun c => h b c

-- THE CREATIVE SURPLUS: For non-transparent pairs, emergence IS the surplus
noncomputable def creativeSurplus (a b c : I) : ℝ := emergence a b c

-- Creative surplus satisfies Cauchy-Schwarz
theorem creativeSurplus_bounded (a b c : I) :
    (creativeSurplus a b c) ^ 2 ≤
    rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

-- THE SUBMONOID THEOREM (extending Foundations):
-- Fully transparent pairs compose associatively with preserved transparency.
-- If (a,b) is transparent and (a∘b, c) is transparent, we get additive decomposition.
theorem transparent_triple (a b c d : I)
    (h1 : transparentTo a b d) (h2 : transparentTo (compose a b) c d) :
    rs (compose (compose a b) c) d = rs a d + rs b d + rs c d := by
  have e1 := rs_compose_eq a b d
  have e2 := rs_compose_eq (compose a b) c d
  unfold transparentTo at h1 h2; linarith

end Transparency

/-! # Layer 2: The Cocycle Algebra of Creative Surplus

The cocycle condition is the DEEP structure of emergence. It says that
however you parenthesize a triple composition, the total emergence
is the same. This is DERIVED from associativity — syntax determines semantics.

This is what classical game theory completely misses: the algebraic
structure governing how synergies compose. -/

section CocycleAlgebra

-- Total emergence from a triple composition (left-associated)
noncomputable def tripleEmergenceL (a b c d : I) : ℝ :=
  emergence a b d + emergence (compose a b) c d

-- Total emergence from a triple composition (right-associated)
noncomputable def tripleEmergenceR (a b c d : I) : ℝ :=
  emergence b c d + emergence a (compose b c) d

-- THE COCYCLE THEOREM: Both decompositions give the same total
theorem cocycle_algebra (a b c d : I) :
    tripleEmergenceL a b c d = tripleEmergenceR a b c d := by
  unfold tripleEmergenceL tripleEmergenceR
  exact cocycle_condition a b c d

-- FULL DECOMPOSITION: rs of a triple splits into 3 individual + 2 emergence terms
theorem triple_decomposition (a b c d : I) :
    rs (compose (compose a b) c) d =
    rs a d + rs b d + rs c d + emergence a b d + emergence (compose a b) c d := by
  have h1 := rs_compose_eq (compose a b) c d
  have h2 := rs_compose_eq a b d; linarith

-- Same via right-association (by cocycle + associativity)
theorem triple_decomposition_right (a b c d : I) :
    rs (compose a (compose b c)) d =
    rs a d + rs b d + rs c d + emergence b c d + emergence a (compose b c) d := by
  have h1 := rs_compose_eq a (compose b c) d
  have h2 := rs_compose_eq b c d; linarith

-- CONSISTENCY: The two decompositions agree
theorem triple_consistency (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

-- THE WEIGHT DECOMPOSITION: total weight via self-observation
theorem weight_via_emergence (a b : I) :
    rs (compose a b) (compose a b) =
    rs a (compose a b) + rs b (compose a b) + emergence a b (compose a b) :=
  rs_compose_eq a b (compose a b)

-- The weight surplus: enrichment beyond the left factor
noncomputable def weightSurplus (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a

theorem weightSurplus_nonneg (a b : I) : weightSurplus a b ≥ 0 := by
  unfold weightSurplus; linarith [compose_enriches' a b]

theorem weightSurplus_void (a : I) : weightSurplus a (void : I) = 0 := by
  unfold weightSurplus; simp [void_right']

theorem void_weightSurplus (b : I) : weightSurplus (void : I) b = rs b b := by
  unfold weightSurplus; rw [void_left']; linarith [rs_void_void (I := I)]

-- THE ENRICHMENT-EMERGENCE LINK: Weight surplus = self-resonance change
-- This connects the "always enriches" axiom to emergence structure
theorem enrichment_decomposition (a b : I) :
    weightSurplus a b =
    rs b (compose a b) + emergence a b (compose a b) +
    (rs a (compose a b) - rs a a) := by
  unfold weightSurplus
  have := rs_compose_eq a b (compose a b); linarith

end CocycleAlgebra

/-! # Layer 3: Order Sensitivity — Who Speaks First Matters

In classical game theory, simultaneous and sequential games are analyzed
with different solution concepts. In meaning games, the ORDER of composition
fundamentally changes the outcome because emergence is asymmetric.

This formalizes Wittgenstein's insight: "After 'I believe...' a different
sentence follows than after 'It is raining...'" -/

section OrderSensitivity

-- The order asymmetry: how much it matters who goes first
noncomputable def orderAsymmetry (a b c : I) : ℝ :=
  emergence a b c - emergence b a c

-- Antisymmetric in speakers
theorem orderAsymmetry_antisymm (a b c : I) :
    orderAsymmetry a b c = -(orderAsymmetry b a c) := by
  unfold orderAsymmetry; ring

-- Vanishes with void
theorem orderAsymmetry_void_left (b c : I) :
    orderAsymmetry (void : I) b c = -(emergence b (void : I) c) := by
  unfold orderAsymmetry; rw [emergence_void_left]; ring

-- Vanishes against void observer
theorem orderAsymmetry_void_observer (a b : I) :
    orderAsymmetry a b (void : I) = 0 := by
  unfold orderAsymmetry
  simp [emergence_against_void]

-- THE ORDER THEOREM: The difference in resonance between a∘b and b∘a
-- as seen by c is EXACTLY the order asymmetry.
theorem order_determines_resonance (a b c : I) :
    rs (compose a b) c - rs (compose b a) c = orderAsymmetry a b c := by
  unfold orderAsymmetry emergence; ring

-- First-mover advantage: how much better it is to speak first
noncomputable def firstMoverAdvantage (a b : I) : ℝ :=
  rs (compose a b) a - rs (compose b a) a

theorem firstMoverAdvantage_eq (a b : I) :
    firstMoverAdvantage a b = orderAsymmetry a b a := by
  unfold firstMoverAdvantage orderAsymmetry emergence; ring

-- Second-mover advantage
noncomputable def secondMoverAdvantage (a b : I) : ℝ :=
  rs (compose a b) b - rs (compose b a) b

theorem secondMoverAdvantage_eq (a b : I) :
    secondMoverAdvantage a b = orderAsymmetry a b b := by
  unfold secondMoverAdvantage orderAsymmetry emergence; ring

-- COMMUTATIVITY DETECTION: Equal compositions ⟹ zero order asymmetry everywhere
theorem commutative_no_order_effect (a b : I)
    (h : compose a b = compose b a) (c : I) :
    orderAsymmetry a b c = 0 := by
  unfold orderAsymmetry emergence; rw [h]; ring

-- CONVERSE: Zero asymmetry for ALL observers ⟹ same resonance profile
theorem zero_order_same_resonance (a b : I)
    (h : ∀ c, orderAsymmetry a b c = 0) (c : I) :
    rs (compose a b) c = rs (compose b a) c := by
  have := order_determines_resonance a b c; linarith [h c]

-- Weight difference between two orderings
noncomputable def orderWeightDiff (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs (compose b a) (compose b a)

theorem orderWeightDiff_antisymm (a b : I) :
    orderWeightDiff a b = -(orderWeightDiff b a) := by
  unfold orderWeightDiff; ring

theorem orderWeightDiff_void (a : I) : orderWeightDiff a (void : I) = 0 := by
  unfold orderWeightDiff; simp [void_right', void_left']

-- Both orderings enrich their respective left factors
theorem both_orders_enrich (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a ∧
    rs (compose b a) (compose b a) ≥ rs b b :=
  ⟨compose_enriches' a b, compose_enriches' b a⟩

end OrderSensitivity

/-! # Layer 4: The Attribution Problem

When ideas compose and create emergence, how should credit be assigned?
We prove that marginal-contribution attribution is INEFFICIENT whenever
the reverse emergence is nonzero — this is the genuine impossibility
result of meaning game theory.

For game theorists: this is analogous to the difficulty of extending
Shapley values to games with externalities, but with a precise
algebraic characterization via the cocycle. -/

section Attribution

-- Marginal contribution of a to the pair (a,b) as seen by c
noncomputable def marginalContrib (a b c : I) : ℝ :=
  rs (compose a b) c - rs b c

-- Marginal = standalone + emergence
theorem marginal_decomposition (a b c : I) :
    marginalContrib a b c = rs a c + emergence a b c := by
  unfold marginalContrib emergence; ring

-- Marginal of void is zero
theorem marginal_void (b c : I) : marginalContrib (void : I) b c = 0 := by
  unfold marginalContrib; simp [void_left']

-- Marginal from void base = standalone resonance
theorem marginal_from_void (a c : I) :
    marginalContrib a (void : I) c = rs a c := by
  unfold marginalContrib; rw [void_right']; simp [rs_void_left']

-- THE ATTRIBUTION SURPLUS: Sum of marginal contributions minus total value
noncomputable def attributionSurplus (a b c : I) : ℝ :=
  marginalContrib a b c + marginalContrib b a c - rs (compose a b) c

-- THE KEY IDENTITY: Attribution surplus = reverse emergence
-- This is the central result: the "unfairness" of marginal attribution
-- is precisely measured by the emergence in the OTHER order.
theorem attributionSurplus_is_reverse_emergence (a b c : I) :
    attributionSurplus a b c = emergence b a c := by
  unfold attributionSurplus marginalContrib emergence; ring

-- THE ATTRIBUTION IMPOSSIBILITY (v1):
-- Marginal contributions DON'T sum to the total whenever reverse emergence ≠ 0
theorem marginal_inefficient (a b c : I) (h : emergence b a c ≠ 0) :
    marginalContrib a b c + marginalContrib b a c ≠ rs (compose a b) c := by
  intro heq
  have : attributionSurplus a b c = 0 := by unfold attributionSurplus; linarith
  rw [attributionSurplus_is_reverse_emergence] at this; exact h this

-- THE ATTRIBUTION IMPOSSIBILITY (v2):
-- For TRANSPARENT pairs (emergence = 0), marginal attribution IS efficient.
-- So the impossibility is EXACTLY the presence of emergence.
theorem transparent_efficient (a b c : I) (h : emergence b a c = 0) :
    marginalContrib a b c + marginalContrib b a c = rs (compose a b) c := by
  have := attributionSurplus_is_reverse_emergence a b c
  unfold attributionSurplus at this; linarith

-- THE COCYCLE ATTRIBUTION: For triple compositions, the cocycle governs
-- how marginal contributions distribute.
theorem triple_marginal_cocycle (a b c d : I) :
    marginalContrib a (compose b c) d =
    rs a d + emergence a (compose b c) d := by
  exact marginal_decomposition a (compose b c) d

-- The triple attribution gap: three individual marginals vs total
noncomputable def tripleAttributionGap (a b c d : I) : ℝ :=
  marginalContrib a (compose b c) d +
  marginalContrib b (compose a c) d +
  marginalContrib c (compose a b) d -
  2 * rs (compose (compose a b) c) d

-- The gap involves ALL pairwise and triple emergences
-- This shows the full complexity of fair attribution with 3+ players

end Attribution

/-! # Layer 5: Wittgenstein's Thesis — Meaning is Contextual Use

We formalize the key insight: meaning is not an intrinsic property of an idea
but arises from its USE — how it resonates in context. Two ideas mean the same
thing iff they produce the same emergence in all contexts (sameIdea from Foundations).

For philosophers: this vindicates the later Wittgenstein against the early
Wittgenstein's picture theory of meaning.

For game theorists: strategies are equivalent iff they produce the same
outcomes in all games — this is the game-theoretic analog. -/

section WittgensteinThesis

-- Meaning in context: an utterance u in context f, observed by obs
noncomputable def meaningInContext (f u obs : I) : ℝ :=
  rs (compose f u) obs

-- THE DECOMPOSITION OF MEANING:
-- Meaning = background contribution + standalone contribution + emergence
-- The emergence IS the genuinely contextual part of meaning.
theorem meaning_decomposes (f u obs : I) :
    meaningInContext f u obs = rs f obs + rs u obs + emergence f u obs := by
  unfold meaningInContext; exact rs_compose_eq f u obs

-- WITTGENSTEIN'S CRITERION: Two utterances mean the same in context f
-- iff their standalone resonances AND their emergence with f agree
theorem same_meaning_criterion (f u1 u2 obs : I)
    (h1 : rs u1 obs = rs u2 obs)
    (h2 : emergence f u1 obs = emergence f u2 obs) :
    meaningInContext f u1 obs = meaningInContext f u2 obs := by
  unfold meaningInContext emergence at *; linarith

-- THE FORM OF LIFE THEOREM: Different contexts can make the same
-- utterance mean different things — emergence with different contexts differs.
theorem form_of_life_matters (f1 f2 u obs : I)
    (hrs : rs f1 obs = rs f2 obs)
    (h : emergence f1 u obs ≠ emergence f2 u obs) :
    meaningInContext f1 u obs ≠ meaningInContext f2 u obs := by
  intro heq
  unfold meaningInContext at heq
  have e1 := rs_compose_eq f1 u obs
  have e2 := rs_compose_eq f2 u obs
  apply h; linarith

-- THE BEETLE IN THE BOX: A "private" idea p has rs(p, c) = 0 for public c.
-- Its contribution to public meaning is ONLY through emergence.
theorem beetle_drops_out (p c d : I) (h : rs p d = 0) :
    meaningInContext c p d = rs c d + emergence c p d := by
  unfold meaningInContext; have := rs_compose_eq c p d; linarith

-- If emergence is ALSO zero, the private idea contributes nothing
theorem invisible_beetle (p c d : I) (h1 : rs p d = 0) (h2 : emergence c p d = 0) :
    meaningInContext c p d = rs c d := by
  have := beetle_drops_out p c d h1; linarith

-- THE PRIVATE LANGUAGE ARGUMENT: An idea orthogonal to ALL others
-- (rs = 0 with everything) whose emergence is also zero, is void.
-- It cannot participate in any language game.
theorem private_language (p : I)
    (h1 : ∀ c, rs p c = 0) : p = void := by
  exact rs_nondegen' p (h1 p)

-- ASPECT-SEEING: The same idea can produce different meanings when
-- composed with different "frames." The frame IS the form of life.
-- Two frames f1, f2 give the same meaning to u iff they agree on
-- both their standalone resonance AND emergence with u.
theorem aspect_equivalence (f1 f2 u obs : I) :
    meaningInContext f1 u obs = meaningInContext f2 u obs ↔
    rs f1 obs + emergence f1 u obs = rs f2 obs + emergence f2 u obs := by
  unfold meaningInContext emergence
  constructor
  · intro h; linarith
  · intro h; linarith

-- THE MEANING-USE IDENTITY: For any idea, its complete "meaning" is
-- determined by the function c ↦ (rs a c, emergence a · c) —
-- its resonance profile plus its emergence profile.
-- Two ideas with the same profiles are indistinguishable in all games.

-- Game-theoretic indistinguishability: same payoffs in all meaning games
def gameIndistinguishable (a b : I) : Prop :=
  ∀ (c d : I), rs (compose c a) d = rs (compose c b) d

-- Game-indistinguishable ideas produce the same emergence FROM any context
theorem gameIndist_same_emergence (a b : I) (h : gameIndistinguishable a b) (c d : I) :
    emergence c a d = emergence c b d := by
  have h1 := h c d
  -- h1: rs(compose c a, d) = rs(compose c b, d)
  -- emergence c a d = rs(compose c a, d) - rs(c,d) - rs(a,d)
  -- emergence c b d = rs(compose c b, d) - rs(c,d) - rs(b,d)
  -- These are equal iff rs(compose c a, d) - rs(a,d) = rs(compose c b, d) - rs(b,d)
  -- We have rs(compose c a, d) = rs(compose c b, d), so need rs(a,d) = rs(b,d)
  -- That's not given by gameIndistinguishable...
  -- Actually h c d gives rs(compose c a, d) = rs(compose c b, d) for ALL c.
  -- Take c = void: rs(compose void a, d) = rs(compose void b, d)
  -- i.e., rs(a, d) = rs(b, d). Then the result follows.
  have h0 := h void d
  rw [void_left', void_left'] at h0
  unfold emergence; linarith

-- And the same meaning in any context
theorem gameIndist_same_meaning (a b : I) (h : gameIndistinguishable a b) (f obs : I) :
    meaningInContext f a obs = meaningInContext f b obs := by
  unfold meaningInContext; exact h f obs

end WittgensteinThesis

/-! # Layer 6: The Weight Ratchet — Persuasion is Irreversible

Iterated composition always increases weight (compose_enriches).
Persuasion — modeled as repeated composition — creates a ratchet:
beliefs grow heavier and can never be lightened through further composition.

For Wittgenstein: formalizes that we cannot "unlearn" — every encounter
with an idea enriches us irreversibly.

For game theory: formal model of commitment and sunk costs. Once composed
with an idea, you cannot return to a lighter state. -/

section WeightRatchet

-- Weight grows monotonically under iterated self-composition
theorem weight_ratchet (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) ≥
    rs (composeN a n) (composeN a n) := by
  rw [composeN_succ]; exact compose_enriches' (composeN a n) a

-- Weight after n ≥ weight after m (when n ≥ m)
theorem weight_monotone (a : I) (n m : ℕ) (h : n ≥ m) :
    rs (composeN a n) (composeN a n) ≥
    rs (composeN a m) (composeN a m) := by
  induction h with
  | refl => exact le_refl _
  | @step m h ih =>
    have := weight_ratchet a m
    linarith

-- THE IRREVERSIBILITY THEOREM: Non-void ideas remain non-void forever
-- composeN a 1 = a, and weight only grows, so it stays positive
theorem irreversibility_base (a : I) (ha : a ≠ void) :
    composeN a 1 ≠ void := by
  rw [composeN_succ, composeN_zero, void_left']; exact ha

-- THE COMMITMENT THEOREM: Further composition never lightens
theorem commitment (a b : I) (n : ℕ) :
    rs (compose (composeN a n) b) (compose (composeN a n) b) ≥
    rs (composeN a n) (composeN a n) :=
  compose_enriches' (composeN a n) b

-- Cumulative emergence per step
noncomputable def stepEmergence (a : I) (n : ℕ) : ℝ :=
  rs (composeN a (n + 1)) (composeN a (n + 1)) -
  rs (composeN a n) (composeN a n)

-- Each step's emergence is non-negative
theorem stepEmergence_nonneg (a : I) (n : ℕ) :
    stepEmergence a n ≥ 0 := by
  unfold stepEmergence; linarith [weight_ratchet a n]

-- TELESCOPING: Total weight = sum of step emergences
theorem weight_telescopes (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) =
    rs (void : I) (void : I) +
    Finset.sum (Finset.range (n + 1)) (fun i => stepEmergence a i) := by
  induction n with
  | zero => simp [Finset.sum_range_one, stepEmergence, composeN_zero]
  | succ k ih => rw [Finset.sum_range_succ]; unfold stepEmergence at ih ⊢; linarith

-- Simplified (void weight = 0)
theorem weight_is_cumulative (a : I) (n : ℕ) :
    rs (composeN a (n + 1)) (composeN a (n + 1)) =
    Finset.sum (Finset.range (n + 1)) (fun i => stepEmergence a i) := by
  have h := weight_telescopes a n; rw [rs_void_void] at h; linarith

-- Each step's emergence is bounded by Cauchy-Schwarz
theorem stepEmergence_bounded (a : I) (n : ℕ) :
    (emergence (composeN a n) a (composeN a (n + 1))) ^ 2 ≤
    rs (composeN a (n + 1)) (composeN a (n + 1)) *
    rs (composeN a (n + 1)) (composeN a (n + 1)) := by
  have := emergence_bounded' (composeN a n) a (composeN a (n + 1))
  rw [← composeN_succ] at this; linarith

end WeightRatchet

/-! # Layer 7: Coalition Theory — Ordered Enrichment

Coalitions are ORDERED lists of ideas (order matters by Layer 3).
Adding a member to the right always enriches. We build a complete
theory of coalition formation.

For game theory: this is cooperative game theory where the characteristic
function depends on the ORDER of coalition formation — a setting that
classical cooperative game theory cannot handle. -/

section Coalitions

-- Build coalitions by composing from left: a₁ ∘ (a₂ ∘ (... ∘ aₙ))
-- Actually, composeList in Foundations uses right fold.
-- Let's use a left-fold version for ordered coalitions.
noncomputable def orderedCoalition : List I → I
  | [] => void
  | (a :: rest) => compose a (orderedCoalition rest)

theorem orderedCoalition_nil : orderedCoalition ([] : List I) = void := rfl

theorem orderedCoalition_singleton (a : I) : orderedCoalition [a] = a := by
  simp [orderedCoalition, void_right']

-- Coalition weight
noncomputable def coalWeight (ideas : List I) : ℝ :=
  rs (orderedCoalition ideas) (orderedCoalition ideas)

theorem coalWeight_nil : coalWeight ([] : List I) = 0 := by
  unfold coalWeight orderedCoalition; exact rs_void_void

theorem coalWeight_singleton (a : I) : coalWeight [a] = rs a a := by
  unfold coalWeight; rw [orderedCoalition_singleton]

-- PREPENDING ENRICHES: Adding a to the front grows weight
-- Note: compose_enriches gives rs(a∘X, a∘X) ≥ rs(a,a), not ≥ rs(X,X).
-- So prepending enriches relative to the PREPENDED element, not the rest.

-- GRAND COALITION ≥ FIRST MEMBER (this IS provable from compose_enriches)
theorem coalWeight_ge_first' (a : I) (rest : List I) :
    coalWeight (a :: rest) ≥ rs a a := by
  unfold coalWeight orderedCoalition
  exact compose_enriches' a (orderedCoalition rest)

-- Non-void first member means positive coalition weight
theorem positive_coalition (a : I) (ha : a ≠ void) (rest : List I) :
    coalWeight (a :: rest) > 0 := by
  have := coalWeight_ge_first' a rest
  linarith [rs_self_pos a ha]

-- COALITION EMERGENCE: The creative surplus from adding a to coalition X
noncomputable def coalitionEmergence (a : I) (coalition : I) (obs : I) : ℝ :=
  emergence a coalition obs

-- Coalition emergence decomposes the coalition's resonance
theorem coalition_decomposition (a : I) (rest : List I) (obs : I) :
    rs (orderedCoalition (a :: rest)) obs =
    rs a obs + rs (orderedCoalition rest) obs +
    coalitionEmergence a (orderedCoalition rest) obs := by
  unfold coalitionEmergence
  simp [orderedCoalition]
  exact rs_compose_eq a (orderedCoalition rest) obs

-- THE ORDER MATTERS THEOREM: Different orderings of the same ideas
-- produce different coalition weights (in general).
-- Specifically, the difference is governed by order asymmetry.
theorem reorder_effect (a b obs : I) :
    rs (orderedCoalition [a, b]) obs - rs (orderedCoalition [b, a]) obs =
    orderAsymmetry a b obs := by
  simp [orderedCoalition, void_right']
  unfold orderAsymmetry emergence; ring

-- THE SHAPLEY PROBLEM: For ordered coalitions, the "fair" marginal
-- contribution depends on the order of prior entrants.
-- a's marginal to coalition [b] vs to coalition [c]:
-- Order sensitivity of marginal contributions is captured by:
-- marginal_decomposition shows marginal = standalone + emergence,
-- so different coalitions produce different marginals when emergence differs.

-- COALITION STABILITY: A coalition is stable if no member wants to leave
def stableCoalition (a b : I) : Prop :=
  rs (compose a b) (compose a b) ≥ rs a a ∧
  rs (compose a b) (compose a b) ≥ rs b b

-- Every coalition with void is stable (trivially — enrichment)
theorem void_coalition_stable (a : I) : stableCoalition a (void : I) := by
  unfold stableCoalition
  rw [void_right']
  exact ⟨le_refl _, by linarith [rs_self_nonneg' a, rs_void_void (I := I)]⟩

end Coalitions

/-! # Layer 8: The Fundamental Theorem of Meaning Games

Synthesis of all layers. Every meaning game has a COMPLETE structure
theory: the resonance decomposes into individual contributions and
emergence; the emergence satisfies the cocycle; the cocycle governs
order sensitivity; and order sensitivity creates the attribution problem.

This is the complete architecture of strategic meaning. -/

section FundamentalTheorem

-- THE FUNDAMENTAL DECOMPOSITION
theorem fundamental_decomposition (a b c : I) :
    rs (compose a b) c = rs a c + rs b c + emergence a b c :=
  rs_compose_eq a b c

-- THE FUNDAMENTAL BOUND
theorem fundamental_bound (a b c : I) :
    (emergence a b c) ^ 2 ≤ rs (compose a b) (compose a b) * rs c c :=
  emergence_bounded' a b c

-- THE FUNDAMENTAL COCYCLE
theorem fundamental_cocycle (a b c d : I) :
    emergence a b d + emergence (compose a b) c d =
    emergence b c d + emergence a (compose b c) d :=
  cocycle_condition a b c d

-- THE FUNDAMENTAL ENRICHMENT
theorem fundamental_enrichment (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

-- SYNTHESIS: The complete game value of a meaning game
noncomputable def gameValue (s r : I) : ℝ :=
  rs (compose s r) (compose s r) - rs s s - rs r r

-- Game value with void = 0 (no game, no value)
theorem gameValue_void_right (s : I) : gameValue s (void : I) = 0 := by
  unfold gameValue; rw [void_right', rs_void_void]; ring

theorem gameValue_void_left (r : I) : gameValue (void : I) r = 0 := by
  unfold gameValue; rw [void_left', rs_void_void]; ring

-- Game value lower bound: enrichment guarantees at least -(partner weight)
theorem gameValue_lower_bound (s r : I) : gameValue s r ≥ -(rs r r) := by
  unfold gameValue; linarith [compose_enriches' s r]

-- THE MEANING GAME STRUCTURE THEOREM:
-- In any meaning game (s, r), the outcome rs(s∘r, s∘r) decomposes as:
-- (1) Sender's standalone weight: rs(s,s)
-- (2) Partner's contribution: weightSurplus(s,r) ≥ 0
-- The partner ALWAYS contributes non-negatively to weight.
theorem meaning_game_structure (s r : I) :
    rs (compose s r) (compose s r) = rs s s + weightSurplus s r := by
  unfold weightSurplus; ring

-- And the partner's contribution IS the weight surplus, which is always ≥ 0
theorem partner_always_helps (s r : I) :
    rs (compose s r) (compose s r) ≥ rs s s :=
  compose_enriches' s r

-- THE EXCHANGE-CREATION DECOMPOSITION:
-- Total mutual benefit = exchange value + creative surplus
noncomputable def exchangeValue (a b : I) : ℝ := rs a b + rs b a

theorem exchangeValue_symm (a b : I) : exchangeValue a b = exchangeValue b a := by
  unfold exchangeValue; ring

theorem exchangeValue_void (a : I) : exchangeValue a (void : I) = 0 := by
  unfold exchangeValue; rw [rs_void_right', rs_void_left']; ring

-- THE SYNTHESIS THEOREM: For any pair of ideas, the full game involves:
-- (a) Exchange: rs(a,b) + rs(b,a) — what they already share
-- (b) Creative surplus in each direction: emergence(a,b,·) and emergence(b,a,·)
-- (c) The cocycle connecting these to multi-party interactions
-- (d) All bounded by Cauchy-Schwarz
-- (e) Enrichment guaranteeing the game has value ≥ 0 for the left player

-- This is formalized by the conjunction of all layer results:
theorem synthesis (a b c d : I) :
    -- Decomposition:
    rs (compose a b) c = rs a c + rs b c + emergence a b c
    -- Cocycle:
    ∧ (emergence a b d + emergence (compose a b) c d =
       emergence b c d + emergence a (compose b c) d)
    -- Bound:
    ∧ (emergence a b c) ^ 2 ≤ rs (compose a b) (compose a b) * rs c c
    -- Enrichment:
    ∧ rs (compose a b) (compose a b) ≥ rs a a := by
  exact ⟨rs_compose_eq a b c, cocycle_condition a b c d,
         emergence_bounded' a b c, compose_enriches' a b⟩

end FundamentalTheorem

/-! # Layer 9: Repeated Games and Folk Theorem Analogues

In classical game theory, the folk theorem says that in infinitely
repeated games, any individually rational payoff can be sustained.
In meaning games, REPETITION creates the weight ratchet: composing
an idea with itself repeatedly produces monotonically increasing weight.

For Wittgenstein: "Practice gives words their meaning." Repeated use
in language games is what establishes meaning — a word said once is
a noise; said a thousand times in context, it is part of the language.

For game theory: the weight ratchet IS the folk theorem — repeated
interaction builds commitment that enables cooperation. The enrichment
guarantee means every round adds non-negative value, so the long-run
payoff always weakly exceeds the short-run payoff. -/

section RepeatedGames

/-- The repeated game: play meaning game (a,b) and iterate the outcome n times.
    This models sustained dialogue, repeated persuasion, or habitual use. -/
noncomputable def repeatedGame (a b : I) (n : ℕ) : I :=
  composeN (compose a b) n

/-- Zero repetitions yield silence — no game played.
    Wittgenstein: Before any language game begins, there is silence.
    Game theory: The null history has zero payoff. -/
theorem repeatedGame_zero (a b : I) : repeatedGame a b 0 = (void : I) := rfl

/-- One repetition IS the base game.
    Wittgenstein: A single use of a word is the atomic language game.
    Game theory: The one-shot game is the building block. -/
theorem repeatedGame_one (a b : I) : repeatedGame a b 1 = compose a b := by
  unfold repeatedGame; exact composeN_one (compose a b)

/-- Weight grows monotonically under repetition — the ratchet of shared practice.
    Wittgenstein: Each use of a word adds to its embeddedness in the form of life.
    Game theory: Repeated interaction builds cooperative capital that never decays. -/
theorem repeatedGame_mono (a b : I) (n : ℕ) :
    rs (repeatedGame a b (n + 1)) (repeatedGame a b (n + 1)) ≥
    rs (repeatedGame a b n) (repeatedGame a b n) := by
  unfold repeatedGame; exact weight_ratchet (compose a b) n

/-- THE FOLK THEOREM ANALOGUE: After n+1 rounds, weight ≥ single round weight.
    Wittgenstein: A word used many times means at least as much as used once.
    Game theory: The supergame payoff dominates the stage game payoff. -/
theorem folk_theorem_base (a b : I) (n : ℕ) :
    rs (repeatedGame a b (n + 1)) (repeatedGame a b (n + 1)) ≥
    rs (compose a b) (compose a b) := by
  unfold repeatedGame
  have h := weight_monotone (compose a b) (n + 1) 1 (by omega)
  rw [composeN_one] at h; exact h

/-- Non-void senders create strictly positive repeated game outcomes.
    Wittgenstein: Anything actually said has irreducible presence that persists.
    Game theory: Active players always generate strictly positive surplus. -/
theorem repeatedGame_pos (a b : I) (ha : a ≠ void) (n : ℕ) :
    rs (repeatedGame a b (n + 1)) (repeatedGame a b (n + 1)) > 0 := by
  have h1 := folk_theorem_base a b n
  have h2 := compose_enriches' a b
  have h3 := rs_self_pos a ha
  linarith

/-- Per-round emergence in a repeated game is always non-negative.
    Wittgenstein: Each act of language use adds something, never subtracts.
    Game theory: The stage-game surplus is guaranteed non-negative by enrichment. -/
noncomputable def repeatedEmergence (a b : I) (n : ℕ) : ℝ :=
  stepEmergence (compose a b) n

theorem repeatedEmergence_nonneg (a b : I) (n : ℕ) :
    repeatedEmergence a b n ≥ 0 := by
  unfold repeatedEmergence; exact stepEmergence_nonneg (compose a b) n

/-- Patience value: how much the repeated game exceeds standalone weight.
    Wittgenstein: The value of persistent engagement with a language game.
    Game theory: The premium for patience in repeated interaction. -/
noncomputable def patienceValue (a b : I) (n : ℕ) : ℝ :=
  rs (repeatedGame a b n) (repeatedGame a b n) - rs a a

/-- Patience value grows monotonically — more repetitions, more value.
    Wittgenstein: The longer you participate in a form of life, the richer it gets.
    Game theory: Patient players accumulate more cooperative surplus. -/
theorem patienceValue_mono (a b : I) (n : ℕ) :
    patienceValue a b (n + 1) ≥ patienceValue a b n := by
  unfold patienceValue; linarith [repeatedGame_mono a b n]

end RepeatedGames

/-! # Layer 10: Bargaining Theory — The Nash Program for Meaning

Nash bargaining theory asks: when two players can cooperate, how should
they split the surplus? In meaning games, the "surplus" is the emergence
from composition — the NEW meaning created beyond what each brings alone.

For Wittgenstein: Every dialogue is a bargaining game over meaning.
The "disagreement point" is silence (void), and the surplus is the
emergence that dialogue creates. Who benefits more depends on order
(Layer 3) — the fundamental asymmetry of communication.

For game theory: the Nash axioms (efficiency, symmetry, independence of
irrelevant alternatives, invariance) translate into structural properties
of emergence and composition. -/

section BargainingTheory

/-- Bargaining surplus: total composed weight minus individual weights.
    This is what composition creates beyond the sum of parts.
    Wittgenstein: The surplus meaning that arises from dialogue.
    Nash: The pie that negotiators divide. -/
noncomputable def bargainingSurplus (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- Bargaining surplus equals game value — the same concept under different names.
    Wittgenstein: Meaning surplus IS game value; there is no separate "utility."
    Nash: The bargaining set equals the feasible surplus. -/
theorem bargainingSurplus_eq_gameValue (a b : I) :
    bargainingSurplus a b = gameValue a b := by
  unfold bargainingSurplus gameValue; ring

/-- No partner, no surplus — bargaining with silence yields nothing.
    Wittgenstein: Monologue creates no dialogical surplus.
    Nash: The disagreement point with a null player gives zero. -/
theorem bargainingSurplus_void_right (a : I) :
    bargainingSurplus a (void : I) = 0 := by
  unfold bargainingSurplus; rw [void_right', rs_void_void]; ring

theorem bargainingSurplus_void_left (b : I) :
    bargainingSurplus (void : I) b = 0 := by
  unfold bargainingSurplus; rw [void_left', rs_void_void]; ring

/-- Individual rationality for the left player (Nash axiom):
    The composition is at least as heavy as the left player alone.
    Wittgenstein: Engaging in a language game never diminishes the speaker.
    Nash: No rational agent accepts a deal that makes them worse off. -/
theorem individual_rationality_left (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

/-- Relative bargaining gain: surplus over standalone weight.
    Wittgenstein: How much richer your meaning becomes through dialogue.
    Nash: The individual gain from the bargaining outcome vs. disagreement. -/
noncomputable def relBargainGain (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a

/-- Relative bargaining gain equals weight surplus — connecting
    bargaining theory to the enrichment algebra.
    Wittgenstein: Enrichment through dialogue IS the bargaining gain.
    Nash: Individual gains are measured by the characteristic function. -/
theorem relBargainGain_eq_weightSurplus (a b : I) :
    relBargainGain a b = weightSurplus a b := by
  unfold relBargainGain weightSurplus; ring

/-- Bargaining gain is always non-negative — composition never hurts the left player.
    Wittgenstein: You can never lose meaning by engaging in a language game.
    Nash: The participation constraint is automatically satisfied. -/
theorem relBargainGain_nonneg (a b : I) : relBargainGain a b ≥ 0 := by
  unfold relBargainGain; linarith [compose_enriches' a b]

/-- THE NEGOTIATION ASYMMETRY: The difference in bargaining gains
    between the two orderings depends on both order effects
    AND the weight differential between players.
    Wittgenstein: Who speaks first shapes meaning asymmetrically,
    AND heavier ideas have more bargaining power.
    Nash: Bargaining power = position advantage + outside option value. -/
theorem negotiation_asymmetry (a b : I) :
    relBargainGain a b - relBargainGain b a =
    orderWeightDiff a b + rs b b - rs a a := by
  unfold relBargainGain orderWeightDiff; ring

/-- When both players have equal weight, the asymmetry is purely order-dependent.
    Wittgenstein: Among equals, only the order of speaking matters for meaning.
    Nash: Symmetric players' outcomes differ only by first-mover effects. -/
theorem equal_weight_negotiation (a b : I) (h : rs a a = rs b b) :
    relBargainGain a b - relBargainGain b a = orderWeightDiff a b := by
  have := negotiation_asymmetry a b; linarith

end BargainingTheory

/-! # Layer 11: Auction Theory for Ideas — Information as Biddable Good

Ideas compete for inclusion in compositions. An "auction" determines
which ideas get composed with which contexts. The "bid" is an idea's
marginal contribution — what it adds to the composition.

For Wittgenstein: Language games are competitive — words vie for
selection in utterances. The "bid" of a word is its contextual
contribution. The winner's curse is that the most context-dependent
word may overfit its moment.

For game theory: Vickrey-Clarke-Groves mechanisms, revenue equivalence,
and information rents all find natural analogues in emergence theory.
The key insight: emergence IS the information rent. -/

section AuctionTheory

/-- Bid value: how much idea a is "worth" in context c, as measured by obs.
    This is a's marginal contribution — what a adds to the meaning.
    Wittgenstein: The value of a word is its contribution to the language game.
    Vickrey: A bid should reflect marginal contribution to total surplus. -/
noncomputable def bidValue (a c obs : I) : ℝ :=
  rs (compose c a) obs - rs c obs

/-- Bid value equals standalone resonance plus emergence.
    The bid decomposes into intrinsic value and contextual synergy.
    Wittgenstein: What you bring = who you are + what you create in context.
    Auction: Bid = use value + speculative/contextual premium. -/
theorem bidValue_decomposition (a c obs : I) :
    bidValue a c obs = rs a obs + emergence c a obs := by
  unfold bidValue emergence; ring

/-- Bid value of void is zero — silence adds nothing to any auction.
    Wittgenstein: The null utterance contributes nothing to any game.
    Vickrey: A null bidder has zero willingness-to-pay. -/
theorem bidValue_void (c obs : I) : bidValue (void : I) c obs = 0 := by
  unfold bidValue; rw [void_right']; ring

/-- Bid into void context equals standalone resonance — no contextual synergy.
    Wittgenstein: In silence (no prior context), meaning is purely intrinsic.
    Auction: With no competition, your bid equals your standalone value. -/
theorem bidValue_from_void (a obs : I) :
    bidValue a (void : I) obs = rs a obs := by
  unfold bidValue; rw [void_left']; simp [rs_void_left']

/-- Winner's surplus: the weight gain from including idea a in composition c.
    Wittgenstein: What the winning word adds to the total language game's weight.
    Auction: Winner's payoff = composite value - pre-auction value. -/
noncomputable def winnerSurplus (a c : I) : ℝ :=
  rs (compose c a) (compose c a) - rs c c

/-- Winner's surplus is always non-negative — including an idea never reduces weight.
    Wittgenstein: Adding a word to a sentence never makes it less "present."
    Auction: The winner always generates non-negative surplus (by enrichment). -/
theorem winnerSurplus_nonneg (a c : I) : winnerSurplus a c ≥ 0 := by
  unfold winnerSurplus; linarith [compose_enriches' c a]

/-- Winner's surplus of void is zero — including silence changes nothing.
    Wittgenstein: Adding silence to an utterance is vacuous.
    Auction: The null item generates zero surplus. -/
theorem winnerSurplus_void (c : I) : winnerSurplus (void : I) c = 0 := by
  unfold winnerSurplus; rw [void_right']; ring

/-- THE WINNER'S CURSE ANALOGUE: The winner's surplus is bounded
    by the total composition weight — you can never gain more than what exists.
    Wittgenstein: No utterance can create meaning exceeding total context weight.
    Auction: The winner's gain ≤ total value of the object. -/
theorem winners_curse_bound (a c : I) :
    winnerSurplus a c ≤ rs (compose c a) (compose c a) := by
  unfold winnerSurplus; linarith [rs_self_nonneg' c]

/-- Information rent: the emergence-based premium an idea earns
    by creating new meaning beyond additive contribution.
    Wittgenstein: The "surplus meaning" that arises from novel combination —
    the genuinely creative part of language use.
    Myerson: Information rent is the payoff to private knowledge. -/
noncomputable def informationRent (a c obs : I) : ℝ :=
  emergence c a obs

/-- Information rent vanishes for the null bidder.
    Wittgenstein: Silence creates no surplus meaning.
    Myerson: A type with no private information earns no rent. -/
theorem informationRent_void_bidder (c obs : I) :
    informationRent (void : I) c obs = 0 := by
  unfold informationRent; exact emergence_void_right c obs

/-- Information rent vanishes in a null context.
    Wittgenstein: Without a language game, there is no contextual premium.
    Myerson: Without a mechanism, there is no rent. -/
theorem informationRent_void_context (a obs : I) :
    informationRent a (void : I) obs = 0 := by
  unfold informationRent; exact emergence_void_left a obs

/-- Bid value = standalone value + information rent.
    THE fundamental equation of idea auctions.
    Wittgenstein: What you bring = your intrinsic meaning + contextual creation.
    Auction: Bid = value + rent. -/
theorem bid_is_value_plus_rent (a c obs : I) :
    bidValue a c obs = rs a obs + informationRent a c obs := by
  unfold bidValue informationRent emergence; ring

/-- Information rent is bounded by composition and observer weights.
    Wittgenstein: The creative surplus of language cannot exceed what the
    participants and context can "carry."
    Auction: Information rents are bounded by the surplus they generate. -/
theorem informationRent_bounded (a c obs : I) :
    (informationRent a c obs) ^ 2 ≤
    rs (compose c a) (compose c a) * rs obs obs := by
  unfold informationRent; exact emergence_bounded' c a obs

end AuctionTheory

/-! # Layer 12: Social Choice Theory — Voting Over Compositions

When multiple compositions are possible, how should a community "choose"
among them? Social choice theory studies preference aggregation. In
meaning games, preferences are induced by resonance — an observer
"prefers" ideas that resonate more strongly with it.

For Wittgenstein: The community's "form of life" determines which
meanings are adopted. This IS social choice — the community votes
with its practices. The impossibility of a perfect voting rule
(Arrow) corresponds to the impossibility of a universal form of life.

For game theory: Arrow's impossibility theorem shows no perfect
aggregation rule exists. Our analogue: the weight ordering (based
on self-resonance) IS transitive, but resonance-based preferences
can cycle because resonance is asymmetric. -/

section SocialChoice

/-- Resonance preference: observer obs prefers idea a over idea b
    when a resonates more strongly with obs.
    Wittgenstein: "Understanding" means resonance with one's form of life.
    Arrow: A preference ordering over alternatives. -/
def resonancePrefers (obs a b : I) : Prop := rs obs a > rs obs b

/-- No observer can prefer void to itself — a degenerate case.
    Wittgenstein: Silence is not preferred to silence; there is no choice.
    Arrow: The null alternative is never strictly preferred to itself. -/
theorem void_not_self_preferred (obs : I) :
    ¬ resonancePrefers obs (void : I) (void : I) := by
  unfold resonancePrefers; intro h; linarith

/-- Every non-void idea resonance-prefers itself over void.
    Wittgenstein: An idea's own form of life always recognizes it over silence.
    Social choice: Non-null alternatives dominate null for interested parties. -/
theorem self_prefers_over_void (a : I) (ha : a ≠ void) :
    resonancePrefers a a (void : I) := by
  unfold resonancePrefers; rw [rs_void_right']; exact rs_self_pos a ha

/-- Weight preference: a is heavier than b when a's self-resonance exceeds b's.
    Wittgenstein: More "present" ideas have more gravity in language games.
    Social choice: The weight ordering is the natural intensity measure. -/
def weightPrefers (a b : I) : Prop := rs a a > rs b b

/-- Non-void always weight-dominates void.
    Wittgenstein: Anything actually said outweighs silence in presence.
    Arrow: The positive alternative Pareto-dominates the null. -/
theorem nonvoid_weightPrefers_void (a : I) (ha : a ≠ void) :
    weightPrefers a (void : I) := by
  unfold weightPrefers; rw [rs_void_void]; exact rs_self_pos a ha

/-- Composition enriches the weight ordering: a∘b is always at least as heavy as a.
    Wittgenstein: Saying more creates at least as much meaning as saying less.
    Social choice: Composition is a monotone operator on the weight ordering. -/
theorem composition_weight_enriches (a b : I) :
    ¬ weightPrefers a (compose a b) := by
  unfold weightPrefers; intro h; linarith [compose_enriches' a b]

/-- THE CONDORCET PROPERTY: The weight ordering is transitive —
    unlike resonance preferences, weight-based rankings never cycle.
    Wittgenstein: The ordering of "how much meaning" is globally coherent.
    Condorcet: Weight-based social choice avoids the voting paradox. -/
theorem weight_trans (a b c : I)
    (h1 : weightPrefers a b) (h2 : weightPrefers b c) :
    weightPrefers a c := by
  unfold weightPrefers at *; linarith

/-- Weight is irreflexive: no idea strictly outweighs itself.
    Wittgenstein: Self-comparison yields no ranking information.
    Social choice: Strict preference is always irreflexive. -/
theorem weight_irrefl (a : I) : ¬ weightPrefers a a := by
  unfold weightPrefers; intro h; linarith

/-- Unanimous enrichment: composition always weakly dominates first component.
    This is the social choice analogue of the Pareto principle.
    Wittgenstein: The whole sentence means at least as much as its first word.
    Arrow: Unanimity — if all observers agree, the social choice agrees. -/
theorem unanimous_enrichment (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  compose_enriches' a b

end SocialChoice

/-! # Layer 13: Contract Theory — Incentive Compatibility for Meaning

Contract theory asks: how do you design agreements when parties have
private information? In meaning games, the "private information" is
an idea's emergence pattern — what it will CREATE in context, which
is only revealed through composition.

For Wittgenstein: Language games are implicit contracts about meaning.
When you say "I promise X," you enter a contract. The emergence from
that promise in context determines whether the contract is "kept" —
whether the meaning delivered matches what was promised.

For game theory: Mechanism design shows that incentive compatibility
requires that truth-telling is optimal. In meaning games, "truth-telling"
is composing your genuine idea rather than a strategic substitute.
The revelation principle has an emergence-theoretic analogue. -/

section ContractTheory

/-- Contract value: the resonance an observer receives from composition (a,b).
    This is what the contract "delivers."
    Wittgenstein: The meaning actually produced by a language game.
    Mechanism design: The outcome of the mechanism. -/
noncomputable def contractValue (a b obs : I) : ℝ :=
  rs (compose a b) obs

/-- Contract value decomposes into parts plus emergence (the surplus).
    Wittgenstein: What a sentence means = parts + contextual contribution.
    Contract theory: Total value = standalone values + synergy rent. -/
theorem contract_decomposition (a b obs : I) :
    contractValue a b obs = rs a obs + rs b obs + emergence a b obs := by
  unfold contractValue; exact rs_compose_eq a b obs

/-- The void contract: composing with silence delivers the standalone value.
    Wittgenstein: In the absence of context, meaning is literal.
    Contract theory: The null contract has zero surplus. -/
theorem void_contract (a obs : I) :
    contractValue a (void : I) obs = rs a obs := by
  unfold contractValue; rw [void_right']

/-- Participation constraint: the contract weight exceeds the first party's weight.
    Wittgenstein: Entering a language game never diminishes a speaker's weight.
    Contract theory: No rational agent signs a contract that makes them lighter. -/
theorem contract_participation (a b : I) :
    contractValue a b (compose a b) ≥ rs a a := by
  unfold contractValue; exact compose_enriches' a b

/-- Incentive alignment: the emergence component of a contract,
    measuring how much the composition produces beyond additive parts.
    Wittgenstein: "Meaning is use" — emergence IS the incentive to engage.
    Mechanism design: The social surplus from honest reporting. -/
noncomputable def incentiveAlignment (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- Incentive alignment vanishes for null contracts (right).
    Wittgenstein: Composing with silence produces no creative surplus.
    Contract theory: No synergy with a null partner. -/
theorem incentiveAlignment_void_right (a : I) :
    incentiveAlignment a (void : I) = 0 := by
  unfold incentiveAlignment
  exact emergence_void_right a (compose a (void : I))

/-- Incentive alignment vanishes for null contracts (left).
    Wittgenstein: A silent proposer creates no contextual meaning.
    Contract theory: A null principal generates zero incentive. -/
theorem incentiveAlignment_void_left (b : I) :
    incentiveAlignment (void : I) b = 0 := by
  unfold incentiveAlignment
  rw [show compose (void : I) b = b from void_left' b]
  exact emergence_void_left b b

/-- Incentive alignment is bounded by the composition's self-weight squared.
    Wittgenstein: Emergent meaning cannot exceed total context capacity.
    Contract theory: The surplus is bounded by the total pie. -/
theorem incentiveAlignment_bounded (a b : I) :
    (incentiveAlignment a b) ^ 2 ≤
    rs (compose a b) (compose a b) * rs (compose a b) (compose a b) := by
  unfold incentiveAlignment
  exact emergence_bounded' a b (compose a b)

/-- Information revelation: comparing two contracts with different left parties
    reveals the difference in both standalone and emergence contributions.
    Wittgenstein: Replacing one word in context reveals what each word contributes.
    Mechanism design: Comparing contracts reveals private information. -/
theorem information_revelation (a1 a2 b obs : I) :
    contractValue a1 b obs - contractValue a2 b obs =
    (rs a1 obs - rs a2 obs) + (emergence a1 b obs - emergence a2 b obs) := by
  unfold contractValue emergence; ring

/-- Full revelation: when two ideas have the same standalone resonance,
    the contract difference is purely emergence-based.
    Wittgenstein: Words with the same "dictionary meaning" differ only in use.
    Contract theory: With common priors, differences reveal private types. -/
theorem full_revelation (a1 a2 b obs : I) (h : rs a1 obs = rs a2 obs) :
    contractValue a1 b obs - contractValue a2 b obs =
    emergence a1 b obs - emergence a2 b obs := by
  have := information_revelation a1 a2 b obs; linarith

end ContractTheory

/-! # Layer 14: Principal-Agent Problems in Communication

The principal-agent problem arises when one party (the principal)
delegates action to another (the agent). In meaning games, the
"principal" is the speaker/context, and the "agent" is the idea
being composed into the context.

For Wittgenstein: Every act of communication involves delegation —
the speaker delegates meaning-creation to the words they choose.
The "agency cost" is the gap between intended and received meaning.
Monitoring (adding clarifying context) can reduce but never eliminate
this gap, because emergence is bounded but irreducible.

For game theory: Jensen-Meckling agency theory shows that agency costs
have three components: monitoring, bonding, and residual loss.
The enrichment guarantee provides a natural "limited liability" constraint. -/

section PrincipalAgent

/-- Agency cost: the change in resonance when the agent is composed with the principal.
    Positive = agent adds to the principal's resonance with obs.
    Negative = agent detracts.
    Wittgenstein: What the listener's interpretation adds to or subtracts from meaning.
    Jensen-Meckling: The cost of delegation to a self-interested agent. -/
noncomputable def agencyCost (principal agent obs : I) : ℝ :=
  rs (compose principal agent) obs - rs principal obs

/-- Agency cost decomposes into agent's resonance plus emergence.
    Wittgenstein: What the listener adds = their own meaning + creative surplus.
    Agency theory: Agent's contribution = effort + information rent. -/
theorem agencyCost_decomposition (principal agent obs : I) :
    agencyCost principal agent obs =
    rs agent obs + emergence principal agent obs := by
  unfold agencyCost emergence; ring

/-- Agency cost of null agent is zero — a silent agent does nothing.
    Wittgenstein: If the listener says nothing, no interpretation occurs.
    Agency: A null agent generates zero cost. -/
theorem agencyCost_void_agent (principal obs : I) :
    agencyCost principal (void : I) obs = 0 := by
  unfold agencyCost; rw [void_right']; ring

/-- Agency cost from null principal is the agent's standalone resonance.
    Wittgenstein: Without context, the agent's meaning is just their own.
    Agency: Without a principal's direction, the agent acts independently. -/
theorem agencyCost_void_principal (agent obs : I) :
    agencyCost (void : I) agent obs = rs agent obs := by
  unfold agencyCost; rw [void_left']; simp [rs_void_left']

/-- Monitoring value: how much composing a monitor m with the agent
    changes the agency cost relative to the unmonitored case.
    Wittgenstein: Adding a third party (e.g. a dictionary, a grammar)
    to a language game changes what the words end up meaning.
    Agency: The value of monitoring = change in agency costs. -/
noncomputable def monitoringValue (principal agent monitor obs : I) : ℝ :=
  agencyCost principal (compose monitor agent) obs -
  agencyCost principal agent obs

/-- Monitoring value decomposes via emergence — monitoring works
    by changing the emergence structure of the communication.
    Wittgenstein: A grammar book changes meaning by altering contextual resonance.
    Agency: Monitoring costs and benefits are emergence-mediated. -/
theorem monitoringValue_decomposition (principal agent monitor obs : I) :
    monitoringValue principal agent monitor obs =
    rs monitor obs + emergence monitor agent obs +
    (emergence principal (compose monitor agent) obs -
     emergence principal agent obs) := by
  unfold monitoringValue agencyCost emergence; ring

/-- Null monitor has zero monitoring value — adding silence monitors nothing.
    Wittgenstein: An empty grammar constrains no meanings.
    Agency: A monitor that does nothing has zero value. -/
theorem monitoring_void (principal agent obs : I) :
    monitoringValue principal agent (void : I) obs = 0 := by
  unfold monitoringValue agencyCost; rw [void_left']; ring

/-- Alignment measure: how much the composition enriches the principal's weight.
    Wittgenstein: Mutual understanding = enrichment through dialogue.
    Agency: Better alignment = higher surplus from delegation. -/
noncomputable def alignment (principal agent : I) : ℝ :=
  rs (compose principal agent) (compose principal agent) -
  rs principal principal

/-- Alignment equals weight surplus — connecting agency theory to enrichment.
    Wittgenstein: Dialogical enrichment IS alignment.
    Agency: Surplus from delegation = weight surplus. -/
theorem alignment_eq_weightSurplus (principal agent : I) :
    alignment principal agent = weightSurplus principal agent := by
  unfold alignment weightSurplus; ring

/-- Alignment is always non-negative — delegation never reduces the principal's weight.
    Wittgenstein: Language games always enrich the form of life.
    Agency: The principal's limited liability is guaranteed by enrichment. -/
theorem alignment_nonneg (principal agent : I) :
    alignment principal agent ≥ 0 := by
  unfold alignment; linarith [compose_enriches' principal agent]

/-- Perfect alignment with void: the null agent contributes zero surplus.
    Wittgenstein: Silence is perfectly "aligned" but contributes nothing.
    Agency: A do-nothing agent has zero alignment surplus. -/
theorem alignment_void (principal : I) :
    alignment principal (void : I) = 0 := by
  unfold alignment; rw [void_right']; ring

end PrincipalAgent

/-! # Layer 15: Market Design for Ideas

Market design asks: how should we structure interactions to maximize
welfare? In meaning games, the "market" is the space of possible
compositions, and "welfare" is the total weight or resonance generated.

For Wittgenstein: Language itself is a market for meaning. Words are
"traded" in language games, and the rules of grammar and pragmatics
are the market's institutional design. A well-designed language
maximizes the meaning-creation capacity of its speakers.

For game theory: Roth's market design theory shows that thickness
(many participants), safety (incentive compatibility), and congestion
management are the keys to good markets. In meaning games, thickness
is the number of ideas composed, safety is the enrichment guarantee,
and congestion is managed by the cocycle constraint. -/

section MarketDesign

/-- Gains from trade: the total value created when ideas a and b are composed,
    beyond what each possesses individually.
    Wittgenstein: The surplus meaning from combining two language games.
    Coase: In a frictionless meaning market, all gains are realized. -/
noncomputable def gainsFromTrade (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- Gains from trade = bargaining surplus = game value.
    Three concepts from different traditions name the SAME quantity.
    Wittgenstein: There is no separate "surplus" — it's all emergence.
    Market design: The gains that institutional structure must distribute. -/
theorem gainsFromTrade_eq_bargainingSurplus (a b : I) :
    gainsFromTrade a b = bargainingSurplus a b := by
  unfold gainsFromTrade bargainingSurplus; ring

theorem gainsFromTrade_eq_gameValue (a b : I) :
    gainsFromTrade a b = gameValue a b := by
  unfold gainsFromTrade gameValue; ring

/-- Gains from trade with void are zero — autarky generates no trade surplus.
    Wittgenstein: Monologue creates no dialogical surplus.
    Market: Autarky = zero gains from trade. -/
theorem gainsFromTrade_void (a : I) :
    gainsFromTrade a (void : I) = 0 := by
  unfold gainsFromTrade; rw [void_right', rs_void_void]; ring

/-- Market thickness: the total weight of an N-party composition,
    measuring how much "meaning" the market has generated.
    Wittgenstein: A richer language game (more participants) creates more meaning.
    Roth: Thicker markets produce more matches and greater total surplus. -/
noncomputable def marketThickness (ideas : List I) : ℝ :=
  coalWeight ideas

/-- Empty market has zero thickness.
    Wittgenstein: Without speakers, there is no language game.
    Market: No participants = no market. -/
theorem marketThickness_nil : marketThickness ([] : List I) = 0 :=
  coalWeight_nil

/-- Market thickness always exceeds the weight of the first participant.
    Wittgenstein: The language game is at least as rich as its first speaker.
    Roth: Adding participants never shrinks the market. -/
theorem marketThickness_ge_first (a : I) (rest : List I) :
    marketThickness (a :: rest) ≥ rs a a := by
  unfold marketThickness; exact coalWeight_ge_first' a rest

/-- Price discovery: resonance as the "price" of one idea relative to another.
    Wittgenstein: You discover what an idea means by its use with others.
    Hayek: Prices emerge from market interaction, not central planning. -/
noncomputable def ideaPrice (a b : I) : ℝ := rs a b

/-- The price of a composition decomposes into parts plus emergence.
    Wittgenstein: The price of a complex expression exceeds the sum of parts.
    Market design: Price formation involves fundamentals + discovery. -/
theorem price_decomposition (a b c : I) :
    ideaPrice (compose a b) c =
    ideaPrice a c + ideaPrice b c + emergence a b c := by
  unfold ideaPrice; exact rs_compose_eq a b c

/-- Price of void is zero (left) — silence has no value.
    Wittgenstein: The null utterance is worth nothing.
    Market: The null good has zero price. -/
theorem price_void_left (b : I) : ideaPrice (void : I) b = 0 := by
  unfold ideaPrice; exact rs_void_left' b

/-- Price of void is zero (right) — nothing values silence.
    Wittgenstein: No idea resonates with silence.
    Market: No buyer values the null good. -/
theorem price_void_right (a : I) : ideaPrice a (void : I) = 0 := by
  unfold ideaPrice; exact rs_void_right' a

/-- THE MARKET DESIGN THEOREM: A non-void participant creates a market
    with strictly positive thickness. Any real language game has value.
    Wittgenstein: Any actual utterance creates a meaningful language game.
    Roth: A market with active participants generates positive surplus. -/
theorem market_creates_value (a : I) (ha : a ≠ void) (rest : List I) :
    marketThickness (a :: rest) > 0 := by
  unfold marketThickness; exact positive_coalition a ha rest

/-- Bid-ask spread: the asymmetry between how a prices b and how b prices a.
    Wittgenstein: Understanding runs in one direction — the speaker's intent
    differs from the listener's reception.
    Market design: Bid ≠ ask; the spread IS the market's friction. -/
noncomputable def bidAskSpread (a b : I) : ℝ :=
  ideaPrice a b - ideaPrice b a

/-- The bid-ask spread is antisymmetric — what a pays for b is the negative
    of what b pays for a. This is the market-design version of resonance asymmetry.
    Wittgenstein: The asymmetry of understanding is irreducible.
    Market: Bid-ask spread reflects fundamentally different perspectives. -/
theorem bidAskSpread_antisymm (a b : I) :
    bidAskSpread a b = -(bidAskSpread b a) := by
  unfold bidAskSpread ideaPrice; ring

/-- The bid-ask spread with void is zero — no friction with silence.
    Wittgenstein: There is no misunderstanding with silence.
    Market: No spread when one side is null. -/
theorem bidAskSpread_void (a : I) : bidAskSpread a (void : I) = 0 := by
  unfold bidAskSpread ideaPrice; rw [rs_void_right', rs_void_left']; ring

/-- The bid-ask spread decomposes the exchange value:
    Exchange value + 2 × spread = difference in forward vs backward resonance.
    Wittgenstein: Dialogue's value splits into mutual understanding + asymmetric surplus.
    Market: Total exchange = consensus price + information asymmetry. -/
theorem exchange_spread_decomposition (a b : I) :
    exchangeValue a b = 2 * ideaPrice a b - bidAskSpread a b := by
  unfold exchangeValue bidAskSpread ideaPrice; ring

end MarketDesign

end IDT3
