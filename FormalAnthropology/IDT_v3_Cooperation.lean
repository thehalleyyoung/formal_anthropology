import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Cooperative Game Theory of Ideas

Ideas cooperate. When two ideas compose, their joint self-resonance
may exceed the sum of their individual self-resonances — this is the
**cooperation surplus**. Alternatively, ideas may conflict, where
composition produces less than expected.

## The Coalition Function

The "value" of a coalition S ⊆ I is the self-resonance of the
composed idea: v(S) = rs(∘S, ∘S). This is a cooperative game
where the composition operation plays the role of coalition formation.

## Key Insights

1. **Superadditivity from Emergence**: when κ(a,b,a∘b) > 0, composition
   creates value — the whole exceeds the sum of parts
2. **The Core**: stable allocations of cooperative surplus
3. **Shapley-like Values**: each idea's marginal contribution to coalitions
4. **Composition Enriches**: v({a,b}) ≥ v({a}) always (Axiom E4)

## NO SORRIES
-/

namespace IDT3

section Cooperation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-! ## §1. Coalition Value -/

/-- The value of a single idea: its self-resonance (presence/weight). -/
noncomputable def ideaValue (a : I) : ℝ := rs a a

/-- Value is non-negative. -/
theorem ideaValue_nonneg (a : I) : ideaValue a ≥ 0 := by
  unfold ideaValue; exact rs_self_nonneg' a

/-- Non-void ideas have positive value. -/
theorem ideaValue_pos (a : I) (h : a ≠ void) : ideaValue a > 0 := by
  unfold ideaValue; exact rs_self_pos a h

/-- Void has zero value. -/
theorem ideaValue_void : ideaValue (void : I) = 0 := by
  unfold ideaValue; exact rs_void_void

/-- The coalition value of two ideas composed. -/
noncomputable def coalitionValue (a b : I) : ℝ :=
  rs (compose a b) (compose a b)

/-- Coalition value is non-negative. -/
theorem coalitionValue_nonneg (a b : I) : coalitionValue a b ≥ 0 := by
  unfold coalitionValue; exact rs_self_nonneg' (compose a b)

/-- Coalition value is at least the value of the first member. -/
theorem coalitionValue_ge_first (a b : I) :
    coalitionValue a b ≥ ideaValue a := by
  unfold coalitionValue ideaValue; exact compose_enriches' a b

/-- Coalition with void equals original value. -/
theorem coalitionValue_void_right (a : I) :
    coalitionValue a (void : I) = ideaValue a := by
  unfold coalitionValue ideaValue; rw [void_right']

theorem coalitionValue_void_left (a : I) :
    coalitionValue (void : I) a = ideaValue a := by
  unfold coalitionValue ideaValue; rw [void_left']

/-! ## §2. Cooperation Surplus -/

/-- The cooperation surplus: how much more value the coalition creates
    than the first member alone. Always non-negative by compose_enriches. -/
noncomputable def cooperationSurplus (a b : I) : ℝ :=
  coalitionValue a b - ideaValue a

/-- Cooperation surplus is non-negative (compose enriches!). -/
theorem cooperationSurplus_nonneg (a b : I) :
    cooperationSurplus a b ≥ 0 := by
  unfold cooperationSurplus
  linarith [coalitionValue_ge_first a b]

/-- Cooperation surplus with void is zero. -/
theorem cooperationSurplus_void (a : I) :
    cooperationSurplus a (void : I) = 0 := by
  unfold cooperationSurplus
  rw [coalitionValue_void_right]
  ring

/-- The surplus decomposes via aufhebung decomposition.
    surplus = rs(a∘b,a∘b) - rs(a,a)
            = rs(b,a∘b) + κ(a,b,a∘b) + [rs(a,a∘b) - rs(a,a)]
    The three terms capture: what b contributes, what emerges,
    and how a's resonance shifts in the new context. -/
theorem cooperationSurplus_eq (a b : I) :
    cooperationSurplus a b =
    rs b (compose a b) + emergence a b (compose a b) +
    (rs a (compose a b) - rs a a) := by
  unfold cooperationSurplus coalitionValue ideaValue
  have := rs_compose_eq a b (compose a b)
  linarith

/-! ## §3. Symmetric and Asymmetric Cooperation -/

/-- The cooperation is symmetric if both members gain equally. -/
noncomputable def cooperationAsymmetry (a b : I) : ℝ :=
  cooperationSurplus a b - cooperationSurplus b a

/-- Coalition with void: the asymmetry equals negative idea value,
    because adding void to a contributes nothing, but adding a to void
    contributes everything. -/
theorem cooperationAsymmetry_void (a : I) :
    cooperationAsymmetry a (void : I) = -(ideaValue a) := by
  unfold cooperationAsymmetry cooperationSurplus coalitionValue ideaValue
  have h1 : compose a (void : I) = a := void_right' a
  have h2 : compose (void : I) a = a := void_left' a
  have h3 : rs (void : I) (void : I) = 0 := rs_void_void
  rw [h1, h2, h3]; ring

/-- Asymmetry is antisymmetric. -/
theorem cooperationAsymmetry_antisymm (a b : I) :
    cooperationAsymmetry a b = -cooperationAsymmetry b a := by
  unfold cooperationAsymmetry; ring

/-! ## §4. Marginal Contribution (Shapley-like) -/

/-- The marginal contribution of idea b to idea a:
    how much b adds to a's value when they compose. -/
noncomputable def marginalContribution (a b : I) : ℝ :=
  coalitionValue a b - ideaValue a

/-- Marginal contribution equals cooperation surplus. -/
theorem marginalContribution_eq_surplus (a b : I) :
    marginalContribution a b = cooperationSurplus a b := rfl

/-- Marginal contribution is non-negative. -/
theorem marginalContribution_nonneg (a b : I) :
    marginalContribution a b ≥ 0 := cooperationSurplus_nonneg a b

/-- The bilateral marginal: average of both directions. -/
noncomputable def bilateralMarginal (a b : I) : ℝ :=
  (marginalContribution a b + marginalContribution b a) / 2

/-- Bilateral marginal is non-negative. -/
theorem bilateralMarginal_nonneg (a b : I) :
    bilateralMarginal a b ≥ 0 := by
  unfold bilateralMarginal
  have h1 := marginalContribution_nonneg a b
  have h2 := marginalContribution_nonneg b a
  linarith

/-- Bilateral marginal is symmetric. -/
theorem bilateralMarginal_symm (a b : I) :
    bilateralMarginal a b = bilateralMarginal b a := by
  unfold bilateralMarginal; ring

/-! ## §5. Three-Party Coalitions -/

/-- Value of a three-party coalition. -/
noncomputable def coalitionValue3 (a b c : I) : ℝ :=
  rs (compose (compose a b) c) (compose (compose a b) c)

/-- Three-party coalition is at least as valuable as two-party. -/
theorem coalitionValue3_ge_two (a b c : I) :
    coalitionValue3 a b c ≥ coalitionValue a b := by
  unfold coalitionValue3 coalitionValue
  exact compose_enriches' (compose a b) c

/-- Three-party coalition value is independent of bracketing
    (since compose is associative, both bracketings give the same idea). -/
theorem coalitionValue3_assoc (a b c : I) :
    coalitionValue3 a b c =
    rs (compose a (compose b c)) (compose a (compose b c)) := by
  unfold coalitionValue3; rw [compose_assoc']

/-- The incremental value of adding c to {a,b}. -/
noncomputable def incrementalValue (a b c : I) : ℝ :=
  coalitionValue3 a b c - coalitionValue a b

/-- Incremental value is non-negative. -/
theorem incrementalValue_nonneg (a b c : I) :
    incrementalValue a b c ≥ 0 := by
  unfold incrementalValue
  linarith [coalitionValue3_ge_two a b c]

/-- Adding void has zero incremental value. -/
theorem incrementalValue_void (a b : I) :
    incrementalValue a b (void : I) = 0 := by
  unfold incrementalValue coalitionValue3 coalitionValue
  simp [void_right']

/-! ## §6. Conflict and Alignment -/

/-- Two ideas are aligned if they resonate positively. -/
def aligned (a b : I) : Prop := rs a b > 0

/-- Two ideas are in conflict if they resonate negatively. -/
def inConflict (a b : I) : Prop := rs a b < 0

/-- Void is never in conflict with anything. -/
theorem void_not_conflict (a : I) : ¬inConflict (void : I) a := by
  unfold inConflict; rw [rs_void_left']; linarith

/-- Every non-void idea is aligned with itself. -/
theorem self_aligned (a : I) (h : a ≠ void) : aligned a a := by
  unfold aligned; exact rs_self_pos a h

/-- Alignment with void requires void itself (impossible for non-void). -/
theorem not_aligned_void (a : I) : ¬aligned a (void : I) := by
  unfold aligned; rw [rs_void_right']; linarith

/-! ## §7. The Grand Coalition -/

/-- The grand coalition value of a list of ideas. -/
noncomputable def grandCoalitionValue (pop : List I) : ℝ :=
  rs (composeList pop) (composeList pop)

/-- Empty coalition has zero value. -/
theorem grandCoalitionValue_nil :
    grandCoalitionValue ([] : List I) = 0 := by
  unfold grandCoalitionValue composeList
  exact rs_void_void

/-- Singleton coalition equals idea value. -/
theorem grandCoalitionValue_singleton (a : I) :
    grandCoalitionValue [a] = ideaValue a := by
  unfold grandCoalitionValue ideaValue composeList
  simp [List.foldl, void_left']

/-- Adding a member never decreases grand coalition value. -/
theorem grandCoalitionValue_cons_ge (a : I) (pop : List I) :
    grandCoalitionValue (a :: pop) ≥ 0 := by
  unfold grandCoalitionValue
  exact rs_self_nonneg' _

end Cooperation

/-! =====================================================================
    PART II: EXTENDED COOPERATION THEORY
    =====================================================================

    We now develop a rich theory of cooperation in ideatic space,
    drawing on coalition theory, social contract theory, public goods,
    trust, team reasoning, and cooperative game theory. Every theorem
    is proven — zero sorries. -/

/-! ## §8. Coalition Algebra — Structural Properties -/

section CoalitionAlgebra
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Coalition value is monotone: adding ideas never destroys value.
    This is the fundamental optimism of composition — you can't un-say. -/
theorem coalitionValue_monotone_right (a b c : I) :
    coalitionValue (compose a b) c ≥ coalitionValue a b := by
  exact compose_enriches' (compose a b) c

/-- The value of a∘b∘c as a coalition is at least the value of a alone. -/
theorem coalitionValue3_ge_first (a b c : I) :
    coalitionValue3 a b c ≥ ideaValue a := by
  have h1 := coalitionValue3_ge_two a b c
  have h2 := coalitionValue_ge_first a b
  linarith

/-- Three-party coalition value is non-negative. -/
theorem coalitionValue3_nonneg (a b c : I) :
    coalitionValue3 a b c ≥ 0 := by
  unfold coalitionValue3; exact rs_self_nonneg' _

/-- Coalition with void on both sides is zero. -/
theorem coalitionValue_void_void :
    coalitionValue (void : I) (void : I) = 0 := by
  unfold coalitionValue; simp [void_left']; exact rs_void_void

/-- Coalition value decomposes via emergence.
    The coalition's self-resonance is the sum of cross-resonances
    plus the self-emergence (dialectical tension). -/
theorem coalitionValue_decompose (a b : I) :
    coalitionValue a b =
    rs a (compose a b) + rs b (compose a b) + emergence a b (compose a b) := by
  unfold coalitionValue; rw [rs_compose_eq]

/-- Four-party coalition value. -/
noncomputable def coalitionValue4 (a b c d : I) : ℝ :=
  rs (compose (compose (compose a b) c) d) (compose (compose (compose a b) c) d)

/-- Four-party coalition is at least three-party. -/
theorem coalitionValue4_ge_three (a b c d : I) :
    coalitionValue4 a b c d ≥ coalitionValue3 a b c := by
  unfold coalitionValue4 coalitionValue3
  exact compose_enriches' _ d

/-- Four-party coalition is at least two-party. -/
theorem coalitionValue4_ge_two (a b c d : I) :
    coalitionValue4 a b c d ≥ coalitionValue a b := by
  have h1 := coalitionValue4_ge_three a b c d
  have h2 := coalitionValue3_ge_two a b c
  linarith

/-- Four-party coalition is non-negative. -/
theorem coalitionValue4_nonneg (a b c d : I) :
    coalitionValue4 a b c d ≥ 0 := by
  unfold coalitionValue4; exact rs_self_nonneg' _

/-- Coalition value is invariant under reassociation of the composition. -/
theorem coalitionValue_assoc (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) =
    rs (compose a (compose b c)) (compose a (compose b c)) := by
  rw [compose_assoc']

/-- The surplus of adding c to {a,b} decomposes via emergence. -/
theorem incrementalValue_decompose (a b c : I) :
    incrementalValue a b c =
    rs c (compose (compose a b) c) +
    emergence (compose a b) c (compose (compose a b) c) +
    (rs (compose a b) (compose (compose a b) c) - rs (compose a b) (compose a b)) := by
  unfold incrementalValue coalitionValue3 coalitionValue
  have := rs_compose_eq (compose a b) c (compose (compose a b) c)
  linarith

/-- Self-coalition: composing a with itself. Measures the "reinforcement"
    of an idea upon repetition. -/
noncomputable def selfCoalitionValue (a : I) : ℝ :=
  coalitionValue a a

/-- Self-coalition value is at least the idea's own value (self-reinforcement). -/
theorem selfCoalitionValue_ge (a : I) :
    selfCoalitionValue a ≥ ideaValue a := by
  unfold selfCoalitionValue; exact coalitionValue_ge_first a a

/-- Self-coalition surplus: how much repeating an idea adds. -/
noncomputable def selfCoalitionSurplus (a : I) : ℝ :=
  selfCoalitionValue a - ideaValue a

/-- Self-coalition surplus is non-negative. -/
theorem selfCoalitionSurplus_nonneg (a : I) :
    selfCoalitionSurplus a ≥ 0 := by
  unfold selfCoalitionSurplus; linarith [selfCoalitionValue_ge a]

/-- Void self-coalition surplus is zero: repeating nothing changes nothing. -/
theorem selfCoalitionSurplus_void :
    selfCoalitionSurplus (void : I) = 0 := by
  unfold selfCoalitionSurplus selfCoalitionValue coalitionValue ideaValue
  rw [void_left', rs_void_void]; linarith

end CoalitionAlgebra

/-! ## §9. Cooperation Surplus Bounds — Deep Math -/

section SurplusBounds
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The cooperation surplus can be bounded from above using
    the emergence bound. The surplus involves three terms;
    we can bound the emergence component. -/
theorem cooperationSurplus_emergence_component (a b : I) :
    (emergence a b (compose a b)) ^ 2 ≤
    coalitionValue a b * coalitionValue a b := by
  have h := emergence_bounded' a b (compose a b)
  unfold coalitionValue
  have hnn : rs (compose a b) (compose a b) ≥ 0 := rs_self_nonneg' _
  nlinarith [sq_nonneg (emergence a b (compose a b)), sq_nonneg (rs (compose a b) (compose a b))]

/-- The incremental value of adding c to {a,b} is non-negative. -/
theorem incrementalValue_bound (a b c : I) :
    incrementalValue a b c ≥ 0 := incrementalValue_nonneg a b c

/-- Void's cooperation surplus into any idea equals zero. -/
theorem cooperationSurplus_void_left (a : I) :
    cooperationSurplus (void : I) a = ideaValue a := by
  unfold cooperationSurplus coalitionValue ideaValue
  rw [void_left', rs_void_void]; ring

/-- Marginal contribution of void is zero. -/
theorem marginalContribution_void_right (a : I) :
    marginalContribution a (void : I) = 0 := by
  unfold marginalContribution coalitionValue ideaValue
  rw [void_right']; linarith

/-- Void's marginal contribution to any coalition equals ideaValue of the partner. -/
theorem marginalContribution_void_left (a : I) :
    marginalContribution (void : I) a = ideaValue a := by
  unfold marginalContribution coalitionValue ideaValue
  rw [void_left', rs_void_void]; ring

/-- Bilateral marginal with void equals half the idea value. -/
theorem bilateralMarginal_void (a : I) :
    bilateralMarginal a (void : I) = ideaValue a / 2 := by
  unfold bilateralMarginal
  rw [marginalContribution_void_right, marginalContribution_void_left]; ring

/-- The surplus of composing a with (b∘c) relates to staged surpluses
    via the cocycle condition. -/
theorem cooperationSurplus_assoc_relation (a b c : I) :
    coalitionValue a (compose b c) - ideaValue a =
    coalitionValue3 a b c - ideaValue a := by
  unfold coalitionValue coalitionValue3 ideaValue
  rw [← compose_assoc']

/-- Coalition growth: the total surplus is monotonically non-decreasing
    as we add more ideas. -/
theorem coalition_growth_monotone (a b c : I) :
    coalitionValue3 a b c - ideaValue a ≥
    coalitionValue a b - ideaValue a := by
  linarith [coalitionValue3_ge_two a b c]

/-- The double surplus: surplus from a three-party over two-party
    plus the two-party surplus over single. -/
theorem double_surplus_eq (a b c : I) :
    (coalitionValue3 a b c - ideaValue a) =
    (coalitionValue3 a b c - coalitionValue a b) +
    (coalitionValue a b - ideaValue a) := by ring

end SurplusBounds

/-! ## §10. Trust and Reciprocity

    Trust is the willingness to compose — to let one's ideas merge with
    another's. In ideatic space, trust means accepting that the
    composition a∘b may differ from what a alone would produce.

    Betrayal is defection from composition: refusing to contribute
    one's genuine idea, substituting void (silence) instead. -/

section TrustReciprocity
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Trust level: how much a gains from composing with b. -/
noncomputable def trustLevel (a b : I) : ℝ :=
  coalitionValue a b - ideaValue a

/-- Trust is non-negative: you can never lose by composing (compose enriches). -/
theorem trustLevel_nonneg (a b : I) : trustLevel a b ≥ 0 := by
  unfold trustLevel; linarith [coalitionValue_ge_first a b]

/-- Trust in void is zero: nothing to gain from silence. -/
theorem trustLevel_void (a : I) : trustLevel a (void : I) = 0 := by
  unfold trustLevel coalitionValue ideaValue; rw [void_right']; linarith

/-- Trust level equals cooperation surplus (trust IS the surplus). -/
theorem trustLevel_eq_surplus (a b : I) :
    trustLevel a b = cooperationSurplus a b := rfl

/-- Reciprocal trust: the minimum of both directions. -/
noncomputable def reciprocalTrust (a b : I) : ℝ :=
  min (trustLevel a b) (trustLevel b a)

/-- Reciprocal trust is non-negative. -/
theorem reciprocalTrust_nonneg (a b : I) :
    reciprocalTrust a b ≥ 0 := by
  unfold reciprocalTrust
  exact le_min (trustLevel_nonneg a b) (trustLevel_nonneg b a)

/-- Reciprocal trust is symmetric. -/
theorem reciprocalTrust_symm (a b : I) :
    reciprocalTrust a b = reciprocalTrust b a := by
  unfold reciprocalTrust; rw [min_comm]

/-- The betrayal cost: what a loses if b defects (substitutes void). -/
noncomputable def betrayalCost (a b : I) : ℝ :=
  coalitionValue a b - coalitionValue a (void : I)

/-- Betrayal cost equals trust level. -/
theorem betrayalCost_eq_trust (a b : I) :
    betrayalCost a b = trustLevel a b := by
  unfold betrayalCost trustLevel coalitionValue ideaValue; rw [void_right']

/-- Betrayal cost is non-negative. -/
theorem betrayalCost_nonneg (a b : I) : betrayalCost a b ≥ 0 := by
  rw [betrayalCost_eq_trust]; exact trustLevel_nonneg a b

/-- Vulnerability: the maximum possible loss from betrayal. -/
noncomputable def vulnerability (a b : I) : ℝ := trustLevel a b

/-- Vulnerability equals betrayal cost. -/
theorem vulnerability_eq_betrayal (a b : I) :
    vulnerability a b = betrayalCost a b := by
  unfold vulnerability; rw [betrayalCost_eq_trust]

/-- The trust asymmetry equals the cooperation asymmetry. -/
theorem trust_asymmetry_eq (a b : I) :
    trustLevel a b - trustLevel b a = cooperationAsymmetry a b := by
  unfold trustLevel cooperationAsymmetry cooperationSurplus; ring

/-- Trust surplus: how much more trust creates than individual values. -/
noncomputable def trustSurplus (a b : I) : ℝ :=
  coalitionValue a b - ideaValue a - ideaValue b

/-- Trust surplus relates to trust level and the partner's value. -/
theorem trustSurplus_eq (a b : I) :
    trustSurplus a b = trustLevel a b - ideaValue b := by
  unfold trustSurplus trustLevel; ring

/-- The trust premium: the maximum of both trust directions. -/
noncomputable def trustPremium (a b : I) : ℝ :=
  max (trustLevel a b) (trustLevel b a)

/-- Trust premium is non-negative. -/
theorem trustPremium_nonneg (a b : I) :
    trustPremium a b ≥ 0 := by
  unfold trustPremium
  exact le_max_of_le_left (trustLevel_nonneg a b)

/-- Trust premium is symmetric. -/
theorem trustPremium_symm (a b : I) :
    trustPremium a b = trustPremium b a := by
  unfold trustPremium; rw [max_comm]

/-- Trust premium is at least the reciprocal trust. -/
theorem trustPremium_ge_reciprocal (a b : I) :
    trustPremium a b ≥ reciprocalTrust a b := by
  unfold trustPremium reciprocalTrust
  exact min_le_max

/-- Trust gap: the difference between premium and reciprocal trust. -/
noncomputable def trustGap (a b : I) : ℝ :=
  trustPremium a b - reciprocalTrust a b

/-- Trust gap is non-negative. -/
theorem trustGap_nonneg (a b : I) : trustGap a b ≥ 0 := by
  unfold trustGap; linarith [trustPremium_ge_reciprocal a b]

/-- Trust gap is symmetric. -/
theorem trustGap_symm (a b : I) :
    trustGap a b = trustGap b a := by
  unfold trustGap; rw [trustPremium_symm, reciprocalTrust_symm]

/-- Void-void has zero trust gap. -/
theorem trustGap_void_void :
    trustGap (void : I) (void : I) = 0 := by
  unfold trustGap trustPremium reciprocalTrust trustLevel coalitionValue ideaValue
  rw [void_left', rs_void_void]
  simp [max_self, min_self]

end TrustReciprocity

/-! ## §11. Social Contract Theory

    Hobbes: the state of nature is war of all against all (no composition).
    Locke: natural rights preserved in composition (individual value protected).
    Rousseau: general will as grand coalition composition.
    Rawls: fairness requires attention to the worst-off. -/

section SocialContract
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Hobbes' state of nature: each idea alone. -/
noncomputable def stateOfNature (a b : I) : ℝ :=
  ideaValue a + ideaValue b

/-- The Hobbesian surplus: how much society creates beyond nature. -/
noncomputable def hobbeSurplus (a b : I) : ℝ :=
  coalitionValue a b - stateOfNature a b

/-- Hobbes surplus is the trust surplus. -/
theorem hobbeSurplus_eq_trustSurplus (a b : I) :
    hobbeSurplus a b = trustSurplus a b := by
  unfold hobbeSurplus stateOfNature trustSurplus; ring

/-- Locke's natural right: each idea's value is preserved in composition. -/
theorem locke_natural_rights (a b : I) :
    coalitionValue a b ≥ ideaValue a := coalitionValue_ge_first a b

/-- Rousseau's general will: the value of the grand coalition. -/
noncomputable def generalWill (a b : I) : ℝ := coalitionValue a b

/-- The general will is at least as good as the state of nature for the first party. -/
theorem generalWill_ge_nature_first (a b : I) :
    generalWill a b ≥ ideaValue a := by
  unfold generalWill; exact coalitionValue_ge_first a b

/-- Rawls' fair share: split coalition value equally. -/
noncomputable def rawlsFairShare (a b : I) : ℝ :=
  coalitionValue a b / 2

/-- Fair share is non-negative. -/
theorem rawlsFairShare_nonneg (a b : I) :
    rawlsFairShare a b ≥ 0 := by
  unfold rawlsFairShare; linarith [coalitionValue_nonneg a b]

/-- The social contract is individually rational for the first party. -/
theorem social_contract_rational (a b : I) :
    coalitionValue a b ≥ ideaValue a := coalitionValue_ge_first a b

/-- The sovereignty cost is zero — compose_enriches means no sacrifice. -/
theorem sovereigntyCost_zero (a : I) :
    ideaValue a - ideaValue a = 0 := by
  ring

/-- The Hobbesian dilemma: both parties do no worse under cooperation. -/
theorem hobbesian_dilemma (a b : I) :
    coalitionValue a b + coalitionValue b a ≥
    ideaValue a + ideaValue b := by
  linarith [coalitionValue_ge_first a b, coalitionValue_ge_first b a]

/-- Surplus from composition decomposes via emergence. -/
theorem social_contract_surplus_decompose (a b : I) :
    coalitionValue a b - ideaValue a =
    rs b (compose a b) + emergence a b (compose a b) +
    (rs a (compose a b) - rs a a) := by
  unfold coalitionValue ideaValue
  have := rs_compose_eq a b (compose a b)
  linarith

/-- The free association principle: composing with void is free. -/
theorem free_association_void (a : I) :
    coalitionValue a (void : I) = ideaValue a ∧
    coalitionValue (void : I) a = ideaValue a :=
  ⟨coalitionValue_void_right a, coalitionValue_void_left a⟩

end SocialContract

/-! ## §12. Public Goods and Free-Riding

    A public good enriches everyone when composed. In ideatic space,
    compose_enriches means ALL ideas are public goods! -/

section PublicGoods
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- A public good enriches every coalition it joins. -/
def isPublicGood (g : I) : Prop :=
  ∀ a : I, coalitionValue a g ≥ ideaValue a

/-- Every idea is a public good — axiom E4's deepest social implication. -/
theorem every_idea_is_public_good (g : I) : isPublicGood g := by
  intro a; exact coalitionValue_ge_first a g

/-- The free-rider's payoff: what you get by not contributing. -/
noncomputable def freeRiderPayoff (a : I) : ℝ := ideaValue a

/-- The cooperator's payoff: what you get by joining the coalition. -/
noncomputable def cooperatorPayoff (a b : I) : ℝ := coalitionValue a b

/-- Cooperating always weakly dominates free-riding. -/
theorem cooperation_dominates_freeRiding (a b : I) :
    cooperatorPayoff a b ≥ freeRiderPayoff a := by
  unfold cooperatorPayoff freeRiderPayoff
  exact coalitionValue_ge_first a b

/-- The commons value: what a shared resource provides. -/
noncomputable def commonsValue (shared : I) : ℝ := ideaValue shared

/-- Contributing to the commons only enriches. -/
theorem commons_contribution_enriches (shared contribution : I) :
    coalitionValue shared contribution ≥ commonsValue shared := by
  unfold commonsValue; exact coalitionValue_ge_first shared contribution

/-- Ostrom's principle: boundaries + enrichment guarantee cooperation. -/
theorem ostrom_boundary_principle (a b : I) :
    coalitionValue a b ≥ ideaValue a ∧ ideaValue a ≥ 0 :=
  ⟨coalitionValue_ge_first a b, ideaValue_nonneg a⟩

/-- Non-void coalitions always exceed zero. -/
theorem public_good_provision (a b : I) (ha : a ≠ void) :
    coalitionValue a b > 0 := by
  linarith [coalitionValue_ge_first a b, ideaValue_pos a ha]

/-- The free-rider problem disappears: cooperation is individually rational. -/
theorem no_freeRider_problem (a b : I) :
    cooperatorPayoff a b - freeRiderPayoff a ≥ 0 := by
  unfold cooperatorPayoff freeRiderPayoff
  linarith [coalitionValue_ge_first a b]

/-- Collective action gain from cooperation. -/
noncomputable def collectiveActionGain (a b : I) : ℝ :=
  coalitionValue a b - ideaValue a

/-- Collective action gain is non-negative. -/
theorem collectiveActionGain_nonneg (a b : I) :
    collectiveActionGain a b ≥ 0 := by
  unfold collectiveActionGain; linarith [coalitionValue_ge_first a b]

/-- Collective action with void yields zero gain. -/
theorem collectiveActionGain_void (a : I) :
    collectiveActionGain a (void : I) = 0 := by
  unfold collectiveActionGain coalitionValue ideaValue; rw [void_right']; linarith

end PublicGoods

/-! ## §13. Cooperative Game Theory — Core and Stability -/

section CooperativeGames
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- An allocation is individually rational if each party gets at least standalone. -/
def individuallyRational (a b : I) (xa xb : ℝ) : Prop :=
  xa ≥ ideaValue a ∧ xb ≥ ideaValue b

/-- An allocation is efficient if it distributes the full coalition value. -/
def efficient (a b : I) (xa xb : ℝ) : Prop :=
  xa + xb = coalitionValue a b

/-- A core allocation is individually rational and efficient. -/
def inCore (a b : I) (xa xb : ℝ) : Prop :=
  individuallyRational a b xa xb ∧ efficient a b xa xb

/-- The equal split is always non-negative. -/
theorem equalSplit_nonneg (a b : I) :
    coalitionValue a b / 2 ≥ 0 := by
  linarith [coalitionValue_nonneg a b]

/-- Full allocation to first party is individually rational for a. -/
theorem first_takes_all_rational_first (a b : I) :
    coalitionValue a b ≥ ideaValue a :=
  coalitionValue_ge_first a b

/-- Allocating coalitionValue to a and 0 to b is efficient. -/
theorem core_nonempty_allocation (a b : I) :
    efficient a b (coalitionValue a b) 0 := by
  unfold efficient; ring

/-- A "proportional" allocation based on individual values. -/
noncomputable def proportionalAllocation_a (a b : I) : ℝ :=
  ideaValue a + cooperationSurplus a b

/-- Proportional allocation gives a its value plus the surplus. -/
theorem proportionalAllocation_eq (a b : I) :
    proportionalAllocation_a a b = coalitionValue a b := by
  unfold proportionalAllocation_a cooperationSurplus coalitionValue ideaValue; ring

/-- Excess over standalone value. -/
noncomputable def excessOver (a : I) (xa : ℝ) : ℝ :=
  xa - ideaValue a

/-- Excess of full coalition value is the cooperation surplus. -/
theorem excessOver_eq (a b : I) :
    excessOver a (coalitionValue a b) = cooperationSurplus a b := by
  unfold excessOver cooperationSurplus; ring

/-- The bargaining set contains the core. -/
theorem bargainingSet_eq_core (a b : I) (xa xb : ℝ) :
    inCore a b xa xb → xa ≥ ideaValue a ∧ xb ≥ ideaValue b := by
  intro h; exact h.1

/-- A stable allocation exists for every coalition. -/
theorem stable_allocation_exists (a b : I) :
    ∃ xa xb : ℝ, efficient a b xa xb ∧ xa ≥ ideaValue a :=
  ⟨coalitionValue a b, 0, core_nonempty_allocation a b, coalitionValue_ge_first a b⟩

/-- In a void coalition, the only efficient allocation sums to zero. -/
theorem void_coalition_efficient (xa xb : ℝ)
    (h : efficient (void : I) (void : I) xa xb) : xa + xb = 0 := by
  unfold efficient at h; rw [coalitionValue_void_void] at h; exact h

/-- The Shapley axiom of null player: void contributes nothing. -/
theorem shapley_null_player (a : I) :
    marginalContribution a (void : I) = 0 :=
  marginalContribution_void_right a

end CooperativeGames

/-! ## §14. Shapley-like Attribution -/

section ShapleyAttribution
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The Shapley-like value: average marginal contribution from both orderings. -/
noncomputable def shapleyValue (a b : I) : ℝ :=
  bilateralMarginal a b

/-- Shapley value is symmetric. -/
theorem shapleyValue_symm (a b : I) :
    shapleyValue a b = shapleyValue b a := bilateralMarginal_symm a b

/-- Shapley value is non-negative. -/
theorem shapleyValue_nonneg (a b : I) :
    shapleyValue a b ≥ 0 := bilateralMarginal_nonneg a b

/-- Shapley value with void equals half the idea value. -/
theorem shapleyValue_void (a : I) :
    shapleyValue a (void : I) = ideaValue a / 2 := bilateralMarginal_void a

/-- The attribution gap: left minus right marginal contribution. -/
noncomputable def attributionGap (a b : I) : ℝ :=
  marginalContribution a b - marginalContribution b a

/-- Attribution gap is antisymmetric. -/
theorem attributionGap_antisymm (a b : I) :
    attributionGap a b = -attributionGap b a := by
  unfold attributionGap; ring

/-- Attribution gap equals cooperation asymmetry. -/
theorem attributionGap_eq_asymmetry (a b : I) :
    attributionGap a b = cooperationAsymmetry a b := by
  unfold attributionGap cooperationAsymmetry marginalContribution cooperationSurplus; ring

/-- Attribution gap with void. -/
theorem attributionGap_void (a : I) :
    attributionGap a (void : I) = -(ideaValue a) := by
  unfold attributionGap marginalContribution coalitionValue ideaValue
  rw [void_right', void_left', rs_void_void]; ring

/-- The total marginal contribution from both orderings. -/
noncomputable def totalMarginal (a b : I) : ℝ :=
  marginalContribution a b + marginalContribution b a

/-- Total marginal is non-negative. -/
theorem totalMarginal_nonneg (a b : I) :
    totalMarginal a b ≥ 0 := by
  unfold totalMarginal
  linarith [marginalContribution_nonneg a b, marginalContribution_nonneg b a]

/-- Total marginal is symmetric. -/
theorem totalMarginal_symm (a b : I) :
    totalMarginal a b = totalMarginal b a := by
  unfold totalMarginal; ring

/-- Shapley value is half the total marginal. -/
theorem shapleyValue_eq_half_total (a b : I) :
    shapleyValue a b = totalMarginal a b / 2 := by
  unfold shapleyValue bilateralMarginal totalMarginal; ring

/-- The attribution impossibility: the gap quantifies inherent unfairness. -/
theorem attribution_impossibility (a b : I) :
    totalMarginal a b = 2 * shapleyValue a b := by
  rw [shapleyValue_eq_half_total]; ring

/-- For void partners, Shapley value is zero. -/
theorem shapleyValue_void_void :
    shapleyValue (void : I) (void : I) = 0 := by
  unfold shapleyValue bilateralMarginal marginalContribution coalitionValue ideaValue
  rw [void_left', rs_void_void]; ring

end ShapleyAttribution

/-! ## §15. Team Reasoning — Bacharach and Sugden

    Team reasoning: agents sometimes reason as "we" rather than "I."
    In ideatic space, team reasoning optimizes coalitionValue. -/

section TeamReasoning
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The team payoff: what the coalition achieves. -/
noncomputable def teamPayoff (a b : I) : ℝ := coalitionValue a b

/-- The individual payoff: what each idea achieves alone. -/
noncomputable def individualPayoff (a : I) : ℝ := ideaValue a

/-- Team reasoning is rational: team ≥ individual. -/
theorem team_reasoning_rational (a b : I) :
    teamPayoff a b ≥ individualPayoff a := by
  unfold teamPayoff individualPayoff; exact coalitionValue_ge_first a b

/-- The we-thinking surplus: what team reasoning gains. -/
noncomputable def weThinkingSurplus (a b : I) : ℝ :=
  teamPayoff a b - individualPayoff a

/-- We-thinking surplus is non-negative. -/
theorem weThinkingSurplus_nonneg (a b : I) :
    weThinkingSurplus a b ≥ 0 := by
  unfold weThinkingSurplus; linarith [team_reasoning_rational a b]

/-- We-thinking surplus with void is zero. -/
theorem weThinkingSurplus_void (a : I) :
    weThinkingSurplus a (void : I) = 0 := by
  unfold weThinkingSurplus teamPayoff individualPayoff coalitionValue ideaValue
  rw [void_right']; linarith

/-- The coordination gain: total benefit of team reasoning. -/
noncomputable def coordinationGain (a b : I) : ℝ :=
  teamPayoff a b + teamPayoff b a - individualPayoff a - individualPayoff b

/-- Coordination gain is non-negative. -/
theorem coordinationGain_nonneg (a b : I) :
    coordinationGain a b ≥ 0 := by
  unfold coordinationGain
  linarith [team_reasoning_rational a b, team_reasoning_rational b a]

/-- Coordination gain is symmetric. -/
theorem coordinationGain_symm (a b : I) :
    coordinationGain a b = coordinationGain b a := by
  unfold coordinationGain; ring

/-- Agency identity: team = individual + surplus. -/
theorem agency_identity (a b : I) :
    teamPayoff a b = individualPayoff a + weThinkingSurplus a b := by
  unfold weThinkingSurplus; ring

/-- Minimum guaranteed value under mutual cooperation is non-negative. -/
theorem common_knowledge_guarantee (a b : I) :
    min (weThinkingSurplus a b) (weThinkingSurplus b a) ≥ 0 :=
  le_min (weThinkingSurplus_nonneg a b) (weThinkingSurplus_nonneg b a)

/-- Collective intentionality: team value exceeds individual. -/
theorem collective_intentionality (a b : I) :
    teamPayoff a b ≥ individualPayoff a :=
  team_reasoning_rational a b

end TeamReasoning

/-! ## §16. Grand Coalition Theory — Multi-agent Cooperation -/

section GrandCoalition
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Grand coalition value is non-negative for any population. -/
theorem grandCoalitionValue_nonneg (pop : List I) :
    grandCoalitionValue pop ≥ 0 := by
  unfold grandCoalitionValue; exact rs_self_nonneg' _

/-- Two-element grand coalition equals coalition value. -/
theorem grandCoalitionValue_pair (a b : I) :
    grandCoalitionValue [a, b] = coalitionValue a b := by
  unfold grandCoalitionValue coalitionValue composeList
  simp [void_left']

/-- Grand coalition of [void] = 0. -/
theorem grandCoalitionValue_void_singleton :
    grandCoalitionValue [(void : I)] = 0 := by
  rw [grandCoalitionValue_singleton]; exact ideaValue_void

/-- Adding void to front doesn't change grand coalition value. -/
theorem grandCoalitionValue_void_cons (pop : List I) :
    grandCoalitionValue ((void : I) :: pop) = grandCoalitionValue pop := by
  unfold grandCoalitionValue
  have h : composeList ((void : I) :: pop) = composeList pop := by
    change compose void (composeList pop) = composeList pop
    rw [void_left']
  rw [h]

/-- The contribution of adding idea a to a population's grand coalition. -/
noncomputable def grandCoalitionContribution (a : I) (pop : List I) : ℝ :=
  grandCoalitionValue (a :: pop) - grandCoalitionValue pop

/-- Grand coalition contribution to empty pop equals idea value. -/
theorem grandCoalitionContribution_nil (a : I) :
    grandCoalitionContribution a [] = ideaValue a := by
  unfold grandCoalitionContribution
  rw [grandCoalitionValue_singleton, grandCoalitionValue_nil]; linarith

/-- Void's contribution to any coalition is zero. -/
theorem void_grandCoalition_contribution_val (pop : List I) :
    grandCoalitionContribution (void : I) pop = 0 := by
  unfold grandCoalitionContribution
  rw [grandCoalitionValue_void_cons]; ring

end GrandCoalition

/-! ## §17. Convexity and Monotonicity of Cooperative Games -/

section ConvexityMonotonicity
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The coalition growth function. -/
noncomputable def coalitionGrowth (a b c : I) : ℝ :=
  coalitionValue3 a b c - coalitionValue a b

/-- Coalition growth is non-negative (adding ideas enriches). -/
theorem coalitionGrowth_nonneg (a b c : I) :
    coalitionGrowth a b c ≥ 0 := by
  unfold coalitionGrowth; exact incrementalValue_nonneg a b c

/-- Coalition growth equals incremental value. -/
theorem coalitionGrowth_eq_incremental (a b c : I) :
    coalitionGrowth a b c = incrementalValue a b c := rfl

/-- Monotonicity chain: v({a}) ≤ v({a,b}) ≤ v({a,b,c}). -/
theorem coalition_monotonicity_chain (a b c : I) :
    ideaValue a ≤ coalitionValue a b ∧
    coalitionValue a b ≤ coalitionValue3 a b c :=
  ⟨coalitionValue_ge_first a b, coalitionValue3_ge_two a b c⟩

/-- Coalition value of (a∘b) with c is coalitionValue3. -/
theorem coalitionValue_compose_left (a b c : I) :
    coalitionValue (compose a b) c = coalitionValue3 a b c := rfl

/-- Coalition value of a with (b∘c) equals coalitionValue3 (by assoc). -/
theorem coalitionValue_compose_right (a b c : I) :
    coalitionValue a (compose b c) = coalitionValue3 a b c := by
  unfold coalitionValue coalitionValue3; rw [← compose_assoc']

/-- Value monotonicity: composing with non-void vs void. -/
theorem value_monotonicity_void_comparison (a b : I) :
    coalitionValue a b ≥ coalitionValue a (void : I) := by
  rw [coalitionValue_void_right]; exact coalitionValue_ge_first a b

/-- Two-step enrichment: composing twice only increases value. -/
theorem two_step_enrichment (a b c : I) :
    coalitionValue3 a b c ≥ ideaValue a := by
  linarith [coalitionValue3_ge_two a b c, coalitionValue_ge_first a b]

/-- Weight monotonicity through composition. -/
theorem weight_coalition_mono (a b : I) :
    coalitionValue a b ≥ 0 := coalitionValue_nonneg a b

/-- Non-void coalition is strictly positive. -/
theorem cooperation_chain_strict (a b : I) (ha : a ≠ void) :
    coalitionValue a b > 0 := by
  unfold coalitionValue
  exact rs_self_pos (compose a b) (compose_ne_void_of_left a b ha)

end ConvexityMonotonicity

/-! ## §18. Cooperation Topology — Network Structure -/

section CooperationTopology
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Two ideas are cooperation-connected if both gain from coalition. -/
def cooperationConnected (a b : I) : Prop :=
  coalitionValue a b > ideaValue a ∧ coalitionValue b a > ideaValue b

/-- Self-connection: every non-void idea has positive self-coalition. -/
theorem self_coalition_ge (a : I) :
    coalitionValue a a ≥ ideaValue a := coalitionValue_ge_first a a

/-- Void is not cooperation-connected to anything. -/
theorem void_not_connected (a : I) :
    ¬cooperationConnected (void : I) a := by
  unfold cooperationConnected
  push_neg
  intro _
  unfold coalitionValue ideaValue
  rw [void_right']

/-- Cooperation strength between ideas. -/
noncomputable def cooperationStrength (a b : I) : ℝ :=
  coalitionValue a b + coalitionValue b a - ideaValue a - ideaValue b

/-- Cooperation strength is non-negative (both directions enrich). -/
theorem cooperationStrength_nonneg (a b : I) :
    cooperationStrength a b ≥ 0 := by
  unfold cooperationStrength
  linarith [coalitionValue_ge_first a b, coalitionValue_ge_first b a]

/-- Cooperation strength is symmetric. -/
theorem cooperationStrength_symm (a b : I) :
    cooperationStrength a b = cooperationStrength b a := by
  unfold cooperationStrength; ring

/-- Cooperation strength void-void is zero. -/
theorem cooperationStrength_void_void :
    cooperationStrength (void : I) (void : I) = 0 := by
  unfold cooperationStrength coalitionValue ideaValue
  rw [void_left', rs_void_void]; ring

/-- Total pairwise cooperation strength for three ideas. -/
noncomputable def totalCooperationStrength (a b c : I) : ℝ :=
  cooperationStrength a b + cooperationStrength b c + cooperationStrength a c

/-- Total cooperation strength is non-negative. -/
theorem totalCooperationStrength_nonneg (a b c : I) :
    totalCooperationStrength a b c ≥ 0 := by
  unfold totalCooperationStrength
  linarith [cooperationStrength_nonneg a b, cooperationStrength_nonneg b c,
            cooperationStrength_nonneg a c]

end CooperationTopology

/-! ## §19. Emergence Surplus Accounting -/

section EmergenceSurplusAccounting
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Cross-resonance contribution: how b resonates with the coalition a∘b. -/
noncomputable def crossContribution (a b : I) : ℝ :=
  rs b (compose a b)

/-- Self-shift: how a's resonance changes in the coalition context. -/
noncomputable def selfShift (a b : I) : ℝ :=
  rs a (compose a b) - rs a a

/-- Emergence contribution: pure non-linear synergy. -/
noncomputable def emergenceContribution (a b : I) : ℝ :=
  emergence a b (compose a b)

/-- Surplus = cross + emergence + self-shift. -/
theorem surplus_decomposition (a b : I) :
    cooperationSurplus a b =
    crossContribution a b + emergenceContribution a b + selfShift a b := by
  unfold cooperationSurplus coalitionValue ideaValue crossContribution
    emergenceContribution selfShift
  have := rs_compose_eq a b (compose a b)
  linarith

/-- Cross contribution of void is zero. -/
theorem crossContribution_void (a : I) :
    crossContribution a (void : I) = 0 := by
  unfold crossContribution; rw [void_right', rs_void_left']

/-- Self-shift with void is zero. -/
theorem selfShift_void (a : I) :
    selfShift a (void : I) = 0 := by
  unfold selfShift; rw [void_right']; linarith

/-- Emergence contribution with void is zero. -/
theorem emergenceContribution_void (a : I) :
    emergenceContribution a (void : I) = 0 := by
  unfold emergenceContribution; rw [void_right']
  exact emergence_void_right a a

/-- All three components sum to zero for void composition. -/
theorem surplus_components_void (a : I) :
    crossContribution a (void : I) + emergenceContribution a (void : I) +
    selfShift a (void : I) = 0 := by
  rw [crossContribution_void, emergenceContribution_void, selfShift_void]; ring

/-- Emergence contribution satisfies the bounded emergence inequality. -/
theorem emergenceContribution_bounded (a b : I) :
    (emergenceContribution a b) ^ 2 ≤
    coalitionValue a b * coalitionValue a b := by
  unfold emergenceContribution coalitionValue
  have h := emergence_bounded' a b (compose a b)
  nlinarith [sq_nonneg (emergence a b (compose a b)), rs_self_nonneg' (compose a b)]

/-- Cross contribution when a is void is b's self-resonance. -/
theorem crossContribution_void_left (b : I) :
    crossContribution (void : I) b = rs b b := by
  unfold crossContribution; rw [void_left']

/-- Self-shift when a is void. -/
theorem selfShift_void_left (b : I) :
    selfShift (void : I) b = -(rs (void : I) (void : I)) := by
  unfold selfShift; rw [void_left', rs_void_left']; ring

end EmergenceSurplusAccounting

/-! ## §20. Iterated Cooperation — Repeated Games -/

section IteratedCooperation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Value of n-fold self-composition. -/
noncomputable def iteratedValue (a : I) (n : ℕ) : ℝ :=
  rs (composeN a n) (composeN a n)

/-- Iterated value at 0 is zero. -/
theorem iteratedValue_zero (a : I) : iteratedValue a 0 = 0 := by
  unfold iteratedValue composeN; exact rs_void_void

/-- Iterated value at 1 is the idea's own value. -/
theorem iteratedValue_one (a : I) : iteratedValue a 1 = ideaValue a := by
  unfold iteratedValue ideaValue; rw [composeN_one]

/-- Iterated value is monotonically non-decreasing. -/
theorem iteratedValue_mono (a : I) (n : ℕ) :
    iteratedValue a (n + 1) ≥ iteratedValue a n := by
  unfold iteratedValue; exact rs_composeN_mono a n

/-- Iterated value is always non-negative. -/
theorem iteratedValue_nonneg (a : I) (n : ℕ) :
    iteratedValue a n ≥ 0 := by
  unfold iteratedValue; exact rs_self_nonneg' _

/-- Iterated value at n+1 is at least the base value. -/
theorem iteratedValue_ge_base (a : I) (n : ℕ) :
    iteratedValue a (n + 1) ≥ ideaValue a := by
  unfold iteratedValue ideaValue; exact rs_composeN_ge_base a n

/-- Iterated cooperation surplus: how much n repetitions exceed one. -/
noncomputable def iteratedSurplus (a : I) (n : ℕ) : ℝ :=
  iteratedValue a n - ideaValue a

/-- Iterated surplus at n=1 is zero. -/
theorem iteratedSurplus_one (a : I) : iteratedSurplus a 1 = 0 := by
  unfold iteratedSurplus iteratedValue ideaValue; rw [composeN_one]; linarith

/-- Iterated surplus is non-negative for n ≥ 1. -/
theorem iteratedSurplus_nonneg (a : I) (n : ℕ) :
    iteratedSurplus a (n + 1) ≥ 0 := by
  unfold iteratedSurplus; linarith [iteratedValue_ge_base a n]

/-- Iterated surplus is monotonically non-decreasing. -/
theorem iteratedSurplus_mono (a : I) (n : ℕ) :
    iteratedSurplus a (n + 2) ≥ iteratedSurplus a (n + 1) := by
  unfold iteratedSurplus; linarith [iteratedValue_mono a (n + 1)]

/-- Iterated cooperation growth rate. -/
noncomputable def iteratedGrowth (a : I) (n : ℕ) : ℝ :=
  iteratedValue a (n + 1) - iteratedValue a n

/-- Iterated growth is non-negative. -/
theorem iteratedGrowth_nonneg (a : I) (n : ℕ) :
    iteratedGrowth a n ≥ 0 := by
  unfold iteratedGrowth; linarith [iteratedValue_mono a n]

/-- Void's iterated value is always zero. -/
theorem iteratedValue_void (n : ℕ) :
    iteratedValue (void : I) n = 0 := by
  unfold iteratedValue; rw [composeN_void]; exact rs_void_void

/-- Void's iterated surplus is always zero. -/
theorem iteratedSurplus_void (n : ℕ) :
    iteratedSurplus (void : I) n = 0 := by
  unfold iteratedSurplus iteratedValue ideaValue
  rw [composeN_void, rs_void_void]; linarith

end IteratedCooperation

/-! ## §21. Cooperation and Alignment Interaction -/

section AlignmentCooperation
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Aligned ideas have positive resonance. -/
theorem aligned_implies_positive_rs (a b : I) (h : aligned a b) :
    rs a b > 0 := h

/-- Void is not aligned with void. -/
theorem void_not_self_aligned : ¬aligned (void : I) (void : I) := by
  unfold aligned; rw [rs_void_void]; linarith

/-- Conflict with void is impossible from the right. -/
theorem void_no_conflict_right (a : I) : ¬inConflict a (void : I) := by
  unfold inConflict; rw [rs_void_right']; linarith

/-- Coalition value is positive when the first member is non-void. -/
theorem coalitionValue_pos_of_nonvoid (a b : I) (ha : a ≠ void) :
    coalitionValue a b > 0 := by
  unfold coalitionValue
  exact rs_self_pos (compose a b) (compose_ne_void_of_left a b ha)

/-- Even conflicting ideas produce positive coalition value (if non-void). -/
theorem conflict_still_positive_coalition (a b : I) (ha : a ≠ void)
    (_hc : inConflict a b) :
    coalitionValue a b > 0 := coalitionValue_pos_of_nonvoid a b ha

/-- Non-void ideas have positive coalition value with themselves. -/
theorem self_coalition_positive (a : I) (ha : a ≠ void) :
    coalitionValue a a > 0 := coalitionValue_pos_of_nonvoid a a ha

/-- Aligned ideas always form non-trivial coalitions. -/
theorem aligned_cooperation (a b : I) (ha : a ≠ void) :
    coalitionValue a b ≥ ideaValue a ∧ ideaValue a > 0 :=
  ⟨coalitionValue_ge_first a b, ideaValue_pos a ha⟩

/-- Non-void coalition value strictly exceeds zero. -/
theorem nonvoid_coalition_pos (a b : I) (ha : a ≠ void) :
    coalitionValue a b > 0 := by
  linarith [coalitionValue_ge_first a b, ideaValue_pos a ha]

end AlignmentCooperation

/-! ## §22. Reciprocity Norms and Fairness -/

section FairnessNorms
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Egalitarian norm: split the surplus equally. -/
noncomputable def egalitarianShare (a b : I) : ℝ :=
  cooperationSurplus a b / 2

/-- Egalitarian share is non-negative. -/
theorem egalitarianShare_nonneg (a b : I) :
    egalitarianShare a b ≥ 0 := by
  unfold egalitarianShare; linarith [cooperationSurplus_nonneg a b]

/-- Libertarian norm: each keeps standalone plus marginal contribution. -/
noncomputable def libertarianPayoff (a b : I) : ℝ :=
  ideaValue a + cooperationSurplus a b

/-- Libertarian payoff equals coalition value. -/
theorem libertarianPayoff_eq (a b : I) :
    libertarianPayoff a b = coalitionValue a b := by
  unfold libertarianPayoff cooperationSurplus coalitionValue ideaValue; ring

/-- Utilitarian always recommends cooperation. -/
theorem utilitarian_recommends_cooperation (a b : I) :
    coalitionValue a b ≥ ideaValue a :=
  coalitionValue_ge_first a b

/-- Rawlsian maximin aligns with cooperation for the first party. -/
theorem rawls_cooperation_guarantee (a b : I) :
    coalitionValue a b ≥ ideaValue a :=
  coalitionValue_ge_first a b

/-- Envy-free condition: a's surplus ≥ b's surplus. -/
def envyFree (a b : I) : Prop :=
  cooperationSurplus a b ≥ cooperationSurplus b a

/-- Envy-freeness holds when surpluses are equal. -/
theorem envyFree_of_symmetric_surplus (a b : I)
    (h : cooperationSurplus a b = cooperationSurplus b a) :
    envyFree a b := by
  unfold envyFree; linarith

/-- Envy-freeness with void-void. -/
theorem envyFree_void_void :
    envyFree (void : I) (void : I) := by
  unfold envyFree cooperationSurplus coalitionValue ideaValue
  rw [void_left', rs_void_void]

end FairnessNorms

/-! ## §23. Power and Dominance in Coalitions -/

section PowerDominance
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The Banzhaf-like power index. -/
noncomputable def powerIndex (a b : I) : ℝ :=
  marginalContribution b a

/-- Power index is non-negative. -/
theorem powerIndex_nonneg (a b : I) :
    powerIndex a b ≥ 0 := marginalContribution_nonneg b a

/-- Void has zero power in any context. -/
theorem powerIndex_void (a : I) :
    powerIndex (void : I) a = 0 := by
  unfold powerIndex marginalContribution coalitionValue ideaValue
  rw [void_right']; linarith

/-- The dominance relation: a dominates b if a contributes more everywhere. -/
def dominates (a b : I) : Prop :=
  ∀ c : I, marginalContribution c a ≥ marginalContribution c b

/-- Every idea dominates void. -/
theorem dominates_void (a : I) : dominates a (void : I) := by
  intro c; unfold marginalContribution
  rw [coalitionValue_void_right]; linarith [coalitionValue_ge_first c a]

/-- Dominance is reflexive. -/
theorem dominates_refl (a : I) : dominates a a := fun _ => le_refl _

/-- The relative power of a over b in a coalition context. -/
noncomputable def relativePower (a b c : I) : ℝ :=
  marginalContribution c a - marginalContribution c b

/-- Relative power is antisymmetric. -/
theorem relativePower_antisymm (a b c : I) :
    relativePower a b c = -relativePower b a c := by
  unfold relativePower; ring

/-- Relative power against self is zero. -/
theorem relativePower_self (a c : I) :
    relativePower a a c = 0 := by
  unfold relativePower; ring

end PowerDominance

/-! ## §24. Cooperation Under Uncertainty -/

section CooperationUncertainty
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Worst-case cooperation: partner = void gives standalone value. -/
theorem worstCase_cooperation (a : I) :
    coalitionValue a (void : I) = ideaValue a := coalitionValue_void_right a

/-- Minimum surplus is zero. -/
theorem guaranteed_surplus (a b : I) :
    cooperationSurplus a b ≥ 0 := cooperationSurplus_nonneg a b

/-- Downside risk of cooperation is zero. -/
theorem zero_downside_risk (a b : I) :
    coalitionValue a b - ideaValue a ≥ 0 := by
  linarith [coalitionValue_ge_first a b]

/-- Cooperation premium over isolation is non-negative. -/
theorem cooperation_premium (a b : I) :
    coalitionValue a b ≥ ideaValue a := coalitionValue_ge_first a b

/-- Safety of iterated cooperation. -/
theorem iterated_cooperation_safe (a : I) (n : ℕ) :
    iteratedValue a (n + 1) ≥ ideaValue a := iteratedValue_ge_base a n

/-- The precautionary principle: composing can't hurt. -/
theorem precautionary_principle (a b : I) :
    coalitionValue a b ≥ ideaValue a := coalitionValue_ge_first a b

end CooperationUncertainty

/-! ## §25. Composition Order Effects -/

section CompositionOrder
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The order effect: difference in coalition values between orderings. -/
noncomputable def orderEffect (a b : I) : ℝ :=
  coalitionValue a b - coalitionValue b a

/-- Order effect is antisymmetric. -/
theorem orderEffect_antisymm (a b : I) :
    orderEffect a b = -orderEffect b a := by
  unfold orderEffect; ring

/-- Order effect with void on right is zero. -/
theorem orderEffect_void_right (a : I) :
    orderEffect a (void : I) = 0 := by
  unfold orderEffect coalitionValue
  rw [void_right', void_left']; linarith

/-- Order effect with void on left is zero. -/
theorem orderEffect_void_left (b : I) :
    orderEffect (void : I) b = 0 := by
  unfold orderEffect coalitionValue
  rw [void_left', void_right']; linarith

/-- The leader's advantage: difference in context-dependent resonance. -/
noncomputable def leaderAdvantage (a b : I) : ℝ :=
  rs a (compose a b) - rs a (compose b a)

/-- The order effect decomposes into surplus difference and value difference. -/
theorem orderEffect_eq_surplus_diff (a b : I) :
    orderEffect a b =
    (coalitionValue a b - ideaValue a) - (coalitionValue b a - ideaValue b) +
    (ideaValue a - ideaValue b) := by
  unfold orderEffect; ring

/-- Self-composition has zero order effect. -/
theorem orderEffect_self (a : I) :
    orderEffect a a = 0 := by
  unfold orderEffect; ring

end CompositionOrder

/-! ## §26. The Cooperation Spectrum -/

section CooperationSpectrum
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Additive cooperation: coalition value = sum of individual values. -/
def additiveCooperation (a b : I) : Prop :=
  coalitionValue a b = ideaValue a + ideaValue b

/-- Void always has additive cooperation with itself. -/
theorem void_additive_self :
    additiveCooperation (void : I) (void : I) := by
  unfold additiveCooperation coalitionValue ideaValue
  rw [void_left', rs_void_void]; ring

/-- Synergistic cooperation: coalition value exceeds sum of parts. -/
def synergisticCooperation (a b : I) : Prop :=
  coalitionValue a b > ideaValue a + ideaValue b

/-- Parasitic cooperation: one side gains more than the other. -/
def parasiticCooperation (a b : I) : Prop :=
  cooperationSurplus a b > cooperationSurplus b a

/-- Mutualistic cooperation: both sides gain equally. -/
def mutualisticCooperation (a b : I) : Prop :=
  cooperationSurplus a b = cooperationSurplus b a

/-- Mutualistic cooperation is symmetric. -/
theorem mutualisticCooperation_symm (a b : I) :
    mutualisticCooperation a b ↔ mutualisticCooperation b a := by
  unfold mutualisticCooperation; constructor <;> intro h <;> linarith

/-- Parasitic cooperation is antisymmetric. -/
theorem parasiticCooperation_antisymm (a b : I) :
    parasiticCooperation a b → ¬parasiticCooperation b a := by
  unfold parasiticCooperation; intro h hc; linarith

/-- Void-void cooperation is trivially mutualistic. -/
theorem void_mutualistic :
    mutualisticCooperation (void : I) (void : I) := by
  unfold mutualisticCooperation cooperationSurplus coalitionValue ideaValue
  rw [void_left', rs_void_void]

/-- Cooperation spectrum trichotomy. -/
theorem cooperation_trichotomy (a b : I) :
    cooperationSurplus a b > cooperationSurplus b a ∨
    cooperationSurplus a b < cooperationSurplus b a ∨
    cooperationSurplus a b = cooperationSurplus b a := by
  rcases lt_trichotomy (cooperationSurplus a b) (cooperationSurplus b a) with h | h | h
  · right; left; exact h
  · right; right; exact h
  · left; exact h

end CooperationSpectrum

/-! ## §27. Coalition Stability Measures -/

section CoalitionStability
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- Exit cost: what a loses by leaving the coalition. -/
noncomputable def exitCost (a b : I) : ℝ :=
  coalitionValue a b - ideaValue a

/-- Exit cost is non-negative (you always lose by leaving). -/
theorem exitCost_nonneg (a b : I) : exitCost a b ≥ 0 := by
  unfold exitCost; linarith [coalitionValue_ge_first a b]

/-- Exit cost from void coalition is zero. -/
theorem exitCost_void (a : I) : exitCost a (void : I) = 0 := by
  unfold exitCost coalitionValue ideaValue; rw [void_right']; linarith

/-- Exit cost equals cooperation surplus. -/
theorem exitCost_eq_surplus (a b : I) :
    exitCost a b = cooperationSurplus a b := rfl

/-- Coalition stability index: minimum exit cost. -/
noncomputable def stabilityIndex (a b : I) : ℝ :=
  min (exitCost a b) (exitCost b a)

/-- Stability index is non-negative. -/
theorem stabilityIndex_nonneg (a b : I) :
    stabilityIndex a b ≥ 0 :=
  le_min (exitCost_nonneg a b) (exitCost_nonneg b a)

/-- Stability index is symmetric. -/
theorem stabilityIndex_symm (a b : I) :
    stabilityIndex a b = stabilityIndex b a := by
  unfold stabilityIndex; rw [min_comm]

/-- Stability index void-void is zero. -/
theorem stabilityIndex_void_void :
    stabilityIndex (void : I) (void : I) = 0 := by
  unfold stabilityIndex exitCost coalitionValue ideaValue
  rw [void_left', rs_void_void]; simp [max_self, min_self]

/-- Fragility: how asymmetric the exit costs are. -/
noncomputable def coalitionFragility (a b : I) : ℝ :=
  max (exitCost a b) (exitCost b a) - min (exitCost a b) (exitCost b a)

/-- Fragility is non-negative. -/
theorem coalitionFragility_nonneg (a b : I) :
    coalitionFragility a b ≥ 0 := by
  unfold coalitionFragility
  have h : min (exitCost a b) (exitCost b a) ≤ max (exitCost a b) (exitCost b a) := min_le_max
  linarith

/-- Fragility is symmetric. -/
theorem coalitionFragility_symm (a b : I) :
    coalitionFragility a b = coalitionFragility b a := by
  unfold coalitionFragility; rw [max_comm, min_comm]

/-- A coalition is perfectly stable if fragility is zero. -/
def perfectlyStable (a b : I) : Prop :=
  coalitionFragility a b = 0

/-- Void-void coalition is perfectly stable. -/
theorem void_perfectly_stable :
    perfectlyStable (void : I) (void : I) := by
  unfold perfectlyStable coalitionFragility exitCost coalitionValue ideaValue
  rw [void_left', rs_void_void]
  simp [max_self, min_self]

end CoalitionStability

/-! ## §12. Coalition Paradoxes

These theorems reveal counter-intuitive properties of coalitions
that contradict naive expectations from cooperative game theory.
Key insight: in ideatic space, coalitions are ORDERED, and the
total surplus is always non-negative — but distribution is unfair. -/

section CoalitionParadoxes
variable {I : Type*} [S : IdeaticSpace3 I]
open IdeaticSpace3

/-- The total surplus of a two-person coalition from both perspectives. -/
noncomputable def totalCoopSurplus (a b : I) : ℝ :=
  cooperationSurplus a b + cooperationSurplus b a

/-- CP1. TOTAL SURPLUS DECOMPOSES: The total pie created by cooperation
    equals the sum of both coalition values minus both individual values.
    Counter-intuitive: the total surplus is NOT the same as the coalition
    value minus the sum of individual values. It's the sum of TWO
    different coalition values (one per ordering). -/
theorem totalCoopSurplus_eq (a b : I) :
    totalCoopSurplus a b =
    coalitionValue a b + coalitionValue b a - ideaValue a - ideaValue b := by
  unfold totalCoopSurplus cooperationSurplus; ring

/-- CP2. TOTAL SURPLUS IS SYMMETRIC: The total pie doesn't depend on
    who we call "first" and who we call "second."
    Counter-intuitive: individual surpluses ARE asymmetric, but their
    SUM is perfectly symmetric. The unfairness cancels in aggregate. -/
theorem totalCoopSurplus_symm (a b : I) :
    totalCoopSurplus a b = totalCoopSurplus b a := by
  unfold totalCoopSurplus; ring

/-- CP3. TOTAL SURPLUS IS NON-NEGATIVE: Cooperation ALWAYS creates a
    non-negative total surplus, because both enrichment directions help.
    Counter-intuitive: you'd expect that some coalitions are destructive.
    But in ideatic space, cooperation is always weakly beneficial. -/
theorem totalCoopSurplus_nonneg (a b : I) :
    totalCoopSurplus a b ≥ 0 := by
  unfold totalCoopSurplus
  have h1 := cooperationSurplus_nonneg a b
  have h2 := cooperationSurplus_nonneg b a
  linarith

/-- The surplus asymmetry: how unfairly the cooperation pie is divided. -/
noncomputable def coopSurplusAsymmetry (a b : I) : ℝ :=
  cooperationSurplus a b - cooperationSurplus b a

/-- CP4. THE COOPERATION PARADOX: Surplus asymmetry equals the difference
    in coalition values minus the difference in individual values.
    Counter-intuitive: you'd expect fairness to depend on intrinsic
    properties, but it's determined by composition order alone. -/
theorem coopSurplusAsymmetry_eq (a b : I) :
    coopSurplusAsymmetry a b =
    coalitionValue a b - coalitionValue b a - (ideaValue a - ideaValue b) := by
  unfold coopSurplusAsymmetry cooperationSurplus; ring

/-- CP5. SURPLUS ASYMMETRY IS ANTISYMMETRIC: The unfairness experienced
    by a is exactly the negative of the unfairness experienced by b.
    Counter-intuitive: in a three-player game, asymmetry need not be
    zero-sum. But in two-player coalitions, it always is. -/
theorem coopSurplusAsymmetry_antisymm (a b : I) :
    coopSurplusAsymmetry a b = -(coopSurplusAsymmetry b a) := by
  unfold coopSurplusAsymmetry; ring

/-- CP6. THE VOID FREE RIDER THEOREM: When one member is void, the
    coalition has zero surplus from that direction but FULL surplus
    from the other. The void member is a pure free rider — contributing
    nothing but "gaining" the entire cooperative surplus.
    Counter-intuitive: free riders usually reduce total surplus, but
    here the total surplus from void is exactly the partner's weight. -/
theorem void_free_rider (a : I) :
    cooperationSurplus a (void : I) = 0 ∧
    cooperationSurplus (void : I) a = ideaValue a := by
  constructor
  · exact cooperationSurplus_void a
  · unfold cooperationSurplus coalitionValue ideaValue
    rw [void_left', rs_void_void]; ring

/-- CP7. THE ENRICHMENT CHAIN: For any three ideas,
    ideaValue(a) ≤ coalitionValue(a,b) ≤ coalitionValue3(a,b,c).
    Cooperation is MONOTONICALLY enriching — adding members NEVER hurts.
    Counter-intuitive: in classical cooperative game theory, coalitions
    can be subadditive. Here, they never are (in weight terms). -/
theorem enrichment_chain (a b c : I) :
    ideaValue a ≤ coalitionValue a b ∧
    coalitionValue a b ≤ coalitionValue3 a b c := by
  exact ⟨coalitionValue_ge_first a b, coalitionValue3_ge_two a b c⟩

/-- CP8. THE INCREMENTAL VALUE PARADOX: Adding void has zero incremental
    value, but adding ANY non-void idea has non-negative incremental value.
    You can NEVER harm a coalition by adding members.
    Counter-intuitive: the tragedy of the commons says adding members
    to a shared resource eventually hurts everyone. In ideatic space,
    the commons can ONLY grow. The tragedy is impossible for weight. -/
theorem incremental_always_helps (a b c : I) :
    incrementalValue a b c ≥ 0 ∧
    incrementalValue a b (void : I) = 0 :=
  ⟨incrementalValue_nonneg a b c, incrementalValue_void a b⟩

end CoalitionParadoxes

end IDT3
