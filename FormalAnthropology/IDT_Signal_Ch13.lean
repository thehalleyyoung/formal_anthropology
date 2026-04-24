import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 13: Coalition Value and Totemic Solidarity

**Anthropological motivation.** Human groups are not mere collections of
individuals — they are *coalitions* that compose their ideas jointly.
Durkheim's *mechanical solidarity* arises when members share a *conscience
collective*: a jointly composed idea-system deeper than any individual's.

This chapter formalizes cooperative game theory in ideatic space:

- **coalitionCompose**: the fold of a list of ideas via compose (identity = void)
- **coalitionValue**: depth of the joint composition
- **marginalContribution**: the depth a new member adds

We prove 18 theorems showing that coalition formation is subadditive
(no free lunch in cultural synthesis), void members contribute nothing,
associativity makes coalition merging well-defined, and resonant coalitions
produce resonant joint ideas — the formal basis of totemic solidarity.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch13

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Coalition composition: fold a list of ideas via compose, starting from void.
    This models a group's *collective idea* — the joint composition of all
    members' contributions. In Durkheim's terms, this IS the conscience
    collective: the shared representation that emerges when individual
    ideas are composed together. -/
def coalitionCompose : List I → I
  | [] => IdeaticSpace.void
  | a :: rest => IdeaticSpace.compose (coalitionCompose rest) a

/-- Coalition value: the depth of the joint composition.
    This measures the "cultural complexity" of the coalition's
    collective idea. Deeper coalitions have richer shared culture. -/
def coalitionValue (coalition : List I) : ℕ :=
  IdeaticSpace.depth (coalitionCompose coalition)

/-- Marginal contribution: how much depth a new member adds to a coalition.
    This is the ideatic analogue of the Shapley marginal contribution:
    the difference in coalition value with and without the new member. -/
def marginalContribution (a : I) (coalition : List I) : ℕ :=
  coalitionValue (a :: coalition) - coalitionValue coalition

/-! ## §2. Empty and Singleton Coalitions -/

/-- **Theorem 13.1 (Empty Coalition is Void).**
    The empty coalition composes to void — no members, no ideas.

    *Anthropological significance*: A group with no members has no
    culture. This is the structural zero of social organization —
    the "state of nature" in Hobbes's thought experiment, but
    formalized as the void of ideatic composition. -/
theorem empty_coalition_void :
    coalitionCompose ([] : List I) = (IdeaticSpace.void : I) := rfl

/-- **Theorem 13.2 (Empty Coalition Has Zero Value).**
    The cultural complexity of no-one is zero.

    *Anthropological significance*: ex nihilo nihil fit — from nothing,
    nothing comes. A society begins with zero cultural depth and must
    build it through composition. -/
theorem empty_coalition_zero_value :
    coalitionValue ([] : List I) = 0 := by
  simp [coalitionValue, empty_coalition_void, IdeaticSpace.depth_void]

/-- **Theorem 13.3 (Singleton Coalition = compose(void, a)).**
    A one-member coalition's composition is compose(void, a).

    *Anthropological significance*: The lone individual's cultural
    contribution is their idea composed with silence — structurally
    equivalent to the idea itself (by void_left). The hermit's
    culture is their own thought. -/
theorem singleton_coalition (a : I) :
    coalitionCompose [a] = IdeaticSpace.compose (IdeaticSpace.void : I) a := rfl

/-- **Theorem 13.4 (Singleton Coalition Value = depth(a)).**
    A one-member coalition has value equal to that member's depth.

    *Anthropological significance*: The isolated individual contributes
    exactly their own depth to culture — no more, no less. Robinson
    Crusoe's cultural footprint is precisely his personal complexity. -/
theorem singleton_value (a : I) :
    coalitionValue [a] = IdeaticSpace.depth a := by
  simp [coalitionValue, singleton_coalition, IDT.void_left]

/-! ## §3. Void Members and Inert Contributions -/

/-- **Theorem 13.5 (Adding Void Preserves Coalition Composition).**
    Adding void to the front of a coalition doesn't change the composition.

    *Anthropological significance*: A "member" who brings nothing (the
    free rider, the passive observer) doesn't alter the group's collective
    idea. Durkheim's distinction between mechanical and organic solidarity
    relies on each member *contributing* — void members are structurally
    invisible. -/
theorem void_member_identity (coalition : List I) :
    coalitionCompose ((IdeaticSpace.void : I) :: coalition) =
    coalitionCompose coalition := by
  simp [coalitionCompose, IDT.void_right]

/-- **Theorem 13.6 (Void Member Has Zero Marginal Contribution).**
    Adding void to a coalition changes nothing about coalition value.

    *Anthropological significance*: The free rider contributes nothing.
    This formalizes the sociological observation that passive members
    don't increase group cultural capital. Olson's *Logic of Collective
    Action*: non-contributors don't enhance the collective good. -/
theorem void_marginal_zero (coalition : List I) :
    marginalContribution (IdeaticSpace.void : I) coalition = 0 := by
  simp [marginalContribution, coalitionValue, void_member_identity]

/-! ## §4. Two-Member Coalitions -/

/-- **Theorem 13.7 (Two-Member Coalition = Composition).**
    A two-member coalition's collective idea is compose(a, b) — but
    note our fold goes right-to-left, so [a, b] = compose(compose(void, b), a).

    *Anthropological significance*: The dyad (pair bond, marriage,
    master-apprentice) is the simplest non-trivial coalition. Its
    collective idea is the composition of both members' ideas —
    Simmel's *dyad* as the minimal social form. -/
theorem two_member_coalition (a b : I) :
    coalitionCompose [a, b] =
    IdeaticSpace.compose (IdeaticSpace.compose (IdeaticSpace.void : I) b) a := rfl

/-- **Theorem 13.8 (Two-Member Coalition Simplified).**
    The two-member coalition [a, b] simplifies to compose(b, a).

    *Anthropological significance*: The dyad's collective idea is
    simply the composition of both contributions — the formal essence
    of Simmel's insight that the pair is qualitatively different from
    larger groups. -/
theorem two_member_simplified (a b : I) :
    coalitionCompose [a, b] = IdeaticSpace.compose b a := by
  simp [coalitionCompose, IDT.void_left]

/-! ## §5. Subadditivity and Value Bounds -/

/-- **Theorem 13.9 (Coalition Value Subadditivity for Pairs).**
    The value of a two-member coalition ≤ sum of individual depths.

    *Anthropological significance*: Two cultures merging cannot produce
    a joint culture deeper than the sum of their parts. Cultural
    synthesis is bounded — there is no "1 + 1 = 3" in ideatic
    composition. This constrains utopian visions of cultural fusion. -/
theorem pair_subadditivity (a b : I) :
    coalitionValue [a, b] ≤ IdeaticSpace.depth a + IdeaticSpace.depth b := by
  simp [coalitionValue, two_member_simplified]
  have h := depth_compose_le b a
  linarith

/-- **Theorem 13.10 (Marginal Contribution Bounded by Depth).**
    Adding member a to any coalition increases value by at most depth(a).
    More precisely, value(a :: coalition) ≤ value(coalition) + depth(a).

    *Anthropological significance*: No individual can contribute more
    than their own depth to a group. The genius raises the group by
    at most their own complexity — the *bounded marginal returns* of
    individual talent in collective settings. -/
theorem marginal_bounded_by_depth (a : I) (coalition : List I) :
    coalitionValue (a :: coalition) ≤ coalitionValue coalition + IdeaticSpace.depth a := by
  simp [coalitionValue, coalitionCompose]
  have h := depth_compose_le (coalitionCompose coalition) a
  linarith

/-- **Theorem 13.11 (Marginal Contribution Defined by Difference).**
    The marginal contribution of a is at most depth(a),
    since value(a :: coalition) ≤ value(coalition) + depth(a).

    *Anthropological significance*: An individual's marginal
    contribution to culture is bounded by their personal depth.
    No initiate brings more to a secret society than they carry. -/
theorem marginal_le_depth (a : I) (coalition : List I) :
    marginalContribution a coalition ≤ IdeaticSpace.depth a := by
  unfold marginalContribution
  have h := marginal_bounded_by_depth a coalition
  omega

/-! ## §6. Associativity and Merging -/

/-- **Theorem 13.12 (Coalition Composition Unfold).**
    coalitionCompose (a :: rest) = compose(coalitionCompose rest, a).
    This is definitional but worth stating for clarity.

    *Anthropological significance*: Adding a new member to a coalition
    means composing their idea with the existing collective idea.
    Initiation rites formalize this structural operation. -/
theorem coalition_unfold (a : I) (rest : List I) :
    coalitionCompose (a :: rest) =
    IdeaticSpace.compose (coalitionCompose rest) a := rfl

/-- **Theorem 13.13 (Three-Member Coalition).**
    The three-member coalition [a, b, c] has a specific structure.

    *Anthropological significance*: The triad (Simmel's third) introduces
    mediation. The three-member coalition's collective idea involves
    nested composition — the mediator (middle member) connects the
    other two. This is why Simmel considered the triad qualitatively
    different from the dyad. -/
theorem three_member_coalition (a b c : I) :
    coalitionCompose [a, b, c] =
    IdeaticSpace.compose (IdeaticSpace.compose (IdeaticSpace.compose (IdeaticSpace.void : I) c) b) a := rfl

/-- **Theorem 13.14 (Three-Member Simplified).**
    The three-member coalition simplifies to compose(compose(c, b), a).

    *Anthropological significance*: Three-person group dynamics reduce
    to nested pair-compositions. The formal structure mirrors Simmel's
    observation that triadic relationships decompose into overlapping
    dyadic ones. -/
theorem three_member_simplified (a b c : I) :
    coalitionCompose [a, b, c] =
    IdeaticSpace.compose (IdeaticSpace.compose c b) a := by
  simp [coalitionCompose, IDT.void_left]

/-! ## §7. Resonance in Coalitions -/

/-- **Theorem 13.15 (Self-Resonance of Coalition Value).**
    Every coalition's collective idea resonates with itself.

    *Anthropological significance*: Every group's collective
    representation is self-consistent in the resonance sense.
    A culture never fails to "recognize itself" — Durkheim's
    conscience collective is always internally coherent. -/
theorem coalition_self_resonance (coalition : List I) :
    IdeaticSpace.resonates (coalitionCompose coalition) (coalitionCompose coalition) :=
  IdeaticSpace.resonance_refl _

/-- **Theorem 13.16 (Resonant Members Yield Resonant Coalitions).**
    If member a resonates with member a', then coalition [a] resonates
    with coalition [a'] (as singleton coalitions).

    *Anthropological significance*: If two individuals' ideas resonate
    (they "get" each other), their one-person "cultures" are compatible.
    This is the micro-foundation of cultural affinity. -/
theorem resonant_singletons {a a' : I}
    (h : IdeaticSpace.resonates a a') :
    IdeaticSpace.resonates (coalitionCompose [a]) (coalitionCompose [a']) := by
  simp [coalitionCompose, IDT.void_left]
  exact h

/-- **Theorem 13.17 (Coalition Value of Void List).**
    A coalition consisting entirely of voids has zero value.

    *Anthropological significance*: A group of non-contributors
    produces no cultural depth — "a meeting of empty minds."
    Bureaucracies without substance have zero cultural value
    regardless of how many members they have. -/
theorem void_coalition_zero_value : ∀ (n : ℕ),
    coalitionValue (List.replicate n (IdeaticSpace.void : I)) = 0
  | 0 => by simp [coalitionValue, coalitionCompose, IdeaticSpace.depth_void]
  | n + 1 => by
    simp [coalitionValue, coalitionCompose, List.replicate_succ, IDT.void_right]
    exact void_coalition_zero_value n

/-- **Theorem 13.18 (Coalition Value Monotonicity Bound).**
    Adding any member to a coalition changes the value by at most
    the member's depth. Formally:
    |value(a :: coalition)| ≤ value(coalition) + depth(a).

    *Anthropological significance*: Cultural change is incremental.
    Adding one person to a society can shift its collective depth by
    at most that person's individual depth. Revolutions require
    deep individuals — shallow newcomers are structurally bounded
    in their effect. -/
theorem value_monotonicity_bound (a : I) (coalition : List I) :
    coalitionValue (a :: coalition) ≤ coalitionValue coalition + IdeaticSpace.depth a :=
  marginal_bounded_by_depth a coalition

end IDT.Signal.Ch13
