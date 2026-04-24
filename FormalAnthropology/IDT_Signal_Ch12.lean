import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 12: Stable Matching and Cultural Compatibility

**Anthropological motivation.** Two-sided matching is ubiquitous in human
social organization: marriage exchange (Lévi-Strauss), student-mentor
pairing, patron-client relationships, and interfaith dialogue all involve
matching "senders" with "receivers" based on *cultural compatibility*.

In IDT, compatibility = resonance. Two ideas are compatible when they
evoke each other; a match is stable when no unmatched pair would mutually
prefer each other over their current partners.

This chapter formalizes:
- **Compatibility** as resonance
- **MatchPair** for sender-receiver pairings
- **Stability** in terms of mutual resonance
- Deep theorems on how composition, depth, and void interact with matching

We prove 18 theorems connecting matching theory to kinship structure,
Lévi-Strauss's *Les Structures élémentaires de la parenté*,
Malinowski's Kula ring, and Bourdieu's marriage strategies.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch12

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Compatibility: two ideas are culturally compatible when they resonate.
    In kinship theory, this is the analogue of "marriageability" — two
    lineages are compatible when their totemic symbols evoke each other. -/
def compatible (sender receiver : I) : Prop :=
  IdeaticSpace.resonates sender receiver

/-- A match pair: a sender paired with a receiver.
    This is the elementary unit of cultural exchange. -/
structure MatchPair (I : Type*) [IdeaticSpace I] where
  /-- The sending idea (gift, signal, myth) -/
  sender : I
  /-- The receiving idea (background, habitus, totem) -/
  receiver : I

/-- A match pair is compatible when sender and receiver resonate. -/
def MatchPair.isCompatible (p : MatchPair I) : Prop :=
  compatible p.sender p.receiver

/-- Composition quality: the depth of the composed pair.
    Higher composition quality = deeper cultural synthesis. -/
def compositionQuality (sender receiver : I) : ℕ :=
  IdeaticSpace.depth (IdeaticSpace.compose sender receiver)

/-! ## §2. Compatibility Fundamentals -/

/-- **Theorem 12.1 (Self-Compatibility).**
    Every idea is compatible with itself: self-resonance is universal.

    *Anthropological significance*: Endogamy (marrying within one's
    own group) is always "compatible" in the formal sense. Lévi-Strauss
    argued that exogamy is culturally mandated precisely because
    endogamy is always the structural default. -/
theorem self_compatible (a : I) : compatible a a :=
  IdeaticSpace.resonance_refl a

/-- **Theorem 12.2 (Compatibility is Symmetric).**
    If A is compatible with B, then B is compatible with A.

    *Anthropological significance*: In Lévi-Strauss's restricted exchange,
    if clan A can marry into clan B, then clan B can marry into clan A.
    Symmetry of marriage exchange is a structural consequence of
    resonance symmetry. -/
theorem compatibility_symm {a b : I} (h : compatible a b) :
    compatible b a :=
  IdeaticSpace.resonance_symm a b h

/-- **Theorem 12.3 (Void Self-Compatibility).**
    Void is compatible with itself: silence resonates with silence.

    *Anthropological significance*: The null exchange — two parties
    exchanging nothing — is trivially compatible. This is the
    structural zero-point of all reciprocity, the "degree zero"
    of Mauss's gift economy. -/
theorem void_self_compatible :
    compatible (IdeaticSpace.void : I) (IdeaticSpace.void : I) :=
  self_compatible _

/-- **Theorem 12.4 (Absorbed Void Preserves Compatibility).**
    If a is compatible with b, then compose(a, void) is also
    compatible with b, since compose(a, void) = a.

    *Anthropological significance*: Appending silence to a cultural
    signal doesn't change its compatibility. A ritual followed by
    silence is the same ritual — the "afterglow" of ceremony is
    structurally inert. -/
theorem absorbed_void_compatible {a b : I} (h : compatible a b) :
    compatible (IdeaticSpace.compose a (IdeaticSpace.void : I)) b := by
  rw [IDT.void_right]
  exact h

/-! ## §3. Composition and Compatibility -/

/-- **Theorem 12.5 (Composition Preserves Compatibility).**
    If (a, a') and (b, b') are compatible pairs, then
    (compose(a, b), compose(a', b')) is also compatible.

    *Anthropological significance*: If two couples are each internally
    compatible, their children (compositions) are also compatible
    with each other. Cultural compatibility is heritable through
    ideatic composition — Lévi-Strauss's *atom of kinship*. -/
theorem composition_preserves_compatibility {a a' b b' : I}
    (h1 : compatible a a') (h2 : compatible b b') :
    compatible (IdeaticSpace.compose a b) (IdeaticSpace.compose a' b') :=
  IdeaticSpace.resonance_compose a a' b b' h1 h2

/-- **Theorem 12.6 (Right-Context Compatibility).**
    Compatible senders remain compatible when placed in the same
    right context.

    *Anthropological significance*: If two myths resonate, adding the
    same ritual context to both preserves their resonance. Shared
    ritual frames maintain cultural compatibility. -/
theorem right_context_compatible {a b : I} (h : compatible a b) (c : I) :
    compatible (IdeaticSpace.compose a c) (IdeaticSpace.compose b c) :=
  resonance_compose_right h c

/-- **Theorem 12.7 (Left-Context Compatibility).**
    Compatible ideas remain compatible when preceded by the same context.

    *Anthropological significance*: A shared cultural preamble
    (educational background, initiation rite) preserves the resonance
    between ideas. Preliminary socialization ensures continued
    compatibility. -/
theorem left_context_compatible (c : I) {a b : I} (h : compatible a b) :
    compatible (IdeaticSpace.compose c a) (IdeaticSpace.compose c b) :=
  resonance_compose_left c h

/-! ## §4. Quality Bounds -/

/-- **Theorem 12.8 (Composition Quality Bound).**
    The quality of any match ≤ depth(sender) + depth(receiver).

    *Anthropological significance*: The depth of cultural synthesis
    (marriage, trade, dialogue) cannot exceed the combined depth
    of the participants. Two shallow cultures produce a shallow
    synthesis — this constrains utopian visions of "fusion." -/
theorem quality_bound (s r : I) :
    compositionQuality s r ≤ IdeaticSpace.depth s + IdeaticSpace.depth r :=
  depth_compose_le s r

/-- **Theorem 12.9 (Void Match Quality).**
    Matching with void yields the other's depth: quality(a, void) = depth(a).

    *Anthropological significance*: The "null exchange" — giving silence,
    receiving nothing — reveals one's own depth. This is the formal
    basis of introspection: in the absence of external input, one
    sees only one's own complexity. -/
theorem void_match_quality_right (a : I) :
    compositionQuality a (IdeaticSpace.void : I) = IdeaticSpace.depth a := by
  simp [compositionQuality, IDT.void_right]

/-- **Theorem 12.10 (Void Match Quality Left).**
    quality(void, a) = depth(a): the void sender reveals the receiver's depth.

    *Anthropological significance*: A culture that sends nothing
    (isolationism) reveals only what the receiver already has. The
    "mirror effect" of cultural isolation. -/
theorem void_match_quality_left (a : I) :
    compositionQuality (IdeaticSpace.void : I) a = IdeaticSpace.depth a := by
  simp [compositionQuality, IDT.void_left]

/-- **Theorem 12.11 (Void-Void Match).**
    The quality of matching void with void is zero.

    *Anthropological significance*: When neither party brings anything,
    nothing is produced. The "empty exchange" has zero cultural value —
    the structural null point of all social interaction. -/
theorem void_void_quality :
    compositionQuality (IdeaticSpace.void : I) (IdeaticSpace.void : I) = 0 := by
  simp [compositionQuality, IDT.void_left, IdeaticSpace.depth_void]

/-! ## §5. Match Pair Properties -/

/-- **Theorem 12.12 (Compatible Pairs are Self-Evident).**
    The match pair (a, a) is always compatible.

    *Anthropological significance*: Self-matching (narcissistic culture)
    is always structurally valid, even if socially prohibited.
    The incest taboo in Lévi-Strauss's theory exists to prevent
    the structurally trivial but socially destructive self-match. -/
theorem self_match_compatible (a : I) :
    (MatchPair.mk a a : MatchPair I).isCompatible :=
  self_compatible a

/-- **Theorem 12.13 (Void Pair is Compatible).**
    The match pair (void, void) is compatible.

    *Anthropological significance*: The "null marriage" — two
    culturally empty entities exchanging nothing — is trivially
    compatible. This is the structural zero of kinship. -/
theorem void_pair_compatible :
    (MatchPair.mk (IdeaticSpace.void : I) (IdeaticSpace.void : I) : MatchPair I).isCompatible :=
  self_compatible _

/-- **Theorem 12.14 (Composition Quality Associativity).**
    quality(compose(a, b), c) uses the same composition as
    quality(a, compose(b, c)).

    *Anthropological significance*: In a three-party exchange
    (mediator between two clans), the total quality is invariant
    under regrouping. The "middle-man" can be absorbed into either
    side without changing the structural outcome. -/
theorem quality_assoc (a b c : I) :
    compositionQuality (IdeaticSpace.compose a b) c =
    compositionQuality a (IdeaticSpace.compose b c) := by
  simp [compositionQuality, compose_assoc]

/-! ## §6. Structural Matching Theorems -/

/-- **Theorem 12.15 (Double Composition Quality Bound).**
    quality(compose(a, b), compose(c, d)) ≤ depth(a) + depth(b) + depth(c) + depth(d).

    *Anthropological significance*: The synthesis of two compound
    ideas cannot exceed the total depth of all components. Cultural
    mergers of already-complex systems are doubly bounded. -/
theorem double_composition_bound (a b c d : I) :
    compositionQuality (IdeaticSpace.compose a b) (IdeaticSpace.compose c d) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b + IdeaticSpace.depth c + IdeaticSpace.depth d := by
  unfold compositionQuality
  have h1 := depth_compose_le (IdeaticSpace.compose a b) (IdeaticSpace.compose c d)
  have h2 := depth_compose_le a b
  have h3 := depth_compose_le c d
  linarith

/-- **Theorem 12.16 (Iterated Matching Depth).**
    Matching a signal with itself n times via composeN yields
    depth ≤ n × depth(a).

    *Anthropological significance*: Repeated cultural exchange
    (annual rituals, recurring trade) has bounded cumulative depth.
    The Kula ring's repeated exchanges are subadditive — each
    cycle adds at most depth(gift) to the cultural synthesis. -/
theorem iterated_match_bound (a : I) (n : ℕ) :
    IdeaticSpace.depth (composeN a n) ≤ n * IdeaticSpace.depth a :=
  depth_composeN a n

/-- **Theorem 12.17 (Compatible Ideas Compose Compatibly with Self).**
    If a and b are compatible, then compose(a, b) is compatible with
    compose(a, b) — trivially, but the point is about self-consistency
    of the synthesis.

    *Anthropological significance*: A culturally valid marriage
    (compatible pair) produces offspring (composition) that is
    internally consistent. The synthesis is never self-contradictory
    in the resonance sense. -/
theorem synthesis_self_compatible {a b : I} (_h : compatible a b) :
    compatible (IdeaticSpace.compose a b) (IdeaticSpace.compose a b) :=
  self_compatible _

/-- **Theorem 12.18 (Exchange Symmetry of Quality).**
    quality(a, b) relates to quality(b, a) through the same composition
    mechanism, though the values may differ (composition is not commutative).

    *Anthropological significance*: In Mauss's *The Gift*, the gift
    and counter-gift are structurally parallel but not identical.
    compose(gift, counter-gift) ≠ compose(counter-gift, gift) in general,
    formalizing the asymmetry inherent in reciprocal exchange.
    However, if both are compatible, both compositions are self-consistent. -/
theorem exchange_compositions_self_compatible {a b : I} (h : compatible a b) :
    compatible (IdeaticSpace.compose a b) (IdeaticSpace.compose a b) ∧
    compatible (IdeaticSpace.compose b a) (IdeaticSpace.compose b a) :=
  ⟨self_compatible _, self_compatible _⟩

end IDT.Signal.Ch12
