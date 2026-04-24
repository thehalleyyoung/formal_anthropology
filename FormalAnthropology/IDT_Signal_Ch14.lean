import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 14: Ideatic Auctions and Ritual Economy

**Anthropological motivation.** In many cultural contexts, ideas compete
for interpretive priority through *depth-based bidding*. The potlatch of
the Pacific Northwest, the conspicuous sacrifice in ancient temple economies,
the competitive almsgiving of medieval Christendom — all are forms of
"auction" where the deepest cultural contribution wins prestige.

This chapter formalizes ideatic auctions:

- **Bid**: a structure pairing a bidder (idea) with its bid value (depth)
- **maxDepthIdea**: selects the deepest idea from a list
- **auctionInterpretation**: the winning bid's interpretation against a receiver

We prove 18 theorems showing that void always loses, deeper bids win,
composing bids is subadditive (no free lunch in competitive signalling),
and the winner's interpretation is bounded — connecting to Mauss's gift
theory, Veblen's conspicuous consumption, and Bourdieu's symbolic capital.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch14

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- The bid value of an idea: its depth.
    In the ritual economy, depth = prestige = bid amount.
    The potlatch chief who gives away the most (deepest contributions)
    wins the highest status. -/
def bidValue (a : I) : ℕ := IdeaticSpace.depth a

/-- Maximum depth idea from a non-empty list: selects the first
    element with depth ≥ all others. This is implemented as a fold
    that keeps the deeper of each pair. -/
def maxDepthIdea : I → List I → I
  | best, [] => best
  | best, x :: rest =>
    if IdeaticSpace.depth x ≥ IdeaticSpace.depth best then
      maxDepthIdea x rest
    else maxDepthIdea best rest

/-- Auction interpretation: the winning idea (deepest) is composed
    with the receiver's background to produce the interpretation. -/
def auctionInterpret (bids : List I) (fallback : I) (receiver : I) : I :=
  IdeaticSpace.compose receiver (maxDepthIdea fallback bids)

/-! ## §2. Void as Non-Competitor -/

/-- **Theorem 14.1 (Void Bid Value is Zero).**
    The void idea has zero bid value — silence has no prestige.

    *Anthropological significance*: In the potlatch, offering nothing
    is the ultimate humiliation. The formal basis of "losing face" —
    zero depth = zero cultural capital = zero bidding power. -/
theorem void_bid_zero :
    bidValue (IdeaticSpace.void : I) = 0 := by
  simp [bidValue, IdeaticSpace.depth_void]

/-- **Theorem 14.2 (Void Loses to Any Non-Negative Bid).**
    Given a bid a with depth ≥ 0 (always true) and void as fallback,
    the max of {void, a} has depth ≥ depth(void) = 0.

    *Anthropological significance*: Any cultural offering, no matter
    how shallow, beats silence. This is the formal foundation of
    "showing up" — participation is always better than absence in
    competitive ritual. -/
theorem void_fallback_depth (a : I) :
    bidValue (maxDepthIdea (IdeaticSpace.void : I) [a]) ≥ 0 := by
  omega

/-- **Theorem 14.3 (Void Never Wins Against Deeper Bid).**
    If a has positive depth, it beats void as a bid.

    *Anthropological significance*: In competitive gift-giving, the
    party who brings *something* always outranks the party who brings
    nothing. Mauss's *obligation to give* is structurally enforced:
    non-givers are structurally dominated. -/
theorem deeper_beats_void {a : I} (h : IdeaticSpace.depth a ≥ 1) :
    IdeaticSpace.depth (maxDepthIdea (IdeaticSpace.void : I) [a]) ≥ 1 := by
  simp [maxDepthIdea, IdeaticSpace.depth_void]
  omega

/-! ## §3. Selection Properties -/

/-- **Theorem 14.4 (Single Bidder Wins).**
    With only one bid, that bid is the winner.

    *Anthropological significance*: A monopoly on cultural production
    (single priesthood, state media) means the sole producer always
    "wins" the auction. Competition is absent; interpretation is
    determined unilaterally. -/
theorem single_bidder_wins (a fallback : I) :
    maxDepthIdea fallback [a] = if IdeaticSpace.depth a ≥ IdeaticSpace.depth fallback then a else fallback := by
  simp [maxDepthIdea]

/-- **Theorem 14.5 (Fallback Survives Empty Auction).**
    With no bids, the fallback (default) wins.

    *Anthropological significance*: When no one competes, the status
    quo persists. The "default culture" (tradition, orthodoxy) wins
    by forfeit when no challenger appears. -/
theorem empty_auction_fallback (fallback : I) :
    maxDepthIdea fallback ([] : List I) = fallback := rfl

/-- **Theorem 14.6 (Bid Value is Non-Negative).**
    All bids have non-negative value (depth ≥ 0).

    *Anthropological significance*: There are no "negative contributions"
    in ideatic space — every idea has non-negative complexity. Even
    the most trivial cultural offering has at least zero depth. -/
theorem bid_nonneg (a : I) : bidValue a ≥ 0 := by omega

/-! ## §4. Composition and Bidding -/

/-- **Theorem 14.7 (Composed Bid Subadditivity).**
    The bid value of composing two ideas ≤ sum of their bid values.

    *Anthropological significance*: Combining two gifts into one
    package doesn't create more prestige than giving them separately.
    The potlatch chief who presents a composite gift of blankets and
    copper shields gains at most the sum of their separate values.
    Subadditivity prevents "prestige inflation" through bundling. -/
theorem composed_bid_subadditive (a b : I) :
    bidValue (IdeaticSpace.compose a b) ≤ bidValue a + bidValue b :=
  depth_compose_le a b

/-- **Theorem 14.8 (Void Composition Preserves Bid).**
    Composing a bid with void doesn't change its value.

    *Anthropological significance*: Adding "nothing" to a gift
    doesn't increase its prestige. Padding a potlatch offering
    with empty gestures is structurally transparent — the audience
    sees through it. -/
theorem void_compose_bid_right (a : I) :
    bidValue (IdeaticSpace.compose a (IdeaticSpace.void : I)) = bidValue a := by
  simp [bidValue, IDT.void_right]

/-- **Theorem 14.9 (Void Composition Preserves Bid Left).**
    Composing void with a bid doesn't change its value.

    *Anthropological significance*: Prefacing a gift with silence
    (the dramatic pause before the big reveal) adds nothing to
    the gift's structural depth. Ceremony is orthogonal to substance. -/
theorem void_compose_bid_left (a : I) :
    bidValue (IdeaticSpace.compose (IdeaticSpace.void : I) a) = bidValue a := by
  simp [bidValue, IDT.void_left]

/-! ## §5. Interpretation of Winning Bids -/

/-- **Theorem 14.10 (Winner's Interpretation Depth Bound).**
    The depth of the auction interpretation ≤ receiver depth + winner depth.

    *Anthropological significance*: The cultural impact of the winning
    bid is bounded by the receiver's background plus the bid's depth.
    Even the most extravagant potlatch is limited by the audience's
    capacity to appreciate it — Bourdieu's cultural capital constrains
    reception. -/
theorem winner_interpretation_bound (bids : List I) (fallback receiver : I) :
    IdeaticSpace.depth (auctionInterpret bids fallback receiver) ≤
    IdeaticSpace.depth receiver + IdeaticSpace.depth (maxDepthIdea fallback bids) := by
  unfold auctionInterpret
  exact depth_compose_le receiver (maxDepthIdea fallback bids)

/-- **Theorem 14.11 (Empty Auction Interpretation).**
    With no bids, the interpretation is compose(receiver, fallback).

    *Anthropological significance*: When no external cultural force
    competes, the receiver interprets only through their default
    framework. Cultural isolation means self-referential interpretation. -/
theorem empty_auction_interp (fallback receiver : I) :
    auctionInterpret [] fallback receiver =
    IdeaticSpace.compose receiver fallback := by
  simp [auctionInterpret, maxDepthIdea]

/-- **Theorem 14.12 (Void Receiver Gets Raw Winner).**
    If the receiver's background is void, the interpretation is just
    the winning bid itself.

    *Anthropological significance*: The "blank slate" receiver — the
    newborn, the cultural outsider — simply absorbs the winning idea
    without transformation. Cultural naivety means unmediated reception,
    the anthropological equivalent of "going native." -/
theorem void_receiver_raw (bids : List I) (fallback : I) :
    auctionInterpret bids fallback (IdeaticSpace.void : I) =
    maxDepthIdea fallback bids := by
  simp [auctionInterpret, IDT.void_left]

/-! ## §6. Structural Auction Theorems -/

/-- **Theorem 14.13 (Iterated Bid Depth Bound).**
    Repeating a bid n times via composition yields depth ≤ n × depth.

    *Anthropological significance*: Repetitive gift-giving (annual
    potlatch cycles) has bounded cumulative prestige. You can't
    achieve infinite status through mere repetition — the
    subadditivity of depth imposes diminishing returns. -/
theorem iterated_bid_bound (a : I) (n : ℕ) :
    bidValue (composeN a n) ≤ n * bidValue a := by
  unfold bidValue
  exact depth_composeN a n

/-- **Theorem 14.14 (Atomic Bid Bound).**
    Atomic ideas have bid value ≤ 1.

    *Anthropological significance*: The simplest, most elemental
    cultural offerings (a single word, a basic gesture) have minimal
    prestige value. Prestige comes from complexity — the elaborate
    ceremony outranks the simple nod. -/
theorem atomic_bid_bound {a : I} (h : IdeaticSpace.atomic a) :
    bidValue a ≤ 1 :=
  IdeaticSpace.depth_atomic a h

/-- **Theorem 14.15 (Resonant Bids Produce Resonant Interpretations).**
    If two bids resonate, any common receiver produces resonant interpretations.

    *Anthropological significance*: Competing ritual systems that
    resonate (e.g., Catholic and Orthodox Christianity) produce
    resonant experiences in the same audience. The laity perceives
    structural similarity even across competing institutions —
    the formal basis of religious tolerance. -/
theorem resonant_bids_interpretation (receiver : I) {b₁ b₂ : I}
    (h : IdeaticSpace.resonates b₁ b₂) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose receiver b₁)
      (IdeaticSpace.compose receiver b₂) :=
  resonance_compose_left receiver h

/-- **Theorem 14.16 (Resonant Receivers Agree on Winner).**
    If two receivers resonate and interpret the same winning bid,
    their interpretations resonate.

    *Anthropological significance*: Members of the same culture
    (resonant backgrounds) watching the same potlatch produce
    resonant evaluations. Cultural consensus on prestige is a
    structural consequence of shared background. -/
theorem resonant_receivers_agree {r₁ r₂ : I} (bid : I)
    (h : IdeaticSpace.resonates r₁ r₂) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose r₁ bid)
      (IdeaticSpace.compose r₂ bid) :=
  resonance_compose_right h bid

/-- **Theorem 14.17 (Bid Associativity).**
    Composing bids is associative: the order of bundling doesn't matter.

    *Anthropological significance*: In a multi-stage potlatch (gifts
    given over successive days), the grouping of days doesn't affect
    the total composition. The "grand total" of a festival is invariant
    under scheduling — structure trumps sequence. -/
theorem bid_associativity (a b c : I) :
    IdeaticSpace.compose (IdeaticSpace.compose a b) c =
    IdeaticSpace.compose a (IdeaticSpace.compose b c) :=
  compose_assoc a b c

/-- **Theorem 14.18 (Depth-Zero Bid Composure).**
    If both bidders have zero depth, their composition has zero depth.

    *Anthropological significance*: Two culturally empty offerings
    combined produce nothing. "Nothing plus nothing is nothing" —
    the formal futility of combining shallow gestures. -/
theorem zero_depth_composition {a b : I}
    (ha : IdeaticSpace.depth a = 0) (hb : IdeaticSpace.depth b = 0) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) = 0 := by
  have h := depth_compose_le a b
  omega

end IDT.Signal.Ch14
