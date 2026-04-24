import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 10: Multi-Receiver Signalling and Public Ritual

**Anthropological motivation.** The defining feature of public ritual is
that the SAME signal is sent to MULTIPLE receivers with DIFFERENT cultural
backgrounds. A Catholic mass, a presidential inauguration, a national
anthem—each is a single performance witnessed by many minds, each of
which interprets it through their own repertoire.

Geertz's "thick description" captures this: the same cockfight means
"gambling" to one observer, "status contest" to another, "art" to a third.
Turner's "social drama" extends this to ritual: the same ceremony produces
different (but structurally related) experiences in different participants.

This chapter formalizes **multi-receiver signalling**:

- **Audience**: a list of repertoires (different minds)
- **audienceOutcome**: the list of interpretation lists
- **audienceConsensus**: all pairwise-resonant interpretations
- **Same signal, different minds**: interpretation count preserved per mind
- **Void signal transparent for all**: silence changes no one
- **Resonant audiences produce resonant outcomes**: structural similarity implies similar reactions

The central anthropological insight: public ritual WORKS not because
everyone gets the same meaning, but because everyone gets RESONANT meanings.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch10

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- A repertoire: one mind's stock of ideas. -/
abbrev Repertoire (I : Type*) := List I

/-- Interpretation through a single repertoire. -/
def interpret (rep : Repertoire I) (signal : I) : List I :=
  rep.map (fun r => IdeaticSpace.compose r signal)

/-- An audience: a collection of minds, each with its own repertoire.
    This is the formal model of a "public"—a heterogeneous collection
    of culturally distinct agents witnessing the same event. -/
abbrev Audience (I : Type*) := List (Repertoire I)

/-- The outcome of sending signal `s` to an audience: each mind
    produces its own list of interpretations. The result is a list of
    lists—one interpretation-list per audience member. -/
def audienceOutcome (audience : Audience I) (s : I) : List (List I) :=
  audience.map (fun rep => interpret rep s)

/-- Total audience depth sum: the sum of all depth sums across all minds. -/
def totalAudienceDepth (outcomes : List (List I)) : ℕ :=
  (outcomes.map (fun interp => depthSum interp)).sum

/-! ## §2. Structural Invariants -/

/-- **Theorem 10.1 (Audience Size Preservation).**
    The number of interpretation lists equals the audience size.
    Sending a signal doesn't create or destroy minds.

    *Anthropological significance*: A public ritual has exactly as many
    "experiences" as there are participants. No ghost observers, no
    merged consciousnesses. Each mind is counted exactly once. -/
theorem audience_outcome_length (audience : Audience I) (s : I) :
    (audienceOutcome audience s).length = audience.length := by
  simp [audienceOutcome]

/-- **Theorem 10.2 (Per-Receiver Interpretation Count).**
    Each mind produces exactly as many interpretations as it has ideas
    in its repertoire. The signal doesn't create or destroy ideas.

    *Anthropological significance*: Cultural contact transforms
    each schema but doesn't change how many schemas a mind holds.
    A five-category mind produces five interpretations; a fifty-category
    mind produces fifty. -/
theorem per_receiver_count (rep : Repertoire I) (s : I) :
    (interpret rep s).length = rep.length := by
  simp [interpret]

/-- **Theorem 10.3 (Same Signal Different Minds — Length Preserved).**
    For any member of the audience, their interpretation list has the
    same length as their repertoire.

    *Anthropological significance*: The "same ceremony, different meanings"
    principle—each participant brings their own framework and gets
    their own number of meanings, determined by THEIR background, not
    the signal. -/
theorem same_signal_different_minds (audience : Audience I) (s : I)
    (rep : Repertoire I) (hmem : rep ∈ audience) :
    (interpret rep s).length = rep.length := by
  simp [interpret]

/-! ## §3. Void Signal: Universal Transparency -/

/-- **Theorem 10.4 (Void Signal Transparent For All).**
    Silence leaves every mind unchanged: `interpret rep void = rep`.

    *Anthropological significance*: The minute of silence, the Quaker
    meeting, the Buddhist noble silence—all exploit this: by saying
    nothing, every participant's existing worldview remains intact.
    Silence is the only signal that is universally transparent. -/
theorem void_transparent_single (rep : Repertoire I) :
    interpret rep (IdeaticSpace.void : I) = rep := by
  induction rep with
  | nil => rfl
  | cons r rest ih =>
    simp only [interpret, List.map_cons]
    rw [IDT.void_right]
    exact congrArg (List.cons r) ih

/-- **Theorem 10.5 (Void Signal Transparent For All Audiences).**
    Silence leaves every audience member unchanged.

    *Anthropological significance*: Universal transparency of silence
    is the formal foundation of the "null ritual"—a ceremony that
    changes nothing. Every culture has such ceremonies: they serve
    social functions without altering anyone's ideas. -/
theorem void_transparent_audience (audience : Audience I) :
    audienceOutcome audience (IdeaticSpace.void : I) = audience := by
  induction audience with
  | nil => rfl
  | cons rep rest ih =>
    simp only [audienceOutcome, List.map_cons]
    rw [void_transparent_single]
    exact congrArg (List.cons rep) ih

/-! ## §4. Depth Bounds Across Audiences -/

/-- **Theorem 10.6 (Single Receiver Depth Bound).**
    One receiver's total interpretation depth ≤ their repertoire depth
    + |rep| × signal depth.

    *Game-theoretic significance*: Each audience member's "persuasion
    exposure" is linearly bounded. -/
theorem single_receiver_depth_bound (rep : Repertoire I) (s : I) :
    depthSum (interpret rep s) ≤
    depthSum rep + rep.length * IdeaticSpace.depth s := by
  induction rep with
  | nil => simp [interpret, depthSum]
  | cons r rest ih =>
    simp only [interpret, List.map_cons]
    rw [depthSum_cons, depthSum_cons]
    have hcomp := depth_compose_le r s
    have hlen : (r :: rest).length = rest.length + 1 := rfl
    rw [hlen]
    have : (rest.length + 1) * IdeaticSpace.depth s =
           rest.length * IdeaticSpace.depth s + IdeaticSpace.depth s := by ring
    simp only [interpret] at ih
    linarith

/-- **Theorem 10.7 (Audience Depth Bound — Per Member).**
    Each audience member's depth is individually bounded.

    *Anthropological significance*: In a public ceremony, each
    participant's total interpretive transformation is bounded by
    their own cultural depth plus the ceremony's complexity. A PhD
    and a child at the same concert are both bounded, but differently. -/
theorem audience_member_depth_bound (audience : Audience I) (s : I)
    (rep : Repertoire I) (hmem : rep ∈ audience) :
    depthSum (interpret rep s) ≤
    depthSum rep + rep.length * IdeaticSpace.depth s :=
  single_receiver_depth_bound rep s

/-- **Theorem 10.8 (Empty Audience Has Empty Outcome).**
    An audience with no members produces no interpretations.

    *Anthropological significance*: A ritual with no participants
    produces no effects. Performance requires an audience. -/
theorem empty_audience_outcome (s : I) :
    audienceOutcome ([] : Audience I) s = [] := rfl

/-- **Theorem 10.9 (Singleton Audience Outcome).**
    An audience of one produces exactly one interpretation list.

    *Anthropological significance*: A private ritual (one participant)
    produces exactly one set of meanings—the formal model of
    individual meditation or private prayer. -/
theorem singleton_audience_outcome (rep : Repertoire I) (s : I) :
    audienceOutcome [rep] s = [interpret rep s] := rfl

/-! ## §5. Resonance Across Audiences -/

/-- **Theorem 10.10 (Resonant Signals Same Audience).**
    If two signals resonate, then for each audience member, the
    interpretations of both signals are pairwise resonant.

    *Anthropological significance*: Christmas and Hanukkah are "resonant
    signals"—structurally similar festivals. Each participant's
    experience of one resonates with their experience of the other.
    This is why comparative religion is intellectually productive. -/
theorem resonant_signals_same_mind {s₁ s₂ : I}
    (hs : IdeaticSpace.resonates s₁ s₂) (r : I) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose r s₁) (IdeaticSpace.compose r s₂) :=
  resonance_compose_left r hs

/-- **Theorem 10.11 (Same Signal Resonant Receivers).**
    If two receivers' background ideas resonate, their interpretations
    of the same signal resonate.

    *Anthropological significance*: Two members of the same culture
    (resonant backgrounds) always produce resonant interpretations of
    the same event. This is Durkheim's *conscience collective*:
    cultural consensus is a structural consequence of shared backgrounds. -/
theorem same_signal_resonant_receivers {r₁ r₂ : I}
    (hr : IdeaticSpace.resonates r₁ r₂) (s : I) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose r₁ s) (IdeaticSpace.compose r₂ s) :=
  resonance_compose_right hr s

/-- **Theorem 10.12 (Full Resonance: Resonant Receivers + Resonant Signals).**
    Both receivers AND signals resonate ⇒ interpretations resonate.

    *Anthropological significance*: Members of allied cultures witnessing
    similar rituals produce resonant experiences. This is Turner's
    *communitas*: spontaneous solidarity arising when similar people
    undergo similar experiences. -/
theorem full_resonance {r₁ r₂ s₁ s₂ : I}
    (hr : IdeaticSpace.resonates r₁ r₂) (hs : IdeaticSpace.resonates s₁ s₂) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose r₁ s₁) (IdeaticSpace.compose r₂ s₂) :=
  IdeaticSpace.resonance_compose r₁ r₂ s₁ s₂ hr hs

/-- **Theorem 10.13 (Self-Resonance of All Audience Outcomes).**
    Every audience member's interpretation self-resonates.

    *Anthropological significance*: Each participant's experience of
    a ritual is internally consistent—regardless of how different
    participants' experiences are from each other. -/
theorem audience_self_resonance (rep : Repertoire I) (s : I) (r : I)
    (hr : r ∈ rep) :
    IdeaticSpace.resonates
      (IdeaticSpace.compose r s) (IdeaticSpace.compose r s) :=
  IdeaticSpace.resonance_refl _

/-! ## §6. Audience Composition and Merging -/

/-- **Theorem 10.14 (Audience Concatenation).**
    Merging two audiences then signalling = signalling each then merging results.

    *Anthropological significance*: A joint ceremony for two communities
    (e.g., an interfaith service) produces results that are just the
    concatenation of what each community would have experienced separately.
    There is no mysterious "synergy" in public ritual—just the union of
    individual experiences. -/
theorem audience_concat (aud₁ aud₂ : Audience I) (s : I) :
    audienceOutcome (aud₁ ++ aud₂) s =
    audienceOutcome aud₁ s ++ audienceOutcome aud₂ s := by
  simp [audienceOutcome, List.map_append]

/-- **Theorem 10.15 (Replicated Audience).**
    An audience of n identical minds produces n identical interpretation lists.

    *Anthropological significance*: A perfectly homogeneous community
    (n copies of the same cultural background) produces perfectly
    homogeneous responses to any signal. This is the theoretical
    limit of cultural uniformity—the formal "ideal type" of a
    totalitarian society. -/
theorem replicated_audience (rep : Repertoire I) (s : I) (n : ℕ) :
    audienceOutcome (List.replicate n rep) s =
    List.replicate n (interpret rep s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate, audienceOutcome, List.map_cons]
    exact congrArg (List.cons (interpret rep s)) ih

/-! ## §7. Advanced Multi-Receiver Properties -/

/-- **Theorem 10.16 (Sequential Signal to Audience).**
    Each audience member's interpretation of compose(s₁, s₂) equals
    their interpretation of s₂ with background pre-composed with s₁.

    *Anthropological significance*: A two-act ritual (overture + main act)
    is equivalent to the main act performed for an audience that has
    already absorbed the overture. The first act transforms the audience;
    the second act addresses the transformed audience. -/
theorem sequential_signal_audience (r s₁ s₂ : I) :
    IdeaticSpace.compose r (IdeaticSpace.compose s₁ s₂) =
    IdeaticSpace.compose (IdeaticSpace.compose r s₁) s₂ :=
  (compose_assoc r s₁ s₂).symm

/-- **Theorem 10.17 (Void Audience Member is Transparent).**
    A void-only mind (`[void]`) produces the signal itself as its interpretation.

    *Anthropological significance*: The "naive observer" with no cultural
    baggage sees the signal as-is. This formalizes the (impossible) ideal
    of Husserl's *epoché*—bracketing all presuppositions. -/
theorem void_audience_member (s : I) :
    interpret [(IdeaticSpace.void : I)] s = [s] := by
  simp [interpret, IDT.void_left]

/-- **Theorem 10.18 (Depth Bound for Void Outcome Across Audience).**
    When signal is void, every audience member's interpretation preserves
    their original depth sum.

    *Anthropological significance*: The "information cost" of silence is
    exactly zero for every audience member simultaneously. This is the
    formal foundation of the *status quo*: doing nothing changes nothing
    for anyone, regardless of their background. -/
theorem void_outcome_depth_preserved (rep : Repertoire I) :
    depthSum (interpret rep (IdeaticSpace.void : I)) = depthSum rep := by
  rw [void_transparent_single]

end IDT.Signal.Ch10
