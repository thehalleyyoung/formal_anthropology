import FormalAnthropology.IDT_Foundations

/-!
# Signalling Games in IDT — Chapter 6: Interpretive Equilibrium

**Anthropological motivation.** Stable cultural forms—greetings, taboos,
marriage rules, religious rituals—persist not because they are "optimal"
in any absolute sense, but because no individual can unilaterally improve
their situation by deviating. They are *Nash equilibria* of interpretation.

This chapter formalizes the game-theoretic concept of equilibrium within
IDT's framework:

- **InterpGame**: a game with repertoire, sender payoff, receiver payoff
- **outcome**: interpretation of a signal through a game's repertoire
- **IsEquilibrium**: a signal that maximizes sender payoff
- **Babbling Equilibrium**: void is always an equilibrium (Schelling)
- **Constant-Payoff Equilibrium**: if all signals pay equally, all are optimal
- **Resonance-Preserving Transformations**: equilibria are robust under
  meaning-preserving cultural change

The central anthropological insight: cultural stability is not about truth
or beauty—it is about the impossibility of profitable deviation.

## 18 Theorems, 0 Sorries
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.Signal.Ch6

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- A repertoire: the receiver's stock of ideas. -/
abbrev Repertoire (I : Type*) := List I

/-- Interpretation: composing each background idea with a signal. -/
def interpret (rep : Repertoire I) (signal : I) : List I :=
  rep.map (fun r => IdeaticSpace.compose r signal)

/-- An interpretation game: a repertoire plus payoff functions for sender
    and receiver. The payoff depends on the *interpretation* (the list of
    composed ideas), not the signal directly. This captures the anthropological
    insight that meaning is always mediated by the receiver's culture. -/
structure InterpGame (I : Type*) [IdeaticSpace I] where
  /-- The receiver's cultural background -/
  repertoire : Repertoire I
  /-- The sender's payoff from the resulting interpretation -/
  sender_payoff : List I → ℕ
  /-- The receiver's payoff from the resulting interpretation -/
  receiver_payoff : List I → ℕ

/-- The outcome of sending signal `s` in game `G`: the interpretation
    produced by composing the repertoire with the signal. -/
def outcome (G : InterpGame I) (s : I) : List I :=
  interpret G.repertoire s

/-- A signal `s` is an equilibrium if no alternative signal yields a
    strictly higher sender payoff. This is the Nash equilibrium condition
    for the sender: given the receiver's fixed repertoire, `s` is a best
    response. -/
def IsEquilibrium (G : InterpGame I) (s : I) : Prop :=
  ∀ (s' : I), G.sender_payoff (outcome G s') ≤ G.sender_payoff (outcome G s)

/-! ## §2. Babbling Equilibrium

"When nothing you say can improve on silence, silence is optimal."
— The formal foundation of Schelling's focal point theory. -/

/-- Outcome of void signal equals the repertoire itself: silence leaves
    meaning unchanged. -/
theorem outcome_void (G : InterpGame I) :
    outcome G (IdeaticSpace.void : I) = G.repertoire := by
  simp only [outcome, interpret]
  induction G.repertoire with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.map_cons]
    rw [IDT.void_right]
    exact congrArg (List.cons r) ih

/-- **Theorem 6.1 (Babbling Equilibrium / Schelling's Silence).**
    If no signal produces a strictly better payoff than silence,
    then void is an equilibrium. This always holds when the sender
    cannot improve on the status quo.

    *Anthropological significance*: In any culture, doing nothing is
    always a viable strategy. This explains the persistence of
    "babbling equilibria"—situations where signals carry no information
    because all parties know that no message can improve on silence.
    Lewis (1969) showed these exist in every signalling game. -/
theorem babbling_equilibrium (G : InterpGame I)
    (h : ∀ s : I, G.sender_payoff (outcome G s) ≤
         G.sender_payoff (outcome G (IdeaticSpace.void : I))) :
    IsEquilibrium G (IdeaticSpace.void : I) :=
  h

/-- **Theorem 6.2 (Constant-Payoff Equilibrium).**
    If every signal yields the same payoff, then every signal is an equilibrium.

    *Anthropological significance*: In a society where all cultural forms
    are equally valued (radical cultural relativism), there is no pressure
    to change any signal. Every ritual is as good as any other. This
    formalizes the anthropological observation that in highly egalitarian
    societies, ritual variation persists because there's no selection pressure. -/
theorem constant_payoff_equilibrium (G : InterpGame I) (k : ℕ)
    (hconst : ∀ s : I, G.sender_payoff (outcome G s) = k)
    (s : I) : IsEquilibrium G s := by
  intro s'
  rw [hconst s', hconst s]

/-- **Theorem 6.3 (Equilibrium is Reflexive).**
    Every signal is at least as good as itself: the equilibrium condition
    is reflexively satisfied at the reference point.

    *Game-theoretic significance*: This is the trivial direction of the
    Nash equilibrium definition—every strategy weakly dominates itself. -/
theorem equilibrium_refl (G : InterpGame I) (s : I) :
    G.sender_payoff (outcome G s) ≤ G.sender_payoff (outcome G s) :=
  le_refl _

/-! ## §3. Outcome Structural Properties -/

/-- **Theorem 6.4 (Outcome Length Invariance).**
    The number of interpretations equals the repertoire size, regardless
    of the signal sent. Signals transform but never create or destroy ideas.

    *Anthropological significance*: Cultural contact does not change how
    many schemas a society holds—it transforms each one. The "size" of a
    culture's conceptual inventory is invariant under external signalling. -/
theorem outcome_length (G : InterpGame I) (s : I) :
    (outcome G s).length = G.repertoire.length := by
  simp [outcome, interpret]

/-- **Theorem 6.5 (Outcome Length Independence).**
    Two different signals produce interpretation lists of the same length.

    *Game-theoretic significance*: The "action space" of interpretations
    has constant dimensionality across all possible signals. -/
theorem outcome_length_eq (G : InterpGame I) (s₁ s₂ : I) :
    (outcome G s₁).length = (outcome G s₂).length := by
  simp [outcome, interpret]

/-- **Theorem 6.6 (Empty Repertoire Trivial Outcome).**
    A receiver with no ideas produces no interpretations for any signal.

    *Anthropological significance*: A mind with zero cultural content
    cannot interpret anything. There is no "raw perception"—interpretation
    requires prior ideas. -/
theorem empty_repertoire_outcome (s : I) :
    outcome (⟨[], fun _ => 0, fun _ => 0⟩ : InterpGame I) s = [] := by
  rfl

/-- **Theorem 6.7 (Singleton Repertoire Outcome).**
    A single-idea mind produces exactly one interpretation.

    *Anthropological significance*: Monocultural societies have exactly
    one interpretation of every event. -/
theorem singleton_outcome (r s : I) (sp rp : List I → ℕ) :
    outcome (⟨[r], sp, rp⟩ : InterpGame I) s = [IdeaticSpace.compose r s] := by
  rfl

/-! ## §4. Depth Bounds on Outcomes -/

/-- **Theorem 6.8 (Outcome Depth Bound).**
    The total depth of all interpretations is bounded by
    repertoire depth + |rep| × signal depth.

    *Game-theoretic significance*: The sender's "persuasive reach" is
    linearly bounded by signal complexity times audience size. -/
theorem outcome_depth_bound (rep : Repertoire I) (s : I) (sp rp : List I → ℕ) :
    depthSum (outcome (⟨rep, sp, rp⟩ : InterpGame I) s) ≤
    depthSum rep + rep.length * IdeaticSpace.depth s := by
  induction rep with
  | nil => simp [outcome, interpret, depthSum]
  | cons r rest ih =>
    simp only [outcome, interpret, List.map_cons]
    rw [depthSum_cons, depthSum_cons]
    have hcomp := depth_compose_le r s
    have hlen : (r :: rest).length = rest.length + 1 := rfl
    rw [hlen]
    have : (rest.length + 1) * IdeaticSpace.depth s =
           rest.length * IdeaticSpace.depth s + IdeaticSpace.depth s := by ring
    have ihm := ih
    simp only [outcome, interpret] at ihm
    linarith

/-- **Theorem 6.9 (Void Outcome Preserves Depth).**
    Silence preserves total interpretive complexity exactly.

    *Anthropological significance*: The "cost" of silence is exactly zero
    in every dimension—not just payoff, but information content. -/
theorem void_outcome_depth (G : InterpGame I) :
    depthSum (outcome G (IdeaticSpace.void : I)) = depthSum G.repertoire := by
  rw [outcome_void]

/-! ## §5. Resonance and Equilibrium -/

/-- **Theorem 6.10 (Resonant Signals Produce Resonant Outcomes).**
    If two signals resonate, their outcomes are pairwise resonant:
    for each position in the repertoire, the two interpretations resonate.

    *Anthropological significance*: Structurally similar rituals
    (Christmas vs. Hanukkah, weddings across cultures) produce
    structurally similar experiences for each participant. This is
    why comparative anthropology is possible at all. -/
theorem resonant_signals_resonant_outcomes
    (G : InterpGame I) {s₁ s₂ : I}
    (h : IdeaticSpace.resonates s₁ s₂) (r : I) (hr : r ∈ G.repertoire) :
    IdeaticSpace.resonates (IdeaticSpace.compose r s₁) (IdeaticSpace.compose r s₂) :=
  resonance_compose_left r h

/-- **Theorem 6.11 (Self-Resonance of Outcomes).**
    Every outcome resonates with itself at each position.

    *Game-theoretic significance*: Consistency of interpretation is
    guaranteed—a single signal always produces self-consistent interpretations. -/
theorem outcome_self_resonance (G : InterpGame I) (s : I)
    (r : I) (hr : r ∈ G.repertoire) :
    IdeaticSpace.resonates (IdeaticSpace.compose r s) (IdeaticSpace.compose r s) :=
  IdeaticSpace.resonance_refl _

/-- **Theorem 6.12 (Equilibrium Under Payoff Majorization).**
    If G₁'s payoff always dominates G₂'s for signal s, and s is an
    equilibrium for G₂, and G₁ = G₂ on the repertoire and alternatives,
    then s is an equilibrium for G₁ too (when payoffs agree on all outcomes).

    *Anthropological significance*: If a cultural form is stable in a
    less-rewarding environment, it remains stable in a more-rewarding one
    with the same relative rankings. -/
theorem equilibrium_payoff_agreement
    (G₁ G₂ : InterpGame I)
    (hrep : G₁.repertoire = G₂.repertoire)
    (hpay : ∀ s : I, G₁.sender_payoff (outcome G₁ s) = G₂.sender_payoff (outcome G₂ s))
    (s : I) (heq : IsEquilibrium G₂ s) :
    IsEquilibrium G₁ s := by
  intro s'
  rw [hpay s', hpay s]
  exact heq s'

/-! ## §6. Composition and Sequential Signalling -/

/-- **Theorem 6.13 (Sequential Signal Composition).**
    Interpreting signal s₁ then s₂ through a single background idea
    equals interpreting the composed signal compose(s₁, s₂) once,
    with the background pre-composed with s₁.

    *Anthropological significance*: A ritual with two acts can be
    understood as a single compound act—but only from the perspective
    of someone who has already absorbed the first act into their background. -/
theorem sequential_signal (r s₁ s₂ : I) :
    IdeaticSpace.compose (IdeaticSpace.compose r s₁) s₂ =
    IdeaticSpace.compose r (IdeaticSpace.compose s₁ s₂) :=
  compose_assoc r s₁ s₂

/-- **Theorem 6.14 (Equilibrium Stability Under Void Extension).**
    If s is an equilibrium, composing s with void on the right doesn't
    change the outcome (and hence doesn't affect equilibrium status).

    *Game-theoretic significance*: Padding a message with silence
    doesn't change the game. This is the formal version of "cheap talk
    is irrelevant when it carries no information." -/
theorem equilibrium_void_extension (G : InterpGame I) (s : I) :
    outcome G (IdeaticSpace.compose s (IdeaticSpace.void : I)) = outcome G s := by
  simp only [outcome, interpret]
  congr 1
  ext r
  show IdeaticSpace.compose r (IdeaticSpace.compose s IdeaticSpace.void) =
       IdeaticSpace.compose r s
  rw [IDT.void_right]

/-- **Theorem 6.15 (Dual Repertoire Combination).**
    The outcome for a combined repertoire equals the concatenation of
    individual outcomes.

    *Anthropological significance*: A bilingual mind's interpretation
    is the union of each language's interpretation—there is no mysterious
    "third space" of bilingual meaning, just the disjoint combination. -/
theorem dual_repertoire_outcome (rep₁ rep₂ : Repertoire I) (s : I)
    (sp rp : List I → ℕ) :
    outcome (⟨rep₁ ++ rep₂, sp, rp⟩ : InterpGame I) s =
    outcome (⟨rep₁, sp, rp⟩ : InterpGame I) s ++
    outcome (⟨rep₂, sp, rp⟩ : InterpGame I) s := by
  simp [outcome, interpret, List.map_append]

/-! ## §7. Advanced Equilibrium Properties -/

/-- **Theorem 6.16 (Maximum Payoff Equilibrium).**
    If a signal achieves the maximum possible sender payoff (bounded by
    some `M`), it is an equilibrium.

    *Anthropological significance*: The most sacred ritual—the one that
    maximizes collective effervescence (Durkheim)—is always in equilibrium
    because nothing can improve on the maximum. -/
theorem max_payoff_equilibrium (G : InterpGame I) (s : I) (M : ℕ)
    (hmax : G.sender_payoff (outcome G s) = M)
    (hbound : ∀ s' : I, G.sender_payoff (outcome G s') ≤ M) :
    IsEquilibrium G s := by
  intro s'
  rw [hmax]
  exact hbound s'

/-- **Theorem 6.17 (Equilibrium Preserved Under Monotone Payoff Transform).**
    If f is a monotone transformation of payoffs and s is an equilibrium
    under the original payoff, then s is an equilibrium under f ∘ payoff.

    *Anthropological significance*: Cultural stability is robust under
    monotone "revaluation." If a society decides that all payoffs should
    be doubled (inflation), the same cultural forms remain stable. -/
theorem equilibrium_monotone_transform (G : InterpGame I) (s : I)
    (f : ℕ → ℕ) (hf : ∀ a b : ℕ, a ≤ b → f a ≤ f b)
    (heq : IsEquilibrium G s) :
    ∀ s' : I, f (G.sender_payoff (outcome G s')) ≤ f (G.sender_payoff (outcome G s)) := by
  intro s'
  exact hf _ _ (heq s')

/-- **Theorem 6.18 (Void Equilibrium in Zero-Payoff Games).**
    In a game where every signal yields zero payoff, void is trivially
    an equilibrium.

    *Anthropological significance*: In a society where communication
    carries no reward (radical anomie), silence is always optimal.
    This is the formal model of communicative breakdown. -/
theorem void_equilibrium_zero_game (rep : Repertoire I) :
    IsEquilibrium (⟨rep, fun _ => 0, fun _ => 0⟩ : InterpGame I) (IdeaticSpace.void : I) := by
  intro s'
  exact le_refl 0

end IDT.Signal.Ch6
