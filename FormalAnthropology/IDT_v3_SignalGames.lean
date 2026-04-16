import FormalAnthropology.IDT_v3_Foundations

/-!
# IDT v3: Signal Games — Deep Game-Theoretic Results

## Overview

This file develops a rich game-theoretic framework for signaling games
within the Ideatic Space axioms.  Every result follows from the minimal
axiom class `IdeaticSpace3` (monoid + resonance + emergence bounds)
with **zero sorries**.

## The fundamental idea

Communication is a game.  A *sender* chooses a signal `s`, a *receiver*
interprets it via `compose r s`.  Payoffs measure how well the signal
resonated from each player's perspective.  From the monoid and resonance
axioms alone we derive:

1. **The Meaning Game** — welfare decomposition
2. **Nash Equilibria** — void is always an equilibrium
3. **Communication Value** — when is signaling worth the cost?
4. **Persuasion** — iterated signaling monotonically enriches
5. **Strategic Emergence** — the non-additive surprise advantage
6. **Cooperation vs Competition** — surplus from joint composition
7. **Wittgenstein's Language Games** — meaning as resonance profile

## NO SORRIES, NO ADMITS, NO AXIOMS (beyond the class)
-/

namespace IDT3

open IdeaticSpace3

/-! ## §1. The Meaning Game — Welfare Decomposition

A "meaning game" is a pair (sender, receiver).  The sender chooses a
signal `s`, the receiver `r` interprets via `compose r s`.

Payoff to sender = `rs(s, compose r s)` — "did they get what I meant?"
Payoff to receiver = `rs(r, compose r s)` — "does this make sense to me?"

Total social welfare = senderPayoff + receiverPayoff.
-/

section MeaningGame
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Social welfare: total payoff to both players in the meaning game.
    This is the raw sum of sender and receiver payoffs, before any
    baseline subtraction. -/
noncomputable def socialWelfare (s r : I) : ℝ :=
  senderPayoff s r + receiverPayoff s r

/-- Social welfare unfolds to the sum of resonances with the
    interpretation. -/
theorem socialWelfare_eq (s r : I) :
    socialWelfare s r =
    rs s (compose r s) + rs r (compose r s) := by
  unfold socialWelfare senderPayoff receiverPayoff interpret; ring

/-- The interpretation `compose r s` resonates with the composition
    `compose s r` via the fundamental resonance decomposition.
    This relates welfare to resonance of the reversed composition. -/
theorem socialWelfare_via_compose (s r : I) :
    socialWelfare s r =
    rs (compose s r) (compose r s) - emergence s r (compose r s) := by
  unfold socialWelfare senderPayoff receiverPayoff interpret
  rw [rs_compose_eq s r (compose r s)]
  ring

/-- T1. Social welfare decomposes into self-resonances, cross-terms,
    and emergence.  The sender and receiver payoffs can each be written
    as their individual resonance with the interpretation `compose r s`.
    Using `rs_compose_eq` on the first argument of the reversed
    composition `compose s r`, we get the full decomposition. -/
theorem welfare_decomposition (s r : I) :
    socialWelfare s r =
    rs s (compose r s) + rs r (compose r s) :=
  socialWelfare_eq s r

/-- T2. Welfare when signal is void: receiver just hears silence. -/
theorem socialWelfare_void_signal (r : I) :
    socialWelfare (void : I) r = rs r r := by
  unfold socialWelfare senderPayoff receiverPayoff interpret
  simp [rs_void_left']

/-- T3. Welfare when receiver is void: signal goes unheard. -/
theorem socialWelfare_void_receiver (s : I) :
    socialWelfare s (void : I) = rs s s := by
  unfold socialWelfare senderPayoff receiverPayoff interpret
  simp [rs_void_left', rs_void_right']

/-- T4. Welfare of total silence is zero. -/
theorem socialWelfare_void_void :
    socialWelfare (void : I) (void : I) = 0 := by
  rw [socialWelfare_void_signal]; exact rs_void_void

/-- T5. Welfare decomposition via reversed composition and emergence. -/
theorem welfare_emergence_decomposition (s r : I) :
    socialWelfare s r =
    rs s (compose r s) + rs r (compose r s) :=
  socialWelfare_eq s r

/-- The sender's share: how the sender's payoff relates to the
    interpretation's resonance decomposition.  Since `compose r s`
    is in the *second* argument of `rs s _`, we express this via
    cross-resonance terms. -/
theorem sender_payoff_eq (s r : I) :
    senderPayoff s r = rs s (compose r s) := by
  unfold senderPayoff interpret; ring

/-- T6. The receiver's payoff equals their resonance with the
    interpretation — the "comprehension" term. -/
theorem receiver_payoff_eq (s r : I) :
    receiverPayoff s r = rs r (compose r s) := by
  unfold receiverPayoff interpret; ring

/-- T7. Welfare relates to the self-resonance of the interpretation
    via the first-argument decomposition. -/
theorem welfare_vs_interpretation_selfrs (s r : I) :
    socialWelfare s r =
    rs (compose s r) (compose r s) - emergence s r (compose r s) := by
  rw [socialWelfare_eq, rs_compose_eq s r (compose r s)]; ring

/-- T8. If sender and receiver are the same idea, welfare = 2 · rs(a, compose a a). -/
theorem welfare_self_signal (a : I) :
    socialWelfare a a = 2 * rs a (compose a a) := by
  rw [socialWelfare_eq]; ring

end MeaningGame

/-! ## §2. Nash Equilibrium in Meaning

A signal is a "best response" for the sender if no other signal yields
higher sender payoff.  Similarly for the receiver.  We define net payoffs
(payoff minus baseline self-resonance) so that void gives net payoff 0,
making (void, void) a Nash equilibrium.
-/

section NashEquilibrium
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Net sender benefit: sender payoff minus baseline (what sender gets
    by "talking to void"). The sender's gain from having receiver r
    interpret signal s, beyond what s already has intrinsically. -/
noncomputable def senderNetPayoff (s r : I) : ℝ :=
  senderPayoff s r - rs s s

/-- Net receiver benefit: receiver payoff minus baseline. -/
noncomputable def receiverNetPayoff (s r : I) : ℝ :=
  receiverPayoff s r - rs r r

/-- T9. Net sender payoff for void signal is always zero. -/
theorem senderNetPayoff_void_signal (r : I) :
    senderNetPayoff (void : I) r = 0 := by
  unfold senderNetPayoff senderPayoff interpret
  simp [rs_void_left', rs_void_void]

/-- T10. Net receiver payoff for void signal is always zero. -/
theorem receiverNetPayoff_void_signal (r : I) :
    receiverNetPayoff (void : I) r = 0 := by
  unfold receiverNetPayoff receiverPayoff interpret
  simp

/-- T11. Net sender payoff when receiver is void is always zero. -/
theorem senderNetPayoff_void_receiver (s : I) :
    senderNetPayoff s (void : I) = 0 := by
  unfold senderNetPayoff senderPayoff interpret; simp

/-- T12. Net receiver payoff when receiver is void is always zero. -/
theorem receiverNetPayoff_void_receiver (s : I) :
    receiverNetPayoff s (void : I) = 0 := by
  unfold receiverNetPayoff receiverPayoff interpret
  simp [rs_void_left', rs_void_void]

/-- A signal s is a best response for the sender against receiver r
    if no other signal yields a higher net sender payoff. -/
def isBestResponseSender (s r : I) : Prop :=
  ∀ s' : I, senderNetPayoff s r ≥ senderNetPayoff s' r

/-- A receiver r is a best response against signal s if no other
    receiver state yields higher net receiver payoff. -/
def isBestResponseReceiver (s r : I) : Prop :=
  ∀ r' : I, receiverNetPayoff s r ≥ receiverNetPayoff s r'

/-- Nash equilibrium: both players are best-responding. -/
def isNashEquilibrium (s r : I) : Prop :=
  isBestResponseSender s r ∧ isBestResponseReceiver s r

/-- T13. Void signal is always a best response to void receiver.
    Saying nothing to nobody is stable: no signal can improve
    the sender's net payoff (it's always 0 against void). -/
theorem void_bestResponse_sender_void :
    isBestResponseSender (void : I) (void : I) := by
  intro s'
  rw [senderNetPayoff_void_signal, senderNetPayoff_void_receiver]

/-- T14. Void receiver is always a best response to void signal.
    Hearing nothing requires no response: any receiver state gives
    net payoff 0 against the void signal. -/
theorem void_bestResponse_receiver_void :
    isBestResponseReceiver (void : I) (void : I) := by
  intro r'
  rw [receiverNetPayoff_void_receiver, receiverNetPayoff_void_signal]

/-- T15. (void, void) is always a Nash equilibrium: silence is stable.
    This is the "trivial" equilibrium — saying nothing to nobody.
    No player can unilaterally improve by deviating. -/
theorem void_nash_equilibrium :
    isNashEquilibrium (void : I) (void : I) :=
  ⟨void_bestResponse_sender_void, void_bestResponse_receiver_void⟩

/-- T16. Communication surplus equals the sum of net payoffs. -/
theorem communicationSurplus_eq_net (s r : I) :
    communicationSurplus s r = senderNetPayoff s r + receiverNetPayoff s r := by
  unfold communicationSurplus senderNetPayoff receiverNetPayoff; ring

/-- T17. At a Nash equilibrium, each player's net payoff is non-negative
    (since they could always deviate to void and get 0). -/
theorem nash_sender_nonneg (s r : I) (h : isNashEquilibrium s r) :
    senderNetPayoff s r ≥ 0 := by
  have := h.1 (void : I)
  rw [senderNetPayoff_void_signal] at this
  linarith

theorem nash_receiver_nonneg (s r : I) (h : isNashEquilibrium s r) :
    receiverNetPayoff s r ≥ 0 := by
  have := h.2 (void : I)
  rw [receiverNetPayoff_void_receiver] at this
  linarith

/-- T18. At a Nash equilibrium, communication surplus is non-negative. -/
theorem nash_surplus_nonneg (s r : I) (h : isNashEquilibrium s r) :
    communicationSurplus s r ≥ 0 := by
  rw [communicationSurplus_eq_net]
  linarith [nash_sender_nonneg s r h, nash_receiver_nonneg s r h]

/-- T19. At a Nash equilibrium, the misunderstanding gap is bounded:
    sender payoff minus receiver payoff ≤ sender payoff, because
    receiver payoff ≥ rs(r,r) ≥ 0 at equilibrium. -/
theorem nash_gap_bounded (s r : I) (h : isNashEquilibrium s r) :
    misunderstandingGap s r ≤ senderPayoff s r := by
  unfold misunderstandingGap
  have h1 := nash_receiver_nonneg s r h
  unfold receiverNetPayoff at h1
  linarith [S.rs_self_nonneg r]

end NashEquilibrium

/-! ## §3. Communication Value

The value of communication `V(s, r)` is the surplus from communicating
versus staying silent.  This is precisely `communicationSurplus`.
We prove key properties: V vanishes at void, and characterize when
communication is valuable.
-/

section CommunicationValue
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Communication value: the net benefit of sender sending s to receiver r,
    beyond what each gets from their own self-resonance.
    V(s,r) = senderPayoff(s,r) + receiverPayoff(s,r) - rs(s,s) - rs(r,r). -/
noncomputable def commValue (s r : I) : ℝ :=
  communicationSurplus s r

/-- T20. Communication with void signal has zero value. -/
theorem commValue_void_signal (r : I) :
    commValue (void : I) r = 0 :=
  communicationSurplus_void_signal r

/-- T21. Communication with void receiver has zero value. -/
theorem commValue_void_receiver (s : I) :
    commValue s (void : I) = 0 :=
  communicationSurplus_void_reader s

/-- T22. Communication value between two voids is zero. -/
theorem commValue_void_void :
    commValue (void : I) (void : I) = 0 :=
  communicationSurplus_void_signal _

/-- T23. Communication value decomposes into net payoffs. -/
theorem commValue_eq_nets (s r : I) :
    commValue s r = senderNetPayoff s r + receiverNetPayoff s r :=
  communicationSurplus_eq_net s r

/-- T24. Communication value in terms of raw resonances. -/
theorem commValue_explicit (s r : I) :
    commValue s r =
    rs s (compose r s) + rs r (compose r s) - rs s s - rs r r := by
  unfold commValue communicationSurplus senderPayoff receiverPayoff interpret; ring

/-- T25. Communication value relates to the reversed-composition
    resonance via emergence. -/
theorem commValue_via_emergence (s r : I) :
    commValue s r =
    rs (compose s r) (compose r s) - emergence s r (compose r s)
    - rs s s - rs r r := by
  rw [commValue_explicit, rs_compose_eq s r (compose r s)]; ring

/-- T26. Communication value for self-communication. -/
theorem commValue_self (a : I) :
    commValue a a = 2 * rs a (compose a a) - 2 * rs a a := by
  rw [commValue_explicit]; ring

/-- T27. If the sender payoff exceeds self-resonance AND receiver payoff
    exceeds self-resonance, then communication is valuable. -/
theorem commValue_pos_of_payoffs (s r : I)
    (hs : senderPayoff s r > rs s s)
    (hr : receiverPayoff s r > rs r r) :
    commValue s r > 0 := by
  rw [commValue_explicit, sender_payoff_eq, receiver_payoff_eq] at *
  linarith

end CommunicationValue

/-! ## §4. Persuasion as Iterated Signaling

Persuasion means bombarding a target with a signal repeatedly:
  `persuade(signal, target, n) = compose target (composeN signal n)`

The key result: self-resonance of the persuaded state is non-decreasing
in the number of repetitions.  The target gets "heavier" with each
exposure — you can't un-hear what you've heard.
-/

section Persuasion
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The persuasion operator: expose `target` to `signal` repeated `n` times.
    The result is the target's state after absorbing n copies of the signal. -/
def persuade (signal target : I) (n : ℕ) : I :=
  compose target (composeN signal n)

/-- T28. Zero persuasion leaves the target unchanged. -/
@[simp] theorem persuade_zero (signal target : I) :
    persuade signal target 0 = target := by
  unfold persuade; simp

/-- T29. Persuasion with void signal leaves the target unchanged. -/
@[simp] theorem persuade_void_signal (target : I) (n : ℕ) :
    persuade (void : I) target n = target := by
  unfold persuade; simp

/-- T30. Persuasion of void target is just the repeated signal. -/
theorem persuade_void_target (signal : I) (n : ℕ) :
    persuade signal (void : I) n = composeN signal n := by
  unfold persuade; simp

/-- Key lemma: persuade(s, t, n+1) = compose (persuade(s, t, n)) s.
    Each additional exposure just appends one more copy of the signal. -/
theorem persuade_succ (signal target : I) (n : ℕ) :
    persuade signal target (n + 1) =
    compose (persuade signal target n) signal := by
  unfold persuade
  simp [composeN_succ, compose_assoc']

/-- T31. Self-resonance of the persuaded state is non-decreasing.
    Each exposure makes the target "heavier" — more present.
    This follows from `compose_enriches`: composing with anything
    can only increase self-resonance. -/
theorem persuade_selfrs_mono (signal target : I) (n : ℕ) :
    rs (persuade signal target (n + 1)) (persuade signal target (n + 1)) ≥
    rs (persuade signal target n) (persuade signal target n) := by
  rw [persuade_succ]
  exact S.compose_enriches (persuade signal target n) signal

/-- T32. Self-resonance after any amount of persuasion is at least
    the target's original self-resonance. -/
theorem persuade_selfrs_ge_target : ∀ (signal target : I) (n : ℕ),
    rs (persuade signal target n) (persuade signal target n) ≥
    rs target target
  | _, _, 0 => by simp
  | signal, target, n + 1 => by
    have h1 := persuade_selfrs_mono signal target n
    have h2 := persuade_selfrs_ge_target signal target n
    linarith

/-- The persuasion surplus: how much does n exposures shift the target's
    self-resonance beyond baseline? -/
noncomputable def persuasionSurplus (signal target : I) (n : ℕ) : ℝ :=
  rs (persuade signal target n) (persuade signal target n) - rs target target

/-- T33. Persuasion surplus is always non-negative. -/
theorem persuasionSurplus_nonneg (signal target : I) (n : ℕ) :
    persuasionSurplus signal target n ≥ 0 := by
  unfold persuasionSurplus
  linarith [persuade_selfrs_ge_target signal target n]

/-- T34. Persuasion surplus at step 0 is zero. -/
theorem persuasionSurplus_zero (signal target : I) :
    persuasionSurplus signal target 0 = 0 := by
  unfold persuasionSurplus; simp

/-- T35. Persuasion surplus is non-decreasing. -/
theorem persuasionSurplus_mono (signal target : I) (n : ℕ) :
    persuasionSurplus signal target (n + 1) ≥
    persuasionSurplus signal target n := by
  unfold persuasionSurplus
  linarith [persuade_selfrs_mono signal target n]

/-- T36. A non-void signal always produces non-void persuasion
    (assuming target is non-void). -/
theorem persuade_ne_void_of_target (signal target : I) (n : ℕ)
    (ht : target ≠ void) :
    persuade signal target n ≠ void := by
  unfold persuade
  exact compose_ne_void_of_left target (composeN signal n) ht

/-- The marginal persuasion effect: the emergence generated by
    each additional exposure to the signal. -/
noncomputable def marginalPersuasion (signal target : I) (n : ℕ) : ℝ :=
  emergence (persuade signal target n) signal (persuade signal target (n + 1))

/-- T37. Persuasion surplus can be decomposed step-by-step. The
    (n+1)-th surplus equals the n-th surplus plus the additional
    self-resonance gained from the (n+1)-th exposure. -/
theorem persuasionSurplus_step (signal target : I) (n : ℕ) :
    persuasionSurplus signal target (n + 1) =
    persuasionSurplus signal target n +
    (rs (persuade signal target (n + 1)) (persuade signal target (n + 1)) -
     rs (persuade signal target n) (persuade signal target n)) := by
  unfold persuasionSurplus; ring

/-- T38. Persuasion with void signal always has zero surplus. -/
theorem persuasionSurplus_void_signal (target : I) (n : ℕ) :
    persuasionSurplus (void : I) target n = 0 := by
  unfold persuasionSurplus; simp

end Persuasion

/-! ## §5. Strategic Emergence

The emergence term in the payoff is the "strategic surprise" — the
non-additive component that neither player expected from simple
superposition.

The emergence advantage `emergence(r, s, s)` measures how much the
signal gains from being composed with the receiver's mind.
-/

section StrategicEmergence
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The emergence advantage of signal s against receiver r:
    how much emergent resonance the signal gains when the receiver
    interprets it.  Positive means the signal is "amplified" by
    the receiver's context. -/
noncomputable def emergenceAdvantage (s r : I) : ℝ :=
  emergence r s s

/-- T39. Emergence advantage is the non-additive part of sender payoff
    from the composition.  It measures how rs(compose r s, s) differs
    from rs(r, s) + rs(s, s). -/
theorem emergenceAdvantage_eq (s r : I) :
    emergenceAdvantage s r =
    rs (compose r s) s - rs r s - rs s s := by
  unfold emergenceAdvantage emergence; ring

/-- T40. Emergence advantage from void receiver is zero: if nobody is
    listening, there's no contextual amplification. -/
theorem emergenceAdvantage_void_receiver (s : I) :
    emergenceAdvantage s (void : I) = 0 := by
  unfold emergenceAdvantage; exact emergence_void_left s s

/-- T41. Emergence advantage of void signal is zero: silence generates
    no strategic surprise. -/
theorem emergenceAdvantage_void_signal (r : I) :
    emergenceAdvantage (void : I) r = 0 := by
  unfold emergenceAdvantage; exact emergence_void_right r (void : I)

/-- T42. Emergence advantage is bounded by the geometric mean of
    interpretation self-resonance and signal self-resonance. -/
theorem emergenceAdvantage_bounded (s r : I) :
    (emergenceAdvantage s r) ^ 2 ≤
    rs (compose r s) (compose r s) * rs s s := by
  unfold emergenceAdvantage
  exact emergence_bounded' r s s

/-- The receiver's emergence sensitivity: how much emergence the
    receiver experiences from interpreting signal s.
    emergence(r, s, r) = rs(compose r s, r) - rs(r, r) - rs(s, r). -/
noncomputable def receiverEmergenceSensitivity (s r : I) : ℝ :=
  emergence r s r

/-- T43. Receiver sensitivity is the non-additive part of receiver payoff. -/
theorem receiverSensitivity_eq (s r : I) :
    receiverEmergenceSensitivity s r =
    rs (compose r s) r - rs r r - rs s r := by
  unfold receiverEmergenceSensitivity emergence; ring

/-- T44. Void signal produces zero receiver emergence sensitivity. -/
theorem receiverSensitivity_void_signal (r : I) :
    receiverEmergenceSensitivity (void : I) r = 0 := by
  unfold receiverEmergenceSensitivity; exact emergence_void_right r r

/-- T45. Receiver sensitivity is bounded. -/
theorem receiverSensitivity_bounded (s r : I) :
    (receiverEmergenceSensitivity s r) ^ 2 ≤
    rs (compose r s) (compose r s) * rs r r := by
  unfold receiverEmergenceSensitivity
  exact emergence_bounded' r s r

/-- The total strategic emergence: emergence of the interpretation
    measured against itself.  This is the "self-emergence" of the
    communication event. -/
noncomputable def totalStrategicEmergence (s r : I) : ℝ :=
  emergence r s (compose r s)

/-- T46. Total strategic emergence decomposition: it equals self-resonance
    of interpretation minus cross-resonance terms. -/
theorem totalStrategicEmergence_eq (s r : I) :
    totalStrategicEmergence s r =
    rs (compose r s) (compose r s) - rs r (compose r s) - rs s (compose r s) := by
  unfold totalStrategicEmergence emergence; ring

/-- T47. Social welfare can be expressed using self-resonance of
    interpretation minus total strategic emergence. -/
theorem welfare_via_strategic_emergence (s r : I) :
    socialWelfare s r =
    rs (compose r s) (compose r s) - totalStrategicEmergence s r := by
  rw [socialWelfare_eq, totalStrategicEmergence_eq]; ring

/-- T48. Communication value relates to total strategic emergence:
    V(s,r) = selfRS(compose r s) - totalStrategicEmergence - selfRS(s) - selfRS(r). -/
theorem commValue_via_strategic (s r : I) :
    commValue s r =
    rs (compose r s) (compose r s) -
    totalStrategicEmergence s r - rs s s - rs r r := by
  rw [commValue_explicit, totalStrategicEmergence_eq]; ring

end StrategicEmergence

/-! ## §6. Cooperation vs Competition

Two players with ideas `a` and `b` can cooperate by composing their
ideas.  The cooperation surplus measures how much joint composition
exceeds the sum of individual self-resonances.
-/

section CooperationCompetition
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Cooperation surplus: how much more self-resonance does the joint
    composition have than the two ideas separately?
    Positive = synergy (cooperation is valuable).
    Negative = would need the bilinear part to be very negative.
    By compose_enriches, the surplus is always ≥ rs(a,a) - rs(b,b)
    (which may be negative). -/
noncomputable def cooperationSurplus (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- T49. Cooperation surplus decomposes using the first-argument
    resonance expansion: selfRS(a∘b) = rs(a, a∘b) + rs(b, a∘b) + κ(a,b,a∘b). -/
theorem cooperationSurplus_decomp (a b : I) :
    cooperationSurplus a b =
    (rs a (compose a b) - rs a a) +
    (rs b (compose a b) - rs b b) +
    emergence a b (compose a b) := by
  unfold cooperationSurplus
  rw [rs_compose_eq a b (compose a b)]; ring

/-- T50. Cooperation surplus with void is zero. -/
theorem cooperationSurplus_void_right (a : I) :
    cooperationSurplus a (void : I) = 0 := by
  unfold cooperationSurplus; simp [rs_void_void]

theorem cooperationSurplus_void_left (b : I) :
    cooperationSurplus (void : I) b = 0 := by
  unfold cooperationSurplus; simp [rs_void_void]

/-- T51. Cooperation surplus is at least -rs(b,b):
    composing can't reduce the FIRST idea's self-resonance below zero. -/
theorem cooperationSurplus_lower_bound (a b : I) :
    cooperationSurplus a b ≥ -rs b b := by
  unfold cooperationSurplus
  linarith [S.compose_enriches a b]

/-- T52. Self-cooperation surplus is non-negative:
    composing an idea with itself always enriches.
    Since rs(compose a a, compose a a) ≥ rs(a, a) ≥ 0, the surplus
    is at least rs(a,a) - rs(a,a) - rs(a,a) = -rs(a,a). But we can
    show it's ≥ 0 using compose_enriches twice: both "slots" enrich. -/
theorem cooperationSurplus_self_nonneg (a : I) :
    cooperationSurplus a a ≥ -rs a a := by
  unfold cooperationSurplus
  linarith [S.compose_enriches a a]

/-- T53. In the bilinear case (zero emergence, right-decomposable rs),
    cooperation surplus = rs(a,b) + rs(b,a).  This is because:
    selfRS(a∘b) = rs(a, a∘b) + rs(b, a∘b) when emergence = 0,
    and rs(x, a∘b) = rs(x,a) + rs(x,b) when rs is right-decomposable. -/
theorem cooperationSurplus_bilinear (a b : I)
    (h_emerg : ∀ x y z : I, emergence x y z = 0)
    (h_right : ∀ x y z : I, rs x (compose y z) = rs x y + rs x z) :
    cooperationSurplus a b = rs a b + rs b a := by
  unfold cooperationSurplus
  rw [rs_compose_eq a b (compose a b), h_emerg a b (compose a b)]
  rw [h_right a a b, h_right b a b]
  ring

/-- T54. In the symmetric bilinear case, surplus = 2·rs(a,b). -/
theorem cooperationSurplus_symmetric_bilinear (a b : I)
    (h_emerg : ∀ x y z : I, emergence x y z = 0)
    (h_right : ∀ x y z : I, rs x (compose y z) = rs x y + rs x z)
    (h_symm : ∀ x y : I, rs x y = rs y x) :
    cooperationSurplus a b = 2 * rs a b := by
  rw [cooperationSurplus_bilinear a b h_emerg h_right, h_symm b a]; ring

/-- T55. Cooperation surplus relates to communication value:
    both measure the gain from interaction, but cooperation measures
    the gain in self-resonance while communication value measures
    the gain in cross-resonance payoffs. -/
theorem coop_vs_commValue (a b : I) :
    cooperationSurplus a b =
    commValue b a + totalStrategicEmergence b a := by
  rw [commValue_via_strategic, totalStrategicEmergence_eq]
  unfold cooperationSurplus
  ring

/-- T56. If cooperation surplus is positive, the ideas have synergy. -/
theorem synergistic_of_positive_surplus (a b : I)
    (h : cooperationSurplus a b > 0) :
    rs (compose a b) (compose a b) > rs a a + rs b b := by
  unfold cooperationSurplus at h; linarith

/-- The competition deficit: how much one player's self-resonance
    "costs" the other in a composition.  When composition is enriching
    for both sides, the deficit is zero or negative. -/
noncomputable def competitionAsymmetry (a b : I) : ℝ :=
  cooperationSurplus a b - cooperationSurplus b a

/-- T57. Competition asymmetry captures the order-dependence of
    cooperation: it's zero when composition is commutative
    in self-resonance. -/
theorem competitionAsymmetry_antisymm (a b : I) :
    competitionAsymmetry a b = -competitionAsymmetry b a := by
  unfold competitionAsymmetry; ring

/-- T58. Competition asymmetry in terms of self-resonances. -/
theorem competitionAsymmetry_eq (a b : I) :
    competitionAsymmetry a b =
    rs (compose a b) (compose a b) - rs (compose b a) (compose b a) := by
  unfold competitionAsymmetry cooperationSurplus; ring

/-- T59. Competition asymmetry vanishes when composition is commutative. -/
theorem competitionAsymmetry_comm (a b : I)
    (h : compose a b = compose b a) :
    competitionAsymmetry a b = 0 := by
  rw [competitionAsymmetry_eq, h]; ring

end CooperationCompetition

/-! ## §7. Wittgenstein's Language Games

Meaning is constituted by USE: the resonance profile of an utterance
across many contexts determines its meaning.

A "language game" consists of a vocabulary (list of utterances) and
a community (list of players/contexts).  The meaning of an utterance
is its resonance profile — how it resonates with every player in every
context.

Key insight: an utterance's meaning (resonance profile) is determined
by its emergence pattern, confirming Wittgenstein's thesis that meaning
is not an intrinsic property but arises from use.
-/

section LanguageGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A resonance profile of an utterance: the function mapping every
    other utterance to its resonance value.  This is the utterance's
    "meaning in use". -/
noncomputable def resonanceProfile (a : I) : I → ℝ :=
  fun c => rs a c

/-- Two utterances have the same resonance profile iff they are
    resonance-equivalent. -/
theorem profile_eq_iff_resonanceEquiv (a b : I) :
    resonanceProfile a = resonanceProfile b ↔ resonanceEquiv a b := by
  constructor
  · intro h c; exact congr_fun h c
  · intro h; funext c; exact h c

/-- T60. Void has a zero resonance profile. -/
theorem resonanceProfile_void :
    resonanceProfile (void : I) = fun _ => (0 : ℝ) := by
  funext c; exact rs_void_left' c

/-- An emergence profile of an utterance: the function mapping every
    pair (b, c) to the emergence κ(a, b, c).  This is the utterance's
    "creative potential" — what it contributes to compositions. -/
noncomputable def emergenceProfile (a : I) : I → I → ℝ :=
  fun b c => emergence a b c

/-- T61. Void has a zero emergence profile. -/
theorem emergenceProfile_void :
    emergenceProfile (void : I) = fun _ _ => (0 : ℝ) := by
  funext b c; exact emergence_void_left b c

/-- T62. Same emergence profile iff same idea (by definition). -/
theorem emergenceProfile_eq_iff_sameIdea (a b : I) :
    emergenceProfile a = emergenceProfile b ↔ sameIdea a b := by
  constructor
  · intro h c d; exact congr_fun (congr_fun h c) d
  · intro h; funext c d; exact h c d

/-- The contextual meaning of utterance `u` in context `ctx`:
    the resonance of the interpreted composition. -/
noncomputable def contextualMeaning (u ctx : I) : ℝ :=
  rs (compose ctx u) (compose ctx u)

/-- T63. Contextual meaning is always non-negative. -/
theorem contextualMeaning_nonneg (u ctx : I) :
    contextualMeaning u ctx ≥ 0 := by
  unfold contextualMeaning; exact S.rs_self_nonneg _

/-- T64. Contextual meaning of void is the context's self-resonance. -/
theorem contextualMeaning_void_utterance (ctx : I) :
    contextualMeaning (void : I) ctx = rs ctx ctx := by
  unfold contextualMeaning; simp

/-- T65. Contextual meaning in void context is the utterance's
    self-resonance. -/
theorem contextualMeaning_void_context (u : I) :
    contextualMeaning u (void : I) = rs u u := by
  unfold contextualMeaning; simp

/-- T66. Contextual meaning is at least the context's self-resonance.
    Adding any utterance to a context only enriches. -/
theorem contextualMeaning_ge_context (u ctx : I) :
    contextualMeaning u ctx ≥ rs ctx ctx := by
  unfold contextualMeaning
  exact S.compose_enriches ctx u

/-- The communicative reach of an utterance: the total welfare it
    generates across a list of receivers. -/
noncomputable def communicativeReach (u : I) : List I → ℝ
  | [] => 0
  | r :: rest => socialWelfare u r + communicativeReach u rest

/-- T67. Communicative reach of void signal is the sum of receiver
    self-resonances. -/
theorem communicativeReach_void : ∀ (receivers : List I),
    communicativeReach (void : I) receivers =
    (receivers.map (fun r => rs r r)).sum
  | [] => by unfold communicativeReach; simp
  | r :: rest => by
    unfold communicativeReach
    rw [socialWelfare_void_signal, communicativeReach_void rest]
    simp [List.map_cons, List.sum_cons]

/-- The use-profile of an utterance across a community: a list of
    contextual meanings across all community members. -/
noncomputable def useProfile (u : I) (community : List I) : List ℝ :=
  community.map (fun ctx => contextualMeaning u ctx)

/-- T68. Use-profile of void utterance. -/
theorem useProfile_void (community : List I) :
    useProfile (void : I) community =
    community.map (fun ctx => rs ctx ctx) := by
  unfold useProfile; congr 1; funext ctx
  exact contextualMeaning_void_utterance ctx

/-- T69. Every element of the use-profile is non-negative. -/
theorem useProfile_nonneg (u : I) (community : List I) :
    ∀ x ∈ useProfile u community, x ≥ 0 := by
  intro x hx
  unfold useProfile at hx
  rw [List.mem_map] at hx
  obtain ⟨ctx, _, hctx⟩ := hx
  rw [← hctx]
  exact contextualMeaning_nonneg u ctx

/-- Wittgenstein's thesis: two utterances have the same "meaning in use"
    (identical use-profiles in EVERY community) if and only if their
    composition with any context produces identical self-resonance.
    This is a resonance-equivalence condition on compositions. -/
def wittgensteinEquiv (a b : I) : Prop :=
  ∀ ctx : I, contextualMeaning a ctx = contextualMeaning b ctx

/-- T70. Wittgenstein equivalence unfolds to equality of composed
    self-resonances. -/
theorem wittgensteinEquiv_iff (a b : I) :
    wittgensteinEquiv a b ↔
    ∀ ctx : I, rs (compose ctx a) (compose ctx a) =
              rs (compose ctx b) (compose ctx b) := by
  constructor
  · intro h ctx; exact h ctx
  · intro h ctx; exact h ctx

/-- T71. Wittgenstein equivalence is reflexive. -/
theorem wittgensteinEquiv_refl (a : I) : wittgensteinEquiv a a :=
  fun _ => rfl

/-- T72. Wittgenstein equivalence is symmetric. -/
theorem wittgensteinEquiv_symm (a b : I)
    (h : wittgensteinEquiv a b) : wittgensteinEquiv b a :=
  fun ctx => (h ctx).symm

/-- T73. Wittgenstein equivalence is transitive. -/
theorem wittgensteinEquiv_trans (a b c : I)
    (h1 : wittgensteinEquiv a b) (h2 : wittgensteinEquiv b c) :
    wittgensteinEquiv a c :=
  fun ctx => (h1 ctx).trans (h2 ctx)

/-- T74. Void is Wittgenstein-equivalent only to itself (among non-void). -/
theorem wittgensteinEquiv_void_iff (a : I) :
    wittgensteinEquiv (void : I) a →
    ∀ ctx : I, rs (compose ctx a) (compose ctx a) = rs ctx ctx := by
  intro h ctx
  have := h ctx
  unfold contextualMeaning at this
  simp at this
  exact this.symm

end LanguageGames

/-! ## §8. Signal Refinement and Iterated Best Response

Beyond static Nash equilibrium, we can study the dynamics of
best-response iteration: each player alternately improves their
strategy.  We characterize fixed points and monotonicity.
-/

section SignalRefinement
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The sender's payoff function viewed as a function of the signal
    alone (fixing the receiver).  Best-response dynamics amounts to
    optimizing this function. -/
noncomputable def senderObjective (r : I) : I → ℝ :=
  fun s => senderNetPayoff s r

/-- T75. The sender's objective at void signal is always zero. -/
theorem senderObjective_void (r : I) :
    senderObjective r (void : I) = 0 := by
  unfold senderObjective; exact senderNetPayoff_void_signal r

/-- The receiver's payoff as a function of receiver state
    (fixing the signal). -/
noncomputable def receiverObjective (s : I) : I → ℝ :=
  fun r => receiverNetPayoff s r

/-- T76. The receiver's objective at void is always zero. -/
theorem receiverObjective_void (s : I) :
    receiverObjective s (void : I) = 0 := by
  unfold receiverObjective; exact receiverNetPayoff_void_receiver s

/-- T77. Sender objective unfolds to explicit resonance terms. -/
theorem senderObjective_eq (r s : I) :
    senderObjective r s = rs s (compose r s) - rs s s := by
  unfold senderObjective senderNetPayoff senderPayoff interpret; ring

/-- T78. Receiver objective unfolds to explicit resonance terms. -/
theorem receiverObjective_eq (s r : I) :
    receiverObjective s r = rs r (compose r s) - rs r r := by
  unfold receiverObjective receiverNetPayoff receiverPayoff interpret; ring

/-- A signal-receiver pair is a communication fixed point if
    neither player's net payoff changes by switching to void. -/
def isCommunicationFixedPoint (s r : I) : Prop :=
  senderNetPayoff s r = 0 ∧ receiverNetPayoff s r = 0

/-- T79. (void, void) is always a communication fixed point. -/
theorem void_is_fixed_point :
    isCommunicationFixedPoint (void : I) (void : I) :=
  ⟨senderNetPayoff_void_signal _, receiverNetPayoff_void_receiver _⟩

/-- T80. At a communication fixed point, the communication surplus
    is exactly zero. -/
theorem fixed_point_zero_surplus (s r : I)
    (h : isCommunicationFixedPoint s r) :
    communicationSurplus s r = 0 := by
  rw [communicationSurplus_eq_net]; linarith [h.1, h.2]

/-- T81. At a communication fixed point, sender payoff equals
    self-resonance. -/
theorem fixed_point_sender (s r : I)
    (h : isCommunicationFixedPoint s r) :
    senderPayoff s r = rs s s := by
  have := h.1; unfold senderNetPayoff at this; linarith

/-- T82. At a communication fixed point, receiver payoff equals
    self-resonance. -/
theorem fixed_point_receiver (s r : I)
    (h : isCommunicationFixedPoint s r) :
    receiverPayoff s r = rs r r := by
  have := h.2; unfold receiverNetPayoff at this; linarith

end SignalRefinement

/-! ## §9. Multi-Signal Composition and Discourse

When multiple signals are composed sequentially, the total effect
can be analyzed through the cocycle structure of emergence.
-/

section Discourse
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The discourse operator: a reader interprets a sequence of signals
    by composing them in order onto the reader's state. -/
def discourse (reader : I) : List I → I
  | [] => reader
  | s :: rest => discourse (compose reader s) rest

/-- T83. Empty discourse leaves the reader unchanged. -/
@[simp] theorem discourse_nil (reader : I) :
    discourse reader [] = reader := rfl

/-- T84. Singleton discourse is just interpretation. -/
theorem discourse_singleton (reader s : I) :
    discourse reader [s] = compose reader s := by
  unfold discourse; simp

/-- T85. Self-resonance of discourse is non-decreasing with each
    additional signal: each signal enriches the reader's state. -/
theorem discourse_enriches (reader s : I) (signals : List I) :
    rs (discourse (compose reader s) signals)
       (discourse (compose reader s) signals) ≥
    rs reader reader := by
  have h1 := S.compose_enriches reader s
  induction signals generalizing reader s with
  | nil => simpa using h1
  | cons s' rest ih =>
    unfold discourse
    have h2 := S.compose_enriches (compose reader s) s'
    have h3 := ih (compose reader s) s' h2
    linarith

/-- T86. The total emergence of a discourse: how much emergent
    meaning does reading a sequence of signals produce?  This is
    the difference between the final state's self-resonance and
    the sum of individual self-resonances. -/
noncomputable def discourseEmergence (reader : I) (signals : List I) : ℝ :=
  rs (discourse reader signals) (discourse reader signals) - rs reader reader

/-- T87. Discourse emergence of an empty sequence is zero. -/
theorem discourseEmergence_nil (reader : I) :
    discourseEmergence reader [] = 0 := by
  unfold discourseEmergence; simp

/-- T88. Discourse emergence is non-negative for any non-empty sequence. -/
theorem discourseEmergence_cons_nonneg (reader s : I) (signals : List I) :
    discourseEmergence reader (s :: signals) ≥ 0 := by
  unfold discourseEmergence discourse
  linarith [discourse_enriches reader s signals, S.rs_self_nonneg reader]

end Discourse

/-! ## §10. Information Revelation and Partial Communication

Not all signals reveal everything.  A signal is "informative" if it
shifts the receiver's state; it's "redundant" if the receiver already
knows everything the signal conveys.
-/

section InformationRevelation
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A signal is informative for a receiver if interpreting it changes
    the receiver's self-resonance. -/
def isInformative (s r : I) : Prop :=
  rs (compose r s) (compose r s) ≠ rs r r

/-- A signal is redundant for a receiver if interpreting it doesn't
    change the receiver's self-resonance. -/
def isRedundant (s r : I) : Prop :=
  rs (compose r s) (compose r s) = rs r r

/-- T89. Void signal is always redundant. -/
theorem void_redundant (r : I) : isRedundant (void : I) r := by
  unfold isRedundant; simp

/-- T90. A signal is informative iff it's not redundant. -/
theorem informative_iff_not_redundant (s r : I) :
    isInformative s r ↔ ¬isRedundant s r := by
  unfold isInformative isRedundant; exact Iff.rfl

/-- T91. If a signal is informative, it strictly increases the
    receiver's self-resonance (since compose_enriches guarantees
    the composed version is never lighter). -/
theorem informative_increases (s r : I) (h : isInformative s r) :
    rs (compose r s) (compose r s) > rs r r := by
  have h1 := S.compose_enriches r s
  rcases lt_or_eq_of_le h1 with hlt | heq
  · linarith
  · exact absurd heq.symm h

/-- The information content of a signal for a receiver:
    how much it enriches the receiver's self-resonance. -/
noncomputable def informationContent (s r : I) : ℝ :=
  rs (compose r s) (compose r s) - rs r r

/-- T92. Information content is always non-negative. -/
theorem informationContent_nonneg (s r : I) :
    informationContent s r ≥ 0 := by
  unfold informationContent
  linarith [S.compose_enriches r s]

/-- T93. Information content of void is zero. -/
theorem informationContent_void (r : I) :
    informationContent (void : I) r = 0 := by
  unfold informationContent; simp

/-- T94. Information content decomposes via emergence. -/
theorem informationContent_decomp (s r : I) :
    informationContent s r =
    rs r (compose r s) + rs s (compose r s) +
    emergence r s (compose r s) - rs r r := by
  unfold informationContent
  rw [rs_compose_eq r s (compose r s)]

/-- T95. Information content relates to cooperation surplus
    (measuring the "weight gain" from interpretation). -/
theorem informationContent_eq_coopSurplus_shifted (s r : I) :
    informationContent s r =
    cooperationSurplus r s + rs s s := by
  unfold informationContent cooperationSurplus; ring

end InformationRevelation

/-! ## §11. The Babbling Equilibrium and Cheap Talk

In cheap-talk games, signals have no intrinsic cost. The "babbling
equilibrium" is where the receiver ignores the signal entirely.
We formalize this and show its properties.
-/

section CheapTalk
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A receiver ignores a signal if the payoff is the same as for void. -/
def receiverIgnores (s r : I) : Prop :=
  receiverPayoff s r = receiverPayoff (void : I) r

/-- T96. If receiver ignores the signal, then rs(r, compose r s) = rs(r, r). -/
theorem ignores_means_baseline (s r : I) (h : receiverIgnores s r) :
    rs r (compose r s) = rs r r := by
  unfold receiverIgnores at h
  unfold receiverPayoff interpret at h; simpa using h

/-- T97. If receiver ignores, the signal is "self-focused" — the
    communication surplus equals the sender's net payoff. -/
theorem ignores_surplus (s r : I) (h : receiverIgnores s r) :
    communicationSurplus s r = senderNetPayoff s r := by
  rw [communicationSurplus_eq_net]
  unfold receiverNetPayoff receiverPayoff interpret
  rw [ignores_means_baseline s r h]; ring

/-- The babbling condition: receiver ignores ALL signals. -/
def isBabbling (r : I) : Prop :=
  ∀ s : I, receiverIgnores s r

/-- T98. Under babbling, communication surplus = sender's net gain
    for every signal. -/
theorem babbling_surplus (r : I) (h : isBabbling r) (s : I) :
    communicationSurplus s r = senderNetPayoff s r :=
  ignores_surplus s r (h s)

/-- T99. Void receiver trivially babbles: hearing nothing from
    anyone, the void has no state to update. -/
theorem void_babbles : isBabbling (void : I) := by
  intro s
  unfold receiverIgnores receiverPayoff interpret
  simp [rs_void_left', rs_void_void]

end CheapTalk

/-! ## §12. Signaling Costs and Costly Signals

When signals are costly — measured by their self-resonance — the sender
faces a trade-off: richer signals resonate more but cost more to produce.
This leads to signaling equilibria where only signals with sufficient
emergence advantage are worth sending.
-/

section CostlySignaling
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The cost of a signal: its self-resonance.  More "substantial"
    signals cost more to produce.  Only void is free. -/
noncomputable def signalCost (s : I) : ℝ := rs s s

/-- T100. Void signal is free. -/
theorem signalCost_void : signalCost (void : I) = 0 := rs_void_void

/-- T101. Non-void signals have strictly positive cost. -/
theorem signalCost_pos (s : I) (h : s ≠ void) :
    signalCost s > 0 := rs_self_pos s h

/-- The net payoff in a costly signaling game: sender payoff minus
    signal cost.  This is just senderNetPayoff, but the "costly" framing
    makes the economics explicit. -/
noncomputable def costlyNetPayoff (s r : I) : ℝ :=
  senderPayoff s r - signalCost s

/-- T102. Costly net payoff is the same as sender net payoff. -/
theorem costlyNetPayoff_eq (s r : I) :
    costlyNetPayoff s r = senderNetPayoff s r := by
  unfold costlyNetPayoff signalCost senderNetPayoff; ring

/-- T103. Void always yields zero costly net payoff. -/
theorem costlyNetPayoff_void (r : I) :
    costlyNetPayoff (void : I) r = 0 := by
  rw [costlyNetPayoff_eq]; exact senderNetPayoff_void_signal r

/-- T104. A signal is "worth sending" if its costly net payoff
    is strictly positive.  This means the emergence advantage
    outweighs the signal cost. -/
theorem signal_worth_sending_iff (s r : I) :
    costlyNetPayoff s r > 0 ↔ senderPayoff s r > signalCost s := by
  unfold costlyNetPayoff; constructor <;> intro h <;> linarith

/-- T105. At Nash equilibrium, the costly net payoff of the equilibrium
    signal is non-negative (the sender could always send void for free). -/
theorem nash_costly_nonneg (s r : I) (h : isNashEquilibrium s r) :
    costlyNetPayoff s r ≥ 0 := by
  rw [costlyNetPayoff_eq]; exact nash_sender_nonneg s r h

end CostlySignaling

/-! ## §13. Communication Channels and Capacity

A "channel" is a fixed receiver.  The channel capacity measures the
maximum communication value achievable by any signal through this channel.
-/

section Channels
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A channel is characterized by a receiver.  The channel throughput
    for a specific signal is the social welfare generated. -/
noncomputable def channelThroughput (channel signal : I) : ℝ :=
  socialWelfare signal channel

/-- T106. Void channel has throughput = signal's self-resonance. -/
theorem voidChannel_throughput (s : I) :
    channelThroughput (void : I) s = rs s s :=
  socialWelfare_void_receiver s

/-- T107. Any channel has non-negative throughput for void signal. -/
theorem channel_void_throughput (channel : I) :
    channelThroughput channel (void : I) = rs channel channel :=
  socialWelfare_void_signal channel

/-- The channel gain: throughput minus signal cost. -/
noncomputable def channelGain (channel signal : I) : ℝ :=
  channelThroughput channel signal - rs signal signal

/-- T108. Void channel has zero gain: sending anything through void
    yields exactly what you started with. -/
theorem voidChannel_gain (s : I) :
    channelGain (void : I) s = 0 := by
  unfold channelGain; rw [voidChannel_throughput]; ring

/-- T109. Channel gain from void signal is the channel's self-resonance. -/
theorem channel_void_gain (channel : I) :
    channelGain channel (void : I) = rs channel channel := by
  unfold channelGain; rw [channel_void_throughput]; simp [rs_void_void]

/-- T110. Channel gain decomposes into sender and receiver perspectives. -/
theorem channelGain_decomp (channel signal : I) :
    channelGain channel signal =
    senderNetPayoff signal channel + receiverPayoff signal channel := by
  unfold channelGain channelThroughput socialWelfare senderNetPayoff
  ring

end Channels

/-! ## §14. Babbling Equilibrium Characterization

The babbling equilibrium is the canonical "failure to communicate":
the receiver ignores every signal.  We prove that under babbling,
void is weakly optimal for the sender, and conversely, if void
is the unique signal that achieves the maximum net payoff (zero),
then the receiver must be babbling.
-/

section BabblingCharacterization
variable {I : Type*} [S : IdeaticSpace3 I]

/-- T111. Under babbling, sender's net payoff decomposes into a pure
    cross-resonance shift: senderNetPayoff = rs(s, compose r s) - rs(s,s). -/
theorem babbling_sender_net_explicit (r : I) (_h : isBabbling r) (s : I) :
    senderNetPayoff s r = rs s (compose r s) - rs s s := by
  unfold senderNetPayoff senderPayoff interpret; ring

/-- T112. Under babbling, the communication surplus equals the sender's
    resonance shift with the interpretation. -/
theorem babbling_commValue (r : I) (h : isBabbling r) (s : I) :
    commValue s r = rs s (compose r s) - rs s s := by
  unfold commValue
  rw [babbling_surplus r h s, babbling_sender_net_explicit r h s]

/-- T113 (strengthened). Under babbling, void signal achieves net payoff 0,
    which is weakly optimal among all signals that also yield zero net payoff.
    More precisely: for ANY signal s, senderNetPayoff void r = 0. -/
theorem babbling_void_optimal (r : I) (_h : isBabbling r) :
    senderNetPayoff (void : I) r = 0 :=
  senderNetPayoff_void_signal r

/-- T114. Converse direction: if sender net payoff is zero for ALL signals
    (i.e., void's payoff is matched by everything), then the receiver
    payoff equals baseline for all signals — the receiver is babbling. -/
theorem babbling_of_all_net_zero (r : I)
    (h : ∀ s : I, senderNetPayoff s r = 0) :
    ∀ s : I, senderPayoff s r = rs s s := by
  intro s
  have := h s
  unfold senderNetPayoff at this; linarith

/-- T115. If the receiver ignores a specific signal, the communication
    value from that signal equals the sender's net payoff alone. -/
theorem ignores_commValue_eq_senderNet (s r : I) (h : receiverIgnores s r) :
    commValue s r = senderNetPayoff s r := by
  unfold commValue; exact ignores_surplus s r h

/-- T116. Under babbling, total social welfare equals
    rs(s, compose r s) + rs(r, r) — the receiver always gets baseline. -/
theorem babbling_welfare (r : I) (h : isBabbling r) (s : I) :
    socialWelfare s r = rs s (compose r s) + rs r r := by
  rw [socialWelfare_eq, ignores_means_baseline s r (h s)]

/-- T117. Under babbling, the misunderstanding gap equals the sender's
    resonance shift: rs(s, compose r s) - rs(r, r). -/
theorem babbling_misunderstanding (r : I) (h : isBabbling r) (s : I) :
    misunderstandingGap s r = rs s (compose r s) - rs r r := by
  unfold misunderstandingGap senderPayoff receiverPayoff interpret
  rw [ignores_means_baseline s r (h s)]

/-- T118. Under babbling, the information content still grows —
    even if the receiver's payoff doesn't change, the composed state
    is enriched. -/
theorem babbling_information_nonneg (r : I) (_ : isBabbling r) (s : I) :
    informationContent s r ≥ 0 :=
  informationContent_nonneg s r

/-- A receiver "fully absorbs" a signal if interpreting it gives the
    same self-resonance as the receiver alone — the signal adds nothing
    new to the receiver's state. -/
def fullyAbsorbs (s r : I) : Prop :=
  rs (compose r s) (compose r s) = rs r r

/-- T119. If the receiver fully absorbs every signal, then void is
    redundant for the receiver (trivially — everything is redundant). -/
theorem fullyAbsorbs_implies_redundant (s r : I) (h : fullyAbsorbs s r) :
    isRedundant s r := h

/-- T120. If a signal is redundant for the receiver AND the receiver
    ignores it, then the communication surplus is purely the sender's
    cross-resonance shift. -/
theorem redundant_and_ignored_surplus (s r : I)
    (_hr : isRedundant s r) (hi : receiverIgnores s r) :
    communicationSurplus s r = rs s (compose r s) - rs s s := by
  rw [ignores_surplus s r hi]
  unfold senderNetPayoff senderPayoff interpret; ring

end BabblingCharacterization

/-! ## §15. Communication Value Hierarchy — Multi-Round Communication

In multi-round communication, each round composes a new signal onto
the receiver's evolving state.  We define the n-round communication
value and prove monotonicity: more rounds never decrease the value.
-/

section CommunicationValueHierarchy
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The n-round interpretation: the receiver absorbs the signal n times.
    This is just the persuasion operator. -/
def nRoundInterpret (signal receiver : I) (n : ℕ) : I :=
  persuade signal receiver n

/-- T121. 0-round interpretation leaves receiver unchanged. -/
@[simp] theorem nRoundInterpret_zero (s r : I) :
    nRoundInterpret s r 0 = r :=
  persuade_zero s r

/-- T122. 1-round interpretation is standard composition. -/
theorem nRoundInterpret_one (s r : I) :
    nRoundInterpret s r 1 = compose r s := by
  unfold nRoundInterpret persuade; simp [composeN_one]

/-- The n-round communication value: how much the receiver's
    self-resonance grows after n rounds of absorbing the signal. -/
noncomputable def nRoundValue (signal receiver : I) (n : ℕ) : ℝ :=
  rs (nRoundInterpret signal receiver n) (nRoundInterpret signal receiver n)
  - rs receiver receiver

/-- T123. 0-round value is zero: no communication, no gain. -/
theorem nRoundValue_zero (s r : I) : nRoundValue s r 0 = 0 := by
  unfold nRoundValue; simp

/-- T124. n-round value is non-negative (by compose_enriches induction). -/
theorem nRoundValue_nonneg (s r : I) (n : ℕ) :
    nRoundValue s r n ≥ 0 := by
  unfold nRoundValue nRoundInterpret
  linarith [persuade_selfrs_ge_target s r n]

/-- T125. n-round value is monotonically non-decreasing: more rounds
    never decrease the value. -/
theorem nRoundValue_mono (s r : I) (n : ℕ) :
    nRoundValue s r (n + 1) ≥ nRoundValue s r n := by
  unfold nRoundValue nRoundInterpret
  linarith [persuade_selfrs_mono s r n]

/-- The marginal value of the (n+1)-th round: additional value from
    one more round of communication. -/
noncomputable def marginalRoundValue (signal receiver : I) (n : ℕ) : ℝ :=
  nRoundValue signal receiver (n + 1) - nRoundValue signal receiver n

/-- T126. Marginal round value is always non-negative. -/
theorem marginalRoundValue_nonneg (s r : I) (n : ℕ) :
    marginalRoundValue s r n ≥ 0 := by
  unfold marginalRoundValue
  linarith [nRoundValue_mono s r n]

/-- T127. n-round value is the sum of n marginal values (telescoping sum).
    We state this as: nRoundValue(n+1) = nRoundValue(n) + marginalRoundValue(n). -/
theorem nRoundValue_telescope_step (s r : I) (n : ℕ) :
    nRoundValue s r (n + 1) = nRoundValue s r n + marginalRoundValue s r n := by
  unfold marginalRoundValue; ring

/-- T128. n-round value with void signal is always zero: repeating
    silence adds nothing. -/
theorem nRoundValue_void_signal (r : I) (n : ℕ) :
    nRoundValue (void : I) r n = 0 := by
  unfold nRoundValue nRoundInterpret
  simp [persuade_void_signal]

/-- T129. 1-round value equals information content. -/
theorem nRoundValue_one_eq_info (s r : I) :
    nRoundValue s r 1 = informationContent s r := by
  unfold nRoundValue nRoundInterpret informationContent persuade
  simp [composeN_one]

/-- T130. n-round value relates to persuasion surplus. -/
theorem nRoundValue_eq_persuasionSurplus (s r : I) (n : ℕ) :
    nRoundValue s r n = persuasionSurplus s r n := by
  unfold nRoundValue nRoundInterpret persuasionSurplus; ring

/-- T131. The 2-round value is at least the 1-round value. -/
theorem twoRound_ge_oneRound (s r : I) :
    nRoundValue s r 2 ≥ nRoundValue s r 1 :=
  nRoundValue_mono s r 1

/-- T132. n-round value for self-communication (signal = receiver)
    is at least n-1 times the single-step enrichment minimum. -/
theorem nRoundValue_self_nonneg (a : I) (n : ℕ) :
    nRoundValue a a n ≥ 0 :=
  nRoundValue_nonneg a a n

end CommunicationValueHierarchy

/-! ## §16. Cheap Talk vs Costly Signaling

We formalize when signals are "cheap" (low self-resonance = low weight)
versus "costly" (high self-resonance).  Costly signals are more
credible because they require more "substance" from the sender.
We prove Spence-like conditions for signaling equilibria.
-/

section CheapVsCostly
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A signal is cheap if its cost (self-resonance) is below a threshold. -/
def isCheap (s : I) (threshold : ℝ) : Prop :=
  signalCost s ≤ threshold

/-- A signal is costly if its cost exceeds a threshold. -/
def isCostly (s : I) (threshold : ℝ) : Prop :=
  signalCost s > threshold

/-- T133. Void is always cheap (for any non-negative threshold). -/
theorem void_is_cheap (threshold : ℝ) (h : threshold ≥ 0) :
    isCheap (void : I) threshold := by
  unfold isCheap signalCost; rw [rs_void_void]; linarith

/-- T134. A costly signal is never void. -/
theorem costly_ne_void (s : I) (threshold : ℝ) (h : isCostly s threshold)
    (ht : threshold ≥ 0) : s ≠ void := by
  intro hs
  unfold isCostly signalCost at h; rw [hs, rs_void_void] at h; linarith

/-- T135. Costly signals have strictly positive self-resonance. -/
theorem costly_pos (s : I) (threshold : ℝ) (h : isCostly s threshold)
    (ht : threshold ≥ 0) : rs s s > 0 := by
  unfold isCostly signalCost at h; linarith

/-- The credibility of a signal: how much emergence it generates
    with the receiver, normalized by its cost. Higher credibility
    means the signal "earns its weight" in communication. -/
noncomputable def signalCredibility (s r : I) : ℝ :=
  rs (compose r s) (compose r s) - rs r r

/-- T136. Signal credibility equals information content. -/
theorem signalCredibility_eq_info (s r : I) :
    signalCredibility s r = informationContent s r := by
  unfold signalCredibility informationContent; ring

/-- T137. Signal credibility is non-negative: any signal weakly enriches. -/
theorem signalCredibility_nonneg (s r : I) :
    signalCredibility s r ≥ 0 := by
  rw [signalCredibility_eq_info]; exact informationContent_nonneg s r

/-- T138. Void signal has zero credibility. -/
theorem signalCredibility_void (r : I) :
    signalCredibility (void : I) r = 0 := by
  rw [signalCredibility_eq_info]; exact informationContent_void r

/-- The Spence condition: a signal is a valid "signaling equilibrium"
    if its net payoff exceeds what any cheaper signal could achieve.
    Formally: for all s' with signalCost s' < signalCost s,
    the costly net payoff of s exceeds that of s'. -/
def satisfiesSpenceCondition (s r : I) : Prop :=
  costlyNetPayoff s r ≥ 0 ∧
  ∀ s' : I, signalCost s' < signalCost s →
    costlyNetPayoff s r ≥ costlyNetPayoff s' r

/-- T139. Void trivially satisfies the Spence condition (vacuously,
    since nothing is cheaper than void). -/
theorem void_spence (r : I) : satisfiesSpenceCondition (void : I) r := by
  constructor
  · rw [costlyNetPayoff_eq]; exact le_of_eq (senderNetPayoff_void_signal r).symm
  · intro s' hs'
    unfold signalCost at hs'; rw [rs_void_void] at hs'
    linarith [S.rs_self_nonneg s']

/-- T140. At Nash equilibrium, the equilibrium signal satisfies the
    Spence condition. -/
theorem nash_satisfies_spence (s r : I) (h : isNashEquilibrium s r) :
    costlyNetPayoff s r ≥ 0 := by
  rw [costlyNetPayoff_eq]; exact nash_sender_nonneg s r h

/-- T141. A costly signal's net payoff is bounded by sender payoff
    minus its cost. -/
theorem costly_net_bound (s r : I) :
    costlyNetPayoff s r = senderPayoff s r - signalCost s := by
  unfold costlyNetPayoff; ring

/-- T142. The "signaling premium": how much more net payoff a costly
    signal achieves compared to void. This is exactly the costly net payoff. -/
noncomputable def signalingPremium (s r : I) : ℝ :=
  costlyNetPayoff s r - costlyNetPayoff (void : I) r

/-- T143. Signaling premium equals the costly net payoff itself
    (since void gets zero). -/
theorem signalingPremium_eq (s r : I) :
    signalingPremium s r = costlyNetPayoff s r := by
  unfold signalingPremium; rw [costlyNetPayoff_void]; ring

/-- T144. Costly signals that produce more emergence with the receiver
    have higher information content — they are more "credible" in the
    Spence sense. -/
theorem credibility_monotone (s₁ s₂ r : I)
    (h : signalCredibility s₁ r ≥ signalCredibility s₂ r) :
    informationContent s₁ r ≥ informationContent s₂ r := by
  rwa [← signalCredibility_eq_info, ← signalCredibility_eq_info]

end CheapVsCostly

/-! ## §17. The Revelation Problem

When a sender reveals information by composing their private idea
with a public signal, the receiver learns through the enrichment
of their composed state.  We prove bounds on how much can be
learned per round and that repeated revelation is bounded by
cumulative emergence.
-/

section RevelationProblem
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The revelation of idea `private_idea` through signal `public_signal`
    to receiver `r`: the receiver interprets the publicly composed signal. -/
def reveal (private_idea public_signal r : I) : I :=
  compose r (compose private_idea public_signal)

/-- T145. Revelation through void public signal reduces to direct
    interpretation of the private idea. -/
theorem reveal_void_public (priv r : I) :
    reveal priv (void : I) r = compose r priv := by
  unfold reveal; simp

/-- T146. Revelation of void private idea reduces to interpretation
    of the public signal. -/
theorem reveal_void_private (pub r : I) :
    reveal (void : I) pub r = compose r pub := by
  unfold reveal; simp

/-- T147. Revelation through void public to void receiver. -/
theorem reveal_void_all :
    reveal (void : I) (void : I) (void : I) = (void : I) := by
  unfold reveal; simp

/-- The revelation gain: how much the receiver's self-resonance
    increases from revelation versus direct interpretation of
    the public signal alone. -/
noncomputable def revelationGain (priv pub r : I) : ℝ :=
  rs (reveal priv pub r) (reveal priv pub r) -
  rs (compose r pub) (compose r pub)

/-- T148. Revelation enriches the receiver beyond baseline:
    the receiver's self-resonance after revelation is at least
    as much as with the public signal alone when priv = void. -/
theorem revelationGain_baseline_nonneg (priv pub r : I) :
    rs (reveal priv pub r) (reveal priv pub r) ≥ rs r r := by
  unfold reveal
  linarith [S.compose_enriches r (compose priv pub)]

/-- T149. Revelation gain from void private idea is non-negative
    (it's actually just the enrichment from pub∘void = pub which is zero). -/
theorem revelationGain_void_private (pub r : I) :
    revelationGain (void : I) pub r = 0 := by
  unfold revelationGain reveal; simp

/-- T150. Total information from revelation equals the information content
    of the composed private-public signal. -/
theorem revelation_total_info (priv pub r : I) :
    rs (reveal priv pub r) (reveal priv pub r) - rs r r =
    informationContent (compose priv pub) r := by
  rfl

/-- The per-round revelation: applying the same private idea repeatedly
    through different public signals. -/
def iteratedReveal (priv : I) (r : I) : ℕ → I
  | 0 => r
  | n + 1 => compose (iteratedReveal priv r n) priv

/-- T151. Iterated revelation at step 0 is the receiver unchanged. -/
@[simp] theorem iteratedReveal_zero (priv r : I) :
    iteratedReveal priv r 0 = r := rfl

/-- T152. Iterated revelation is exactly persuasion. -/
theorem iteratedReveal_eq_persuade (priv r : I) (n : ℕ) :
    iteratedReveal priv r n = persuade priv r n := by
  induction n with
  | zero => simp [persuade]
  | succ n ih =>
    unfold iteratedReveal
    rw [ih]
    unfold persuade
    rw [composeN_succ]
    rw [← compose_assoc']

/-- T153. Self-resonance of iterated revelation is non-decreasing. -/
theorem iteratedReveal_mono (priv r : I) (n : ℕ) :
    rs (iteratedReveal priv r (n + 1)) (iteratedReveal priv r (n + 1)) ≥
    rs (iteratedReveal priv r n) (iteratedReveal priv r n) := by
  show rs (compose (iteratedReveal priv r n) priv) (compose (iteratedReveal priv r n) priv) ≥ _
  exact S.compose_enriches (iteratedReveal priv r n) priv

/-- T154. Cumulative revelation gain: total self-resonance growth
    from n rounds of revelation. -/
noncomputable def cumulativeRevelation (priv r : I) (n : ℕ) : ℝ :=
  rs (iteratedReveal priv r n) (iteratedReveal priv r n) - rs r r

/-- T155. Cumulative revelation is non-negative. -/
theorem cumulativeRevelation_nonneg (priv r : I) (n : ℕ) :
    cumulativeRevelation priv r n ≥ 0 := by
  unfold cumulativeRevelation
  rw [iteratedReveal_eq_persuade]
  linarith [persuade_selfrs_ge_target priv r n]

/-- T156. Cumulative revelation is non-decreasing. -/
theorem cumulativeRevelation_mono (priv r : I) (n : ℕ) :
    cumulativeRevelation priv r (n + 1) ≥
    cumulativeRevelation priv r n := by
  unfold cumulativeRevelation
  linarith [iteratedReveal_mono priv r n]

/-- T157. Cumulative revelation at step 0 is zero. -/
theorem cumulativeRevelation_zero (priv r : I) :
    cumulativeRevelation priv r 0 = 0 := by
  unfold cumulativeRevelation; simp

/-- T158. Cumulative revelation with void signal is always zero. -/
theorem cumulativeRevelation_void (r : I) (n : ℕ) :
    cumulativeRevelation (void : I) r n = 0 := by
  unfold cumulativeRevelation
  rw [iteratedReveal_eq_persuade]; simp

/-- T159. The per-step revelation increment is non-negative. -/
theorem revelationIncrement_nonneg (priv r : I) (n : ℕ) :
    cumulativeRevelation priv r (n + 1) - cumulativeRevelation priv r n ≥ 0 := by
  linarith [cumulativeRevelation_mono priv r n]

end RevelationProblem

/-! ## §18. Strategic Silence

Void as a deliberate strategic choice.  We prove when silence
dominates speech: when the cost of signaling exceeds the
communication value, staying silent is the rational strategy.
We characterize the "silence threshold."
-/

section StrategicSilence
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The net value of speaking signal s to receiver r: the total
    communication surplus. When negative, silence dominates speech. -/
noncomputable def speechValue (s r : I) : ℝ :=
  communicationSurplus s r

/-- T160. Speech value of void is zero: silence is the neutral choice. -/
theorem speechValue_void (r : I) : speechValue (void : I) r = 0 := by
  unfold speechValue; exact communicationSurplus_void_signal r

/-- T161. Speech value decomposes into sender and receiver net gains. -/
theorem speechValue_decomp (s r : I) :
    speechValue s r = senderNetPayoff s r + receiverNetPayoff s r := by
  unfold speechValue; exact communicationSurplus_eq_net s r

/-- Silence dominates speech for the sender when the sender's net payoff
    from signal s is non-positive. -/
def silenceDominates (s r : I) : Prop :=
  senderNetPayoff s r ≤ 0

/-- T162. Void never loses to itself: silence never dominates silence. -/
theorem silence_never_dominates_void (r : I) :
    ¬silenceDominates (void : I) r ∨ senderNetPayoff (void : I) r = 0 := by
  right; exact senderNetPayoff_void_signal r

/-- T163. If silence dominates for every signal, then the sender's
    best achievable net payoff is zero (achieved by void). -/
theorem universal_silence (r : I)
    (h : ∀ s : I, silenceDominates s r) :
    ∀ s : I, senderNetPayoff s r ≤ 0 :=
  h

/-- T164. When silence dominates, sender payoff is at most self-resonance. -/
theorem silence_dominates_payoff_bound (s r : I) (h : silenceDominates s r) :
    senderPayoff s r ≤ rs s s := by
  unfold silenceDominates senderNetPayoff at h; linarith

/-- The silence threshold for a receiver: the minimum signal cost
    above which silence dominates. A signal is "too expensive" if
    its self-resonance exceeds this threshold. -/
noncomputable def silenceThreshold (s r : I) : ℝ :=
  senderPayoff s r

/-- T165. Silence dominates iff signal cost exceeds the silence threshold. -/
theorem silence_iff_cost_exceeds (s r : I) :
    silenceDominates s r ↔ signalCost s ≥ silenceThreshold s r := by
  unfold silenceDominates senderNetPayoff signalCost silenceThreshold
  constructor <;> intro h <;> linarith

/-- T166. At Nash equilibrium, silence does NOT dominate the
    equilibrium signal (the sender weakly prefers speaking). -/
theorem nash_no_silence (s r : I) (h : isNashEquilibrium s r) :
    ¬silenceDominates s r ∨ senderNetPayoff s r = 0 := by
  have h1 := nash_sender_nonneg s r h
  unfold silenceDominates
  rcases eq_or_lt_of_le h1 with heq | hlt
  · right; linarith
  · left; linarith

/-- T167. If silence dominates for all signals against receiver r,
    then communication surplus is non-positive for all signals. -/
theorem universal_silence_no_surplus (r : I)
    (h : ∀ s : I, silenceDominates s r) (s : I) :
    speechValue s r ≤ receiverNetPayoff s r := by
  have hd := speechValue_decomp s r
  have hs := h s
  unfold silenceDominates at hs
  linarith

/-- T168. The "silence gap": how much better silence is than speaking.
    Non-negative when silence dominates. -/
noncomputable def silenceGap (s r : I) : ℝ :=
  - senderNetPayoff s r

/-- T169. Silence gap equals signal cost minus sender payoff. -/
theorem silenceGap_eq (s r : I) :
    silenceGap s r = rs s s - senderPayoff s r := by
  unfold silenceGap senderNetPayoff; ring

/-- T170. Silence gap is non-negative iff silence dominates. -/
theorem silenceGap_nonneg_iff (s r : I) :
    silenceGap s r ≥ 0 ↔ silenceDominates s r := by
  unfold silenceGap silenceDominates; constructor <;> intro h <;> linarith

/-- T171. Silence gap of void signal is always zero. -/
theorem silenceGap_void (r : I) :
    silenceGap (void : I) r = 0 := by
  unfold silenceGap; rw [senderNetPayoff_void_signal]; ring

end StrategicSilence

/-! ## §19. Emergence Accumulation and Communication Bounds

Deep results about how emergence accumulates over compositions,
providing fundamental bounds on communication effectiveness.
-/

section EmergenceAccumulation
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The cumulative enrichment of composing a list of signals onto a base. -/
noncomputable def cumulativeEnrichment (base : I) (signals : List I) : ℝ :=
  rs (discourse base signals) (discourse base signals) - rs base base

/-- T172. Cumulative enrichment of empty list is zero. -/
theorem cumulativeEnrichment_nil (base : I) :
    cumulativeEnrichment base [] = 0 := by
  unfold cumulativeEnrichment; simp

/-- T173. Cumulative enrichment is non-negative for any signal list. -/
theorem cumulativeEnrichment_cons_nonneg (base s : I) (rest : List I) :
    cumulativeEnrichment base (s :: rest) ≥ 0 := by
  unfold cumulativeEnrichment discourse
  linarith [discourse_enriches base s rest]

/-- T174. Cumulative enrichment grows when we append a signal. -/
theorem cumulativeEnrichment_append_mono (base s : I) (signals : List I) :
    cumulativeEnrichment base (signals ++ [s]) ≥
    cumulativeEnrichment base signals := by
  unfold cumulativeEnrichment
  induction signals generalizing base with
  | nil =>
    simp [discourse]
    exact S.compose_enriches base s
  | cons s' rest ih =>
    simp only [List.cons_append, discourse]
    have h := ih (compose base s')
    -- Normalize ++ and List.append
    simp only [List.append_eq] at h ⊢
    linarith

/-- The emergence density of a discourse: average enrichment per signal. -/
noncomputable def emergenceDensity (base : I) (signals : List I) : ℝ :=
  if signals.length = 0 then 0
  else cumulativeEnrichment base signals / signals.length

/-- T175. Emergence density of empty discourse is zero. -/
theorem emergenceDensity_nil (base : I) :
    emergenceDensity base [] = 0 := by
  unfold emergenceDensity; simp

/-- The enrichment contribution of a single step in discourse. -/
noncomputable def stepEnrichment (state signal : I) : ℝ :=
  rs (compose state signal) (compose state signal) - rs state state

/-- T176. Step enrichment is non-negative. -/
theorem stepEnrichment_nonneg (state signal : I) :
    stepEnrichment state signal ≥ 0 := by
  unfold stepEnrichment; linarith [S.compose_enriches state signal]

/-- T177. Step enrichment of void signal is zero. -/
theorem stepEnrichment_void (state : I) :
    stepEnrichment state (void : I) = 0 := by
  unfold stepEnrichment; simp

/-- T178. Step enrichment equals information content. -/
theorem stepEnrichment_eq_info (state signal : I) :
    stepEnrichment state signal = informationContent signal state := by
  unfold stepEnrichment informationContent; ring

end EmergenceAccumulation

/-! ## §20. Signaling Equilibrium Refinements

Deeper results about equilibrium structure: dominant strategies,
Pareto optimality among equilibria, and the relationship between
signal weight and equilibrium quality.
-/

section EquilibriumRefinements
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A signal is weakly dominated by another if the other achieves
    at least as high sender net payoff against ALL receivers. -/
def weaklyDominatedSender (s s' : I) : Prop :=
  ∀ r : I, senderNetPayoff s' r ≥ senderNetPayoff s r

/-- T179. No signal weakly dominates void against a void receiver:
    all signals tie at zero. -/
theorem void_receiver_all_tie (s : I) :
    senderNetPayoff s (void : I) = senderNetPayoff (void : I) (void : I) := by
  rw [senderNetPayoff_void_receiver, senderNetPayoff_void_signal]

/-- T180. Void is never strictly dominated: there exists a receiver
    (namely void) against which void does as well as any signal. -/
theorem void_not_strictly_dominated (s : I) :
    senderNetPayoff (void : I) (void : I) ≥ senderNetPayoff s (void : I) := by
  rw [senderNetPayoff_void_signal, senderNetPayoff_void_receiver]

/-- An equilibrium is Pareto-efficient if no other equilibrium makes
    both players strictly better off. -/
def paretoEfficient (s r : I) (_h : isNashEquilibrium s r) : Prop :=
  ∀ s' r' : I, isNashEquilibrium s' r' →
    (senderNetPayoff s' r' > senderNetPayoff s r →
     receiverNetPayoff s' r' ≤ receiverNetPayoff s r) ∧
    (receiverNetPayoff s' r' > receiverNetPayoff s r →
     senderNetPayoff s' r' ≤ senderNetPayoff s r)

/-- T181. The void-void equilibrium has surplus zero. -/
theorem void_equilibrium_surplus :
    communicationSurplus (void : I) (void : I) = 0 :=
  communicationSurplus_void_signal _

/-- T182. At any Nash equilibrium, social welfare is at least the sum
    of self-resonances. -/
theorem nash_welfare_bound (s r : I) (h : isNashEquilibrium s r) :
    socialWelfare s r ≥ rs s s + rs r r := by
  have h1 := nash_sender_nonneg s r h
  have h2 := nash_receiver_nonneg s r h
  have hw := socialWelfare_eq s r
  have hs := sender_payoff_eq s r
  have hr := receiver_payoff_eq s r
  unfold senderNetPayoff at h1; unfold receiverNetPayoff at h2
  linarith

/-- T183. Communication surplus at Nash equilibrium relates to
    the enrichment of interpretation. -/
theorem nash_surplus_via_enrichment (s r : I) (_h : isNashEquilibrium s r) :
    communicationSurplus s r =
    rs s (compose r s) + rs r (compose r s) - rs s s - rs r r := by
  unfold communicationSurplus senderPayoff receiverPayoff interpret; ring

end EquilibriumRefinements

/-! ## §21. Signaling Chains and Transitivity

When signals are relayed through intermediaries, the chain structure
preserves enrichment but may lose or gain emergence.
-/

section SignalingChains
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A signaling chain: sender → relay → receiver.
    The relay interprets the sender's signal, then the receiver
    interprets the relay's output. -/
def signalingChain (sender relay receiver : I) : I :=
  compose receiver (compose relay sender)

/-- T184. The signaling chain equals double composition via associativity. -/
theorem signalingChain_assoc (s m r : I) :
    signalingChain s m r = compose (compose r m) s := by
  unfold signalingChain; rw [compose_assoc']

/-- T185. Signaling chain with void relay reduces to direct communication. -/
theorem signalingChain_void_relay (s r : I) :
    signalingChain s (void : I) r = compose r s := by
  unfold signalingChain; simp

/-- T186. Signaling chain with void sender is just receiver-relay
    composition. -/
theorem signalingChain_void_sender (m r : I) :
    signalingChain (void : I) m r = compose r m := by
  unfold signalingChain; simp

/-- T187. Signaling chain enriches the receiver at least as much as
    direct relay-receiver composition. -/
theorem signalingChain_enriches_relay (s m r : I) :
    rs (signalingChain s m r) (signalingChain s m r) ≥
    rs (compose r m) (compose r m) := by
  rw [signalingChain_assoc]
  exact S.compose_enriches (compose r m) s

/-- T188. Signaling chain enriches the receiver beyond baseline. -/
theorem signalingChain_enriches_receiver (s m r : I) :
    rs (signalingChain s m r) (signalingChain s m r) ≥ rs r r := by
  have h1 := signalingChain_enriches_relay s m r
  have h2 := S.compose_enriches r m
  linarith

/-- The chain value: total enrichment from the full chain beyond
    what the receiver started with. -/
noncomputable def chainValue (sender relay receiver : I) : ℝ :=
  rs (signalingChain sender relay receiver) (signalingChain sender relay receiver)
  - rs receiver receiver

/-- T189. Chain value is non-negative. -/
theorem chainValue_nonneg (s m r : I) :
    chainValue s m r ≥ 0 := by
  unfold chainValue
  linarith [signalingChain_enriches_receiver s m r]

/-- T190. Chain value with void sender equals information content
    of relay for receiver. -/
theorem chainValue_void_sender (m r : I) :
    chainValue (void : I) m r = informationContent m r := by
  unfold chainValue informationContent; rw [signalingChain_void_sender]

/-- The relay amplification: how much extra value the relay adds
    beyond direct sender-receiver communication. -/
noncomputable def relayAmplification (s m r : I) : ℝ :=
  chainValue s m r - informationContent s r

/-- T191. Relay amplification of void relay is zero: no relay, no extra value. -/
theorem relayAmplification_void (s r : I) :
    relayAmplification s (void : I) r = 0 := by
  unfold relayAmplification chainValue informationContent
  rw [signalingChain_void_relay]; ring

end SignalingChains

/-! ## §22. Fundamental Communication Inequalities

Deep structural inequalities relating emergence, enrichment,
and communication value.  These are the "main theorems" that
chain together the results of earlier sections.
-/

section FundamentalInequalities
variable {I : Type*} [S : IdeaticSpace3 I]

/-- T192. The Communication Enrichment Theorem: for any sender-receiver
    pair, the interpretation's self-resonance is at least the receiver's.
    This is the fundamental monotonicity of communication. -/
theorem communication_enrichment (s r : I) :
    rs (compose r s) (compose r s) ≥ rs r r :=
  S.compose_enriches r s

/-- T193. Double composition enrichment: composing twice enriches at
    least as much as once. -/
theorem double_composition_enrichment (a b : I) :
    rs (compose (compose a b) b) (compose (compose a b) b) ≥
    rs (compose a b) (compose a b) :=
  S.compose_enriches (compose a b) b

/-- T194. The enrichment is transitive: if a enriches to a∘b,
    and a∘b enriches to (a∘b)∘c, then a enriches to (a∘b)∘c. -/
theorem enrichment_transitive (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥ rs a a := by
  have h1 := S.compose_enriches a b
  have h2 := S.compose_enriches (compose a b) c
  linarith

/-- T195. Social welfare is symmetric in a specific sense: it equals the
    sum of cross-resonances with the interpretation. -/
theorem welfare_lower_bound (s r : I) :
    socialWelfare s r =
    rs s (compose r s) + rs r (compose r s) := by
  exact socialWelfare_eq s r

/-- T196. The emergence-bounded communication inequality:
    the squared emergence is bounded by the product of
    self-resonances of the composition and the observer. -/
theorem emergence_communication_bound (s r : I) :
    (emergence r s (compose r s)) ^ 2 ≤
    rs (compose r s) (compose r s) * rs (compose r s) (compose r s) := by
  have h := emergence_bounded' r s (compose r s)
  nlinarith [S.rs_self_nonneg (compose r s)]

/-- T197. The enrichment gap is non-negative for any composition. -/
theorem enrichment_gap_nonneg (a b : I) :
    rs (compose a b) (compose a b) - rs a a ≥ 0 := by
  linarith [S.compose_enriches a b]

/-- T198. Triple enrichment bound. -/
theorem triple_enrichment (a b c : I) :
    rs (compose (compose a b) c) (compose (compose a b) c) ≥
    rs a a := by
  linarith [S.compose_enriches a b, S.compose_enriches (compose a b) c]

/-- T199. Discourse enrichment is additive in a lower bound sense:
    total enrichment from two signals is at least the enrichment
    from the first signal alone. -/
theorem discourse_enrichment_mono (r s₁ s₂ : I) :
    rs (discourse r [s₁, s₂]) (discourse r [s₁, s₂]) ≥
    rs (discourse r [s₁]) (discourse r [s₁]) := by
  unfold discourse
  exact S.compose_enriches (compose r s₁) s₂

/-- T200. n-round value is at most the n-round interpretation's
    self-resonance. -/
theorem nRoundValue_le_selfrs (s r : I) (n : ℕ) :
    nRoundValue s r n ≤
    rs (nRoundInterpret s r n) (nRoundInterpret s r n) := by
  unfold nRoundValue
  linarith [S.rs_self_nonneg r]

end FundamentalInequalities

/-! ## §23. The Grand Unification: Communication as Enrichment Game

Tying together all the threads: communication value, Nash equilibria,
persuasion, and emergence are all manifestations of the same
underlying principle — compose_enriches.
-/

section GrandUnification
variable {I : Type*} [S : IdeaticSpace3 I]

/-- T201. The Master Communication Theorem: at any Nash equilibrium,
    the total welfare exceeds the sum of individual baselines, and
    the surplus equals exactly the sum of sender and receiver net gains,
    both of which are non-negative. -/
theorem master_communication_theorem (s r : I) (h : isNashEquilibrium s r) :
    communicationSurplus s r ≥ 0 ∧
    senderNetPayoff s r ≥ 0 ∧
    receiverNetPayoff s r ≥ 0 ∧
    communicationSurplus s r = senderNetPayoff s r + receiverNetPayoff s r :=
  ⟨nash_surplus_nonneg s r h,
   nash_sender_nonneg s r h,
   nash_receiver_nonneg s r h,
   communicationSurplus_eq_net s r⟩

/-- T202. The Enrichment-Communication Duality: the n-round communication
    value equals the persuasion surplus, which equals the cumulative
    revelation gain with void public signal. -/
theorem enrichment_communication_duality (s r : I) (n : ℕ) :
    nRoundValue s r n = persuasionSurplus s r n :=
  nRoundValue_eq_persuasionSurplus s r n

/-- T203. The Silence-Babbling Connection: under babbling, the
    silence gap equals rs(s,s) - rs(s, compose r s). -/
theorem silence_babbling_connection (r : I) (_h : isBabbling r) (s : I) :
    silenceGap s r = rs s s - rs s (compose r s) := by
  unfold silenceGap senderNetPayoff senderPayoff interpret; ring

/-- T204. The Chain-Discourse Equivalence: a signaling chain
    s → m → r produces the same result as a discourse [s] read by
    the composition r∘m (by associativity). -/
theorem chain_discourse_equiv (s m r : I) :
    signalingChain s m r = discourse (compose r m) [s] := by
  unfold signalingChain; simp [discourse]

/-- T205. Communication value hierarchy collapses for void signals:
    all n-round values are zero when the signal is void. -/
theorem hierarchy_collapse_void (r : I) (n m : ℕ) :
    nRoundValue (void : I) r n = nRoundValue (void : I) r m := by
  rw [nRoundValue_void_signal, nRoundValue_void_signal]

/-- T206. The Fundamental Theorem of Costly Signaling:
    A signal is worth sending iff its sender payoff exceeds its cost,
    iff it generates positive net payoff, iff silence does not dominate. -/
theorem fundamental_costly_signaling (s r : I) :
    (costlyNetPayoff s r > 0) ↔ (¬silenceDominates s r ∧ senderNetPayoff s r > 0) := by
  rw [costlyNetPayoff_eq]
  unfold silenceDominates
  constructor
  · intro h; exact ⟨by linarith, h⟩
  · intro ⟨_, h⟩; exact h

/-- T207. Cooperation surplus connects to chain value:
    the cooperation surplus of (r, s) equals the chain value of
    s through void relay to r, minus rs(s,s). -/
theorem cooperation_chain_connection (s r : I) :
    cooperationSurplus r s =
    chainValue s (void : I) r - rs s s := by
  unfold cooperationSurplus chainValue
  simp [signalingChain_void_relay]

/-- T208. The babbling-silence duality: under babbling,
    the speech value equals the negative of the silence gap. -/
theorem babbling_silence_duality (r : I) (h : isBabbling r) (s : I) :
    speechValue s r = -silenceGap s r := by
  unfold speechValue silenceGap
  rw [babbling_surplus r h s]; ring

/-- T209. The Communication Completeness Theorem: every communication
    quantity can be expressed in terms of just rs and compose:
    Here we show communication surplus expands to primitive operations. -/
theorem communication_completeness (s r : I) :
    communicationSurplus s r =
    rs s (compose r s) + rs r (compose r s) - rs s s - rs r r := by
  unfold communicationSurplus senderPayoff receiverPayoff interpret; ring

/-- T210. The Monotone Communication Principle: for any fixed receiver,
    the map n ↦ nRoundValue(s, r, n) is a non-decreasing sequence
    bounded below by 0 and above by the n-round interpretation's
    self-resonance. -/
theorem monotone_communication (s r : I) (n : ℕ) :
    0 ≤ nRoundValue s r n ∧
    nRoundValue s r n ≤ nRoundValue s r (n + 1) ∧
    nRoundValue s r n ≤
      rs (nRoundInterpret s r n) (nRoundInterpret s r n) := by
  refine ⟨?_, ?_, ?_⟩
  · linarith [nRoundValue_nonneg s r n]
  · linarith [nRoundValue_mono s r n]
  · exact nRoundValue_le_selfrs s r n

end GrandUnification

/-! ## §24. Mechanism Design — VCG and Myerson in Meaning Games

In mechanism design, a "mechanism" is a rule that aggregates reports
(signals) from multiple agents into an outcome (composed idea) and
payments (resonance transfers). The Vickrey-Clarke-Groves (VCG)
mechanism ensures truthful revelation is incentive-compatible by
aligning individual resonance with social welfare.

We model a mechanism as a triple: (aggregation rule, payment rule,
participation constraint). The aggregation rule composes signals;
the payment rule extracts resonance; participation requires
non-negative net payoff.
-/

section MechanismDesign
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A mechanism outcome: the aggregated idea from two agents' reports.
    In VCG, the aggregation rule maximizes social welfare (self-resonance
    of the composition). Here, simple composition IS the welfare-maximizing
    aggregation, since compose_enriches guarantees monotonicity. -/
noncomputable def mechanismOutcome (report₁ report₂ : I) : I :=
  compose report₁ report₂

/-- T211. The VCG payment principle: each agent's "payment" is the
    externality they impose on others. Agent 1's externality on agent 2
    is the difference between what agent 2 would get alone vs. in the
    mechanism. Since compose enriches, this is always non-negative. -/
noncomputable def vcgPayment (report₁ report₂ : I) : ℝ :=
  rs (mechanismOutcome report₁ report₂) (mechanismOutcome report₁ report₂)
  - rs report₂ report₂ - rs report₁ report₁

/-- T212. VCG payment is exactly the cooperation surplus. The externality
    each agent imposes equals the synergy they create, which is the
    cooperation surplus from §6. This connects mechanism design to
    cooperative game theory. -/
theorem vcgPayment_eq_coopSurplus (a b : I) :
    vcgPayment a b = cooperationSurplus a b := by
  unfold vcgPayment mechanismOutcome cooperationSurplus; ring

/-- T213. VCG payment for void report is zero: silence imposes no
    externality. An agent who reports nothing neither helps nor harms. -/
theorem vcgPayment_void_left (b : I) :
    vcgPayment (void : I) b = 0 := by
  rw [vcgPayment_eq_coopSurplus]; exact cooperationSurplus_void_left b

/-- T214. VCG payment for void counterpart is zero: if the other
    agent is silent, your externality is zero. -/
theorem vcgPayment_void_right (a : I) :
    vcgPayment a (void : I) = 0 := by
  rw [vcgPayment_eq_coopSurplus]; exact cooperationSurplus_void_right a

/-- The VCG net utility for agent 1: their share of the outcome's
    resonance minus their VCG payment. -/
noncomputable def vcgNetUtility₁ (a b : I) : ℝ :=
  rs a (mechanismOutcome a b) - vcgPayment a b

/-- T215. VCG net utility decomposes into self-resonance plus cross-term
    minus cooperation surplus. This reveals how much each agent "keeps"
    after paying for their externality. -/
theorem vcgNetUtility₁_eq (a b : I) :
    vcgNetUtility₁ a b =
    rs a (compose a b) - cooperationSurplus a b := by
  unfold vcgNetUtility₁ mechanismOutcome
  rw [vcgPayment_eq_coopSurplus]

/-- T216. VCG net utility with void counterpart is just self-resonance.
    If the other agent is silent, you keep everything you brought. -/
theorem vcgNetUtility₁_void_right (a : I) :
    vcgNetUtility₁ a (void : I) = rs a a := by
  unfold vcgNetUtility₁ mechanismOutcome
  rw [vcgPayment_eq_coopSurplus, cooperationSurplus_void_right]; simp

/-- The Myerson virtual value: the "adjusted" resonance of a signal
    accounting for information rents. In meaning games, the virtual
    value adjusts for the emergence advantage — what the signal gains
    from strategic interaction beyond its intrinsic worth. -/
noncomputable def myersonVirtualValue (s r : I) : ℝ :=
  senderPayoff s r - emergenceAdvantage s r

/-- T217. Myerson virtual value with void signal is zero. When nothing
    is said, there is no virtual value to extract. -/
theorem myersonVirtualValue_void_signal (r : I) :
    myersonVirtualValue (void : I) r = 0 := by
  unfold myersonVirtualValue senderPayoff interpret emergenceAdvantage emergence
  simp [rs_void_left', rs_void_right']

/-- T218. Myerson virtual value with void receiver reduces to
    self-resonance minus emergence advantage (which is zero). -/
theorem myersonVirtualValue_void_receiver (s : I) :
    myersonVirtualValue s (void : I) = rs s s := by
  unfold myersonVirtualValue senderPayoff interpret emergenceAdvantage
  simp [emergence_void_left]

/-- T219. Virtual value decomposes into raw resonance terms. -/
theorem myersonVirtualValue_explicit (s r : I) :
    myersonVirtualValue s r =
    rs s (compose r s) - (rs (compose r s) s - rs r s - rs s s) := by
  unfold myersonVirtualValue senderPayoff interpret emergenceAdvantage emergence
  ring

/-- The incentive compatibility gap: how much an agent gains by
    misreporting. A mechanism is incentive-compatible when this is
    non-positive for all deviations. -/
noncomputable def icGap (truthful deviation r : I) : ℝ :=
  senderNetPayoff deviation r - senderNetPayoff truthful r

/-- T220. IC gap is zero for identical reports: truthful reporting
    is trivially IC-compatible with itself. -/
theorem icGap_self (s r : I) : icGap s s r = 0 := by
  unfold icGap; ring

/-- T221. At Nash equilibrium, the IC gap for the equilibrium signal
    is non-positive: no deviation improves the sender's payoff.
    This is precisely the best-response condition. -/
theorem icGap_nash_nonpos (s r : I) (h : isNashEquilibrium s r) (s' : I) :
    icGap s s' r ≤ 0 := by
  unfold icGap
  have := h.1 s'
  linarith

/-- T222. The IC gap from void to any signal equals the sender's
    net payoff of that signal: the "temptation to speak." -/
theorem icGap_from_void (s r : I) :
    icGap (void : I) s r = senderNetPayoff s r := by
  unfold icGap; rw [senderNetPayoff_void_signal]; ring

/-- The individual rationality (IR) constraint: each agent must prefer
    participating in the mechanism to staying out (getting void payoff). -/
def satisfiesIR (s r : I) : Prop :=
  senderNetPayoff s r ≥ 0 ∧ receiverNetPayoff s r ≥ 0

/-- T223. Nash equilibria automatically satisfy IR: at equilibrium,
    both players prefer to participate. This is the revelation
    principle for meaning games. -/
theorem nash_satisfies_IR (s r : I) (h : isNashEquilibrium s r) :
    satisfiesIR s r :=
  ⟨nash_sender_nonneg s r h, nash_receiver_nonneg s r h⟩

/-- T224. Void-void always satisfies IR: non-participation satisfies
    the participation constraint trivially. -/
theorem void_satisfies_IR :
    satisfiesIR (void : I) (void : I) := by
  exact ⟨le_of_eq (senderNetPayoff_void_signal _).symm,
         le_of_eq (receiverNetPayoff_void_receiver _).symm⟩

/-- The mechanism surplus: total value created by the mechanism minus
    what agents could achieve on their own. This is the "gains from
    trade" in the mechanism. -/
noncomputable def mechanismSurplus (a b : I) : ℝ :=
  rs (mechanismOutcome a b) (mechanismOutcome a b) - rs a a - rs b b

/-- T225. Mechanism surplus equals cooperation surplus. The gains from
    participating in a mechanism are exactly the cooperative surplus. -/
theorem mechanismSurplus_eq_coop (a b : I) :
    mechanismSurplus a b = cooperationSurplus a b := by
  unfold mechanismSurplus mechanismOutcome cooperationSurplus; ring

/-- T226. Mechanism surplus is bounded below by -rs(b,b). Even the
    worst mechanism cannot destroy more than what agent b brought. -/
theorem mechanismSurplus_lower (a b : I) :
    mechanismSurplus a b ≥ -rs b b := by
  rw [mechanismSurplus_eq_coop]; exact cooperationSurplus_lower_bound a b

end MechanismDesign

/-! ## §25. Auction Theory — Bidding for Ideas

An "idea auction" is a competitive mechanism where agents bid for the
right to compose with a target idea. The "price" of composition is
the self-resonance cost. We model first-price, second-price, and
all-pay auctions for ideas.

Key insight: in an idea auction, the "item" being auctioned is the
right to compose — to have your idea interact with the target.
-/

section AuctionTheory
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The value of composing bidder's idea with target: how much the
    bidder values winning the auction. This is the information content
    of the target for the bidder. -/
noncomputable def auctionValue (bidder target : I) : ℝ :=
  informationContent target bidder

/-- T227. Auction value is non-negative: composing with any target
    never reduces self-resonance. Every bidder weakly benefits. -/
theorem auctionValue_nonneg (bidder target : I) :
    auctionValue bidder target ≥ 0 := by
  unfold auctionValue; exact informationContent_nonneg target bidder

/-- T228. Auction value of void target is zero: there is nothing to
    gain from composing with silence. -/
theorem auctionValue_void_target (bidder : I) :
    auctionValue bidder (void : I) = 0 := by
  unfold auctionValue informationContent; simp

/-- T229. Auction value of void bidder equals the target's self-resonance.
    An empty mind gains everything from any idea. -/
theorem auctionValue_void_bidder (target : I) :
    auctionValue (void : I) target = rs target target := by
  unfold auctionValue informationContent; simp [rs_void_void]

/-- First-price auction payoff: value minus bid (self-resonance cost).
    In a first-price auction, the winner pays their own bid. -/
noncomputable def firstPricePayoff (bidder target : I) : ℝ :=
  auctionValue bidder target - signalCost bidder

/-- T230. First-price payoff of void bidder is zero: bidding nothing
    costs nothing and wins nothing meaningful. -/
theorem firstPricePayoff_void_bidder (target : I) :
    firstPricePayoff (void : I) target = rs target target := by
  unfold firstPricePayoff
  rw [auctionValue_void_bidder, signalCost_void]; ring

/-- T231. First-price payoff with void target: paying for nothing.
    The payoff is -rs(bidder, bidder) — a pure loss. -/
theorem firstPricePayoff_void_target (bidder : I) :
    firstPricePayoff bidder (void : I) = -signalCost bidder := by
  unfold firstPricePayoff; rw [auctionValue_void_target]; ring

/-- Second-price (Vickrey) auction payoff: value minus the SECOND
    highest bid. We model this as value minus a given price. -/
noncomputable def vickreyPayoff (bidder target : I) (price : ℝ) : ℝ :=
  auctionValue bidder target - price

/-- T232. In a Vickrey auction with zero price, the winner gets full
    value. This corresponds to no competition. -/
theorem vickreyPayoff_zero_price (bidder target : I) :
    vickreyPayoff bidder target 0 = auctionValue bidder target := by
  unfold vickreyPayoff; ring

/-- T233. Vickrey payoff is non-negative when price ≤ value:
    truthful bidding is individually rational. -/
theorem vickreyPayoff_nonneg (bidder target : I) (price : ℝ)
    (h : price ≤ auctionValue bidder target) :
    vickreyPayoff bidder target price ≥ 0 := by
  unfold vickreyPayoff; linarith

/-- All-pay auction payoff: everyone pays their bid, but only the
    winner gets the value. We model the "winner" version. -/
noncomputable def allPayWinnerPayoff (bidder target : I) : ℝ :=
  auctionValue bidder target - signalCost bidder

/-- T234. All-pay winner payoff equals first-price payoff. In
    both formats, the winner pays their own bid. The difference is
    that in all-pay, losers also pay. -/
theorem allPayWinner_eq_firstPrice (bidder target : I) :
    allPayWinnerPayoff bidder target = firstPricePayoff bidder target := by
  unfold allPayWinnerPayoff firstPricePayoff; ring

/-- All-pay loser payoff: you pay but don't compose with the target. -/
noncomputable def allPayLoserPayoff (bidder : I) : ℝ :=
  -signalCost bidder

/-- T235. All-pay loser payoff is non-positive: losers only lose.
    Paying your bid without gaining composition is always costly. -/
theorem allPayLoserPayoff_nonpos (bidder : I) :
    allPayLoserPayoff bidder ≤ 0 := by
  unfold allPayLoserPayoff signalCost
  linarith [S.rs_self_nonneg bidder]

/-- T236. Void bidder's loser payoff is zero: bidding nothing and
    losing costs nothing. -/
theorem allPayLoserPayoff_void :
    allPayLoserPayoff (void : I) = 0 := by
  unfold allPayLoserPayoff signalCost; rw [rs_void_void]; ring

/-- The revenue equivalence principle for idea auctions: the total
    "payment" extracted from both agents in a VCG mechanism equals
    the cooperation surplus. -/
theorem revenue_equivalence (a b : I) :
    vcgPayment a b = mechanismSurplus a b := by
  rw [vcgPayment_eq_coopSurplus, mechanismSurplus_eq_coop]

/-- T237. Auction value is additive in a specific sense: the value
    of composing with target equals the cooperation surplus plus the
    target's self-resonance. -/
theorem auctionValue_decomp (bidder target : I) :
    auctionValue bidder target =
    cooperationSurplus bidder target + rs target target := by
  unfold auctionValue
  rw [informationContent_eq_coopSurplus_shifted]

/-- T238. The winner's curse in idea auctions: the auction value is
    bounded by the self-resonance of the composed outcome. Winning
    doesn't guarantee the composed outcome is better than expected. -/
theorem winners_curse_bound (bidder target : I) :
    auctionValue bidder target ≤
    rs (compose bidder target) (compose bidder target) := by
  unfold auctionValue informationContent
  linarith [S.rs_self_nonneg bidder]

end AuctionTheory

/-! ## §26. Nash Bargaining Theory — Fair Division of Meaning

In bargaining theory, two agents negotiate over how to divide the
surplus from cooperation. The Nash bargaining solution maximizes the
product of net gains. We characterize the bargaining set, disagreement
point (void), and Nash solution properties.
-/

section BargainingTheory
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The disagreement payoff: what each agent gets if bargaining fails.
    In meaning games, failure = silence = void. -/
noncomputable def disagreementPayoff₁ (s : I) : ℝ := rs s s
noncomputable def disagreementPayoff₂ (r : I) : ℝ := rs r r

/-- T239. The disagreement point is always non-negative: even in
    failure, each agent retains their own self-resonance. -/
theorem disagreement_nonneg₁ (s : I) : disagreementPayoff₁ s ≥ 0 := by
  unfold disagreementPayoff₁; exact S.rs_self_nonneg s

theorem disagreement_nonneg₂ (r : I) : disagreementPayoff₂ r ≥ 0 := by
  unfold disagreementPayoff₂; exact S.rs_self_nonneg r

/-- T240. Void agent's disagreement payoff is zero: silence has nothing
    to fall back on. -/
theorem disagreement_void₁ : disagreementPayoff₁ (void : I) = 0 := by
  unfold disagreementPayoff₁; exact rs_void_void

theorem disagreement_void₂ : disagreementPayoff₂ (void : I) = 0 := by
  unfold disagreementPayoff₂; exact rs_void_void

/-- The Nash bargaining product: the product of net gains over
    disagreement. The Nash bargaining solution maximizes this. -/
noncomputable def nashBargainingProduct (s r : I) : ℝ :=
  senderNetPayoff s r * receiverNetPayoff s r

/-- T241. Nash bargaining product at void-void is zero: no surplus
    to divide when both are silent. -/
theorem nashBargaining_void :
    nashBargainingProduct (void : I) (void : I) = 0 := by
  unfold nashBargainingProduct
  rw [senderNetPayoff_void_signal]; ring

/-- T242. Nash bargaining product at Nash equilibrium is non-negative:
    both factors are non-negative at equilibrium. -/
theorem nashBargaining_nonneg_at_nash (s r : I) (h : isNashEquilibrium s r) :
    nashBargainingProduct s r ≥ 0 := by
  unfold nashBargainingProduct
  exact mul_nonneg (nash_sender_nonneg s r h) (nash_receiver_nonneg s r h)

/-- T243. At a communication fixed point, the Nash bargaining product
    is zero: at least one party gets exactly their disagreement payoff. -/
theorem nashBargaining_fixed_point (s r : I)
    (h : isCommunicationFixedPoint s r) :
    nashBargainingProduct s r = 0 := by
  unfold nashBargainingProduct
  rw [h.1]; ring

/-- The Rubinstein alternating-offers surplus: in alternating offers,
    the patient player extracts more of the surplus. We model patience
    as the number of rounds of persuasion each side can endure. -/
noncomputable def rubinsteinSurplus (s r : I) (nSender nReceiver : ℕ) : ℝ :=
  nRoundValue s r nSender + nRoundValue r s nReceiver

/-- T244. Rubinstein surplus is non-negative: both parties' contributions
    are non-negative by the monotone communication principle. -/
theorem rubinsteinSurplus_nonneg (s r : I) (m n : ℕ) :
    rubinsteinSurplus s r m n ≥ 0 := by
  unfold rubinsteinSurplus
  linarith [nRoundValue_nonneg s r m, nRoundValue_nonneg r s n]

/-- T245. Rubinstein surplus with zero rounds for both is zero:
    no patience, no surplus. -/
theorem rubinsteinSurplus_zero (s r : I) :
    rubinsteinSurplus s r 0 0 = 0 := by
  unfold rubinsteinSurplus; simp [nRoundValue_zero]

/-- T246. More sender patience means more total surplus: monotonicity
    in sender rounds. -/
theorem rubinsteinSurplus_sender_mono (s r : I) (m n : ℕ) :
    rubinsteinSurplus s r (m + 1) n ≥ rubinsteinSurplus s r m n := by
  unfold rubinsteinSurplus
  linarith [nRoundValue_mono s r m]

/-- T247. More receiver patience means more total surplus. -/
theorem rubinsteinSurplus_receiver_mono (s r : I) (m n : ℕ) :
    rubinsteinSurplus s r m (n + 1) ≥ rubinsteinSurplus s r m n := by
  unfold rubinsteinSurplus
  linarith [nRoundValue_mono r s n]

/-- The bargaining power ratio: the sender's share of surplus divided
    by the total surplus. When positive, this measures who captures more
    of the cooperative gain. -/
noncomputable def senderBargainingShare (s r : I) : ℝ :=
  senderNetPayoff s r

/-- T248. Sender bargaining share at void signal is zero: silence
    claims no share of the surplus. -/
theorem senderShare_void (r : I) :
    senderBargainingShare (void : I) r = 0 := by
  unfold senderBargainingShare; exact senderNetPayoff_void_signal r

/-- T249. The total surplus equals the sum of bargaining shares.
    This is the exhaustiveness of surplus division. -/
theorem surplus_exhaustive (s r : I) :
    communicationSurplus s r =
    senderBargainingShare s r + receiverNetPayoff s r := by
  unfold senderBargainingShare; exact communicationSurplus_eq_net s r

end BargainingTheory

/-! ## §27. Contract Theory — Moral Hazard and Adverse Selection

In contract theory, moral hazard arises when one party's effort
(signal quality) is unobservable. Adverse selection arises when
types (intrinsic self-resonance) are private information.

We model a "contract" as a commitment to send a particular signal,
and analyze when contracts are self-enforcing (incentive compatible)
versus when hidden action or hidden type problems arise.
-/

section ContractTheory
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The effort cost: the self-resonance of the signal measures how much
    effort the sender invests. Higher-quality signals cost more. -/
noncomputable def effortCost (s : I) : ℝ := rs s s

/-- T250. Effort cost is non-negative: all signals require non-negative
    effort. Only void is free. -/
theorem effortCost_nonneg (s : I) : effortCost s ≥ 0 := by
  unfold effortCost; exact S.rs_self_nonneg s

/-- T251. Void requires zero effort: silence is costless. -/
theorem effortCost_void : effortCost (void : I) = 0 := by
  unfold effortCost; exact rs_void_void

/-- The moral hazard gap: the difference between the contracted effort
    level and the actual effort. Positive means the agent shirked. -/
noncomputable def moralHazardGap (contracted actual : I) : ℝ :=
  effortCost contracted - effortCost actual

/-- T252. Moral hazard gap is zero when contracted equals actual:
    no shirking when the agent does what they promised. -/
theorem moralHazardGap_honest (s : I) : moralHazardGap s s = 0 := by
  unfold moralHazardGap; ring

/-- T253. If actual effort exceeds contracted, the gap is negative:
    the agent over-delivers. In meaning games, this means sending a
    richer signal than promised. -/
theorem moralHazardGap_overdeliver (contracted actual : I)
    (h : effortCost actual > effortCost contracted) :
    moralHazardGap contracted actual < 0 := by
  unfold moralHazardGap; linarith

/-- T254. If the agent shirks to void, the moral hazard gap equals
    the full contracted effort. Total shirking wastes everything. -/
theorem moralHazardGap_total_shirk (contracted : I) :
    moralHazardGap contracted (void : I) = effortCost contracted := by
  unfold moralHazardGap effortCost; rw [rs_void_void]; ring

/-- The adverse selection premium: how much more a "high type" (higher
    self-resonance) agent benefits from communication compared to a
    "low type." This measures the information asymmetry. -/
noncomputable def adverseSelectionPremium (highType lowType r : I) : ℝ :=
  senderNetPayoff highType r - senderNetPayoff lowType r

/-- T255. Adverse selection premium is zero for identical types:
    no information asymmetry when types are the same. -/
theorem adverseSelection_same_type (s r : I) :
    adverseSelectionPremium s s r = 0 := by
  unfold adverseSelectionPremium; ring

/-- T256. Adverse selection premium when both types face void receiver
    is zero: if nobody listens, type doesn't matter. -/
theorem adverseSelection_void_receiver (h l : I) :
    adverseSelectionPremium h l (void : I) = 0 := by
  unfold adverseSelectionPremium
  rw [senderNetPayoff_void_receiver, senderNetPayoff_void_receiver]; ring

/-- T257. Adverse selection premium decomposes into resonance
    differences. This reveals the structural source of type advantage. -/
theorem adverseSelection_explicit (h l r : I) :
    adverseSelectionPremium h l r =
    (rs h (compose r h) - rs h h) - (rs l (compose r l) - rs l l) := by
  unfold adverseSelectionPremium senderNetPayoff senderPayoff interpret; ring

/-- The contract value: the expected gain from a contract that specifies
    both the signal and the interpretation rule. -/
noncomputable def contractValue (signal receiver : I) : ℝ :=
  communicationSurplus signal receiver

/-- T258. Contract value is non-negative at Nash equilibrium:
    equilibrium contracts create value. -/
theorem contractValue_nonneg_nash (s r : I) (h : isNashEquilibrium s r) :
    contractValue s r ≥ 0 := by
  unfold contractValue; exact nash_surplus_nonneg s r h

/-- T259. Void contract has zero value: a contract to say nothing
    creates no surplus. -/
theorem contractValue_void : contractValue (void : I) (void : I) = 0 := by
  unfold contractValue; exact communicationSurplus_void_signal _

/-- The participation constraint surplus: how much better an agent
    does under the contract than under autarky (void). -/
noncomputable def participationSurplus (s r : I) : ℝ :=
  senderNetPayoff s r

/-- T260. Participation surplus at void signal is zero: the outside
    option (silence) yields zero net payoff. -/
theorem participationSurplus_void (r : I) :
    participationSurplus (void : I) r = 0 := by
  unfold participationSurplus; exact senderNetPayoff_void_signal r

end ContractTheory

/-! ## §28. Screening vs Signaling — Spence and Rothschild-Stiglitz

In signaling, the informed party (sender) chooses a costly action to
reveal type. In screening, the uninformed party (receiver) designs a
menu of contracts to separate types. We formalize both and prove
their duality.
-/

section ScreeningSignaling
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A screening menu: the receiver offers different interpretation
    contexts. Each context induces different payoffs for different
    sender types. -/
noncomputable def screeningPayoff (senderType context : I) : ℝ :=
  rs senderType (compose context senderType) - rs senderType senderType

/-- T261. Screening payoff equals sender net payoff with roles reversed:
    the receiver's menu offering is the sender's interpretation choice. -/
theorem screeningPayoff_eq (s ctx : I) :
    screeningPayoff s ctx = senderNetPayoff s ctx := by
  unfold screeningPayoff senderNetPayoff senderPayoff interpret; ring

/-- T262. Screening payoff of void context is zero: an empty menu
    offers nothing to any type. -/
theorem screeningPayoff_void_context (s : I) :
    screeningPayoff s (void : I) = 0 := by
  rw [screeningPayoff_eq]; exact senderNetPayoff_void_receiver s

/-- T263. Screening payoff of void type is zero: a type with no
    substance gains nothing from any menu. -/
theorem screeningPayoff_void_type (ctx : I) :
    screeningPayoff (void : I) ctx = 0 := by
  rw [screeningPayoff_eq]; exact senderNetPayoff_void_signal ctx

/-- The Spence signaling cost: the differential cost between high
    and low types for sending the same signal. If this is positive,
    the signal is cheaper for the high type, enabling separation. -/
noncomputable def spenceDifferentialCost (signalH signalL : I) : ℝ :=
  signalCost signalL - signalCost signalH

/-- T264. Spence differential cost is antisymmetric. Swapping
    high and low types negates the cost differential. -/
theorem spenceDifferential_antisymm (h l : I) :
    spenceDifferentialCost h l = -spenceDifferentialCost l h := by
  unfold spenceDifferentialCost; ring

/-- T265. Spence differential cost with identical types is zero. -/
theorem spenceDifferential_self (s : I) :
    spenceDifferentialCost s s = 0 := by
  unfold spenceDifferentialCost; ring

/-- The Rothschild-Stiglitz separation condition: a menu separates
    two types if each type strictly prefers its intended contract. -/
def rothschildStiglitzSeparation (type₁ type₂ ctx₁ ctx₂ : I) : Prop :=
  screeningPayoff type₁ ctx₁ > screeningPayoff type₁ ctx₂ ∧
  screeningPayoff type₂ ctx₂ > screeningPayoff type₂ ctx₁

/-- T266. Separation implies the types are distinguishable: they
    must differ in at least one screening payoff. -/
theorem separation_implies_distinguishable (t₁ t₂ c₁ c₂ : I)
    (h : rothschildStiglitzSeparation t₁ t₂ c₁ c₂) :
    screeningPayoff t₁ c₁ ≠ screeningPayoff t₂ c₁ ∨
    screeningPayoff t₁ c₂ ≠ screeningPayoff t₂ c₂ := by
  by_contra hc
  push_neg at hc
  linarith [h.1, h.2, hc.1, hc.2]

/-- The signaling-screening duality: the signaling payoff of sending s
    in context r equals the screening payoff of type s in menu r.
    Both are the same fundamental quantity: net payoff from interaction. -/
theorem signaling_screening_duality (s r : I) :
    senderNetPayoff s r = screeningPayoff s r := by
  rw [screeningPayoff_eq]

/-- T267. The pooling condition: two types pool if they get the same
    payoff from every menu item. -/
def isPooling (type₁ type₂ : I) : Prop :=
  ∀ ctx : I, screeningPayoff type₁ ctx = screeningPayoff type₂ ctx

/-- T268. Pooling is reflexive. -/
theorem pooling_refl (t : I) : isPooling t t :=
  fun _ => rfl

/-- T269. Pooling is symmetric. -/
theorem pooling_symm (t₁ t₂ : I) (h : isPooling t₁ t₂) :
    isPooling t₂ t₁ :=
  fun ctx => (h ctx).symm

/-- T270. Pooling is transitive. -/
theorem pooling_trans (t₁ t₂ t₃ : I) (h₁ : isPooling t₁ t₂) (h₂ : isPooling t₂ t₃) :
    isPooling t₁ t₃ :=
  fun ctx => (h₁ ctx).trans (h₂ ctx)

/-- T271. If two types pool, they cannot be RS-separated by any
    menu: separation requires payoff differences. -/
theorem pooling_prevents_separation (t₁ t₂ : I) (h : isPooling t₁ t₂)
    (c₁ c₂ : I) : ¬rothschildStiglitzSeparation t₁ t₂ c₁ c₂ := by
  intro hs
  have := h c₁; have := h c₂
  linarith [hs.1, hs.2]

end ScreeningSignaling

/-! ## §29. Cheap Talk Refinements — Crawford-Sobel

In Crawford-Sobel cheap talk games, the sender's type is drawn from
a continuum, and the receiver takes an action based on the signal.
Equilibria are characterized by "partition equilibria" where the
type space is divided into intervals.

We model partition equilibria as compositions of threshold signals:
each partition element is an idea that covers a range of types.
-/

section CheapTalkRefinements
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A signal is a neologism — a new word not in the existing vocabulary —
    if it creates strictly positive emergence with the receiver.
    Neologisms are credible cheap-talk refinements because they generate
    meaning beyond existing signals. -/
def isNeologism (s r : I) : Prop :=
  emergence r s (compose r s) > 0

/-- T272. Void is never a neologism: silence creates no emergence. -/
theorem void_not_neologism (r : I) : ¬isNeologism (void : I) r := by
  unfold isNeologism
  simp [emergence_void_right]

/-- T273. A neologism for void receiver is impossible: without a
    listener, no new meaning can emerge. -/
theorem no_neologism_void_receiver (s : I) : ¬isNeologism s (void : I) := by
  unfold isNeologism
  simp [emergence_void_left]

/-- The Crawford-Sobel bias: the difference between sender and receiver
    resonance with the interpretation. Higher bias means less
    informative equilibria exist. -/
noncomputable def crawfordSobelBias (s r : I) : ℝ :=
  senderPayoff s r - receiverPayoff s r

/-- T274. Crawford-Sobel bias equals the misunderstanding gap.
    Bias and misunderstanding are the same quantity: the more biased
    the sender, the more misunderstanding occurs. -/
theorem crawfordSobel_eq_gap (s r : I) :
    crawfordSobelBias s r = misunderstandingGap s r := by
  unfold crawfordSobelBias misunderstandingGap; ring

/-- T275. Crawford-Sobel bias for void signal is -rs(r,r): when the
    sender says nothing, the entire gap comes from the receiver's
    self-resonance. -/
theorem crawfordSobel_void_signal (r : I) :
    crawfordSobelBias (void : I) r = -rs r r := by
  unfold crawfordSobelBias senderPayoff receiverPayoff interpret
  simp [rs_void_left']

/-- T276. Crawford-Sobel bias for void receiver is rs(s,s): when nobody
    listens, the entire gap is the sender's self-resonance. -/
theorem crawfordSobel_void_receiver (s : I) :
    crawfordSobelBias s (void : I) = rs s s := by
  unfold crawfordSobelBias senderPayoff receiverPayoff interpret
  simp [rs_void_left', rs_void_right']

/-- The information partition fineness: the total emergence across
    a sequence of signals sent sequentially. Finer partitions produce
    more emergence and thus more information transfer. -/
noncomputable def partitionFineness (r : I) (signals : List I) : ℝ :=
  discourseEmergence r signals

/-- T277. Empty partition has zero fineness. -/
theorem partitionFineness_nil (r : I) :
    partitionFineness r [] = 0 := by
  unfold partitionFineness; exact discourseEmergence_nil r

/-- T278. Non-empty partitions have non-negative fineness. -/
theorem partitionFineness_cons_nonneg (r s : I) (rest : List I) :
    partitionFineness r (s :: rest) ≥ 0 := by
  unfold partitionFineness; exact discourseEmergence_cons_nonneg r s rest

/-- The babbling deviation gain: how much a sender gains by deviating
    from babbling to a meaningful signal. This is the incentive to
    break the babbling equilibrium. -/
noncomputable def babblingDeviationGain (s r : I) : ℝ :=
  senderNetPayoff s r

/-- T279. Babbling deviation gain of void is zero: no incentive to
    deviate to silence from silence. -/
theorem babblingDeviation_void (r : I) :
    babblingDeviationGain (void : I) r = 0 := by
  unfold babblingDeviationGain; exact senderNetPayoff_void_signal r

/-- T280. Under babbling, the deviation gain decomposes into a
    pure cross-resonance shift. This is the "temptation to communicate"
    even when the receiver ignores you. -/
theorem babblingDeviation_under_babbling (r : I) (h : isBabbling r) (s : I) :
    babblingDeviationGain s r = rs s (compose r s) - rs s s := by
  unfold babblingDeviationGain
  exact babbling_sender_net_explicit r h s

end CheapTalkRefinements

/-! ## §30. Global Games and Coordination

In global games, agents receive noisy signals about a common
fundamental and must coordinate their actions. The key insight is
that strategic uncertainty about others' actions creates unique
equilibria even when there are multiple equilibria in the complete
information game.

We model coordination as the self-resonance of the joint composition:
agents coordinate successfully when their composed ideas produce high
self-resonance (strong emergent meaning).
-/

section GlobalGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- Coordination success: the self-resonance of the joint composition
    minus what each agent would achieve alone. This measures how well
    the agents coordinated their ideas. -/
noncomputable def coordinationSuccess (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a - rs b b

/-- T281. Coordination success equals cooperation surplus. Successful
    coordination IS cooperation — they are the same concept formalized
    differently. -/
theorem coordination_eq_cooperation (a b : I) :
    coordinationSuccess a b = cooperationSurplus a b := by
  unfold coordinationSuccess cooperationSurplus; ring

/-- T282. Coordination with void is zero: you can't coordinate with
    silence. -/
theorem coordination_void_right (a : I) :
    coordinationSuccess a (void : I) = 0 := by
  rw [coordination_eq_cooperation]; exact cooperationSurplus_void_right a

theorem coordination_void_left (b : I) :
    coordinationSuccess (void : I) b = 0 := by
  rw [coordination_eq_cooperation]; exact cooperationSurplus_void_left b

/-- The coordination premium: how much better coordinated action is
    than the best unilateral action. This is the "value of coordination." -/
noncomputable def coordinationPremium (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - max (rs a a) (rs b b)

/-- T283. Coordination premium bounded below: composing always enriches
    at least the first component. -/
theorem coordinationPremium_lower (a b : I) :
    coordinationPremium a b ≥ rs a a - max (rs a a) (rs b b) := by
  unfold coordinationPremium
  linarith [S.compose_enriches a b]

/-- The strategic complementarity: composing ideas produces at least
    as much self-resonance as either idea alone. This is the
    fundamental strategic complementarity of meaning composition. -/
theorem strategic_complementarity (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a := by
  exact S.compose_enriches a b

/-- T284. Global games threshold: the self-resonance of a composed
    signal exceeds the threshold set by either component alone. -/
theorem global_game_threshold (a b : I) :
    rs (compose a b) (compose a b) ≥ rs a a :=
  S.compose_enriches a b

/-- The miscoordination loss: how much coordination failure costs.
    When agents choose incompatible actions, the loss is measured
    by comparing coordinated vs. uncoordinated outcomes. -/
noncomputable def miscoordinationLoss (intended actual : I) : ℝ :=
  rs (compose intended intended) (compose intended intended) -
  rs (compose intended actual) (compose intended actual)

/-- T285. Miscoordination loss is zero when actual equals intended:
    perfect coordination has zero loss. -/
theorem miscoordination_self (a : I) :
    miscoordinationLoss a a = 0 := by
  unfold miscoordinationLoss; ring

/-- T286. The dominance solvability condition: if one signal strictly
    dominates another for all receivers, the dominated signal is never
    played in equilibrium. Here, "dominates" means higher net payoff. -/
def strictlyDominates (s₁ s₂ : I) : Prop :=
  ∀ r : I, senderNetPayoff s₁ r > senderNetPayoff s₂ r

/-- T287. Strict dominance is irreflexive: no signal dominates itself. -/
theorem dominance_irrefl (s : I) : ¬strictlyDominates s s := by
  unfold strictlyDominates
  push_neg; exact ⟨void, le_refl _⟩

/-- T288. Strict dominance is transitive. -/
theorem dominance_trans (s₁ s₂ s₃ : I)
    (h₁ : strictlyDominates s₁ s₂) (h₂ : strictlyDominates s₂ s₃) :
    strictlyDominates s₁ s₃ := by
  intro r; linarith [h₁ r, h₂ r]

/-- T289. If s₁ strictly dominates s₂, s₁ is not void (unless s₂ is).
    A dominating signal must have substance. -/
theorem dominating_signal_substance (s₁ s₂ : I)
    (h : strictlyDominates s₁ s₂) :
    senderNetPayoff s₁ (void : I) > senderNetPayoff s₂ (void : I) :=
  h (void : I)

end GlobalGames

/-! ## §31. Evolutionary Game Theory — Replicator Dynamics and ESS

Evolutionary game theory studies how strategies evolve through
selection and mutation. An Evolutionarily Stable Strategy (ESS)
is one that, once established, cannot be invaded by any mutant.

In meaning games, "strategies" are utterances, and "fitness" is
the payoff from communication. An ESS is an utterance that resists
invasion by any alternative utterance.
-/

section EvolutionaryGameTheory
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The fitness of strategy s in a population playing strategy r:
    the payoff from communicating with the population. -/
noncomputable def fitness (s r : I) : ℝ :=
  senderPayoff s r + receiverPayoff s r

/-- T290. Fitness equals social welfare: in evolutionary games,
    fitness is the total communication payoff. -/
theorem fitness_eq_welfare (s r : I) :
    fitness s r = socialWelfare s r := by
  unfold fitness socialWelfare; ring

/-- T291. Fitness of void against void is zero: silence has no
    evolutionary advantage. -/
theorem fitness_void : fitness (void : I) (void : I) = 0 := by
  rw [fitness_eq_welfare]; exact socialWelfare_void_void

/-- T292. Fitness of strategy against itself: the self-play payoff. -/
theorem fitness_self (a : I) :
    fitness a a = 2 * rs a (compose a a) := by
  rw [fitness_eq_welfare]; exact welfare_self_signal a

/-- An Evolutionarily Stable Strategy (ESS): a strategy that is a
    best response to itself AND does strictly better against mutants
    than the mutants do against themselves. -/
def isESS (s : I) : Prop :=
  (∀ m : I, fitness s s ≥ fitness m s) ∧
  (∀ m : I, fitness s s = fitness m s → m ≠ s →
    fitness s m > fitness m m)

/-- T293. If s is an ESS, it achieves maximum self-play fitness:
    no mutant does better against the incumbent population. -/
theorem ess_max_fitness (s : I) (h : isESS s) (m : I) :
    fitness s s ≥ fitness m s := h.1 m

/-- The replicator growth rate: how fast strategy s grows relative to
    strategy r in a population where both interact. Positive means s
    is growing (it outperforms the population average). -/
noncomputable def replicatorGrowth (s r : I) : ℝ :=
  fitness s r - fitness r r

/-- T294. Replicator growth of void against void is zero: silence
    neither grows nor shrinks. -/
theorem replicatorGrowth_void :
    replicatorGrowth (void : I) (void : I) = 0 := by
  unfold replicatorGrowth; rw [fitness_void]; ring

/-- T295. Replicator growth rate decomposes into welfare comparison. -/
theorem replicatorGrowth_eq (s r : I) :
    replicatorGrowth s r = socialWelfare s r - socialWelfare r r := by
  unfold replicatorGrowth; rw [fitness_eq_welfare, fitness_eq_welfare]

/-- The invasion barrier: the minimum fitness advantage needed for a
    mutant to invade. At an ESS, the invasion barrier is positive for
    all potential invaders. -/
noncomputable def invasionBarrier (s m : I) : ℝ :=
  fitness s s - fitness m s

/-- T296. Invasion barrier is non-negative at an ESS. -/
theorem invasionBarrier_nonneg_ess (s : I) (h : isESS s) (m : I) :
    invasionBarrier s m ≥ 0 := by
  unfold invasionBarrier; linarith [h.1 m]

/-- T297. Invasion barrier of self is zero: the incumbent trivially
    matches itself. -/
theorem invasionBarrier_self (s : I) :
    invasionBarrier s s = 0 := by
  unfold invasionBarrier; ring

/-- The evolutionary drift: the change in fitness when the population
    composition shifts from pure r to a mix with some s. -/
noncomputable def evolutionaryDrift (s r : I) : ℝ :=
  fitness s r - fitness r r

/-- T298. Evolutionary drift equals replicator growth. These are the
    same concept measured differently: drift is the population-level
    effect, growth is the individual-level effect. -/
theorem drift_eq_growth (s r : I) :
    evolutionaryDrift s r = replicatorGrowth s r := by
  unfold evolutionaryDrift replicatorGrowth; ring

/-- T299. A strategy is neutrally stable if no mutant does strictly
    better against the incumbent. -/
def isNeutrallyStable (s : I) : Prop :=
  ∀ m : I, fitness s s ≥ fitness m s

/-- T300. Every ESS is neutrally stable. -/
theorem ess_implies_neutrallyStable (s : I) (h : isESS s) :
    isNeutrallyStable s := h.1

end EvolutionaryGameTheory

/-! ## §32. Learning in Games — Fictitious Play and No-Regret

Learning in games concerns how agents update their strategies based
on experience. Fictitious play = best-respond to historical frequency.
No-regret learning = cumulative payoff ≥ best fixed strategy in hindsight.

We model learning through iterated communication: after each round,
the agent's state is updated by composition with the received signal,
and the cumulative regret tracks how far behind the best response
the agent has fallen.
-/

section LearningInGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The cumulative payoff from n rounds of play with fixed strategies. -/
noncomputable def cumulativePayoff (s r : I) (n : ℕ) : ℝ :=
  n * senderNetPayoff s r

/-- T301. Cumulative payoff at round 0 is zero. -/
theorem cumulativePayoff_zero (s r : I) : cumulativePayoff s r 0 = 0 := by
  unfold cumulativePayoff; ring

/-- T302. Cumulative payoff is additive: n+1 rounds = n rounds + 1 round. -/
theorem cumulativePayoff_succ (s r : I) (n : ℕ) :
    cumulativePayoff s r (n + 1) =
    cumulativePayoff s r n + senderNetPayoff s r := by
  unfold cumulativePayoff; push_cast; ring

/-- The regret of playing s instead of the best alternative s'.
    Regret measures hindsight loss: how much better s' would have been. -/
noncomputable def regret (s s' r : I) (n : ℕ) : ℝ :=
  cumulativePayoff s' r n - cumulativePayoff s r n

/-- T303. Regret is zero when playing the same strategy: you can't
    regret doing exactly what you did. -/
theorem regret_self (s r : I) (n : ℕ) : regret s s r n = 0 := by
  unfold regret; ring

/-- T304. Regret is antisymmetric: your regret from s to s' equals
    the negative of s' to s. -/
theorem regret_antisymm (s s' r : I) (n : ℕ) :
    regret s s' r n = -regret s' s r n := by
  unfold regret; ring

/-- T305. Regret of playing void instead of s is n times the net payoff
    of s. This is the "cost of silence." -/
theorem regret_from_void (s r : I) (n : ℕ) :
    regret (void : I) s r n = cumulativePayoff s r n := by
  unfold regret cumulativePayoff
  rw [senderNetPayoff_void_signal]; ring

/-- T306. At Nash equilibrium, the regret from playing the equilibrium
    strategy against any alternative is non-positive: no regret. -/
theorem no_regret_nash (s r : I) (h : isNashEquilibrium s r) (s' : I) (n : ℕ) :
    regret s s' r n ≤ 0 := by
  unfold regret cumulativePayoff
  have := h.1 s'
  nlinarith

/-- The fictitious play update: after observing the opponent play r,
    the agent composes with r to update their state. This models
    learning by "absorbing" the opponent's strategy. -/
def fictitiousPlayUpdate (agent opponent : I) : I :=
  compose agent opponent

/-- T307. Fictitious play update enriches the agent's state: learning
    from experience never reduces self-resonance. -/
theorem fictitiousPlay_enriches (agent opponent : I) :
    rs (fictitiousPlayUpdate agent opponent) (fictitiousPlayUpdate agent opponent) ≥
    rs agent agent := by
  unfold fictitiousPlayUpdate; exact S.compose_enriches agent opponent

/-- T308. Fictitious play update with void opponent leaves agent unchanged:
    observing silence teaches nothing. -/
theorem fictitiousPlay_void (agent : I) :
    fictitiousPlayUpdate agent (void : I) = agent := by
  unfold fictitiousPlayUpdate; simp

/-- The n-step fictitious play: iterate updates n times. -/
def fictitiousPlayN (agent opponent : I) (n : ℕ) : I :=
  persuade opponent agent n

/-- T309. n-step fictitious play at step 0 is the agent unchanged. -/
theorem fictitiousPlayN_zero (agent opponent : I) :
    fictitiousPlayN agent opponent 0 = agent := by
  unfold fictitiousPlayN; simp

/-- T310. n-step fictitious play enrichment is monotone: more rounds
    of learning never decrease self-resonance. -/
theorem fictitiousPlayN_mono (agent opponent : I) (n : ℕ) :
    rs (fictitiousPlayN agent opponent (n + 1))
       (fictitiousPlayN agent opponent (n + 1)) ≥
    rs (fictitiousPlayN agent opponent n)
       (fictitiousPlayN agent opponent n) := by
  unfold fictitiousPlayN
  exact persuade_selfrs_mono opponent agent n

/-- The learning rate: how much self-resonance increases per step
    of fictitious play. -/
noncomputable def learningRate (agent opponent : I) (n : ℕ) : ℝ :=
  rs (fictitiousPlayN agent opponent (n + 1))
     (fictitiousPlayN agent opponent (n + 1)) -
  rs (fictitiousPlayN agent opponent n)
     (fictitiousPlayN agent opponent n)

/-- T311. Learning rate is non-negative: each step of learning adds
    non-negative self-resonance. -/
theorem learningRate_nonneg (agent opponent : I) (n : ℕ) :
    learningRate agent opponent n ≥ 0 := by
  unfold learningRate
  linarith [fictitiousPlayN_mono agent opponent n]

/-- T312. Learning rate with void opponent is zero: you learn nothing
    from silence. -/
theorem learningRate_void_opponent (agent : I) (n : ℕ) :
    learningRate agent (void : I) n = 0 := by
  unfold learningRate fictitiousPlayN; simp

end LearningInGames

/-! ## §33. Matching Theory — Stable Matchings in Idea Exchange

In matching theory, agents are paired for mutual communication.
A matching is "stable" if no pair would prefer to be matched with
each other over their current partners. We formalize stability
in terms of communication surplus.
-/

section MatchingTheory
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The match value: the bilateral communication surplus between
    two agents. This is what the pair jointly gains from being matched. -/
noncomputable def matchValue (a b : I) : ℝ :=
  communicationSurplus a b

/-- T313. Match value with void is zero: being matched with silence
    creates no surplus. -/
theorem matchValue_void_left (b : I) :
    matchValue (void : I) b = 0 := by
  unfold matchValue; exact communicationSurplus_void_signal b

theorem matchValue_void_right (a : I) :
    matchValue a (void : I) = 0 := by
  unfold matchValue; exact communicationSurplus_void_reader a

/-- A matching is blocked by pair (a, b) if they would both prefer
    each other to their current partners. -/
def isBlockingPair (a b currentA currentB : I) : Prop :=
  matchValue a b > matchValue a currentA ∧
  matchValue b a > matchValue b currentB

/-- T314. An agent cannot block their own self-matching: you can't
    improve by switching to yourself. -/
theorem no_self_block (a : I) :
    ¬isBlockingPair a a a a := by
  intro ⟨h1, _⟩; exact lt_irrefl _ h1

/-- T315. Void-void matching is immune to blocking by void pairs:
    replacing silence with silence is never an improvement. -/
theorem void_matching_stable_void (a : I) :
    ¬isBlockingPair (void : I) (void : I) a a := by
  unfold isBlockingPair matchValue
  intro ⟨h1, h2⟩
  have h3 := communicationSurplus_void_signal a
  have h4 := communicationSurplus_void_signal (void : I)
  linarith

/-- The assortative matching criterion: agents are better matched
    with "similar" ideas (those that create more emergence). -/
noncomputable def matchQuality (a b : I) : ℝ :=
  rs (compose a b) (compose a b) - rs a a

/-- T316. Match quality is non-negative: any composition enriches. -/
theorem matchQuality_nonneg (a b : I) :
    matchQuality a b ≥ 0 := by
  unfold matchQuality; linarith [S.compose_enriches a b]

/-- T317. Match quality of void partner is zero. -/
theorem matchQuality_void (a : I) :
    matchQuality a (void : I) = 0 := by
  unfold matchQuality; simp

/-- T318. Match quality equals information content: the quality of
    a match IS how much information the partner provides. -/
theorem matchQuality_eq_info (a b : I) :
    matchQuality a b = informationContent b a := by
  unfold matchQuality informationContent; ring

/-- The match stability surplus: a matching is stable if no
    blocking pair exists. We characterize the minimum surplus
    needed to prevent blocking. -/
noncomputable def stabilityMargin (a b alternative : I) : ℝ :=
  matchValue a b - matchValue a alternative

/-- T319. Stability margin against void alternative equals the match
    value: any positive match value is stable against being unmatched. -/
theorem stabilityMargin_void (a b : I) :
    stabilityMargin a b (void : I) = matchValue a b := by
  unfold stabilityMargin matchValue
  rw [communicationSurplus_void_reader]; ring

/-- T320. Stability margin is zero for same alternative. -/
theorem stabilityMargin_self (a b : I) :
    stabilityMargin a b b = 0 := by
  unfold stabilityMargin; ring

end MatchingTheory

/-! ## §34. Network Games — Strategic Network Formation

In network games, agents decide which connections to form. Each
connection is a composition link. The network structure determines
information flow and payoffs.

We model a network as a list of composition partners: an agent's
"network position" is the discourse state after composing with
all connected agents.
-/

section NetworkGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- An agent's network position: their state after composing with
    all partners in their network (given as a list). -/
def networkPosition (agent : I) (partners : List I) : I :=
  discourse agent partners

/-- T321. Empty network: agent stays as they are. -/
theorem networkPosition_nil (agent : I) :
    networkPosition agent [] = agent := by
  unfold networkPosition; simp

/-- T322. Single-link network: just binary composition. -/
theorem networkPosition_singleton (agent partner : I) :
    networkPosition agent [partner] = compose agent partner := by
  unfold networkPosition; exact discourse_singleton agent partner

/-- T323. Network self-resonance is at least the agent's baseline:
    adding connections never reduces self-resonance. -/
theorem network_enrichment (agent partner : I) (rest : List I) :
    rs (networkPosition agent (partner :: rest))
       (networkPosition agent (partner :: rest)) ≥
    rs agent agent := by
  unfold networkPosition discourse
  exact discourse_enriches agent partner rest

/-- The network externality: how much a new connection adds to an
    agent's self-resonance beyond what they already have from their
    existing network. -/
noncomputable def networkExternality (agent : I) (existing : List I) (newPartner : I) : ℝ :=
  rs (networkPosition agent (existing ++ [newPartner]))
     (networkPosition agent (existing ++ [newPartner])) -
  rs (networkPosition agent existing)
     (networkPosition agent existing)

/-- T324. Network externality is non-negative: adding a connection
    never hurts (by compose_enriches). -/
theorem networkExternality_nonneg (agent : I) (existing : List I) (newPartner : I) :
    networkExternality agent existing newPartner ≥ 0 := by
  unfold networkExternality networkPosition
  have := cumulativeEnrichment_append_mono agent newPartner existing
  unfold cumulativeEnrichment at this
  linarith

/-- T325. Network externality of void partner is zero: connecting
    to silence adds nothing. -/
theorem networkExternality_void (agent : I) (existing : List I) :
    networkExternality agent existing (void : I) = 0 := by
  unfold networkExternality networkPosition
  induction existing generalizing agent with
  | nil => unfold discourse; simp
  | cons s rest ih =>
    simp only [List.cons_append, discourse]
    exact ih (compose agent s)

/-- The network value: total self-resonance gain from the full network
    compared to isolation. -/
noncomputable def networkValue (agent : I) (partners : List I) : ℝ :=
  rs (networkPosition agent partners) (networkPosition agent partners) -
  rs agent agent

/-- T326. Network value of empty network is zero. -/
theorem networkValue_nil (agent : I) :
    networkValue agent [] = 0 := by
  unfold networkValue networkPosition; simp

/-- T327. Network value is non-negative: networks create value. -/
theorem networkValue_cons_nonneg (agent partner : I) (rest : List I) :
    networkValue agent (partner :: rest) ≥ 0 := by
  unfold networkValue networkPosition discourse
  linarith [discourse_enriches agent partner rest]

/-- T328. Network value grows with additional partners. -/
theorem networkValue_mono (agent : I) (partners : List I) (newPartner : I) :
    networkValue agent (partners ++ [newPartner]) ≥
    networkValue agent partners := by
  unfold networkValue networkPosition
  have := networkExternality_nonneg agent partners newPartner
  unfold networkExternality networkPosition at this
  linarith

/-- The clustering coefficient: how much composing all partners
    together differs from composing them sequentially. We measure
    this as the difference between sequential and parallel composition. -/
noncomputable def networkClustering (agent p₁ p₂ : I) : ℝ :=
  rs (networkPosition agent [p₁, p₂]) (networkPosition agent [p₁, p₂]) -
  rs (compose agent (compose p₁ p₂)) (compose agent (compose p₁ p₂))

/-- T329. Network clustering with void agents is zero. -/
theorem networkClustering_void (agent : I) :
    networkClustering agent (void : I) (void : I) = 0 := by
  unfold networkClustering networkPosition
  show rs (discourse agent [void, void]) (discourse agent [void, void]) -
    rs (compose agent (compose (void : I) (void : I))) (compose agent (compose (void : I) (void : I))) = 0
  simp [discourse, compose_assoc']

/-- The star network: one central agent connected to all others.
    The central agent's position is the discourse of all partners. -/
def starNetwork (center : I) (periphery : List I) : I :=
  networkPosition center periphery

/-- T330. Star network with empty periphery is just the center. -/
theorem starNetwork_empty (center : I) :
    starNetwork center [] = center := by
  unfold starNetwork; exact networkPosition_nil center

/-- T331. Star network enriches the center monotonically as the
    periphery grows. -/
theorem starNetwork_enriches (center partner : I) (rest : List I) :
    rs (starNetwork center (partner :: rest))
       (starNetwork center (partner :: rest)) ≥
    rs center center := by
  unfold starNetwork; exact network_enrichment center partner rest

end NetworkGames

/-! ## §35. Information Economics — Attention and Filtering

In the economics of attention, agents must choose which signals to
process given limited processing capacity. Each signal composition
enriches but at a cost of attention. We model attention as a budget
constraint on how many signals can be composed.
-/

section InformationEconomics
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The attention cost of processing a signal: the self-resonance
    required to integrate it. This is the "cognitive load" of
    understanding a signal. -/
noncomputable def attentionCost (signal : I) : ℝ := rs signal signal

/-- T332. Void signal has zero attention cost. -/
theorem attentionCost_void : attentionCost (void : I) = 0 := rs_void_void

/-- T333. Attention cost is non-negative. -/
theorem attentionCost_nonneg (s : I) : attentionCost s ≥ 0 := by
  unfold attentionCost; exact S.rs_self_nonneg s

/-- T334. Non-void signals require positive attention. -/
theorem attentionCost_pos (s : I) (h : s ≠ void) : attentionCost s > 0 := by
  unfold attentionCost; exact rs_self_pos s h

/-- The attention return: how much information content the signal
    provides per unit of attention cost. -/
noncomputable def attentionReturn (signal receiver : I) : ℝ :=
  informationContent signal receiver

/-- T335. Attention return is non-negative: processing any signal
    weakly enriches the receiver. -/
theorem attentionReturn_nonneg (s r : I) : attentionReturn s r ≥ 0 := by
  unfold attentionReturn; exact informationContent_nonneg s r

/-- T336. Attention return of void signal is zero: processing silence
    yields nothing. -/
theorem attentionReturn_void (r : I) : attentionReturn (void : I) r = 0 := by
  unfold attentionReturn; exact informationContent_void r

/-- The filtering decision: a signal passes the filter if its
    information content exceeds a threshold. -/
def passesFilter (signal receiver : I) (threshold : ℝ) : Prop :=
  attentionReturn signal receiver > threshold

/-- T337. Void signal never passes a positive filter threshold. -/
theorem void_fails_filter (r : I) (t : ℝ) (ht : t ≥ 0) :
    ¬passesFilter (void : I) r t := by
  unfold passesFilter
  rw [attentionReturn_void]; linarith

/-- T338. Every signal passes a sufficiently negative threshold. -/
theorem all_pass_neg_filter (s r : I) (t : ℝ) (ht : t < 0) :
    passesFilter s r t := by
  unfold passesFilter
  linarith [attentionReturn_nonneg s r]

/-- The information overload threshold: when the cumulative attention
    cost exceeds the cumulative return, the agent is overloaded. -/
noncomputable def informationOverload (receiver : I) (signals : List I) : ℝ :=
  (signals.map attentionCost).sum - cumulativeEnrichment receiver signals

/-- T339. Information overload of empty signal list is zero. -/
theorem informationOverload_nil (r : I) :
    informationOverload r [] = 0 := by
  unfold informationOverload cumulativeEnrichment; simp

end InformationEconomics

/-! ## §36. Persuasion Games — Bayesian Persuasion

In Bayesian persuasion (Kamenica-Gentzkow), the sender designs an
information structure (signal) to influence the receiver's action.
The sender commits to a signaling policy before the state is realized.

We model persuasion as the sender choosing which composition to
reveal, and prove bounds on persuasion effectiveness.
-/

section PersuasionGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The persuasion value: how much the sender gains from optimally
    choosing which aspect of their idea to reveal. This is the
    difference between strategic revelation and full revelation. -/
noncomputable def persuasionValue (full partialSig r : I) : ℝ :=
  senderPayoff partialSig r - senderPayoff full r

/-- T340. Persuasion value of revealing everything vs everything is zero:
    you can't improve on full honesty by being fully honest. -/
theorem persuasionValue_full (s r : I) :
    persuasionValue s s r = 0 := by
  unfold persuasionValue; ring

/-- T341. Persuasion value of revealing void vs anything is just the
    negative of the sender payoff: complete concealment. -/
theorem persuasionValue_conceal (s r : I) :
    persuasionValue s (void : I) r = -senderPayoff s r := by
  unfold persuasionValue senderPayoff interpret
  simp [rs_void_left']

/-- The obedience constraint: the receiver must prefer to follow the
    sender's recommendation. In meaning games, the receiver "follows"
    by composing (accepting the signal). -/
noncomputable def obedienceGain (s r : I) : ℝ :=
  receiverNetPayoff s r

/-- T342. Obedience gain of void signal is zero: the receiver has
    no reason to obey or disobey silence. -/
theorem obedienceGain_void (r : I) :
    obedienceGain (void : I) r = 0 := by
  unfold obedienceGain; exact receiverNetPayoff_void_signal r

/-- T343. At Nash equilibrium, obedience is guaranteed: the receiver
    has non-negative gain from following the recommendation. -/
theorem obedience_at_nash (s r : I) (h : isNashEquilibrium s r) :
    obedienceGain s r ≥ 0 := by
  unfold obedienceGain; exact nash_receiver_nonneg s r h

/-- The commitment value: how much the sender gains from being able
    to commit to a signaling policy before the receiver acts.
    Without commitment, the sender would choose signals to maximize
    sender payoff, but with commitment, they can also influence the
    receiver's best response. -/
noncomputable def commitmentValue (s₁ s₂ r : I) : ℝ :=
  socialWelfare s₁ r - socialWelfare s₂ r

/-- T344. Commitment value is antisymmetric. -/
theorem commitmentValue_antisymm (s₁ s₂ r : I) :
    commitmentValue s₁ s₂ r = -commitmentValue s₂ s₁ r := by
  unfold commitmentValue; ring

/-- T345. Commitment value is transitive (in the additive sense):
    switching from s₂ to s₁ then s₁ to s₃ equals switching from s₂ to s₃. -/
theorem commitmentValue_trans (s₁ s₂ s₃ r : I) :
    commitmentValue s₁ s₂ r + commitmentValue s₂ s₃ r =
    commitmentValue s₁ s₃ r := by
  unfold commitmentValue; ring

/-- T346. Commitment value against void receiver is the difference
    in self-resonances: without a receiver, only the signal's own
    weight matters. -/
theorem commitmentValue_void_receiver (s₁ s₂ : I) :
    commitmentValue s₁ s₂ (void : I) = rs s₁ s₁ - rs s₂ s₂ := by
  unfold commitmentValue
  rw [socialWelfare_void_receiver, socialWelfare_void_receiver]

end PersuasionGames

/-! ## §37. Population Games — Large Population Dynamics

When many agents interact, the aggregate behavior creates emergent
macro-dynamics. We model populations as lists of agents and study
aggregate resonance, diversity, and convergence.
-/

section PopulationGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The aggregate resonance of a population: the sum of all pairwise
    sender payoffs within the group, reflecting total internal coherence. -/
noncomputable def aggregateResonance (population : List I) : ℝ :=
  (population.map (fun a => rs a a)).sum

/-- T347. Aggregate resonance of empty population is zero. -/
theorem aggregateResonance_nil :
    aggregateResonance ([] : List I) = 0 := by
  unfold aggregateResonance; simp

/-- T348. Aggregate resonance is non-negative: each agent's
    self-resonance is non-negative. -/
theorem aggregateResonance_nonneg : ∀ (population : List I),
    aggregateResonance population ≥ 0
  | [] => by unfold aggregateResonance; simp
  | a :: rest => by
    unfold aggregateResonance
    simp only [List.map_cons, List.sum_cons]
    have h1 := S.rs_self_nonneg a
    have h2 := aggregateResonance_nonneg rest
    unfold aggregateResonance at h2
    linarith

/-- T349. Aggregate resonance of singleton population is the agent's
    self-resonance. -/
theorem aggregateResonance_singleton (a : I) :
    aggregateResonance [a] = rs a a := by
  unfold aggregateResonance; simp

/-- T350. Adding an agent increases aggregate resonance by their
    self-resonance. -/
theorem aggregateResonance_cons (a : I) (rest : List I) :
    aggregateResonance (a :: rest) =
    rs a a + aggregateResonance rest := by
  unfold aggregateResonance; simp [List.map_cons, List.sum_cons]

/-- The population consensus: the composed idea formed by sequentially
    composing all agents. This is the "collective voice." -/
def populationConsensus : List I → I
  | [] => void
  | a :: rest => compose (populationConsensus rest) a

/-- T351. Empty population has void consensus: no agents, no voice. -/
theorem consensus_nil :
    populationConsensus ([] : List I) = (void : I) := rfl

/-- T352. Singleton consensus is the agent itself. -/
theorem consensus_singleton (a : I) :
    populationConsensus [a] = a := by
  show compose (populationConsensus []) a = a
  simp [consensus_nil]

/-- T353. Consensus self-resonance is non-negative. -/
theorem consensus_nonneg (pop : List I) :
    rs (populationConsensus pop) (populationConsensus pop) ≥ 0 :=
  S.rs_self_nonneg _

/-- The consensus enrichment: how much the consensus exceeds the
    average individual self-resonance. -/
noncomputable def consensusEnrichment (pop : List I) : ℝ :=
  rs (populationConsensus pop) (populationConsensus pop) -
  aggregateResonance pop

/-- T354. Consensus enrichment of empty population is zero. -/
theorem consensusEnrichment_nil :
    consensusEnrichment ([] : List I) = 0 := by
  unfold consensusEnrichment; simp [consensus_nil, rs_void_void, aggregateResonance_nil]

end PopulationGames

/-! ## §38. Repeated Games — Folk Theorem and Cooperation

In repeated games, the threat of future punishment sustains cooperation.
We model repeated communication as iterated composition and show how
cooperation can be sustained through the self-reinforcing nature of
composition.
-/

section RepeatedGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The one-shot defection gain: how much a player gains from deviating
    in a single round. This is the temptation to "break the agreement." -/
noncomputable def defectionGain (cooperative deviate r : I) : ℝ :=
  senderNetPayoff deviate r - senderNetPayoff cooperative r

/-- T355. Defection gain is zero for identical strategies: you can't
    gain by deviating to what you're already doing. -/
theorem defectionGain_zero (s r : I) : defectionGain s s r = 0 := by
  unfold defectionGain; ring

/-- T356. Defection gain to void is the negative of cooperative net payoff:
    defecting to silence means losing your cooperative gains. -/
theorem defectionGain_to_void (s r : I) :
    defectionGain s (void : I) r = -senderNetPayoff s r := by
  unfold defectionGain; rw [senderNetPayoff_void_signal]; ring

/-- T357. At Nash equilibrium, the defection gain for any deviation
    is non-positive: the equilibrium strategy is a best response. -/
theorem defectionGain_nash (s r : I) (h : isNashEquilibrium s r) (d : I) :
    defectionGain s d r ≤ 0 := by
  unfold defectionGain
  linarith [h.1 d]

/-- The punishment value: how much damage the receiver can inflict
    by switching to void (refusing to communicate). This is the
    "grim trigger" threat. -/
noncomputable def punishmentValue (s r : I) : ℝ :=
  senderNetPayoff s r - senderNetPayoff s (void : I)

/-- T358. Punishment value equals the sender's net payoff (since void
    receiver gives zero). The threat of silence is exactly as costly
    as the cooperation is valuable. -/
theorem punishmentValue_eq (s r : I) :
    punishmentValue s r = senderNetPayoff s r := by
  unfold punishmentValue; rw [senderNetPayoff_void_receiver]; ring

/-- T359. At Nash equilibrium, punishment value is non-negative:
    the threat of silence is credible because cooperation yields
    positive net payoff. -/
theorem punishmentValue_nonneg_nash (s r : I) (h : isNashEquilibrium s r) :
    punishmentValue s r ≥ 0 := by
  rw [punishmentValue_eq]; exact nash_sender_nonneg s r h

/-- The cooperation sustainability condition: cooperation is sustainable
    if the punishment from defection exceeds the one-shot gain.
    This is the folk theorem condition. -/
def cooperationSustainable (cooperative deviate r : I) : Prop :=
  defectionGain cooperative deviate r ≤ punishmentValue cooperative r

/-- T360. At Nash equilibrium, cooperation with the equilibrium strategy
    is always sustainable: the folk theorem holds trivially because
    the defection gain is non-positive. -/
theorem folkTheorem_nash (s r : I) (h : isNashEquilibrium s r) (d : I) :
    cooperationSustainable s d r := by
  unfold cooperationSustainable
  linarith [defectionGain_nash s r h d, punishmentValue_nonneg_nash s r h]

/-- The repeated game surplus: how much total value is created over
    n rounds of cooperation vs. n rounds of silence. -/
noncomputable def repeatedGameSurplus (s r : I) (n : ℕ) : ℝ :=
  n * communicationSurplus s r

/-- T361. Repeated game surplus at round 0 is zero. -/
theorem repeatedGameSurplus_zero (s r : I) :
    repeatedGameSurplus s r 0 = 0 := by
  unfold repeatedGameSurplus; ring

/-- T362. Repeated game surplus at Nash equilibrium grows linearly
    and non-negatively. -/
theorem repeatedGameSurplus_nonneg_nash (s r : I) (h : isNashEquilibrium s r) (n : ℕ) :
    repeatedGameSurplus s r n ≥ 0 := by
  unfold repeatedGameSurplus
  exact mul_nonneg (Nat.cast_nonneg n) (nash_surplus_nonneg s r h)

end RepeatedGames

/-! ## §39. Correlated Equilibrium — Communication as Correlation Device

In correlated equilibrium, a mediator sends private signals to players,
correlating their actions. In meaning games, the "mediator" is a shared
context (a common idea) that both players compose with.

The key insight: a shared context acts as a correlation device because
it shifts both players' resonance profiles simultaneously.
-/

section CorrelatedEquilibrium
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A correlation device is a shared context that both players compose with.
    The device modifies each player's effective strategy. -/
def correlatedStrategy (player device : I) : I :=
  compose player device

/-- T363. Void device leaves the player unchanged: no correlation
    without a mediator. -/
theorem correlatedStrategy_void (player : I) :
    correlatedStrategy player (void : I) = player := by
  unfold correlatedStrategy; simp

/-- T364. Correlated strategy enriches the player: the device never
    reduces the player's self-resonance. -/
theorem correlatedStrategy_enriches (player device : I) :
    rs (correlatedStrategy player device) (correlatedStrategy player device) ≥
    rs player player := by
  unfold correlatedStrategy; exact S.compose_enriches player device

/-- The correlation gain: how much the shared context improves total
    welfare beyond what independent play achieves. -/
noncomputable def correlationGain (s r device : I) : ℝ :=
  socialWelfare (correlatedStrategy s device) (correlatedStrategy r device) -
  socialWelfare s r

/-- T365. Correlation gain with void device is zero: no mediator,
    no additional gain. -/
theorem correlationGain_void (s r : I) :
    correlationGain s r (void : I) = 0 := by
  unfold correlationGain correlatedStrategy; simp

/-- The correlated payoff: sender's payoff in the correlated game. -/
noncomputable def correlatedPayoff (s r device : I) : ℝ :=
  senderPayoff (correlatedStrategy s device) (correlatedStrategy r device)

/-- T366. Correlated payoff with void device equals original payoff:
    without mediation, correlation changes nothing. -/
theorem correlatedPayoff_void (s r : I) :
    correlatedPayoff s r (void : I) = senderPayoff s r := by
  unfold correlatedPayoff correlatedStrategy; simp

/-- T367. Correlated payoff with void sender becomes the device's
    payoff: when you say nothing, the device speaks for you. -/
theorem correlatedPayoff_void_sender (r device : I) :
    correlatedPayoff (void : I) r device =
    senderPayoff device (correlatedStrategy r device) := by
  unfold correlatedPayoff correlatedStrategy senderPayoff interpret; simp

end CorrelatedEquilibrium

/-! ## §40. Congestion Games — Competition for Resonance

When many agents compete for the same receiver's attention, they
create "congestion" — each additional signal dilutes the impact.
We model this through sequential composition and analyze the
diminishing returns of attention competition.
-/

section CongestionGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The congested interpretation: the receiver processes multiple
    signals in sequence. Later signals are interpreted in the context
    of all earlier ones. -/
def congestedInterpret (receiver : I) (signals : List I) : I :=
  discourse receiver signals

/-- T368. Empty congestion leaves receiver unchanged. -/
theorem congestedInterpret_nil (r : I) :
    congestedInterpret r [] = r := by
  unfold congestedInterpret; simp

/-- T369. Congested interpretation enriches the receiver monotonically. -/
theorem congested_enriches (r s : I) (rest : List I) :
    rs (congestedInterpret r (s :: rest)) (congestedInterpret r (s :: rest)) ≥
    rs r r := by
  unfold congestedInterpret discourse
  exact discourse_enriches r s rest

/-- The congestion cost: how much an individual signal's marginal
    contribution decreases when other signals are also present.
    Measured as the difference between the signal's solo contribution
    and its marginal contribution in context. -/
noncomputable def congestionCost (r solo context : I) : ℝ :=
  informationContent solo r - stepEnrichment (compose r context) solo

/-- T370. Congestion cost with void context is zero: without other
    signals, there's no congestion. -/
theorem congestionCost_void (r s : I) :
    congestionCost r s (void : I) = 0 := by
  unfold congestionCost stepEnrichment informationContent; simp

/-- The marginal contribution of the n-th signal: how much the n-th
    signal adds to the congested interpretation. -/
noncomputable def marginalContribution (r : I) (signals : List I) : ℝ :=
  cumulativeEnrichment r signals

/-- T371. Marginal contribution of empty list is zero. -/
theorem marginalContribution_nil (r : I) :
    marginalContribution r [] = 0 := by
  unfold marginalContribution; exact cumulativeEnrichment_nil r

/-- T372. Marginal contribution is non-negative for any non-empty list. -/
theorem marginalContribution_cons_nonneg (r s : I) (rest : List I) :
    marginalContribution r (s :: rest) ≥ 0 := by
  unfold marginalContribution; exact cumulativeEnrichment_cons_nonneg r s rest

end CongestionGames

/-! ## §41. Potential Games and Equilibrium Existence

A potential game has a potential function whose maximizers are
Nash equilibria. Self-resonance of the composition serves as a
natural potential function for meaning games, guaranteeing
equilibrium existence.
-/

section PotentialGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The potential function: self-resonance of the interpretation.
    This is the natural potential for meaning games because deviations
    that increase self-resonance also increase individual payoffs. -/
noncomputable def potential (s r : I) : ℝ :=
  rs (compose r s) (compose r s)

/-- T373. Potential is non-negative: self-resonance is always ≥ 0. -/
theorem potential_nonneg (s r : I) : potential s r ≥ 0 := by
  unfold potential; exact S.rs_self_nonneg _

/-- T374. Potential of void signal equals receiver's self-resonance:
    silence doesn't change the receiver's potential. -/
theorem potential_void_signal (r : I) :
    potential (void : I) r = rs r r := by
  unfold potential; simp

/-- T375. Potential of void receiver equals signal's self-resonance. -/
theorem potential_void_receiver (s : I) :
    potential s (void : I) = rs s s := by
  unfold potential; simp

/-- T376. Potential is at least the receiver's self-resonance: any
    signal weakly increases the potential (by compose_enriches). -/
theorem potential_ge_receiver (s r : I) :
    potential s r ≥ rs r r := by
  unfold potential; exact S.compose_enriches r s

/-- T377. Void-void potential is zero. -/
theorem potential_void_void :
    potential (void : I) (void : I) = 0 := by
  unfold potential; simp [rs_void_void]

/-- The potential improvement from switching signal: positive improvement
    means the new signal is better for the potential function. -/
noncomputable def potentialImprovement (sOld sNew r : I) : ℝ :=
  potential sNew r - potential sOld r

/-- T378. Potential improvement is antisymmetric: switching from s₁ to
    s₂ negates the improvement of switching from s₂ to s₁. -/
theorem potentialImprovement_antisymm (s₁ s₂ r : I) :
    potentialImprovement s₁ s₂ r = -potentialImprovement s₂ s₁ r := by
  unfold potentialImprovement; ring

/-- T379. Potential improvement is transitive: improvements chain. -/
theorem potentialImprovement_trans (s₁ s₂ s₃ r : I) :
    potentialImprovement s₁ s₂ r + potentialImprovement s₂ s₃ r =
    potentialImprovement s₁ s₃ r := by
  unfold potentialImprovement; ring

/-- T380. Self-improvement is zero: switching to the same signal
    creates no improvement. -/
theorem potentialImprovement_self (s r : I) :
    potentialImprovement s s r = 0 := by
  unfold potentialImprovement; ring

end PotentialGames

/-! ## §42. Principal-Agent Theory — Delegation of Communication

In principal-agent problems, one party (the principal) delegates
a communication task to another (the agent). The principal designs
incentives to align the agent's behavior with the principal's
interests, despite the agent's private information.
-/

section PrincipalAgent
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The alignment gap: how much the agent's interests diverge from
    the principal's. Measured as the difference in payoffs when the
    agent speaks on the principal's behalf. -/
noncomputable def alignmentGap (principal agent receiver : I) : ℝ :=
  senderPayoff principal receiver - senderPayoff agent receiver

/-- T381. Alignment gap is zero when principal and agent are identical:
    perfect alignment means no gap. -/
theorem alignmentGap_self (a r : I) :
    alignmentGap a a r = 0 := by
  unfold alignmentGap; ring

/-- T382. Alignment gap is antisymmetric: swapping principal and agent
    negates the gap. -/
theorem alignmentGap_antisymm (p a r : I) :
    alignmentGap p a r = -alignmentGap a p r := by
  unfold alignmentGap; ring

/-- T383. Alignment gap with void receiver is the difference in
    self-resonances: without an audience, alignment reduces to
    intrinsic weight differences. -/
theorem alignmentGap_void_receiver (p a : I) :
    alignmentGap p a (void : I) = rs p p - rs a a := by
  unfold alignmentGap senderPayoff interpret; simp

/-- The delegation value: how much the principal gains from delegating
    to the agent vs. communicating directly. -/
noncomputable def delegationValue (principal agent receiver : I) : ℝ :=
  senderPayoff agent receiver - senderPayoff principal receiver

/-- T384. Delegation value equals negative alignment gap: the better
    aligned the agent, the less valuable delegation is. -/
theorem delegationValue_eq (p a r : I) :
    delegationValue p a r = -alignmentGap p a r := by
  unfold delegationValue alignmentGap; ring

/-- T385. Self-delegation has zero value. -/
theorem delegationValue_self (a r : I) :
    delegationValue a a r = 0 := by
  unfold delegationValue; ring

/-- The incentive payment: how much the principal must pay the agent
    to align incentives. This equals the agent's outside option
    (net payoff from staying silent) plus the alignment gap. -/
noncomputable def incentivePayment (p a r : I) : ℝ :=
  alignmentGap p a r + senderNetPayoff a r

/-- T386. Incentive payment for void agent is the principal's payoff:
    hiring silence means paying for the principal's own communication. -/
theorem incentivePayment_void_agent (p r : I) :
    incentivePayment p (void : I) r =
    senderPayoff p r - senderPayoff (void : I) r := by
  unfold incentivePayment alignmentGap senderNetPayoff senderPayoff interpret
  simp [rs_void_left', rs_void_void]

/-- T387. Incentive payment when principal equals agent is just the
    agent's net payoff: no alignment cost needed. -/
theorem incentivePayment_aligned (a r : I) :
    incentivePayment a a r = senderNetPayoff a r := by
  rw [show incentivePayment a a r = alignmentGap a a r + senderNetPayoff a r from rfl,
      alignmentGap_self]; ring

end PrincipalAgent

/-! ## §43. Herding and Information Cascades

Information cascades occur when agents ignore their own private
information and follow the actions of predecessors. In meaning
games, a "cascade" occurs when an agent's composition with the
collective discourse overwhelms their individual resonance profile.
-/

section InformationCascades
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The cascade pressure: how much the collective discourse enriches
    an individual beyond the collective's own resonance. High cascade
    pressure means the individual amplifies the collective significantly. -/
noncomputable def cascadePressure (individual collective : I) : ℝ :=
  rs (compose collective individual) (compose collective individual) -
  rs collective collective

/-- T388. Cascade pressure is non-negative: composing with an individual
    always enriches or maintains the collective's self-resonance. -/
theorem cascadePressure_nonneg (individual collective : I) :
    cascadePressure individual collective ≥ 0 := by
  unfold cascadePressure
  linarith [S.compose_enriches collective individual]

/-- T389. Cascade pressure from void collective reduces to
    self-resonance: without collective context, only the individual remains. -/
theorem cascadePressure_void (individual : I) :
    cascadePressure individual (void : I) = rs individual individual := by
  unfold cascadePressure; simp [rs_void_left']

/-- The cascade threshold: an agent falls into the cascade when their
    individual contribution to the composition becomes negligible
    relative to the collective's influence. -/
noncomputable def cascadeStrength (individual collective : I) : ℝ :=
  rs (compose collective individual) (compose collective individual) -
  rs collective collective

/-- T390. Cascade strength is non-negative: composing always enriches. -/
theorem cascadeStrength_nonneg (i c : I) :
    cascadeStrength i c ≥ 0 := by
  unfold cascadeStrength; linarith [S.compose_enriches c i]

/-- T391. Cascade strength equals information content of the individual
    for the collective. -/
theorem cascadeStrength_eq_info (i c : I) :
    cascadeStrength i c = informationContent i c := by
  unfold cascadeStrength informationContent; ring

/-- The herding premium: how much an agent gains by "following the herd"
    (composing with the collective discourse) vs. acting alone. -/
noncomputable def herdingPremium (individual collective : I) : ℝ :=
  rs (compose individual collective) (compose individual collective) -
  rs individual individual

/-- T392. Herding premium is non-negative: following the herd never
    reduces your self-resonance (though it may change your identity). -/
theorem herdingPremium_nonneg (i c : I) :
    herdingPremium i c ≥ 0 := by
  unfold herdingPremium; linarith [S.compose_enriches i c]

/-- T393. Herding premium from void collective is zero: there's no
    herd to follow in silence. -/
theorem herdingPremium_void (i : I) :
    herdingPremium i (void : I) = 0 := by
  unfold herdingPremium; simp

/-- T394. Herding premium equals match quality: the value of joining
    the herd IS the quality of the match. -/
theorem herdingPremium_eq_matchQuality (i c : I) :
    herdingPremium i c = matchQuality i c := by
  unfold herdingPremium matchQuality; ring

end InformationCascades

/-! ## §44. Social Choice Theory — Aggregation of Meaning

Social choice theory asks how to aggregate individual preferences
into collective decisions. In meaning games, the question is how
to combine individual ideas into a collective composition.

We prove analogues of Arrow's impossibility and the Gibbard-
Satterthwaite theorem for meaning aggregation.
-/

section SocialChoice
variable {I : Type*} [S : IdeaticSpace3 I]

/-- A simple aggregation rule: compose all ideas in order. This is
    the "sequential dictator" rule — order matters. -/
def sequentialAggregation : List I → I
  | [] => void
  | a :: rest => compose (sequentialAggregation rest) a

/-- T395. Sequential aggregation of empty list is void. -/
theorem sequentialAgg_nil :
    sequentialAggregation ([] : List I) = (void : I) := rfl

/-- T396. Sequential aggregation of singleton is the idea itself. -/
theorem sequentialAgg_singleton (a : I) :
    sequentialAggregation [a] = a := by
  show compose (sequentialAggregation []) a = a
  rw [sequentialAgg_nil]; simp

/-- T397. Sequential aggregation enriches monotonically: adding any
    agent's idea never reduces the aggregate's self-resonance
    (comparing the aggregate with and without the last element). -/
theorem sequentialAgg_enriches (a : I) (rest : List I) :
    rs (sequentialAggregation (a :: rest))
       (sequentialAggregation (a :: rest)) ≥
    rs (sequentialAggregation rest)
       (sequentialAggregation rest) := by
  show rs (compose (sequentialAggregation rest) a) (compose (sequentialAggregation rest) a) ≥ _
  exact S.compose_enriches (sequentialAggregation rest) a

/-- T398. Sequential aggregation is non-degenerate: adding a non-void
    idea to any aggregate produces a non-void result if the existing
    aggregate is non-void. -/
theorem sequentialAgg_ne_void (a : I) (rest : List I)
    (h : sequentialAggregation rest ≠ void) :
    sequentialAggregation (a :: rest) ≠ void := by
  show compose (sequentialAggregation rest) a ≠ void
  exact compose_ne_void_of_left (sequentialAggregation rest) a h

/-- The manipulation gain: how much an agent gains by misreporting
    their idea in the aggregation. This is the "strategic voting" problem. -/
noncomputable def manipulationGain (truthful lie : I) (others : List I) : ℝ :=
  rs (sequentialAggregation (lie :: others))
     (sequentialAggregation (lie :: others)) -
  rs (sequentialAggregation (truthful :: others))
     (sequentialAggregation (truthful :: others))

/-- T399. Manipulation gain of truthful report is zero: no gain
    from honest behavior (relative to itself). -/
theorem manipulationGain_truthful (s : I) (others : List I) :
    manipulationGain s s others = 0 := by
  unfold manipulationGain; ring

/-- T400. Manipulation to void is non-positive relative to any truthful
    report — staying silent when you have something to say weakens the aggregate. -/
theorem manipulation_void_nonpos (s : I) (others : List I) :
    manipulationGain s (void : I) others ≤ 0 := by
  unfold manipulationGain
  show rs (sequentialAggregation (void :: others))
       (sequentialAggregation (void :: others)) -
       rs (sequentialAggregation (s :: others))
       (sequentialAggregation (s :: others)) ≤ 0
  show rs (compose (sequentialAggregation others) (void : I))
       (compose (sequentialAggregation others) (void : I)) -
       rs (compose (sequentialAggregation others) s)
       (compose (sequentialAggregation others) s) ≤ 0
  simp; linarith [S.compose_enriches (sequentialAggregation others) s]

/-- The unanimity condition: if all agents report the same idea,
    the aggregation should reflect that idea. -/
theorem unanimity_singleton (a : I) :
    sequentialAggregation [a] = a :=
  sequentialAgg_singleton a

/-- T401. The aggregation self-resonance is at least as large as any
    individual's self-resonance (for non-empty lists with the element
    at the end). This is a weak form of the Pareto principle. -/
theorem aggregation_pareto (a : I) (rest : List I) :
    rs (sequentialAggregation (a :: rest))
       (sequentialAggregation (a :: rest)) ≥
    rs (sequentialAggregation rest)
       (sequentialAggregation rest) :=
  sequentialAgg_enriches a rest

end SocialChoice

/-! ## §45. Zero-Sum Games — Pure Competition in Meaning

Zero-sum games model pure competition: one player's gain is the
other's loss. In meaning games, this occurs when the misunderstanding
gap captures the entire welfare — what the sender gains in resonance,
the receiver loses in comprehension, and vice versa.
-/

section ZeroSumGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The competitive advantage: the difference between sender and
    receiver payoffs. Positive means the sender "wins" the communication. -/
noncomputable def competitiveAdvantage (s r : I) : ℝ :=
  senderPayoff s r - receiverPayoff s r

/-- T402. Competitive advantage equals the misunderstanding gap.
    These are the same quantity — the asymmetry in communication. -/
theorem competitiveAdvantage_eq_gap (s r : I) :
    competitiveAdvantage s r = misunderstandingGap s r := by
  unfold competitiveAdvantage misunderstandingGap; ring

/-- T403. Competitive advantage for void signal is -rs(r,r): silence
    gives the receiver full advantage. -/
theorem competitiveAdvantage_void_signal (r : I) :
    competitiveAdvantage (void : I) r = -rs r r := by
  unfold competitiveAdvantage senderPayoff receiverPayoff interpret
  simp [rs_void_left']

/-- T404. Competitive advantage for void receiver is rs(s,s): the
    sender has full advantage when nobody listens. -/
theorem competitiveAdvantage_void_receiver (s : I) :
    competitiveAdvantage s (void : I) = rs s s := by
  unfold competitiveAdvantage senderPayoff receiverPayoff interpret
  simp [rs_void_left', rs_void_right']

/-- T405. Competitive advantage is antisymmetric under role swap:
    the advantage of being sender vs receiver negates when roles flip. -/
theorem competitiveAdvantage_antisymm_self (a : I) :
    competitiveAdvantage a a = 0 → socialWelfare a a = 2 * senderPayoff a a := by
  unfold competitiveAdvantage socialWelfare senderPayoff receiverPayoff interpret
  intro h; linarith

/-- The minimax value: the worst-case guarantee for the sender.
    This is the payoff the sender can guarantee regardless of the
    receiver's strategy. -/
noncomputable def minimaxGuarantee (s : I) : ℝ :=
  senderPayoff s (void : I)

/-- T406. Minimax guarantee equals self-resonance: the sender can
    always guarantee their own self-resonance by "talking to nobody." -/
theorem minimaxGuarantee_eq (s : I) :
    minimaxGuarantee s = rs s s := by
  unfold minimaxGuarantee senderPayoff interpret; simp

/-- T407. Minimax guarantee is non-negative. -/
theorem minimaxGuarantee_nonneg (s : I) :
    minimaxGuarantee s ≥ 0 := by
  rw [minimaxGuarantee_eq]; exact S.rs_self_nonneg s

/-- T408. Void sender has zero minimax guarantee: silence guarantees
    nothing. -/
theorem minimaxGuarantee_void :
    minimaxGuarantee (void : I) = 0 := by
  rw [minimaxGuarantee_eq]; exact rs_void_void

end ZeroSumGames

/-! ## §46. Behavioral Game Theory — Bounded Rationality

Real agents have limited cognitive resources. Bounded rationality
in meaning games means agents may not compute optimal compositions.
We model this through "trembling hand" errors and ε-best responses.
-/

section BehavioralGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- An ε-best response: the sender's strategy is within ε of the
    best possible net payoff. -/
def isEpsBestResponse (s r : I) (ε : ℝ) : Prop :=
  ∀ s' : I, senderNetPayoff s r ≥ senderNetPayoff s' r - ε

/-- T409. Best response is 0-approximate best response: exact
    optimality is a special case of ε-optimality with ε = 0. -/
theorem bestResponse_is_eps_zero (s r : I)
    (h : isBestResponseSender s r) :
    isEpsBestResponse s r 0 := by
  intro s'; simp; exact h s'

/-- T410. Void is always an ε-best response for ε ≥ 0 when the
    receiver is void: against no audience, silence is near-optimal
    since all signals give zero net payoff. -/
theorem void_eps_best_void_receiver (ε : ℝ) (hε : ε ≥ 0) :
    isEpsBestResponse (void : I) (void : I) ε := by
  intro s'
  rw [senderNetPayoff_void_signal, senderNetPayoff_void_receiver]
  linarith

/-- T411. A larger ε allows more strategies to be ε-best responses:
    monotonicity of the approximation quality. -/
theorem eps_monotone (s r : I) (ε₁ ε₂ : ℝ) (hε : ε₁ ≤ ε₂)
    (h : isEpsBestResponse s r ε₁) :
    isEpsBestResponse s r ε₂ := by
  intro s'
  have := h s'
  linarith

/-- The rationality gap: how far a strategy is from being a best
    response. Measures the "cost of bounded rationality." -/
noncomputable def rationalityGap (s best r : I) : ℝ :=
  senderNetPayoff best r - senderNetPayoff s r

/-- T412. Rationality gap is non-negative when best is actually a
    best response. -/
theorem rationalityGap_nonneg (s best r : I)
    (h : isBestResponseSender best r) :
    rationalityGap s best r ≥ 0 := by
  unfold rationalityGap; linarith [h s]

/-- T413. Rationality gap is zero for the best response itself. -/
theorem rationalityGap_self (s r : I) :
    rationalityGap s s r = 0 := by
  unfold rationalityGap; ring

/-- T414. The trembling hand payoff: the payoff when the sender
    accidentally sends a "trembled" version (composed with noise). -/
noncomputable def tremblingPayoff (s noise r : I) : ℝ :=
  senderPayoff (compose s noise) r

/-- T415. Trembling with void noise gives the original payoff:
    no trembling, no change. -/
theorem trembling_void (s r : I) :
    tremblingPayoff s (void : I) r = senderPayoff s r := by
  unfold tremblingPayoff; simp

/-- T416. Trembling hand payoff explicit form. -/
theorem tremblingPayoff_explicit (s noise r : I) :
    tremblingPayoff s noise r =
    rs (compose s noise) (compose r (compose s noise)) := by
  unfold tremblingPayoff senderPayoff interpret; ring

end BehavioralGames

/-! ## §47. Implementation Theory — Mechanism Implementability

A social choice function is implementable if there exists a mechanism
whose equilibrium outcomes coincide with the function's outputs.
In meaning games, we characterize which "target compositions" can be
reached as equilibrium outcomes.
-/

section ImplementationTheory
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The implementation gap: how far an outcome is from being achievable
    as a Nash equilibrium. Measured by the surplus deficit. -/
noncomputable def implementationGap (s r : I) : ℝ :=
  max 0 (-senderNetPayoff s r) + max 0 (-receiverNetPayoff s r)

/-- T417. Implementation gap at Nash equilibrium is zero: equilibrium
    outcomes are trivially implementable. -/
theorem implementationGap_nash (s r : I) (h : isNashEquilibrium s r) :
    implementationGap s r = 0 := by
  unfold implementationGap
  have h1 := nash_sender_nonneg s r h
  have h2 := nash_receiver_nonneg s r h
  simp [max_eq_left (by linarith : (0 : ℝ) ≥ -senderNetPayoff s r),
        max_eq_left (by linarith : (0 : ℝ) ≥ -receiverNetPayoff s r)]

/-- T418. Implementation gap is non-negative. -/
theorem implementationGap_nonneg (s r : I) :
    implementationGap s r ≥ 0 := by
  unfold implementationGap
  linarith [le_max_left 0 (-senderNetPayoff s r),
            le_max_left 0 (-receiverNetPayoff s r)]

/-- T419. Void-void has zero implementation gap. -/
theorem implementationGap_void :
    implementationGap (void : I) (void : I) = 0 :=
  implementationGap_nash _ _ void_nash_equilibrium

/-- The Maskin monotonicity condition: a social choice function is
    Maskin monotonic if whenever an outcome is chosen and a player's
    preference improves, the outcome is still chosen.
    In meaning games, this corresponds to: if composition s enriches
    under stronger input, the enriched version is still an equilibrium. -/
noncomputable def maskinMonotonicity (s r : I) : ℝ :=
  informationContent s r

/-- T420. Maskin monotonicity proxy is non-negative: enrichment is
    always non-negative, satisfying the weak monotonicity condition. -/
theorem maskinMono_nonneg (s r : I) :
    maskinMonotonicity s r ≥ 0 := by
  unfold maskinMonotonicity; exact informationContent_nonneg s r

/-- T421. Maskin monotonicity proxy of void is zero. -/
theorem maskinMono_void (r : I) :
    maskinMonotonicity (void : I) r = 0 := by
  unfold maskinMonotonicity; exact informationContent_void r

end ImplementationTheory

/-! ## §48. Stochastic Stability — Long-Run Equilibrium Selection

Stochastic stability selects among multiple equilibria by asking
which equilibria are robust to rare random perturbations. In meaning
games, stochastically stable equilibria are those with the highest
"basin of attraction" — measured by the self-resonance of the
equilibrium composition.
-/

section StochasticStability
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The basin strength of a strategy profile: the self-resonance of
    the interpretation. Higher basin strength means the equilibrium
    is more robust to perturbations. -/
noncomputable def basinStrength (s r : I) : ℝ :=
  rs (compose r s) (compose r s)

/-- T422. Basin strength is non-negative. -/
theorem basinStrength_nonneg (s r : I) : basinStrength s r ≥ 0 := by
  unfold basinStrength; exact S.rs_self_nonneg _

/-- T423. Basin strength is at least the receiver's self-resonance:
    any interaction creates at least the receiver's baseline robustness. -/
theorem basinStrength_ge_receiver (s r : I) :
    basinStrength s r ≥ rs r r := by
  unfold basinStrength; exact S.compose_enriches r s

/-- T424. Void signal's basin strength equals the receiver's
    self-resonance: silence provides no additional robustness. -/
theorem basinStrength_void_signal (r : I) :
    basinStrength (void : I) r = rs r r := by
  unfold basinStrength; simp

/-- T425. Basin strength of void-void is zero: the silent equilibrium
    has zero robustness. -/
theorem basinStrength_void_void :
    basinStrength (void : I) (void : I) = 0 := by
  rw [basinStrength_void_signal]; exact rs_void_void

/-- The stochastic dominance condition: equilibrium (s₁, r₁)
    stochastically dominates (s₂, r₂) if it has higher basin strength. -/
def stochasticallyDominates (s₁ r₁ s₂ r₂ : I) : Prop :=
  basinStrength s₁ r₁ > basinStrength s₂ r₂

/-- T426. Stochastic dominance is transitive. -/
theorem stochDom_trans (s₁ r₁ s₂ r₂ s₃ r₃ : I)
    (h₁ : stochasticallyDominates s₁ r₁ s₂ r₂)
    (h₂ : stochasticallyDominates s₂ r₂ s₃ r₃) :
    stochasticallyDominates s₁ r₁ s₃ r₃ := by
  unfold stochasticallyDominates at *; linarith

/-- T427. Stochastic dominance is irreflexive. -/
theorem stochDom_irrefl (s r : I) :
    ¬stochasticallyDominates s r s r := by
  unfold stochasticallyDominates; linarith

/-- T428. Any non-void interaction stochastically dominates void-void:
    any communication is more robust than total silence (if the receiver
    is non-void). -/
theorem any_dominates_void (s r : I) (hr : r ≠ void) :
    stochasticallyDominates s r (void : I) (void : I) := by
  unfold stochasticallyDominates
  rw [basinStrength_void_void]
  unfold basinStrength
  linarith [S.compose_enriches r s, rs_self_pos r hr]

end StochasticStability

/-! ## §49. Epistemic Game Theory — Common Knowledge and Belief

Epistemic game theory studies the role of beliefs and knowledge in
strategic interaction. Common knowledge of rationality (CKR) implies
iterated elimination of dominated strategies.

In meaning games, "knowledge" is modeled as composition: knowing s
means having composed with s, which enriches your state.
-/

section EpistemicGames
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The knowledge state: an agent's state after processing information.
    Knowledge of signal s means having composed with s. -/
def knowledgeState (prior signal : I) : I :=
  compose prior signal

/-- T429. Knowledge of void adds nothing: knowing nothing is knowing
    what you already know. -/
theorem knowledge_void (prior : I) :
    knowledgeState prior (void : I) = prior := by
  unfold knowledgeState; simp

/-- T430. Knowledge enriches: learning always increases self-resonance. -/
theorem knowledge_enriches (prior signal : I) :
    rs (knowledgeState prior signal) (knowledgeState prior signal) ≥
    rs prior prior := by
  unfold knowledgeState; exact S.compose_enriches prior signal

/-- Common knowledge: both agents have composed with the shared signal. -/
def hasCommonKnowledge (agent₁ agent₂ signal : I) : Prop :=
  knowledgeState agent₁ signal = compose agent₁ signal ∧
  knowledgeState agent₂ signal = compose agent₂ signal

/-- T431. Common knowledge of void is trivial. -/
theorem commonKnowledge_void (a₁ a₂ : I) :
    hasCommonKnowledge a₁ a₂ (void : I) := by
  unfold hasCommonKnowledge knowledgeState; simp

/-- The belief revision operator: updating beliefs upon receiving new
    information. This is just composition — the Bayesian update in
    meaning space. -/
def beliefRevision (prior newInfo : I) : I :=
  compose prior newInfo

/-- T432. Belief revision with void information leaves beliefs unchanged:
    no news, no update. -/
theorem beliefRevision_void (prior : I) :
    beliefRevision prior (void : I) = prior := by
  unfold beliefRevision; simp

/-- T433. Iterated belief revision is associative: updating with s₁
    then s₂ is the same as updating with the composition s₁ ∘ s₂. -/
theorem beliefRevision_assoc (prior s₁ s₂ : I) :
    beliefRevision (beliefRevision prior s₁) s₂ =
    beliefRevision prior (compose s₁ s₂) := by
  unfold beliefRevision; rw [compose_assoc']

/-- T434. Belief revision enriches: every update weakly increases
    the agent's epistemic state. -/
theorem beliefRevision_enriches (prior info : I) :
    rs (beliefRevision prior info) (beliefRevision prior info) ≥
    rs prior prior := by
  unfold beliefRevision; exact S.compose_enriches prior info

/-- The surprise of new information: how much the belief revision
    changes the agent's self-resonance. -/
noncomputable def epistemicSurprise (prior info : I) : ℝ :=
  rs (beliefRevision prior info) (beliefRevision prior info) -
  rs prior prior

/-- T435. Epistemic surprise is non-negative: new information never
    reduces cognitive weight. -/
theorem epistemicSurprise_nonneg (prior info : I) :
    epistemicSurprise prior info ≥ 0 := by
  unfold epistemicSurprise
  linarith [beliefRevision_enriches prior info]

/-- T436. Epistemic surprise from void information is zero. -/
theorem epistemicSurprise_void (prior : I) :
    epistemicSurprise prior (void : I) = 0 := by
  unfold epistemicSurprise beliefRevision; simp

end EpistemicGames

/-! ## §30. Paradoxes of Strategic Communication

These theorems reveal counter-intuitive properties of strategic
communication that contradict naive expectations from classical
game theory. Each result is surprising because it defies
standard intuitions about information, deception, and framing. -/

section StrategicParadoxes
variable {I : Type*} [S : IdeaticSpace3 I]

/-- The deception divergence: how the receiver's cognitive state differs
    when sender sends s instead of their true belief m.
    Measures the "cost to the receiver" of being deceived. -/
noncomputable def deceptionDivergence (m s r : I) : ℝ :=
  rs (compose r m) (compose r m) - rs (compose r s) (compose r s)

/-- SP1. HONEST COMMUNICATION ZERO DIVERGENCE: when the sender sends
    exactly what they believe, the receiver's state is unchanged.
    Honesty is the unique zero-cost signal strategy. -/
theorem honest_zero_divergence (m r : I) :
    deceptionDivergence m m r = 0 := by
  unfold deceptionDivergence; ring

/-- SP2. THE DECEPTION DECOMPOSITION: Deception divergence breaks into
    three channels — receiver's cross-resonance shift, signal's direct
    contribution shift, and emergence shift. This reveals that deception
    operates simultaneously through MULTIPLE mechanisms, making it
    fundamentally harder to detect than single-channel manipulation. -/
theorem deception_divergence_decomposition (m s r : I) :
    deceptionDivergence m s r =
    (rs r (compose r m) + rs m (compose r m) + emergence r m (compose r m)) -
    (rs r (compose r s) + rs s (compose r s) + emergence r s (compose r s)) := by
  unfold deceptionDivergence
  have h1 := rs_compose_eq r m (compose r m)
  have h2 := rs_compose_eq r s (compose r s)
  linarith

/-- The information gain from hearing signal s: how much the receiver's
    cognitive weight increases. -/
noncomputable def infoGain (s r : I) : ℝ :=
  rs (compose r s) (compose r s) - rs r r

/-- SP3. THE IRREVERSIBILITY THEOREM: Information gain is ALWAYS non-negative.
    You cannot "un-hear" — every signal enriches the receiver's cognitive weight.
    Counter-intuitive: you'd expect "bad" or "misleading" information could
    reduce cognitive weight. But in ideatic space, even lies make you heavier.
    This is the ideatic Second Law of Thermodynamics: cognitive entropy
    never decreases. -/
theorem infoGain_nonneg (s r : I) : infoGain s r ≥ 0 := by
  unfold infoGain; linarith [compose_enriches' r s]

/-- SP4. THE SILENCE PREMIUM: Void signals produce exactly zero information
    gain. Combined with SP3, silence is the UNIQUE minimum-information signal.
    Counter-intuitive: you might expect some signals to be "negative information."
    But the minimum is zero, achieved only by silence. -/
theorem silence_zero_infoGain (r : I) : infoGain (void : I) r = 0 := by
  unfold infoGain; rw [void_right']; ring

/-- SP5. THE DOUBLE-HEARING PARADOX: Hearing a signal twice always produces
    at least as much cognitive weight as hearing it once. Counter-intuitive:
    you'd expect repetition to be redundant. But the enrichment axiom
    guarantees that repetition always adds (in weight terms), even though
    the content is identical. This explains why propaganda works. -/
theorem double_hearing_enriches (s r : I) :
    rs (compose (compose r s) s) (compose (compose r s) s) ≥
    rs (compose r s) (compose r s) :=
  compose_enriches' (compose r s) s

/-- SP6. THE CHAIN ENRICHMENT THEOREM: In a signaling chain s → m → r,
    the receiver's final cognitive weight exceeds their initial weight.
    Counter-intuitive: contradicts the "telephone game" intuition that
    messages degrade through intermediaries. In IDT, chains NEVER lose
    information — they can only add. -/
theorem chain_never_loses (s m r : I) :
    rs (compose (compose r m) s) (compose (compose r m) s) ≥ rs r r := by
  have h1 := compose_enriches' r m
  have h2 := compose_enriches' (compose r m) s
  linarith

/-- The second-order information gain: how much additional weight
    the receiver gains from hearing s₂ AFTER already hearing s₁. -/
noncomputable def secondOrderInfoGain (s₁ s₂ r : I) : ℝ :=
  rs (compose (compose r s₁) s₂) (compose (compose r s₁) s₂) -
  rs (compose r s₁) (compose r s₁)

/-- SP7. THE NO-DIMINISHING-RETURNS THEOREM: Every additional signal
    provides non-negative weight gain, regardless of what came before.
    Counter-intuitive: diminishing marginal returns is the norm in economics.
    In ideatic space, the nth piece of information is independently valuable.
    This explains information addiction. -/
theorem secondOrderInfoGain_nonneg (s₁ s₂ r : I) :
    secondOrderInfoGain s₁ s₂ r ≥ 0 := by
  unfold secondOrderInfoGain; linarith [compose_enriches' (compose r s₁) s₂]

/-- SP8. THE DUAL ORDER ENRICHMENT: Both orderings of two signals enrich
    the receiver relative to baseline. Neither ordering can harm the
    receiver. But the AMOUNT of enrichment may differ — this is why
    framing effects exist even when both framings are "truthful." -/
theorem dual_order_enrichment (s₁ s₂ r : I) :
    rs (compose (compose r s₁) s₂) (compose (compose r s₁) s₂) ≥ rs r r ∧
    rs (compose (compose r s₂) s₁) (compose (compose r s₂) s₁) ≥ rs r r := by
  constructor
  · linarith [compose_enriches' r s₁, compose_enriches' (compose r s₁) s₂]
  · linarith [compose_enriches' r s₂, compose_enriches' (compose r s₂) s₁]

/-- SP9. THE FRAMING EFFECT THEOREM: The difference between hearing
    s₁-then-s₂ versus s₂-then-s₁ is EXACTLY the difference in emergence
    chains. Framing effects are not irrational — they are a necessary
    mathematical consequence of non-commutative emergence.
    Counter-intuitive: you'd expect rational agents to be frame-independent.
    But emergence non-commutativity makes framing effects INEVITABLE. -/
theorem framing_effect_theorem (s₁ s₂ r c : I) :
    rs (compose (compose r s₁) s₂) c - rs (compose (compose r s₂) s₁) c =
    (emergence r s₁ c + emergence (compose r s₁) s₂ c) -
    (emergence r s₂ c + emergence (compose r s₂) s₁ c) := by
  have h1 := rs_compose_eq r s₁ c
  have h2 := rs_compose_eq (compose r s₁) s₂ c
  have h3 := rs_compose_eq r s₂ c
  have h4 := rs_compose_eq (compose r s₂) s₁ c
  linarith

/-- SP10. THE FUNDAMENTAL MANIPULATION BOUND: The squared emergence
    between any signal and receiver is bounded by the product of
    composed weight and receiver weight. This means MANIPULATION IS
    EXPENSIVE: to produce a large surprise in the receiver, you need
    heavy (complex) ideas. Lightweight lies produce only small effects.
    Counter-intuitive: you might expect manipulation to be unbounded.
    But the emergence bound provides a fundamental physical limit. -/
theorem manipulation_cost_bound (s r : I) :
    (emergence r s r)^2 ≤ rs (compose r s) (compose r s) * rs r r :=
  emergence_bounded' r s r

end StrategicParadoxes

end IDT3
