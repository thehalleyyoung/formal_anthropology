import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Signal Games

Signal games where payoff = resonance strength. A sender transmits signal s,
a receiver with repertoire r interprets as compose(r, s). Payoff measures
the degree of resonance between original ideas and their interpreted composition.

## Key Concepts

- **Interpretation**: compose(r, s) — receiver r incorporates signal s
- **Sender Payoff**: resonance between signal and interpretation
- **Receiver Payoff**: resonance between receiver and interpretation
- **Social Welfare**: sum of both payoffs
- **Pooling Signal**: void — carries no information

## NO SORRIES
-/

namespace IDT2

section SignalGames

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Core Definitions -/

/-- Social welfare: sum of sender and receiver payoffs -/
noncomputable def socialWelfare (s r : I) : ℝ :=
  senderPayoff s r + receiverPayoff s r

/-- The pooling signal: void, carrying no information -/
def poolingSignal : I := (void : I)

/-- Self-resonance of the interpretation -/
noncomputable def interpretationStrength (s r : I) : ℝ :=
  resonanceStrength (interpret s r) (interpret s r)

/-- How much the interpretation strengthens beyond the signal alone -/
noncomputable def interpretationGain (s r : I) : ℝ :=
  interpretationStrength s r - resonanceStrength s s

/-! ## §2. Interpretation Structure -/

/-- T1. Interpretation unfolds to composition -/
theorem interpret_eq_compose (s r : I) : interpret s r = compose r s := rfl

/-- T2. Sequential interpretation = single with composed signal -/
theorem interpret_sequential (s t r : I) :
    interpret s (interpret t r) = interpret (compose t s) r := by
  simp only [interpret]; rw [IdeaticSpace2.compose_assoc]

/-- T3. Composing signals is sequential interpretation -/
theorem compose_signals_sequential (s₁ s₂ r : I) :
    interpret (compose s₁ s₂) r = interpret s₂ (interpret s₁ r) :=
  (interpret_sequential s₂ s₁ r).symm

/-- T4. Interpretation depth bounded by component sum -/
theorem sg_interpret_depth_bound (s r : I) :
    depth (interpret s r) ≤ depth r + depth s :=
  IdeaticSpace2.depth_subadditive r s

/-- T5. Double interpretation depth bound -/
theorem double_interpret_depth (s t r : I) :
    depth (interpret s (interpret t r)) ≤ depth r + depth t + depth s := by
  rw [interpret_sequential]
  have h1 := sg_interpret_depth_bound (compose t s) r
  have h2 := IdeaticSpace2.depth_subadditive t s
  omega

/-- T6. Chaining void interpretations is identity -/
theorem void_interpret_chain (r : I) :
    interpret (void : I) (interpret (void : I) r) = r := by
  simp only [interpret, IdeaticSpace2.void_right]

/-- T7. Adding receiver context factors through interpretation -/
theorem interpret_context_receiver (s r c : I) :
    interpret s (compose c r) = compose c (interpret s r) := by
  simp only [interpret]; rw [IdeaticSpace2.compose_assoc]

/-! ## §3. Pooling Signal -/

/-- T8. Pooling signal equals void -/
theorem poolingSignal_eq_void : (poolingSignal : I) = (void : I) := rfl

/-- T9. Pooling sender payoff -/
theorem pooling_sender_payoff (r : I) :
    senderPayoff (poolingSignal : I) r = resonanceStrength (void : I) r := by
  unfold senderPayoff poolingSignal; rw [interpret_void_signal]

/-- T10. Pooling receiver payoff = self-resonance -/
theorem pooling_receiver_payoff (r : I) :
    receiverPayoff (poolingSignal : I) r = resonanceStrength r r := by
  unfold receiverPayoff poolingSignal; rw [interpret_void_signal]

/-- T11. Pooling sender payoff is nonneg -/
theorem pooling_sender_nonneg (r : I) :
    senderPayoff (poolingSignal : I) r ≥ 0 := by
  rw [pooling_sender_payoff]; exact rs_nonneg' _ _

/-- T12. Pooling receiver payoff ≥ 1 -/
theorem pooling_receiver_ge_one (r : I) :
    receiverPayoff (poolingSignal : I) r ≥ 1 := by
  rw [pooling_receiver_payoff]; exact rs_self_ge_one _

/-! ## §4. Interpretation Resonance Bounds -/

/-- T13. Interpretation strength ≥ sender self-resonance -/
theorem interpretationStrength_ge_sender (s r : I) :
    interpretationStrength s r ≥ resonanceStrength s s := by
  unfold interpretationStrength interpret
  exact rs_compose_self_left s r

/-- T14. Interpretation strength ≥ receiver self-resonance -/
theorem interpretationStrength_ge_receiver (s r : I) :
    interpretationStrength s r ≥ resonanceStrength r r := by
  unfold interpretationStrength interpret
  exact rs_compose_self_right r s

/-- T15. Interpretation strength ≥ 1 -/
theorem interpretationStrength_ge_one (s r : I) :
    interpretationStrength s r ≥ 1 := by
  linarith [interpretationStrength_ge_sender s r, rs_self_ge_one s]

/-- T16. Interpretation gain is nonnegative -/
theorem interpretationGain_nonneg (s r : I) :
    interpretationGain s r ≥ 0 := by
  unfold interpretationGain
  linarith [interpretationStrength_ge_sender s r]

/-- T17. Void signal yields trivial interpretation strength -/
theorem interpretationStrength_void_signal (r : I) :
    interpretationStrength (void : I) r = resonanceStrength r r := by
  unfold interpretationStrength; rw [interpret_void_signal]

/-- T18. Void receiver yields trivial interpretation strength -/
theorem interpretationStrength_void_receiver (s : I) :
    interpretationStrength s (void : I) = resonanceStrength s s := by
  unfold interpretationStrength; rw [interpret_void_receiver]

/-- T19. Interpretation gain with void receiver vanishes -/
theorem interpretationGain_void_receiver (s : I) :
    interpretationGain s (void : I) = 0 := by
  unfold interpretationGain
  rw [interpretationStrength_void_receiver]
  ring

/-! ## §5. Social Welfare -/

/-- T20. Social welfare is nonnegative -/
theorem socialWelfare_nonneg (s r : I) : socialWelfare s r ≥ 0 := by
  unfold socialWelfare
  linarith [senderPayoff_nonneg s r, receiverPayoff_nonneg s r]

/-- T21. Social welfare with both void = 2 -/
theorem socialWelfare_void_void :
    socialWelfare (void : I) (void : I) = 2 := by
  unfold socialWelfare senderPayoff receiverPayoff interpret
  simp only [IdeaticSpace2.void_left]
  linarith [rs_void_unit (I := I)]

/-- T22. Social welfare with void sender -/
theorem socialWelfare_void_sender (r : I) :
    socialWelfare (void : I) r =
    resonanceStrength (void : I) r + resonanceStrength r r := by
  unfold socialWelfare senderPayoff receiverPayoff
  rw [interpret_void_signal]

/-- T23. Social welfare with void receiver -/
theorem socialWelfare_void_receiver (s : I) :
    socialWelfare s (void : I) =
    resonanceStrength s s + resonanceStrength (void : I) s := by
  unfold socialWelfare senderPayoff receiverPayoff
  rw [interpret_void_receiver]

/-- T24. Void symmetry: welfare(void, a) = welfare(a, void) -/
theorem socialWelfare_void_symmetric (a : I) :
    socialWelfare (void : I) a = socialWelfare a (void : I) := by
  rw [socialWelfare_void_sender, socialWelfare_void_receiver]
  rw [rs_symm']
  ring

/-- T25. Social welfare ≥ sender payoff -/
theorem socialWelfare_ge_sender (s r : I) :
    socialWelfare s r ≥ senderPayoff s r := by
  unfold socialWelfare; linarith [receiverPayoff_nonneg s r]

/-- T26. Social welfare ≥ receiver payoff -/
theorem socialWelfare_ge_receiver (s r : I) :
    socialWelfare s r ≥ receiverPayoff s r := by
  unfold socialWelfare; linarith [senderPayoff_nonneg s r]

/-! ## §6. Cauchy-Schwarz Payoff Bounds -/

/-- T27. Sender payoff bounded by Cauchy-Schwarz -/
theorem sender_payoff_cauchy_schwarz (s r : I) :
    senderPayoff s r * senderPayoff s r ≤
    resonanceStrength s s * interpretationStrength s r := by
  unfold senderPayoff interpretationStrength
  exact IdeaticSpace2.rs_cauchy_schwarz s (interpret s r)

/-- T28. Receiver payoff bounded by Cauchy-Schwarz -/
theorem receiver_payoff_cauchy_schwarz (s r : I) :
    receiverPayoff s r * receiverPayoff s r ≤
    resonanceStrength r r * interpretationStrength s r := by
  unfold receiverPayoff interpretationStrength
  exact IdeaticSpace2.rs_cauchy_schwarz r (interpret s r)

/-! ## §7. Context Enrichment -/

/-- T29. Receiver payoff increases with richer context -/
theorem receiverPayoff_context_enrichment (s r c : I) :
    receiverPayoff s (compose c r) ≥ receiverPayoff s r := by
  unfold receiverPayoff interpret
  rw [IdeaticSpace2.compose_assoc c r s]
  exact IdeaticSpace2.rs_compose_left_mono r (compose r s) c

end SignalGames

end IDT2
