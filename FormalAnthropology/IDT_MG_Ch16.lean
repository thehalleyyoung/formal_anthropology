import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 16: Signalling with Ideatic Content

**Core claim.** A sender chooses a signal (idea); a receiver interprets it by
composing the signal with their repertoire. Pooling equilibrium = void signal;
separating equilibrium requires distinct depths.

## 17 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch16

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- A signal is just an idea. -/
abbrev Signal (I : Type*) [IdeaticSpace I] := I

/-- Interpretation: the receiver composes their repertoire element with the signal. -/
def Interpretation (signal : I) (r : I) : I := IdeaticSpace.compose r signal

/-- Repertoire interpretation: map each repertoire element to its interpretation. -/
def RepertoireInterpretation (signal : I) (repertoire : List I) : List I :=
  repertoire.map (fun r => Interpretation signal r)

/-- Interpretation depth: depth of the composed interpretation. -/
def InterpretationDepth (signal : I) (r : I) : ℕ := IdeaticSpace.depth (Interpretation signal r)

/-- Pooling signal: void — all types send the same contentless signal. -/
def PoolingSignal : I := IdeaticSpace.void

/-- Separating condition: two signals differ in depth. -/
def SeparatingCondition (s1 s2 : I) : Prop := IdeaticSpace.depth s1 ≠ IdeaticSpace.depth s2

/-! ## §2. Pooling Equilibrium Theorems -/

/-- Theorem 1: Pooling (void) signal → interpretation = repertoire element. -/
theorem pooling_interpretation (r : I) :
    Interpretation (PoolingSignal : I) r = r := by
  simp [Interpretation, PoolingSignal, void_right]

/-- Theorem 2: Interpretation depth ≤ depth r + depth signal. -/
theorem interpretation_depth_bound (signal r : I) :
    InterpretationDepth signal r ≤ IdeaticSpace.depth r + IdeaticSpace.depth signal := by
  exact depth_compose_le r signal

/-- Theorem 3: Void repertoire element → interpretation = signal. -/
theorem void_receiver_interpretation (signal : I) :
    Interpretation signal (IdeaticSpace.void : I) = signal := by
  simp [Interpretation, void_left]

/-- Theorem 4: If r1 resonates with r2, interpretations of same signal resonate. -/
theorem interpretation_resonance_preserved (signal : I) {r1 r2 : I}
    (h : IdeaticSpace.resonates r1 r2) :
    IdeaticSpace.resonates (Interpretation signal r1) (Interpretation signal r2) := by
  exact resonance_compose_right h signal

/-- Theorem 5: All interpretations bounded by repertoire max depth + signal depth. -/
theorem repertoire_interpretations_depth_bound (signal : I) (repertoire : List I) (d : ℕ)
    (hbound : ∀ (r : I), r ∈ repertoire → IdeaticSpace.depth r ≤ d) :
    ∀ (x : I), x ∈ RepertoireInterpretation signal repertoire →
    IdeaticSpace.depth x ≤ d + IdeaticSpace.depth signal := by
  intro x hx
  simp [RepertoireInterpretation] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  have h1 := depth_compose_le r signal
  have h2 := hbound r hr
  linarith

/-- Theorem 6: Pooling signal is identity mapping on repertoire. -/
theorem pooling_is_identity (repertoire : List I) :
    RepertoireInterpretation (PoolingSignal : I) repertoire = repertoire := by
  simp [RepertoireInterpretation, PoolingSignal, Interpretation, void_right]

/-- Theorem 7: Separating signals have distinct depths (by definition). -/
theorem separating_depth_distinct {s1 s2 : I} (h : SeparatingCondition s1 s2) :
    IdeaticSpace.depth s1 ≠ IdeaticSpace.depth s2 := h

/-- Theorem 8: Void signal + void repertoire element = void. -/
theorem interpretation_void_both :
    Interpretation (PoolingSignal : I) (IdeaticSpace.void : I) = (IdeaticSpace.void : I) := by
  simp [Interpretation, PoolingSignal, void_left]

/-! ## §3. Filtration and Structure -/

/-- Theorem 9: If signal and repertoire in filtration d, interpretation in filtration 2*d. -/
theorem interpretation_in_filtration {d : ℕ} {signal r : I}
    (hs : IdeaticSpace.depth signal ≤ d) (hr : IdeaticSpace.depth r ≤ d) :
    IdeaticSpace.depth (Interpretation signal r) ≤ 2 * d := by
  have h := depth_compose_le r signal
  linarith

/-- Theorem 10: Number of interpretations = repertoire length. -/
theorem repertoire_interpretations_length (signal : I) (repertoire : List I) :
    (RepertoireInterpretation signal repertoire).length = repertoire.length := by
  simp [RepertoireInterpretation]

/-- Theorem 11: Coherent repertoire → interpretations of same signal are coherent. -/
theorem coherent_repertoire_coherent_interpretations (signal : I) (repertoire : List I)
    (h : Coherent repertoire) :
    Coherent (RepertoireInterpretation signal repertoire) := by
  induction repertoire with
  | nil => exact trivial
  | cons a rest ih =>
    cases rest with
    | nil => exact trivial
    | cons b rest' =>
      simp [RepertoireInterpretation, List.map, Interpretation]
      constructor
      · exact resonance_compose_right h.1 signal
      · exact ih h.2

/-- Theorem 12: Atomic signal → interpretation depth ≤ depth r + 1. -/
theorem atomic_signal_interpretation_bound {signal : I}
    (ha : IdeaticSpace.atomic signal) (r : I) :
    InterpretationDepth signal r ≤ IdeaticSpace.depth r + 1 := by
  have h1 := depth_compose_le r signal
  have h2 := IdeaticSpace.depth_atomic signal ha
  linarith

/-- Theorem 13: Deeper signal → higher depth bound on interpretations. -/
theorem signal_depth_as_cost (signal1 signal2 : I) (r : I)
    (h : IdeaticSpace.depth signal1 ≤ IdeaticSpace.depth signal2) :
    InterpretationDepth signal1 r ≤ IdeaticSpace.depth r + IdeaticSpace.depth signal2 := by
  have h1 := depth_compose_le r signal1
  linarith

/-- Theorem 14: Void signal leaves all repertoire elements unchanged. -/
theorem void_signal_preserves_repertoire (repertoire : List I) :
    (RepertoireInterpretation (IdeaticSpace.void : I) repertoire) = repertoire := by
  simp [RepertoireInterpretation, Interpretation, void_right]

/-- Theorem 15: Interpretation resonates with itself (refl). -/
theorem interpretation_resonance_with_signal (r signal : I) :
    IdeaticSpace.resonates (Interpretation signal r) (Interpretation signal r) :=
  resonance_refl _

/-- Theorem 16: Double interpretation → depth bound compounds. -/
theorem double_interpretation (signal1 signal2 r : I) :
    IdeaticSpace.depth (Interpretation signal2 (Interpretation signal1 r)) ≤
    IdeaticSpace.depth r + IdeaticSpace.depth signal1 + IdeaticSpace.depth signal2 := by
  have h1 := depth_compose_le r signal1
  have h2 := depth_compose_le (IdeaticSpace.compose r signal1) signal2
  linarith

/-- Theorem 17: If repertoire elements pairwise resonate, so do interpretations. -/
theorem interpretations_resonate_pairwise {r1 r2 : I} (signal : I)
    (h : IdeaticSpace.resonates r1 r2) :
    IdeaticSpace.resonates (Interpretation signal r1) (Interpretation signal r2) :=
  resonance_compose_right h signal

end IDT.MG.Ch16
