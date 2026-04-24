import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 9: Repeated Composition Games

**Core claim.** When players compose ideas repeatedly, properties accumulate
but are bounded. We model repeated play as a list of ideas composed via foldl.

## 17 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch9

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Repeated outcome: fold ideas left-to-right starting from void. -/
def RepeatedOutcome (history : List I) : I :=
  history.foldl IdeaticSpace.compose IdeaticSpace.void

/-- The depth of the accumulated outcome after a history. -/
def roundDepth (history : List I) : ℕ :=
  IdeaticSpace.depth (RepeatedOutcome history)

/-- A depth bound claim on a history. -/
def HistoryDepthBound (history : List I) (d : ℕ) : Prop :=
  IdeaticSpace.depth (RepeatedOutcome history) ≤ d

/-! ## §2. Base Cases -/

/-- No rounds → outcome is void. -/
theorem empty_history_void :
    RepeatedOutcome ([] : List I) = (IdeaticSpace.void : I) := rfl

/-- One round = that idea. -/
theorem single_round_identity (a : I) :
    RepeatedOutcome [a] = a := by
  simp [RepeatedOutcome, List.foldl, void_left]

/-- Two rounds = compose of the two ideas. -/
theorem two_rounds_compose (a b : I) :
    RepeatedOutcome [a, b] = IdeaticSpace.compose a b := by
  simp [RepeatedOutcome, List.foldl, void_left]

/-! ## §3. Depth Bounds -/

/-- Helper: depth of foldl from an accumulator. -/
private theorem foldl_depth_le (acc : I) (l : List I) :
    IdeaticSpace.depth (l.foldl IdeaticSpace.compose acc) ≤
    IdeaticSpace.depth acc + depthSum l := by
  induction l generalizing acc with
  | nil => simp [depthSum]
  | cons a rest ih =>
    simp only [List.foldl]
    have h := ih (IdeaticSpace.compose acc a)
    have hle := depth_compose_le acc a
    rw [depthSum_cons]; omega

/-- Depth of accumulated outcome ≤ sum of individual depths. -/
theorem history_depth_le_sum (history : List I) :
    IdeaticSpace.depth (RepeatedOutcome history) ≤ depthSum history := by
  unfold RepeatedOutcome
  have h := foldl_depth_le (IdeaticSpace.void : I) history
  simp [depth_void] at h; exact h

/-- Adding void rounds doesn't change outcome. -/
theorem void_rounds_identity (history : List I) :
    RepeatedOutcome (history ++ [IdeaticSpace.void]) = RepeatedOutcome history := by
  simp [RepeatedOutcome, List.foldl_append, List.foldl, void_right]

/-- All-void history → outcome is void. -/
theorem repeated_void_stays_void (n : ℕ) :
    RepeatedOutcome (List.replicate n (IdeaticSpace.void : I)) =
    (IdeaticSpace.void : I) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [RepeatedOutcome] at ih ⊢
    rw [List.replicate_succ, List.foldl_cons, void_left]
    exact ih

/-- n rounds of depth-d ideas → depth ≤ n * d. -/
theorem n_rounds_max_depth (history : List I) (d : ℕ)
    (h : ∀ (a : I), a ∈ history → IdeaticSpace.depth a ≤ d) :
    IdeaticSpace.depth (RepeatedOutcome history) ≤ history.length * d := by
  have hsum : depthSum history ≤ history.length * d := by
    induction history with
    | nil => simp [depthSum]
    | cons a rest ih =>
      rw [depthSum_cons, List.length_cons]
      have ha := h a (List.mem_cons_self a rest)
      have hrest : ∀ (b : I), b ∈ rest → IdeaticSpace.depth b ≤ d :=
        fun b hb => h b (List.mem_cons_of_mem a hb)
      have hih := ih hrest
      have : (rest.length + 1) * d = d + rest.length * d := by ring
      linarith
  have hle := history_depth_le_sum history
  omega

/-- n rounds of atomic ideas → depth ≤ n. -/
theorem repeated_atomic_depth_bound (history : List I)
    (h : ∀ (a : I), a ∈ history → IdeaticSpace.atomic a) :
    IdeaticSpace.depth (RepeatedOutcome history) ≤ history.length := by
  have := n_rounds_max_depth history 1 (fun a ha => IdeaticSpace.depth_atomic a (h a ha))
  omega

/-! ## §4. Monotonicity and Append -/

/-- Appending rounds: depth of appended histories is bounded. -/
theorem history_append_depth (h1 h2 : List I) :
    IdeaticSpace.depth (RepeatedOutcome (h1 ++ h2)) ≤
    depthSum h1 + depthSum h2 := by
  have heq : depthSum (h1 ++ h2) = depthSum h1 + depthSum h2 := by
    induction h1 with
    | nil => simp [depthSum]
    | cons a rest ih => simp [depthSum_cons, ih]; omega
  have h := history_depth_le_sum (h1 ++ h2)
  omega

/-- Void prefix is irrelevant: leading void rounds don't affect outcome. -/
theorem void_prefix_irrelevant (n : ℕ) (history : List I) :
    RepeatedOutcome (List.replicate n (IdeaticSpace.void : I) ++ history) =
    RepeatedOutcome history := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    simp [RepeatedOutcome] at ih ⊢
    exact ih

/-- All depth-0 rounds → depth-0 outcome. -/
theorem history_depth_zero_from_zero (history : List I)
    (h : ∀ (a : I), a ∈ history → IdeaticSpace.depth a = 0) :
    IdeaticSpace.depth (RepeatedOutcome history) = 0 := by
  have hsum : depthSum history = 0 := by
    induction history with
    | nil => simp [depthSum]
    | cons a rest ih =>
      rw [depthSum_cons]
      have ha := h a (List.mem_cons_self a rest)
      have hrest := fun b hb => h b (List.mem_cons_of_mem a hb)
      have := ih hrest; omega
  have hle := history_depth_le_sum history
  omega

/-! ## §5. Associativity and Resonance -/

/-- Three round outcomes respect associativity. -/
theorem three_rounds_assoc (a b c : I) :
    RepeatedOutcome [a, b, c] =
    IdeaticSpace.compose (IdeaticSpace.compose a b) c := by
  simp [RepeatedOutcome, List.foldl, void_left]

/-- History from filtration d → outcome in filtration (length * d). -/
theorem history_filtration (d : ℕ) (history : List I)
    (h : ∀ (a : I), a ∈ history → a ∈ depthFiltration d) :
    RepeatedOutcome history ∈ depthFiltration (history.length * d) := by
  simp [depthFiltration]
  have hsum : depthSum history ≤ history.length * d := by
    induction history with
    | nil => simp [depthSum]
    | cons a rest ih =>
      rw [depthSum_cons, List.length_cons]
      have ha := h a (List.mem_cons_self a rest)
      simp [depthFiltration] at ha
      have hrest := fun b hb => h b (List.mem_cons_of_mem a hb)
      have hih := ih hrest
      have : (rest.length + 1) * d = d + rest.length * d := by ring
      linarith
  have hle := history_depth_le_sum history
  omega

/-- Repeated same idea: composeN equivalence for the first few cases. -/
theorem repeated_same_two (a : I) :
    RepeatedOutcome [a, a] = composeN a 2 := by
  simp [RepeatedOutcome, List.foldl, void_left, composeN]

/-- Repeated composition with same idea: depth ≤ n * depth a. -/
theorem repeated_same_depth (a : I) (n : ℕ) :
    IdeaticSpace.depth (composeN a n) ≤ n * IdeaticSpace.depth a :=
  depth_composeN a n

end IDT.MG.Ch9
