import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 7: Coalitional Composition

**Core claim.** Groups compose ideas jointly. Coalition value = properties of
joint composition. We model coalitions as lists and study the depth, resonance,
and filtration properties of their joint composition.

## 17 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch7

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- Joint composition of a coalition: fold ideas left-to-right starting from void. -/
def coalitionCompose (l : List I) : I :=
  l.foldl IdeaticSpace.compose IdeaticSpace.void

/-! ## §2. Basic Coalition Properties -/

/-- Empty coalition produces void. -/
theorem coalition_nil :
    coalitionCompose ([] : List I) = (IdeaticSpace.void : I) := rfl

/-- Single-member coalition produces that member. -/
theorem coalition_singleton (a : I) :
    coalitionCompose [a] = a := by
  simp [coalitionCompose, List.foldl, void_left]

/-- Two-element coalition equals compose. -/
theorem coalition_two_eq_compose (a b : I) :
    coalitionCompose [a, b] = IdeaticSpace.compose a b := by
  simp [coalitionCompose, List.foldl, void_left]

/-! ## §3. Depth Bound via Helper Lemma -/

/-- Helper: depth of foldl compose from accumulator is bounded. -/
private theorem foldl_depth_bound (acc : I) (l : List I) :
    IdeaticSpace.depth (l.foldl IdeaticSpace.compose acc) ≤
    IdeaticSpace.depth acc + depthSum l := by
  induction l generalizing acc with
  | nil => simp [depthSum]
  | cons a rest ih =>
    simp only [List.foldl]
    have h1 := ih (IdeaticSpace.compose acc a)
    have h2 := depth_compose_le acc a
    rw [depthSum_cons]
    omega

/-- Coalition depth is bounded by depthSum. -/
theorem coalition_depth_bound (l : List I) :
    IdeaticSpace.depth (coalitionCompose l) ≤ depthSum l := by
  unfold coalitionCompose
  have h := foldl_depth_bound (IdeaticSpace.void : I) l
  simp [depth_void] at h
  exact h

/-- Adding void to a coalition doesn't change the output. -/
theorem coalition_void_member_neutral (l : List I) :
    coalitionCompose (l ++ [IdeaticSpace.void]) = coalitionCompose l := by
  simp [coalitionCompose, List.foldl_append, List.foldl, void_right]

/-- All depth-zero members → coalition has depth 0. -/
theorem coalition_depth_zero_from_zero (l : List I)
    (h : ∀ (a : I), a ∈ l → IdeaticSpace.depth a = 0) :
    IdeaticSpace.depth (coalitionCompose l) = 0 := by
  have hsum : depthSum l = 0 := by
    induction l with
    | nil => simp [depthSum]
    | cons a rest ih =>
      rw [depthSum_cons]
      have ha := h a (List.mem_cons_self a rest)
      have hrest : ∀ (b : I), b ∈ rest → IdeaticSpace.depth b = 0 :=
        fun b hb => h b (List.mem_cons_of_mem a hb)
      have := ih hrest
      omega
  have hbound := coalition_depth_bound l
  omega

/-! ## §4. Void and Replicate Coalitions -/

/-- All-void coalition produces void. -/
theorem void_coalition_identity (n : ℕ) :
    coalitionCompose (List.replicate n (IdeaticSpace.void : I)) =
    (IdeaticSpace.void : I) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [coalitionCompose] at ih ⊢
    rw [List.replicate_succ, List.foldl_cons, void_left]
    exact ih

/-- Coalition depth is always ≥ 0 (trivially, it's a Nat). -/
theorem coalition_depth_nonneg (l : List I) :
    0 ≤ IdeaticSpace.depth (coalitionCompose l) :=
  Nat.zero_le _

/-- Replicate a n → depth ≤ n * depth a. -/
theorem coalition_replicate_depth (a : I) (n : ℕ) :
    IdeaticSpace.depth (coalitionCompose (List.replicate n a)) ≤
    n * IdeaticSpace.depth a := by
  have hsum : depthSum (List.replicate n a) = n * IdeaticSpace.depth a := by
    induction n with
    | zero => simp [depthSum]
    | succ n ih =>
      rw [List.replicate_succ, depthSum_cons, ih]
      ring
  have h := coalition_depth_bound (List.replicate n a)
  linarith

/-! ## §5. Cons and Append Properties -/

/-- Adding an element to a coalition: depth bounded by element depth + depthSum. -/
theorem coalition_cons_depth (a : I) (l : List I) :
    IdeaticSpace.depth (coalitionCompose (a :: l)) ≤
    IdeaticSpace.depth a + depthSum l := by
  have h := coalition_depth_bound (a :: l)
  rw [depthSum_cons] at h
  linarith

/-- Atomic coalition (all atomic members) has depth ≤ length. -/
theorem atomic_coalition_depth (l : List I)
    (h : ∀ (a : I), a ∈ l → IdeaticSpace.atomic a) :
    IdeaticSpace.depth (coalitionCompose l) ≤ l.length := by
  have hsum : depthSum l ≤ l.length := by
    induction l with
    | nil => simp [depthSum]
    | cons a rest ih =>
      rw [depthSum_cons, List.length_cons]
      have ha := IdeaticSpace.depth_atomic a (h a (List.mem_cons_self a rest))
      have hrest : ∀ (b : I), b ∈ rest → IdeaticSpace.atomic b :=
        fun b hb => h b (List.mem_cons_of_mem a hb)
      have := ih hrest
      omega
  have hbound := coalition_depth_bound l
  omega

/-! ## §6. Resonance Properties -/

/-- Coalition of same idea resonates with itself. -/
theorem coalition_self_resonance (l : List I) :
    IdeaticSpace.resonates (coalitionCompose l) (coalitionCompose l) :=
  resonance_refl _

/-- If we replace last element with a resonant one, result resonates. -/
theorem coalition_resonance_last_swap (l : List I) (a b : I)
    (hab : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (coalitionCompose (l ++ [a]))
      (coalitionCompose (l ++ [b])) := by
  simp [coalitionCompose, List.foldl_append, List.foldl]
  exact resonance_compose_left _ hab

/-- Coalition from filtration d → result in filtration (length * d). -/
theorem coalition_filtration (d : ℕ) (l : List I)
    (h : ∀ (a : I), a ∈ l → a ∈ depthFiltration d) :
    coalitionCompose l ∈ depthFiltration (l.length * d) := by
  simp [depthFiltration]
  have hsum : depthSum l ≤ l.length * d := by
    induction l with
    | nil => simp [depthSum]
    | cons a rest ih =>
      rw [depthSum_cons, List.length_cons]
      have ha := h a (List.mem_cons_self a rest)
      simp [depthFiltration] at ha
      have hrest : ∀ (b : I), b ∈ rest → b ∈ depthFiltration d :=
        fun b hb => h b (List.mem_cons_of_mem a hb)
      have hih := ih hrest
      have : (rest.length + 1) * d = d + rest.length * d := by ring
      linarith
  have hbound := coalition_depth_bound l
  omega

/-- Marginal contribution: composing a with a coalition. -/
def marginalContribution (a : I) (l : List I) : I :=
  coalitionCompose (a :: l)

/-- Marginal contribution depth is bounded. -/
theorem marginal_depth_bound (a : I) (l : List I) :
    IdeaticSpace.depth (marginalContribution a l) ≤
    IdeaticSpace.depth a + depthSum l := by
  unfold marginalContribution
  have h := coalition_depth_bound (a :: l)
  rw [depthSum_cons] at h
  exact h

/-- Adding void as marginal contribution doesn't increase depth beyond coalition depth. -/
theorem void_marginal_identity (l : List I) :
    IdeaticSpace.depth (marginalContribution (IdeaticSpace.void : I) l) ≤
    depthSum l := by
  have h := marginal_depth_bound (IdeaticSpace.void : I) l
  simp [depth_void] at h
  exact h

end IDT.MG.Ch7
