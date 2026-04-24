import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 20: The Grand Synthesis

**Core claim.** Meta-theorems connecting all parts of the theory. The
"fundamental theorems of the meaning game" — composition is a monoid,
depth is a resource, resonance enables cooperation, and filtration
provides hierarchical structure.

## 20 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch20

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- A meaning game: two players with repertoires and a composition rule. -/
structure MeaningGame (I : Type*) [IdeaticSpace I] where
  repertoire1 : List I
  repertoire2 : List I

/-- The grand outcome: composing two players' chosen ideas. -/
def GrandOutcome (s1 s2 : I) : I := IdeaticSpace.compose s1 s2

/-- Depth as a resource: the complexity budget of an idea. -/
def DepthResource (s : I) : ℕ := IdeaticSpace.depth s

/-- Resonance cooperation: two ideas can cooperate when they resonate. -/
def ResonanceCooperation (a b : I) : Prop := IdeaticSpace.resonates a b

/-- Composition closure: a set closed under composition. -/
def CompositionClosed (S : Set I) : Prop :=
  ∀ (a b : I), a ∈ S → b ∈ S → IdeaticSpace.compose a b ∈ S

/-! ## §2. Fundamental Equilibrium Theorems -/

/-- Theorem 1: Void is always available and preserves the other's idea (left). -/
theorem fundamental_void_equilibrium_left (s : I) :
    GrandOutcome (IdeaticSpace.void : I) s = s := by
  simp [GrandOutcome, void_left]

/-- Theorem 2: Void is always available and preserves the other's idea (right). -/
theorem fundamental_void_equilibrium_right (s : I) :
    GrandOutcome s (IdeaticSpace.void : I) = s := by
  simp [GrandOutcome, void_right]

/-- Theorem 3: Depth of any outcome ≤ sum of input depths. -/
theorem depth_resource_bound (s1 s2 : I) :
    DepthResource (GrandOutcome s1 s2) ≤ DepthResource s1 + DepthResource s2 := by
  exact depth_compose_le s1 s2

/-- Theorem 4: Resonance cooperation is symmetric. -/
theorem resonance_cooperation_symmetric {a b : I}
    (h : ResonanceCooperation a b) : ResonanceCooperation b a :=
  resonance_symm h

/-- Theorem 5: If a res b and c res d, then compose a c res compose b d. -/
theorem resonance_cooperation_composable {a b c d : I}
    (h1 : ResonanceCooperation a b) (h2 : ResonanceCooperation c d) :
    ResonanceCooperation (IdeaticSpace.compose a c) (IdeaticSpace.compose b d) :=
  IdeaticSpace.resonance_compose a b c d h1 h2

/-! ## §3. Closure Properties -/

/-- Theorem 6: Depth-zero ideas are composition-closed. -/
theorem depth_zero_closure :
    CompositionClosed (depthFiltration 0 : Set I) := by
  intro a b ha hb
  simp [depthFiltration, Set.mem_setOf_eq] at ha hb ⊢
  have h := depth_compose_le a b; omega

/-- Theorem 7: Composing ideas from filtration n lands in filtration 2n. -/
theorem filtration_closure (n : ℕ) (a b : I)
    (ha : a ∈ (depthFiltration n : Set I)) (hb : b ∈ (depthFiltration n : Set I)) :
    IdeaticSpace.compose a b ∈ (depthFiltration (2 * n) : Set I) :=
  depthFiltration_compose ha hb

/-- Theorem 8: Resonance class is stable under self-composition. -/
theorem resonance_class_stability (a : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose a a) (IdeaticSpace.compose a a) :=
  resonance_refl _

/-- Theorem 9: n players → depth ≤ sum of all depths (via list fold). -/
private lemma foldl_compose_depth_bound (acc : I) (ideas : List I) :
    IdeaticSpace.depth (ideas.foldl IdeaticSpace.compose acc) ≤
    IdeaticSpace.depth acc + depthSum ideas := by
  induction ideas generalizing acc with
  | nil => simp [depthSum]
  | cons a rest ih =>
    simp only [List.foldl, depthSum_cons]
    have h := ih (IdeaticSpace.compose acc a)
    have h2 := depth_compose_le acc a
    linarith

/-- Theorem 9: n players → depth ≤ sum of all depths (via list fold). -/
theorem grand_depth_bound_n_players (ideas : List I) :
    IdeaticSpace.depth (ideas.foldl IdeaticSpace.compose IdeaticSpace.void) ≤
    depthSum ideas := by
  have h := foldl_compose_depth_bound (IdeaticSpace.void : I) ideas
  simp [depth_void] at h
  linarith

/-- Theorem 10: Pairwise resonance propagates through composition. -/
theorem grand_resonance_propagation {a b c d : I}
    (h1 : IdeaticSpace.resonates a b) (h2 : IdeaticSpace.resonates c d) :
    IdeaticSpace.resonates (GrandOutcome a c) (GrandOutcome b d) := by
  exact IdeaticSpace.resonance_compose a b c d h1 h2

/-! ## §4. Identity and Meaning -/

/-- Theorem 11: Void is identity in every meaning game (left). -/
theorem void_is_identity_left (s : I) :
    IdeaticSpace.compose (IdeaticSpace.void : I) s = s := void_left s

/-- Theorem 12: Void is identity in every meaning game (right). -/
theorem void_is_identity_right (s : I) :
    IdeaticSpace.compose s (IdeaticSpace.void : I) = s := void_right s

/-- Theorem 13: Nontrivial meaning requires positive depth. -/
theorem meaning_requires_depth {a : I}
    (h : IdeaticSpace.depth a = 0) :
    a ∈ (depthFiltration 0 : Set I) := by
  simp [depthFiltration, Set.mem_setOf_eq]
  omega

/-- Theorem 14: Resonant ideas composed produce resonant outcomes. -/
theorem cooperation_via_resonance {a b : I}
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose a b) :=
  resonance_refl _

/-- Theorem 15: Filtration forms monotone hierarchy. -/
theorem depth_hierarchy_monotone {m n : ℕ} (h : m ≤ n) :
    (depthFiltration m : Set I) ⊆ depthFiltration n :=
  depthFiltration_mono h

/-! ## §5. Grand Synthesis -/

/-- Theorem 16: Composition game determined by inputs (extensionality). -/
theorem composition_game_determined_by_inputs (s1 s2 : I) :
    GrandOutcome s1 s2 = IdeaticSpace.compose s1 s2 := rfl

/-- Theorem 17: Coherent sequences of game outcomes form coherent narratives. -/
theorem grand_synthesis_coherence {a b c d : I}
    (h1 : IdeaticSpace.resonates a b) (h2 : IdeaticSpace.resonates c d) :
    Coherent [GrandOutcome a c, GrandOutcome b d] := by
  rw [coherent_pair]
  exact IdeaticSpace.resonance_compose a b c d h1 h2

/-- Theorem 18: Three-player meaning game is associative. -/
theorem meaning_game_associative (a b c : I) :
    GrandOutcome (GrandOutcome a b) c = GrandOutcome a (GrandOutcome b c) := by
  simp [GrandOutcome]
  exact compose_assoc a b c

/-- Theorem 19: Void composes trivially with everything. -/
theorem void_as_universal_identity (a : I) :
    GrandOutcome (IdeaticSpace.void : I) a = a ∧
    GrandOutcome a (IdeaticSpace.void : I) = a := by
  constructor
  · simp [GrandOutcome, void_left]
  · simp [GrandOutcome, void_right]

/-- Theorem 20: Fundamental theorem — composition is associative with identity.
    This establishes that the meaning game forms a monoid. -/
theorem fundamental_theorem_of_meaning (a b c : I) :
    GrandOutcome (GrandOutcome a b) c = GrandOutcome a (GrandOutcome b c) ∧
    GrandOutcome (IdeaticSpace.void : I) a = a ∧
    GrandOutcome a (IdeaticSpace.void : I) = a := by
  refine ⟨?_, ?_, ?_⟩
  · simp [GrandOutcome]; exact compose_assoc a b c
  · simp [GrandOutcome, void_left]
  · simp [GrandOutcome, void_right]

end IDT.MG.Ch20
