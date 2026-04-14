import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Ideatic Diffusion Theory: Topology and Metric Structure

This file develops the **topological and metric** aspects of ideatic spaces.

## Key Insights

1. **Resonance Neighborhoods**: For each element `a`, the set `{b | resonates a b}`
   is its "neighborhood." Reflexive and symmetric but NOT transitive — the resulting
   quasi-topology is genuinely novel.

2. **Depth Filtration**: The sets `F_n = {a | depth a ≤ n}` form a nested filtration
   of the ideatic space, giving a natural stratification by complexity.

3. **Resonance Chains & Distance**: Chains of resonating elements define a
   pseudo-metric. The triangle inequality holds, giving ball-like structures.

4. **Literary Application**: "Distance between ideas" is formalized — ideas in the
   same genre are close, ideas across genres are far, and innovation means
   exploring new resonance balls.

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT_Topology

/-! ## §0. Local Axiom Class

We redefine the `IdeaticSpace` class locally to avoid cross-file imports.
The axioms are identical to `IDT.IdeaticSpace` in Foundations. -/

class IdeaticSpace (I : Type*) where
  compose : I → I → I
  void : I
  resonates : I → I → Prop
  depth : I → ℕ
  atomic : I → Prop
  compose_assoc : ∀ (a b c : I), compose (compose a b) c = compose a (compose b c)
  void_left : ∀ (a : I), compose void a = a
  void_right : ∀ (a : I), compose a void = a
  resonance_refl : ∀ (a : I), resonates a a
  resonance_symm : ∀ (a b : I), resonates a b → resonates b a
  resonance_compose : ∀ (a a' b b' : I),
    resonates a a' → resonates b b' → resonates (compose a b) (compose a' b')
  depth_void : depth void = 0
  depth_subadditive : ∀ (a b : I), depth (compose a b) ≤ depth a + depth b
  depth_atomic : ∀ (a : I), atomic a → depth a ≤ 1
  void_atomic : atomic void

variable {I : Type*} [IdeaticSpace I]

-- Convenience aliases
theorem resonance_refl (a : I) : IdeaticSpace.resonates a a :=
  IdeaticSpace.resonance_refl a

theorem resonance_symm {a b : I} (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates b a :=
  IdeaticSpace.resonance_symm a b h

theorem resonance_compose_left (c : I) {a b : I}
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (IdeaticSpace.compose c a) (IdeaticSpace.compose c b) :=
  IdeaticSpace.resonance_compose c c a b (resonance_refl c) h

theorem resonance_compose_right {a b : I}
    (h : IdeaticSpace.resonates a b) (c : I) :
    IdeaticSpace.resonates (IdeaticSpace.compose a c) (IdeaticSpace.compose b c) :=
  IdeaticSpace.resonance_compose a b c c h (resonance_refl c)

@[simp] theorem void_left (a : I) :
    IdeaticSpace.compose (IdeaticSpace.void : I) a = a :=
  IdeaticSpace.void_left a

@[simp] theorem void_right (a : I) :
    IdeaticSpace.compose a (IdeaticSpace.void : I) = a :=
  IdeaticSpace.void_right a

theorem compose_assoc (a b c : I) :
    IdeaticSpace.compose (IdeaticSpace.compose a b) c =
    IdeaticSpace.compose a (IdeaticSpace.compose b c) :=
  IdeaticSpace.compose_assoc a b c

/-! ## §1. Resonance Neighborhoods

The resonance neighborhood of an idea `a` is the set of all ideas that
resonate with it. This gives a reflexive, symmetric "nearness" structure. -/

section Neighborhoods

/-- The resonance neighborhood of an element: all ideas it evokes. -/
def Neighborhood (a : I) : Set I :=
  {b : I | IdeaticSpace.resonates a b}

/-- T1. Every element is in its own neighborhood. -/
theorem mem_neighborhood_self (a : I) : a ∈ Neighborhood a :=
  resonance_refl a

/-- T2. Neighborhoods are symmetric: if b is near a, then a is near b. -/
theorem neighborhood_symm {a b : I} (h : b ∈ Neighborhood a) :
    a ∈ Neighborhood b :=
  resonance_symm h

/-- T3. Membership in a neighborhood is equivalent to resonance. -/
theorem mem_neighborhood_iff (a b : I) :
    b ∈ Neighborhood a ↔ IdeaticSpace.resonates a b :=
  Iff.rfl

/-- T4. Left-composition maps neighborhoods into neighborhoods.
    If b resonates with a, then c·b resonates with c·a. -/
theorem neighborhood_compose_left (c : I) {a b : I}
    (h : b ∈ Neighborhood a) :
    IdeaticSpace.compose c b ∈ Neighborhood (IdeaticSpace.compose c a) :=
  resonance_compose_left c h

/-- T5. Right-composition maps neighborhoods into neighborhoods. -/
theorem neighborhood_compose_right {a b : I} (c : I)
    (h : b ∈ Neighborhood a) :
    IdeaticSpace.compose b c ∈ Neighborhood (IdeaticSpace.compose a c) :=
  resonance_compose_right h c

/-- T6. Bilateral composition maps neighborhoods: if a' ∈ N(a) and b' ∈ N(b),
    then compose(a',b') ∈ N(compose(a,b)). -/
theorem neighborhood_compose_bilateral {a a' b b' : I}
    (ha : a' ∈ Neighborhood a) (hb : b' ∈ Neighborhood b) :
    IdeaticSpace.compose a' b' ∈ Neighborhood (IdeaticSpace.compose a b) :=
  IdeaticSpace.resonance_compose a a' b b' ha hb

/-- T7. Void resonates with void (trivially). -/
theorem void_mem_neighborhood_void :
    (IdeaticSpace.void : I) ∈ Neighborhood (IdeaticSpace.void : I) :=
  resonance_refl IdeaticSpace.void

/-- The composed neighborhood: image of N(a) × N(b) under compose. -/
def ComposeNeighborhood (a b : I) : Set I :=
  {z : I | ∃ (x : I) (y : I), x ∈ Neighborhood a ∧ y ∈ Neighborhood b ∧
    z = IdeaticSpace.compose x y}

/-- T8. The composition of a with b is in ComposeNeighborhood(a, b). -/
theorem compose_mem_composeNeighborhood (a b : I) :
    IdeaticSpace.compose a b ∈ ComposeNeighborhood a b :=
  ⟨a, b, mem_neighborhood_self a, mem_neighborhood_self b, rfl⟩

/-- T9. ComposeNeighborhood(a, b) ⊆ Neighborhood(compose(a, b)). -/
theorem composeNeighborhood_sub_neighborhood (a b : I) :
    ComposeNeighborhood a b ⊆ Neighborhood (IdeaticSpace.compose a b) := by
  intro z ⟨x, y, hx, hy, hz⟩
  rw [hz]
  exact neighborhood_compose_bilateral hx hy

end Neighborhoods

/-! ## §2. Depth Filtration

The depth function gives a natural stratification. The sets
`DepthLevel n = {a | depth a ≤ n}` are nested and closed under
composition (with degree shift). -/

section DepthFiltration

/-- The n-th depth level: all ideas of depth at most n. -/
def DepthLevel (n : ℕ) : Set I :=
  {a : I | IdeaticSpace.depth a ≤ n}

/-- T10. Void is in DepthLevel 0. -/
theorem void_mem_depthLevel_zero :
    (IdeaticSpace.void : I) ∈ DepthLevel 0 := by
  show IdeaticSpace.depth (IdeaticSpace.void : I) ≤ 0
  rw [IdeaticSpace.depth_void]

/-- T11. Depth filtration is monotone: DepthLevel n ⊆ DepthLevel (n+1). -/
theorem depthLevel_mono {n m : ℕ} (h : n ≤ m) :
    (DepthLevel n : Set I) ⊆ DepthLevel m := by
  intro a (ha : IdeaticSpace.depth a ≤ n)
  exact le_trans ha h

/-- T12. Atomic elements are in DepthLevel 1. -/
theorem atomic_mem_depthLevel_one {a : I} (h : IdeaticSpace.atomic a) :
    a ∈ DepthLevel 1 :=
  IdeaticSpace.depth_atomic a h

/-- T13. Composition respects filtration with degree addition. -/
theorem compose_depthLevel {n m : ℕ} {a b : I}
    (ha : a ∈ DepthLevel n) (hb : b ∈ DepthLevel m) :
    IdeaticSpace.compose a b ∈ DepthLevel (n + m) :=
  le_trans (IdeaticSpace.depth_subadditive a b) (Nat.add_le_add ha hb)

/-- T14. Composing with void preserves depth level. -/
theorem compose_void_depthLevel {n : ℕ} {a : I}
    (ha : a ∈ DepthLevel n) :
    IdeaticSpace.compose a IdeaticSpace.void ∈ DepthLevel n := by
  rw [void_right]
  exact ha

/-- T15. Void-left composition preserves depth level. -/
theorem void_compose_depthLevel {n : ℕ} {a : I}
    (ha : a ∈ DepthLevel n) :
    IdeaticSpace.compose IdeaticSpace.void a ∈ DepthLevel n := by
  rw [void_left]
  exact ha

/-- T16. DepthLevel 0 is always nonempty (it contains void). -/
theorem depthLevel_zero_nonempty : (DepthLevel 0 : Set I).Nonempty :=
  ⟨IdeaticSpace.void, void_mem_depthLevel_zero⟩

/-- The graded component: elements of depth exactly n. -/
def GradedComponent (n : ℕ) : Set I :=
  {a : I | IdeaticSpace.depth a = n}

/-- T17. Void is in GradedComponent 0. -/
theorem void_mem_graded_zero :
    (IdeaticSpace.void : I) ∈ GradedComponent 0 :=
  IdeaticSpace.depth_void

/-- T18. GradedComponent n ⊆ DepthLevel n. -/
theorem graded_sub_depthLevel (n : ℕ) :
    (GradedComponent n : Set I) ⊆ DepthLevel n := by
  intro a (ha : IdeaticSpace.depth a = n)
  exact le_of_eq ha

/-- T19. GradedComponent n and GradedComponent m are disjoint when n ≠ m. -/
theorem graded_disjoint {n m : ℕ} (h : n ≠ m) :
    Disjoint (GradedComponent n : Set I) (GradedComponent m) := by
  rw [Set.disjoint_iff]
  intro a ⟨hn, hm⟩
  exact h (hn.symm.trans hm)

/-- T20. DepthLevel n = union of GradedComponent k for k ≤ n. -/
theorem depthLevel_eq_union (n : ℕ) :
    (DepthLevel n : Set I) = ⋃ (k : ℕ) (_ : k ≤ n), GradedComponent k := by
  ext a
  simp only [DepthLevel, GradedComponent, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro ha
    exact ⟨IdeaticSpace.depth a, ha, rfl⟩
  · rintro ⟨k, hk, hak⟩
    omega

end DepthFiltration

/-! ## §3. Resonance Chains and Connectivity

A resonance chain from `a` to `b` is a sequence `a ~ x₁ ~ x₂ ~ ... ~ b`
where adjacent elements resonate. The minimum chain length defines a
pseudo-metric on the ideatic space. -/

section ResonanceChains

/-- Reachable in at most n resonance steps. This is the core topological
    predicate: `ReachableIn a b n` means there is a chain of length ≤ n
    from a to b where adjacent elements resonate. -/
inductive ReachableIn : I → I → ℕ → Prop where
  | self (a : I) : ReachableIn a a 0
  | step {a b c : I} {n : ℕ} :
      IdeaticSpace.resonates a b → ReachableIn b c n → ReachableIn a c (n + 1)

/-- T21. Every element is reachable from itself in 0 steps. -/
theorem reachableIn_self (a : I) : ReachableIn a a 0 :=
  ReachableIn.self a

/-- T22. Direct resonance implies reachable in 1 step. -/
theorem reachableIn_one {a b : I} (h : IdeaticSpace.resonates a b) :
    ReachableIn a b 1 :=
  ReachableIn.step h (ReachableIn.self b)

/-- T23. Monotonicity: if reachable in n steps, then reachable in n+1 steps. -/
theorem reachableIn_mono {a b : I} {n : ℕ} (h : ReachableIn a b n) :
    ReachableIn a b (n + 1) := by
  induction h with
  | self x => exact ReachableIn.step (resonance_refl x) (ReachableIn.self x)
  | step hr _ ih => exact ReachableIn.step hr ih

/-- Weaken the step bound. -/
theorem reachableIn_le {a b : I} {n m : ℕ} (h : ReachableIn a b n) (hle : n ≤ m) :
    ReachableIn a b m := by
  induction hle with
  | refl => exact h
  | step _ ih => exact reachableIn_mono ih

/-- T24. Transitivity: chains can be concatenated.
    If a reaches b in n steps and b reaches c in m steps,
    then a reaches c in n + m steps. This is the triangle inequality. -/
theorem reachableIn_trans {a b c : I} {n m : ℕ}
    (h1 : ReachableIn a b n) (h2 : ReachableIn b c m) :
    ReachableIn a c (n + m) := by
  induction h1 with
  | self => simpa using h2
  | @step a' b' c' k hr _ ih =>
    have h3 := ih h2
    have heq : k + 1 + m = k + m + 1 := by omega
    rw [heq]
    exact ReachableIn.step hr h3

/-- T25. Symmetry: if a reaches b, then b reaches a (in the same number of steps). -/
theorem reachableIn_symm {a b : I} {n : ℕ} (h : ReachableIn a b n) :
    ReachableIn b a n := by
  induction h with
  | self => exact ReachableIn.self _
  | step hr _ ih =>
    have hba := reachableIn_one (resonance_symm hr)
    have := reachableIn_trans ih hba
    simp [Nat.add_comm] at this
    exact this

/-- T26. Left composition preserves reachability. -/
theorem reachableIn_compose_left (c : I) {a b : I} {n : ℕ}
    (h : ReachableIn a b n) :
    ReachableIn (IdeaticSpace.compose c a) (IdeaticSpace.compose c b) n := by
  induction h with
  | self => exact ReachableIn.self _
  | step hr _ ih =>
    exact ReachableIn.step (resonance_compose_left c hr) ih

/-- T27. Right composition preserves reachability. -/
theorem reachableIn_compose_right {a b : I} (c : I) {n : ℕ}
    (h : ReachableIn a b n) :
    ReachableIn (IdeaticSpace.compose a c) (IdeaticSpace.compose b c) n := by
  induction h with
  | self => exact ReachableIn.self _
  | step hr _ ih =>
    exact ReachableIn.step (resonance_compose_right hr c) ih

end ResonanceChains

/-! ## §4. Resonance Balls

The ball `B(a, n)` consists of all elements reachable from `a` in at most
`n` resonance steps. These balls satisfy monotonicity and nesting properties
analogous to metric balls, but the lack of transitivity for resonance
makes them strictly richer than standard metric balls. -/

section Balls

/-- The resonance ball of radius n centered at a. -/
def Ball (a : I) (n : ℕ) : Set I :=
  {b : I | ReachableIn a b n}

/-- T28. Every element is in its own ball of any radius. -/
theorem mem_ball_self (a : I) (n : ℕ) : a ∈ Ball a n := by
  exact reachableIn_le (reachableIn_self a) (Nat.zero_le n)

/-- T29. Ball monotonicity: Ball(a, n) ⊆ Ball(a, n+1). -/
theorem ball_mono (a : I) (n : ℕ) : Ball a n ⊆ Ball a (n + 1) := by
  intro b hb
  exact reachableIn_mono hb

/-- T30. General ball monotonicity. -/
theorem ball_mono_le (a : I) {n m : ℕ} (h : n ≤ m) :
    Ball a n ⊆ Ball a m := by
  intro b hb
  exact reachableIn_le hb h

/-- T31. Direct resonance implies membership in Ball(a, 1). -/
theorem resonance_mem_ball_one {a b : I}
    (h : IdeaticSpace.resonates a b) : b ∈ Ball a 1 :=
  reachableIn_one h

/-- T32. Ball symmetry: b ∈ Ball(a, n) implies a ∈ Ball(b, n). -/
theorem ball_symm {a b : I} {n : ℕ} (h : b ∈ Ball a n) :
    a ∈ Ball b n :=
  reachableIn_symm h

/-- T33. Triangle inequality for balls:
    if b ∈ Ball(a, n) and c ∈ Ball(b, m), then c ∈ Ball(a, n+m). -/
theorem ball_triangle {a b c : I} {n m : ℕ}
    (h1 : b ∈ Ball a n) (h2 : c ∈ Ball b m) :
    c ∈ Ball a (n + m) :=
  reachableIn_trans h1 h2

/-- T34. Ball(a, 0) = {a} when we only count exact reachability at 0. -/
theorem ball_zero_eq (a : I) : Ball a 0 = {a} := by
  ext b
  constructor
  · intro h
    cases h with
    | self => rfl
  · intro h
    rw [Set.mem_singleton_iff] at h
    rw [h]
    exact ReachableIn.self a

/-- T35. Left composition maps balls to balls. -/
theorem ball_compose_left (c : I) (a : I) (n : ℕ) :
    Set.image (IdeaticSpace.compose c) (Ball a n) ⊆
    Ball (IdeaticSpace.compose c a) n := by
  intro z ⟨b, hb, hbz⟩
  rw [← hbz]
  exact reachableIn_compose_left c hb

/-- T36. Right composition maps balls to balls. -/
theorem ball_compose_right (a : I) (c : I) (n : ℕ) :
    Set.image (fun x => IdeaticSpace.compose x c) (Ball a n) ⊆
    Ball (IdeaticSpace.compose a c) n := by
  intro z ⟨b, hb, hbz⟩
  rw [← hbz]
  exact reachableIn_compose_right c hb

/-- T37. Neighborhood equals Ball of radius 1. -/
theorem neighborhood_eq_ball_one (a : I) :
    Neighborhood a = Ball a 1 := by
  ext b
  constructor
  · intro h
    exact reachableIn_one h
  · intro h
    cases h with
    | step hr htail =>
      cases htail with
      | self => exact hr

end Balls

/-! ## §5. Connected Components and Connectivity

Two ideas are *connected* if there exists a finite resonance chain between them.
This is the transitive closure of resonance. -/

section Connectivity

/-- Two elements are connected if reachable in some finite number of steps. -/
def Connected (a b : I) : Prop :=
  ∃ n : ℕ, ReachableIn a b n

/-- T38. Connectivity is reflexive. -/
theorem connected_refl (a : I) : Connected a a :=
  ⟨0, reachableIn_self a⟩

/-- T39. Connectivity is symmetric. -/
theorem connected_symm {a b : I} (h : Connected a b) : Connected b a := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, reachableIn_symm hn⟩

/-- T40. Connectivity is transitive. -/
theorem connected_trans {a b c : I} (h1 : Connected a b) (h2 : Connected b c) :
    Connected a c := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, reachableIn_trans hn hm⟩

/-- T41. Direct resonance implies connectivity. -/
theorem resonance_to_connected {a b : I} (h : IdeaticSpace.resonates a b) :
    Connected a b :=
  ⟨1, reachableIn_one h⟩

/-- T42. Left composition preserves connectivity. -/
theorem connected_compose_left (c : I) {a b : I} (h : Connected a b) :
    Connected (IdeaticSpace.compose c a) (IdeaticSpace.compose c b) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, reachableIn_compose_left c hn⟩

/-- T43. Right composition preserves connectivity. -/
theorem connected_compose_right {a b : I} (c : I) (h : Connected a b) :
    Connected (IdeaticSpace.compose a c) (IdeaticSpace.compose b c) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, reachableIn_compose_right c hn⟩

/-- The connected component of an element. -/
def ConnectedComponent (a : I) : Set I :=
  {b : I | Connected a b}

/-- T44. Every element is in its own connected component. -/
theorem mem_connectedComponent_self (a : I) :
    a ∈ ConnectedComponent a :=
  connected_refl a

/-- T45. Connected components are symmetric. -/
theorem connectedComponent_symm {a b : I}
    (h : b ∈ ConnectedComponent a) : a ∈ ConnectedComponent b :=
  connected_symm h

/-- T46. Balls are subsets of connected components. -/
theorem ball_sub_connectedComponent (a : I) (n : ℕ) :
    Ball a n ⊆ ConnectedComponent a := by
  intro b hb
  exact ⟨n, hb⟩

/-- T47. Neighborhoods are subsets of connected components. -/
theorem neighborhood_sub_connectedComponent (a : I) :
    Neighborhood a ⊆ ConnectedComponent a := by
  rw [neighborhood_eq_ball_one]
  exact ball_sub_connectedComponent a 1

end Connectivity

/-! ## §6. Filtration Algebra

The depth filtration gives the ideatic space the structure of a filtered
monoid: composition respects filtration with degree addition. -/

section FiltrationAlgebra

/-- T48. Filtered monoid property: composition maps F_n × F_m → F_{n+m}. -/
theorem filteredMonoid_compose {n m : ℕ} {a b : I}
    (ha : a ∈ DepthLevel n) (hb : b ∈ DepthLevel m) :
    IdeaticSpace.compose a b ∈ DepthLevel (n + m) :=
  compose_depthLevel ha hb

/-- T49. The identity (void) is in F_0 — the unit respects the filtration. -/
theorem filteredMonoid_unit :
    (IdeaticSpace.void : I) ∈ DepthLevel 0 :=
  void_mem_depthLevel_zero

/-- Self-composition n times. -/
def selfCompose (a : I) : ℕ → I
  | 0 => IdeaticSpace.void
  | n + 1 => IdeaticSpace.compose (selfCompose a n) a

@[simp] theorem selfCompose_zero (a : I) :
    selfCompose a 0 = (IdeaticSpace.void : I) := rfl

theorem selfCompose_succ (a : I) (n : ℕ) :
    selfCompose a (n + 1) = IdeaticSpace.compose (selfCompose a n) a := rfl

/-- T50. Self-composition respects filtration: a^n ∈ F_{n·d} where d = depth a. -/
theorem selfCompose_depthLevel (a : I) (n : ℕ) :
    selfCompose a n ∈ DepthLevel (n * IdeaticSpace.depth a) := by
  induction n with
  | zero =>
    simp [selfCompose]
    exact void_mem_depthLevel_zero
  | succ k ih =>
    simp only [selfCompose_succ, Nat.succ_mul]
    exact compose_depthLevel ih (le_refl (IdeaticSpace.depth a))

/-- T51. Self-composition of void is always void. -/
@[simp] theorem selfCompose_void (n : ℕ) :
    selfCompose (IdeaticSpace.void : I) n = (IdeaticSpace.void : I) := by
  induction n with
  | zero => rfl
  | succ k ih => simp [selfCompose_succ, ih]

/-- T52. Self-composition 1 equals the element. -/
theorem selfCompose_one (a : I) : selfCompose a 1 = a := by
  simp [selfCompose_succ, selfCompose_zero]

/-- T53. Graded component 0 is always nonempty. -/
theorem graded_zero_nonempty : (GradedComponent 0 : Set I).Nonempty :=
  ⟨IdeaticSpace.void, void_mem_graded_zero⟩

/-- T54. Atomic elements are in GradedComponent 0 or GradedComponent 1. -/
theorem atomic_graded_01 {a : I} (h : IdeaticSpace.atomic a) :
    a ∈ GradedComponent 0 ∨ a ∈ GradedComponent 1 := by
  have hle := IdeaticSpace.depth_atomic a h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · left; exact h0
  · right; exact h1

end FiltrationAlgebra

/-! ## §7. Depth-Bounded Resonance

Interaction between the depth filtration and resonance neighborhoods:
neighborhoods within a fixed depth level. -/

section DepthBoundedResonance

/-- The depth-bounded neighborhood: resonant elements within depth level n. -/
def BoundedNeighborhood (a : I) (n : ℕ) : Set I :=
  Neighborhood a ∩ DepthLevel n

/-- T55. Bounded neighborhoods are subsets of neighborhoods. -/
theorem boundedNeighborhood_sub_neighborhood (a : I) (n : ℕ) :
    BoundedNeighborhood a n ⊆ Neighborhood a :=
  Set.inter_subset_left

/-- T56. Bounded neighborhoods are subsets of depth levels. -/
theorem boundedNeighborhood_sub_depthLevel (a : I) (n : ℕ) :
    BoundedNeighborhood a n ⊆ DepthLevel n :=
  Set.inter_subset_right

/-- T57. Bounded neighborhood monotonicity in the depth parameter. -/
theorem boundedNeighborhood_mono (a : I) {n m : ℕ} (h : n ≤ m) :
    BoundedNeighborhood a n ⊆ BoundedNeighborhood a m := by
  intro b ⟨hres, hdepth⟩
  exact ⟨hres, depthLevel_mono h hdepth⟩

/-- T58. If a ∈ DepthLevel n, then a ∈ BoundedNeighborhood(a, n). -/
theorem mem_boundedNeighborhood_self {a : I} {n : ℕ}
    (h : a ∈ DepthLevel n) : a ∈ BoundedNeighborhood a n :=
  ⟨mem_neighborhood_self a, h⟩

/-- T59. Void is in the bounded neighborhood of void at level 0. -/
theorem void_mem_boundedNeighborhood_zero :
    (IdeaticSpace.void : I) ∈ BoundedNeighborhood IdeaticSpace.void 0 :=
  ⟨void_mem_neighborhood_void, void_mem_depthLevel_zero⟩

/-- Depth-bounded ball: reachable within depth level n. -/
def BoundedBall (a : I) (radius : ℕ) (depthBound : ℕ) : Set I :=
  Ball a radius ∩ DepthLevel depthBound

/-- T60. Bounded balls are subsets of balls. -/
theorem boundedBall_sub_ball (a : I) (r d : ℕ) :
    BoundedBall a r d ⊆ Ball a r :=
  Set.inter_subset_left

/-- T61. Bounded ball monotonicity in radius. -/
theorem boundedBall_mono_radius (a : I) {r₁ r₂ : ℕ} (d : ℕ) (h : r₁ ≤ r₂) :
    BoundedBall a r₁ d ⊆ BoundedBall a r₂ d := by
  intro b ⟨hball, hdepth⟩
  exact ⟨ball_mono_le a h hball, hdepth⟩

/-- T62. Bounded ball monotonicity in depth. -/
theorem boundedBall_mono_depth (a : I) (r : ℕ) {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    BoundedBall a r d₁ ⊆ BoundedBall a r d₂ := by
  intro b ⟨hball, hdepth⟩
  exact ⟨hball, depthLevel_mono h hdepth⟩

end DepthBoundedResonance

/-! ## §8. Diffusion and Topological Dynamics

We study how diffusion operators interact with the topological structure.
A transmission map sends ideas to ideas; its topological properties
(contracting, expanding, filtration-preserving) characterize different
modes of cultural transmission. -/

section DiffusionTopology

/-- A transmission map on the ideatic space. -/
structure Transmission (I : Type*) [IdeaticSpace I] where
  map : I → I

/-- A transmission is conservative if it preserves identity. -/
def Transmission.IsConservative (T : Transmission I) : Prop :=
  ∀ (a : I), T.map a = a

/-- A transmission is depth-nonincreasing if it never increases depth. -/
def Transmission.IsDepthNonincreasing (T : Transmission I) : Prop :=
  ∀ (a : I), IdeaticSpace.depth (T.map a) ≤ IdeaticSpace.depth a

/-- A transmission is strictly contracting if it decreases depth for deep ideas. -/
def Transmission.IsStrictlyContracting (T : Transmission I) (threshold : ℕ) : Prop :=
  ∀ (a : I), IdeaticSpace.depth a > threshold →
    IdeaticSpace.depth (T.map a) < IdeaticSpace.depth a

/-- A transmission preserves resonance if resonant pairs map to resonant pairs. -/
def Transmission.PreservesResonance (T : Transmission I) : Prop :=
  ∀ (a b : I), IdeaticSpace.resonates a b →
    IdeaticSpace.resonates (T.map a) (T.map b)

/-- T63. Conservative transmission preserves depth level membership. -/
theorem conservative_preserves_depthLevel {T : Transmission I}
    (hT : T.IsConservative) {a : I} {n : ℕ} (ha : a ∈ DepthLevel n) :
    T.map a ∈ DepthLevel n := by
  rw [hT a]
  exact ha

/-- T64. Conservative transmission preserves neighborhoods. -/
theorem conservative_preserves_neighborhood {T : Transmission I}
    (hT : T.IsConservative) {a b : I} (h : b ∈ Neighborhood a) :
    T.map b ∈ Neighborhood (T.map a) := by
  rw [hT a, hT b]
  exact h

/-- T65. Depth-nonincreasing transmission maps F_n into F_n. -/
theorem nonincreasing_preserves_depthLevel {T : Transmission I}
    (hT : T.IsDepthNonincreasing) {a : I} {n : ℕ} (ha : a ∈ DepthLevel n) :
    T.map a ∈ DepthLevel n :=
  le_trans (hT a) ha

/-- T66. Resonance-preserving transmission maps neighborhoods to neighborhoods. -/
theorem resonance_preserving_maps_neighborhoods {T : Transmission I}
    (hT : T.PreservesResonance) {a b : I} (h : b ∈ Neighborhood a) :
    T.map b ∈ Neighborhood (T.map a) :=
  hT a b h

/-- T67. Resonance-preserving transmission maps balls to balls. -/
theorem resonance_preserving_maps_balls {T : Transmission I}
    (hT : T.PreservesResonance) {a b : I} {n : ℕ}
    (h : b ∈ Ball a n) : T.map b ∈ Ball (T.map a) n := by
  induction h with
  | self => exact mem_ball_self _ _
  | step hr _ ih => exact ReachableIn.step (hT _ _ hr) ih

/-- T68. Resonance-preserving transmission preserves connectivity. -/
theorem resonance_preserving_connected {T : Transmission I}
    (hT : T.PreservesResonance) {a b : I} (h : Connected a b) :
    Connected (T.map a) (T.map b) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, resonance_preserving_maps_balls hT hn⟩

/-- n-fold iteration of a transmission. -/
def Transmission.iterate (T : Transmission I) : ℕ → I → I
  | 0, a => a
  | n + 1, a => T.map (T.iterate n a)

/-- T69. Zero iterations is identity. -/
theorem Transmission.iterate_zero (T : Transmission I) (a : I) :
    T.iterate 0 a = a := rfl

/-- T70. Depth-nonincreasing transmissions yield monotone depth sequences. -/
theorem iterate_depth_nonincreasing {T : Transmission I}
    (hT : T.IsDepthNonincreasing) (a : I) (n : ℕ) :
    IdeaticSpace.depth (T.iterate n a) ≤ IdeaticSpace.depth a := by
  induction n with
  | zero => exact le_refl _
  | succ k ih => exact le_trans (hT _) ih

/-- T71. Iterating a conservative transmission is identity. -/
theorem conservative_iterate {T : Transmission I}
    (hT : T.IsConservative) (a : I) (n : ℕ) :
    T.iterate n a = a := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show T.map (T.iterate k a) = a
    rw [ih, hT]

end DiffusionTopology

/-! ## §9. Resonance Diameter and Influence Radius

The diameter of a set measures how "spread out" it is in resonance distance.
The influence radius of an idea measures how far its resonance extends. -/

section DiameterInfluence

/-- A set has diameter at most d if every pair is reachable in d steps. -/
def HasDiameter (S : Set I) (d : ℕ) : Prop :=
  ∀ (a b : I), a ∈ S → b ∈ S → ReachableIn a b d

/-- T72. Singletons have diameter 0. -/
theorem singleton_diameter_zero (a : I) : HasDiameter ({a} : Set I) 0 := by
  intro x y hx hy
  rw [Set.mem_singleton_iff] at hx hy
  rw [hx, hy]
  exact ReachableIn.self a

/-- T73. Balls have bounded diameter: Ball(a, n) has diameter at most 2n. -/
theorem ball_diameter (a : I) (n : ℕ) : HasDiameter (Ball a n) (n + n) := by
  intro x y hx hy
  have hxa := reachableIn_symm hx
  exact reachableIn_trans hxa hy

/-- An element has influence radius at least r if its ball of radius r
    intersects every depth level up to some bound. -/
def InfluenceRadius (a : I) (r : ℕ) : Prop :=
  ∀ (b : I), IdeaticSpace.resonates a b → b ∈ Ball a r

/-- T74. Every element has influence radius at least 1 (from reflexivity). -/
theorem influence_radius_one (a : I) : InfluenceRadius a 1 := by
  intro b hb
  exact reachableIn_one hb

/-- T75. Influence radius is monotone. -/
theorem influence_radius_mono {a : I} {r s : ℕ} (h : r ≤ s)
    (hr : InfluenceRadius a r) : InfluenceRadius a s := by
  intro b hb
  exact ball_mono_le a h (hr b hb)

/-- The set of all elements reachable from some element of a set S. -/
def ReachableFrom (S : Set I) (n : ℕ) : Set I :=
  {b : I | ∃ a : I, a ∈ S ∧ ReachableIn a b n}

/-- T76. S ⊆ ReachableFrom(S, n) for any n. -/
theorem subset_reachableFrom (S : Set I) (n : ℕ) :
    S ⊆ ReachableFrom S n := by
  intro a ha
  exact ⟨a, ha, reachableIn_le (reachableIn_self a) (Nat.zero_le n)⟩

/-- T77. ReachableFrom is monotone in the radius. -/
theorem reachableFrom_mono (S : Set I) {n m : ℕ} (h : n ≤ m) :
    ReachableFrom S n ⊆ ReachableFrom S m := by
  intro b ⟨a, ha, hab⟩
  exact ⟨a, ha, reachableIn_le hab h⟩

end DiameterInfluence

/-! ## §10. Literary Application: Genre Distance

We formalize the notion of "genre distance" between ideas. Two ideas in the
same genre are close (small resonance distance); ideas in different genres
are far. Innovation is modeled as exploring a new ball. -/

section GenreDistance

/-- A genre is a connected component — a maximal set of transitively
    resonating ideas. Two ideas are "in the same genre" iff connected. -/
def SameGenre (a b : I) : Prop := Connected a b

/-- T78. SameGenre is reflexive. -/
theorem sameGenre_refl (a : I) : SameGenre a a :=
  connected_refl a

/-- T79. SameGenre is symmetric. -/
theorem sameGenre_symm {a b : I} (h : SameGenre a b) : SameGenre b a :=
  connected_symm h

/-- T80. SameGenre is transitive. -/
theorem sameGenre_trans {a b c : I} (h1 : SameGenre a b) (h2 : SameGenre b c) :
    SameGenre a c :=
  connected_trans h1 h2

/-- T81. Direct resonance implies same genre. -/
theorem resonance_same_genre {a b : I} (h : IdeaticSpace.resonates a b) :
    SameGenre a b :=
  resonance_to_connected h

/-- An idea is "innovative" relative to a set if it's not in the set's
    reachable region within a given radius. -/
def IsInnovative (a : I) (S : Set I) (radius : ℕ) : Prop :=
  a ∉ ReachableFrom S radius

/-- T82. If a is innovative at radius r, it's innovative at any smaller radius. -/
theorem innovative_anti_mono {a : I} {S : Set I} {r s : ℕ}
    (hrs : s ≤ r) (h : IsInnovative a S r) : IsInnovative a S s := by
  intro hmem
  exact h (reachableFrom_mono S hrs hmem)

/-- A tradition is a set closed under resonance — if an idea is in the
    tradition and it resonates with another, that other idea is also in
    the tradition. -/
def IsTradition (S : Set I) : Prop :=
  ∀ (a b : I), a ∈ S → IdeaticSpace.resonates a b → b ∈ S

/-- T83. Connected components are traditions. -/
theorem connectedComponent_is_tradition (a : I) :
    IsTradition (ConnectedComponent a) := by
  intro x y hx hxy
  exact connected_trans hx (resonance_to_connected hxy)

/-- T84. A tradition contains the full neighborhood of each of its members. -/
theorem tradition_contains_neighborhoods {S : Set I} (hS : IsTradition S)
    {a : I} (ha : a ∈ S) : Neighborhood a ⊆ S := by
  intro b hb
  exact hS a b ha hb

/-- T85. A tradition contains the ball of radius n around each member. -/
theorem tradition_contains_balls {S : Set I} (hS : IsTradition S)
    {a : I} (ha : a ∈ S) (n : ℕ) : Ball a n ⊆ S := by
  intro b hb
  induction hb with
  | self => exact ha
  | @step x y z k hr _ ih =>
    exact ih (hS x y ha hr)

end GenreDistance

/-! ## §11. Topological Depth Dynamics

How iterated transmission affects the depth structure. Key theorem:
depth-nonincreasing transmissions eventually stabilize. -/

section DepthDynamics

/-- The depth sequence: depth of T^n(a). -/
def depthSequence (T : Transmission I) (a : I) (n : ℕ) : ℕ :=
  IdeaticSpace.depth (T.iterate n a)

/-- T86. For depth-nonincreasing T, the depth sequence is nonincreasing. -/
theorem depthSequence_nonincreasing {T : Transmission I}
    (hT : T.IsDepthNonincreasing) (a : I) (n : ℕ) :
    depthSequence T a (n + 1) ≤ depthSequence T a n := by
  show IdeaticSpace.depth (T.map (T.iterate n a)) ≤ IdeaticSpace.depth (T.iterate n a)
  exact hT _

/-- T87. The depth sequence is bounded below by 0 (trivially, since ℕ). -/
theorem depthSequence_nonneg (T : Transmission I) (a : I) (n : ℕ) :
    0 ≤ depthSequence T a n :=
  Nat.zero_le _

/-- T88. Depth-nonincreasing transmission maps GradedComponent n into
    DepthLevel n. -/
theorem nonincreasing_graded_to_filtered {T : Transmission I}
    (hT : T.IsDepthNonincreasing) {a : I} {n : ℕ}
    (ha : a ∈ GradedComponent n) :
    T.map a ∈ DepthLevel n := by
  show IdeaticSpace.depth (T.map a) ≤ n
  calc IdeaticSpace.depth (T.map a) ≤ IdeaticSpace.depth a := hT a
    _ = n := ha

/-- T89. For a depth-nonincreasing resonance-preserving transmission,
    bounded balls are mapped into bounded balls. -/
theorem nonincreasing_preserves_boundedBall {T : Transmission I}
    (hT_depth : T.IsDepthNonincreasing) (hT_res : T.PreservesResonance)
    {a : I} {r d : ℕ} {b : I} (hb : b ∈ BoundedBall a r d) :
    T.map b ∈ BoundedBall (T.map a) r d := by
  obtain ⟨hball, hdepth⟩ := hb
  exact ⟨resonance_preserving_maps_balls hT_res hball,
         nonincreasing_preserves_depthLevel hT_depth hdepth⟩

end DepthDynamics

/-! ## §12. Composition Topology

The topology induced by composition: how composing with a fixed element
acts as a "translation" on the topological structure. -/

section CompositionTopology

/-- Left translation by c. -/
def leftTranslate (c : I) : I → I :=
  fun a => IdeaticSpace.compose c a

/-- Right translation by c. -/
def rightTranslate (c : I) : I → I :=
  fun a => IdeaticSpace.compose a c

/-- T90. Left translation preserves resonance. -/
theorem leftTranslate_preserves_resonance (c : I) {a b : I}
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (leftTranslate c a) (leftTranslate c b) :=
  resonance_compose_left c h

/-- T91. Right translation preserves resonance. -/
theorem rightTranslate_preserves_resonance (c : I) {a b : I}
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (rightTranslate c a) (rightTranslate c b) :=
  resonance_compose_right h c

/-- T92. Left translation by void is identity. -/
theorem leftTranslate_void (a : I) :
    leftTranslate (IdeaticSpace.void : I) a = a :=
  void_left a

/-- T93. Right translation by void is identity. -/
theorem rightTranslate_void (a : I) :
    rightTranslate (IdeaticSpace.void : I) a = a :=
  void_right a

/-- T94. Left translation maps balls to balls. -/
theorem leftTranslate_ball (c : I) (a : I) (n : ℕ) :
    Set.image (leftTranslate c) (Ball a n) ⊆
    Ball (leftTranslate c a) n :=
  ball_compose_left c a n

/-- T95. Left translation increases depth by at most depth(c). -/
theorem leftTranslate_depth (c : I) (a : I) :
    IdeaticSpace.depth (leftTranslate c a) ≤ IdeaticSpace.depth c + IdeaticSpace.depth a :=
  IdeaticSpace.depth_subadditive c a

/-- T96. Right translation increases depth by at most depth(c). -/
theorem rightTranslate_depth (c : I) (a : I) :
    IdeaticSpace.depth (rightTranslate c a) ≤ IdeaticSpace.depth a + IdeaticSpace.depth c :=
  IdeaticSpace.depth_subadditive a c

/-- T97. Composing translations: left then right. -/
theorem compose_translations (c d a : I) :
    rightTranslate d (leftTranslate c a) =
    IdeaticSpace.compose (IdeaticSpace.compose c a) d := rfl

/-- T98. Translation preserves connectivity. -/
theorem leftTranslate_preserves_connected (c : I) {a b : I}
    (h : Connected a b) :
    Connected (leftTranslate c a) (leftTranslate c b) :=
  connected_compose_left c h

end CompositionTopology

/-! ## §13. Neighborhood Algebra

Algebraic operations on neighborhoods: unions, intersections, and
composition of neighborhood sets. -/

section NeighborhoodAlgebra

/-- The intersection of two neighborhoods. -/
def NeighborhoodInter (a b : I) : Set I :=
  Neighborhood a ∩ Neighborhood b

/-- T99. If c ∈ NeighborhoodInter(a, b), then c resonates with both a and b. -/
theorem mem_neighborhoodInter_iff {a b c : I} :
    c ∈ NeighborhoodInter a b ↔
    (IdeaticSpace.resonates a c ∧ IdeaticSpace.resonates b c) :=
  Iff.rfl

/-- The union of two neighborhoods. -/
def NeighborhoodUnion (a b : I) : Set I :=
  Neighborhood a ∪ Neighborhood b

/-- T100. Neighborhoods are subsets of their union. -/
theorem neighborhood_sub_union_left (a b : I) :
    Neighborhood a ⊆ NeighborhoodUnion a b :=
  Set.subset_union_left

/-- T101. The compose-neighborhood: N(a) composed with N(b). -/
def composeNeighborhoods (a b : I) : Set I :=
  {z : I | ∃ (x : I) (y : I),
    IdeaticSpace.resonates a x ∧ IdeaticSpace.resonates b y ∧
    z = IdeaticSpace.compose x y}

/-- T102. compose(a,b) is in composeNeighborhoods(a,b). -/
theorem compose_mem_composeNeighborhoods (a b : I) :
    IdeaticSpace.compose a b ∈ composeNeighborhoods a b :=
  ⟨a, b, resonance_refl a, resonance_refl b, rfl⟩

/-- T103. composeNeighborhoods(a,b) ⊆ Neighborhood(compose(a,b)). -/
theorem composeNeighborhoods_sub (a b : I) :
    composeNeighborhoods a b ⊆ Neighborhood (IdeaticSpace.compose a b) := by
  intro z ⟨x, y, hax, hby, hzeq⟩
  rw [hzeq]
  exact IdeaticSpace.resonance_compose a x b y hax hby

/-- T104. Neighborhood of void contains void. -/
theorem void_in_void_neighborhood :
    (IdeaticSpace.void : I) ∈ Neighborhood (IdeaticSpace.void : I) :=
  resonance_refl _

end NeighborhoodAlgebra

/-! ## §14. Chain Properties

Detailed properties of resonance chains and their interaction
with composition and depth. -/

section ChainProperties

/-- T105. Two-step reachability: a ~ x ~ b means a reaches b in 2 steps. -/
theorem reachable_two_step {a x b : I}
    (h1 : IdeaticSpace.resonates a x) (h2 : IdeaticSpace.resonates x b) :
    ReachableIn a b 2 :=
  ReachableIn.step h1 (ReachableIn.step h2 (ReachableIn.self b))

/-- T106. If a reaches b in n steps and they are composed with c,
    then c·a reaches c·b in n steps. -/
theorem reachable_under_left_compose (c : I) {a b : I} {n : ℕ}
    (h : ReachableIn a b n) :
    ReachableIn (IdeaticSpace.compose c a) (IdeaticSpace.compose c b) n :=
  reachableIn_compose_left c h

/-- T107. Reachability from void: void reaches a in n steps iff a is reachable
    from void. This relates to "how many resonance jumps from silence." -/
theorem reachable_from_void_ball (n : ℕ) :
    Ball (IdeaticSpace.void : I) n =
    {a : I | ReachableIn IdeaticSpace.void a n} := rfl

/-- T108. Void is in every ball centered at void. -/
theorem void_mem_void_ball (n : ℕ) :
    (IdeaticSpace.void : I) ∈ Ball (IdeaticSpace.void : I) n :=
  mem_ball_self _ n

/-- T109. If a reaches b in n steps, compose(a,a) reaches compose(b,b)
    in n steps (by bilateral composition). -/
theorem reachable_compose_self {a b : I} {n : ℕ}
    (h : ReachableIn a b n) :
    ReachableIn (IdeaticSpace.compose a a) (IdeaticSpace.compose b b) n := by
  induction h with
  | self => exact ReachableIn.self _
  | step hr _ ih =>
    have : IdeaticSpace.resonates
        (IdeaticSpace.compose _ _) (IdeaticSpace.compose _ _) :=
      IdeaticSpace.resonance_compose _ _ _ _ hr hr
    exact ReachableIn.step this ih

/-- T110. Self-composition preserves connectivity. -/
theorem selfCompose_connected {a b : I} (h : Connected a b) (n : ℕ) :
    Connected (selfCompose a n) (selfCompose b n) := by
  induction n with
  | zero => exact connected_refl _
  | succ k ih =>
    simp only [selfCompose_succ]
    exact connected_trans
      (connected_compose_right _ ih)
      (connected_compose_left _ h)

end ChainProperties

/-! ## §15. Topological Invariants

Properties that are preserved by resonance-preserving maps. -/

section TopologicalInvariants

/-- A map between ideatic spaces is a resonance morphism if it preserves
    resonance. -/
def IsResonanceMorphism (f : I → I) : Prop :=
  ∀ (a b : I), IdeaticSpace.resonates a b → IdeaticSpace.resonates (f a) (f b)

/-- T111. Identity is a resonance morphism. -/
theorem id_is_resonanceMorphism : IsResonanceMorphism (id : I → I) := by
  intro a b h
  exact h

/-- T112. Composition of resonance morphisms is a resonance morphism. -/
theorem comp_resonanceMorphism {f g : I → I}
    (hf : IsResonanceMorphism f) (hg : IsResonanceMorphism g) :
    IsResonanceMorphism (f ∘ g) := by
  intro a b h
  exact hf _ _ (hg _ _ h)

/-- T113. Resonance morphisms map neighborhoods into neighborhoods. -/
theorem resonanceMorphism_neighborhood {f : I → I} (hf : IsResonanceMorphism f)
    {a b : I} (h : b ∈ Neighborhood a) :
    f b ∈ Neighborhood (f a) :=
  hf a b h

/-- T114. Resonance morphisms preserve reachability. -/
theorem resonanceMorphism_reachable {f : I → I} (hf : IsResonanceMorphism f)
    {a b : I} {n : ℕ} (h : ReachableIn a b n) :
    ReachableIn (f a) (f b) n := by
  induction h with
  | self => exact ReachableIn.self _
  | step hr _ ih => exact ReachableIn.step (hf _ _ hr) ih

/-- T115. Resonance morphisms preserve connectivity. -/
theorem resonanceMorphism_connected {f : I → I} (hf : IsResonanceMorphism f)
    {a b : I} (h : Connected a b) :
    Connected (f a) (f b) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, resonanceMorphism_reachable hf hn⟩

/-- T116. Resonance morphisms preserve genre. -/
theorem resonanceMorphism_sameGenre {f : I → I} (hf : IsResonanceMorphism f)
    {a b : I} (h : SameGenre a b) :
    SameGenre (f a) (f b) :=
  resonanceMorphism_connected hf h

/-- T117. Left translation is a resonance morphism. -/
theorem leftTranslate_is_morphism (c : I) :
    IsResonanceMorphism (leftTranslate c : I → I) := by
  intro a b h
  exact leftTranslate_preserves_resonance c h

/-- T118. Right translation is a resonance morphism. -/
theorem rightTranslate_is_morphism (c : I) :
    IsResonanceMorphism (rightTranslate c : I → I) := by
  intro a b h
  exact rightTranslate_preserves_resonance c h

end TopologicalInvariants

end IDT_Topology
