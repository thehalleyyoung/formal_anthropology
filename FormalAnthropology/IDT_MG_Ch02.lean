import FormalAnthropology.IDT_Foundations

/-!
# The Meaning Game — Chapter 2: Repertoires and Feasible Strategy Sets

**Core claim.** Players have *repertoires* — lists of ideas constraining
their strategy choices. The feasible outcomes of a meaning game are
determined by the pairwise compositions of the two players' repertoires.

## Definitions

- `Repertoire := List I`
- `BoundedRepertoire d r` — every element has depth ≤ d
- `repertoireDepth r := depthSum r`
- `feasibleOutcomes r1 r2` — all pairwise compositions

## 17 Theorems, 0 Sorries
-/

set_option pp.unicode.fun true
set_option autoImplicit false
set_option linter.unusedVariables false

namespace IDT.MG.Ch2

open IDT IdeaticSpace

variable {I : Type*} [IdeaticSpace I]

/-! ## §1. Core Definitions -/

/-- A repertoire: the set of strategies available to a player. -/
abbrev Repertoire (I : Type*) := List I

/-- A bounded repertoire: every element has depth at most d. -/
def BoundedRepertoire (d : ℕ) (r : Repertoire I) : Prop :=
  ∀ (x : I), x ∈ r → IdeaticSpace.depth x ≤ d

/-- The total depth of a repertoire. -/
def repertoireDepth (r : Repertoire I) : ℕ := depthSum r

/-- All pairwise compositions of two repertoires. -/
def feasibleOutcomes (r1 r2 : Repertoire I) : List I :=
  r1.flatMap (fun s1 => r2.map (fun s2 => IdeaticSpace.compose s1 s2))

/-! ## §2. Boundedness Theorems -/

/-- Void can always be added without breaking the bounded property. -/
theorem void_in_any_repertoire (d : ℕ) (r : Repertoire I)
    (hr : BoundedRepertoire d r) :
    BoundedRepertoire d ((IdeaticSpace.void : I) :: r) := by
  intro x hx
  simp [List.mem_cons] at hx
  rcases hx with rfl | hx
  · simp [IdeaticSpace.depth_void]
  · exact hr x hx

/-- depthSum of a bounded repertoire ≤ length × d. -/
theorem bounded_repertoire_depth_sum (d : ℕ) (r : Repertoire I)
    (hr : BoundedRepertoire d r) :
    depthSum r ≤ r.length * d := by
  exact depthSum_bound r d hr

/-- Composing two elements from bounded repertoires stays within sum bound. -/
theorem bounded_compose_bounded (d1 d2 : ℕ) (a b : I)
    (ha : IdeaticSpace.depth a ≤ d1) (hb : IdeaticSpace.depth b ≤ d2) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤ d1 + d2 := by
  have h := depth_compose_le a b
  omega

/-- Every feasible outcome has bounded depth when repertoires are bounded. -/
theorem feasible_outcome_depth_bound (d : ℕ) (r1 r2 : Repertoire I)
    (h1 : BoundedRepertoire d r1) (h2 : BoundedRepertoire d r2)
    (x : I) (hx : x ∈ feasibleOutcomes r1 r2) :
    IdeaticSpace.depth x ≤ 2 * d := by
  simp [feasibleOutcomes, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨s1, hs1, s2, hs2, rfl⟩ := hx
  have ha := h1 s1 hs1
  have hb := h2 s2 hs2
  have h := depth_compose_le s1 s2
  omega

/-! ## §3. Empty and Singleton Repertoires -/

/-- Empty repertoire yields no feasible outcomes. -/
theorem empty_repertoire_no_outcomes (r2 : Repertoire I) :
    feasibleOutcomes ([] : Repertoire I) r2 = [] := by
  simp [feasibleOutcomes]

/-- Singleton repertoire outcomes = map compose over opponent's repertoire. -/
theorem singleton_repertoire_outcomes (s : I) (r2 : Repertoire I) :
    feasibleOutcomes [s] r2 = r2.map (fun s2 => IdeaticSpace.compose s s2) := by
  simp [feasibleOutcomes]

/-! ## §4. Void Repertoire Theorems -/

/-- Adding void preserves boundedness. -/
theorem bounded_repertoire_closed_under_void (d : ℕ) (r : Repertoire I)
    (hr : BoundedRepertoire d r) :
    BoundedRepertoire d ((IdeaticSpace.void : I) :: r) :=
  void_in_any_repertoire d r hr

/-- All-void repertoire: replicate void n times has depthSum 0. -/
theorem void_repertoire_depth_zero (n : ℕ) :
    depthSum (List.replicate n (IdeaticSpace.void : I)) = 0 :=
  depthSum_void_replicate n

/-- All-void repertoire produces void outcomes when opponent also plays void. -/
theorem all_void_repertoire_trivial (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (x : I)
    (hx : x ∈ feasibleOutcomes
      (List.replicate n (IdeaticSpace.void : I))
      (List.replicate m (IdeaticSpace.void : I))) :
    x = (IdeaticSpace.void : I) := by
  simp only [feasibleOutcomes, List.mem_flatMap, List.mem_map, List.mem_replicate] at hx
  obtain ⟨s1, hs1, s2, hs2, rfl⟩ := hx
  obtain ⟨_, rfl⟩ := hs1
  obtain ⟨_, rfl⟩ := hs2
  simp [void_left]

/-! ## §5. Depth and Monotonicity -/

/-- Sub-repertoire has ≤ depthSum (for prefix via cons). -/
theorem repertoire_depth_monotone (a : I) (r : Repertoire I) :
    depthSum r ≤ depthSum (a :: r) := by
  rw [depthSum_cons]
  omega

/-- Adding an element increases depthSum by its depth. -/
theorem extend_repertoire_depth (a : I) (r : Repertoire I) :
    depthSum (a :: r) = IdeaticSpace.depth a + depthSum r :=
  depthSum_cons a r

/-- All-atomic repertoire has depthSum ≤ length. -/
theorem atomic_repertoire_shallow (r : Repertoire I)
    (h : ∀ (x : I), x ∈ r → IdeaticSpace.atomic x) :
    depthSum r ≤ r.length := by
  have hb : ∀ (x : I), x ∈ r → IdeaticSpace.depth x ≤ 1 := by
    intro x hx; exact IdeaticSpace.depth_atomic x (h x hx)
  have := depthSum_bound r 1 hb
  omega

/-- Sublist of bounded repertoire is bounded. -/
theorem bounded_sublist_bounded (d : ℕ) (r : Repertoire I)
    (hr : BoundedRepertoire d r) (x : I) (hx : x ∈ r) :
    IdeaticSpace.depth x ≤ d :=
  hr x hx

/-! ## §6. Resonance and Coherence -/

/-- Outcomes from depth-d repertoires land in filtration 2d. -/
theorem outcome_in_filtration (d : ℕ) (r1 r2 : Repertoire I)
    (h1 : BoundedRepertoire d r1) (h2 : BoundedRepertoire d r2)
    (x : I) (hx : x ∈ feasibleOutcomes r1 r2) :
    x ∈ depthFiltration (2 * d) :=
  feasible_outcome_depth_bound d r1 r2 h1 h2 x hx

/-- If all items in a repertoire resonate with a, their compositions with
    any b also resonate with compose a b. -/
theorem repertoire_resonance_closure (a b : I) (r : Repertoire I)
    (h : ∀ (x : I), x ∈ r → IdeaticSpace.resonates x a) (x : I) (hx : x ∈ r) :
    IdeaticSpace.resonates (IdeaticSpace.compose x b) (IdeaticSpace.compose a b) :=
  resonance_compose_right (h x hx) b

/-- A coherent repertoire has pairwise resonance along its chain. -/
theorem coherent_repertoire_resonance (r : Repertoire I) (a b : I)
    (h : Coherent (a :: b :: r)) :
    IdeaticSpace.resonates a b :=
  h.1

end IDT.MG.Ch2
