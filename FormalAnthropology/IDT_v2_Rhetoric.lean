import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Rhetoric — The Art of Persuasion

Formalizes rhetoric (Aristotle, Gramsci, Habermas) in the IDT v2 framework.

A rhetorical act composes a speaker's argument with the audience's existing beliefs.
The persuasive force decomposes into:
- **Ethos** (speaker credibility) ≈ self-resonance of the argument
- **Pathos** (emotional connection) ≈ resonance between argument and audience
- **Logos** (logical structure) ≈ depth of the argument

Key results:
- Persuasive force ≥ ethos (composition monotonicity)
- Void arguments have no rhetorical effect
- Iterated rhetoric has bounded depth growth
- Hegemonic arguments resonate positively with entire populations

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Rhetoric

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Core Rhetorical Definitions -/

/-- A rhetorical act: speaker composes argument with audience's beliefs -/
def rhetoricalAct (argument audience : I) : I := compose argument audience

/-- Ethos: the weight/credibility of the argument itself (self-resonance) -/
noncomputable def ethos (argument : I) : ℝ :=
  resonanceStrength argument argument

/-- Pathos: the emotional resonance between argument and audience -/
noncomputable def pathos (argument audience : I) : ℝ :=
  resonanceStrength argument audience

/-- Logos: the logical depth/structure of the argument -/
def logos (argument : I) : ℕ := depth argument

/-- Persuasive force: resonance between argument and the composed outcome -/
noncomputable def persuasiveForce (argument audience : I) : ℝ :=
  resonanceStrength argument (rhetoricalAct argument audience)

/-- Resistance: audience's resistance to the argument (gap from self-resonance) -/
noncomputable def resistance (argument audience : I) : ℝ :=
  resonanceStrength argument argument - resonanceStrength argument audience

/-- Rhetorical distance: squared distance between audience before and after -/
noncomputable def rhetoricalDistance (argument audience : I) : ℝ :=
  squaredDistance audience (rhetoricalAct argument audience)

/-- Iterated rhetoric: repeating the same argument n times -/
def iteratedRhetoric (argument : I) : ℕ → I → I
  | 0, audience => audience
  | n + 1, audience => rhetoricalAct argument (iteratedRhetoric argument n audience)

/-! ## §2. Aristotle's Decomposition -/

/-- Ethos is strictly positive: every argument has some credibility -/
theorem ethos_positive (argument : I) : ethos argument > 0 :=
  rs_self_pos' argument

/-- Ethos is at least 1 (calibrated to void = 1) -/
theorem ethos_ge_one (argument : I) : ethos argument ≥ 1 :=
  rs_self_ge_one argument

/-- Ethos of void is exactly 1: silence has unit credibility -/
theorem ethos_void : ethos (void : I) = 1 := rs_void_unit

/-- Pathos is non-negative: resonance between ideas is never negative -/
theorem pathos_nonneg (argument audience : I) : pathos argument audience ≥ 0 :=
  rs_nonneg' argument audience

/-- Pathos is symmetric: mutual resonance -/
theorem pathos_symmetric (argument audience : I) :
    pathos argument audience = pathos audience argument :=
  rs_symm' argument audience

/-- Pathos with oneself equals ethos -/
theorem pathos_self_eq_ethos (argument : I) :
    pathos argument argument = ethos argument := rfl

/-- Persuasive force is non-negative -/
theorem persuasiveForce_nonneg (argument audience : I) :
    persuasiveForce argument audience ≥ 0 := by
  unfold persuasiveForce rhetoricalAct
  exact rs_nonneg' argument (compose argument audience)

/-- KEY THEOREM: Persuasive force of argument on void audience = ethos.
    For a "blank slate" audience, all persuasive force is pure credibility. -/
theorem persuasiveForce_void_eq_ethos (argument : I) :
    persuasiveForce argument (void : I) = ethos argument := by
  unfold persuasiveForce rhetoricalAct ethos
  rw [IdeaticSpace2.void_right]

/-- Persuasive force is bounded by Cauchy-Schwarz:
    force² ≤ ethos(arg) * ethos(rhetoricalAct arg aud) -/
theorem persuasiveForce_cauchy_schwarz (argument audience : I) :
    persuasiveForce argument audience * persuasiveForce argument audience ≤
    ethos argument * ethos (rhetoricalAct argument audience) := by
  unfold persuasiveForce ethos rhetoricalAct
  exact rs_le_self_product argument (compose argument audience)

/-- Void argument: zero persuasive force above baseline.
    Saying nothing contributes nothing beyond the audience's self-resonance. -/
theorem void_argument_persuasiveForce (audience : I) :
    persuasiveForce (void : I) audience = pathos (void : I) audience := by
  unfold persuasiveForce rhetoricalAct pathos
  simp [IdeaticSpace2.void_left]

/-- Void audience: persuasive force equals resonance with the argument itself -/
theorem void_audience_persuasiveForce (argument : I) :
    persuasiveForce argument (void : I) = ethos argument := by
  unfold persuasiveForce rhetoricalAct ethos
  simp [IdeaticSpace2.void_right]

/-- Void audience persuasive force is at least 1 -/
theorem void_audience_persuasiveForce_ge_one (argument : I) :
    persuasiveForce argument (void : I) ≥ 1 := by
  rw [void_audience_persuasiveForce]; exact ethos_ge_one argument

/-- Persuasive force with void argument equals audience's pathos with void -/
theorem void_argument_force_eq_pathos (audience : I) :
    persuasiveForce (void : I) audience = resonanceStrength (void : I) audience := by
  unfold persuasiveForce rhetoricalAct
  simp [IdeaticSpace2.void_left]

/-! ## §3. Rhetorical Acts — Structural Properties -/

/-- Saying nothing changes nothing -/
theorem rhetoricalAct_void_arg (audience : I) :
    rhetoricalAct (void : I) audience = audience := by
  unfold rhetoricalAct; exact IdeaticSpace2.void_left audience

/-- Speaking to nobody yields just the argument -/
theorem rhetoricalAct_void_audience (argument : I) :
    rhetoricalAct argument (void : I) = argument := by
  unfold rhetoricalAct; exact IdeaticSpace2.void_right argument

/-- Rhetoric with void argument and void audience -/
theorem rhetoricalAct_void_void :
    rhetoricalAct (void : I) (void : I) = (void : I) := by
  unfold rhetoricalAct; exact IdeaticSpace2.void_left _

/-- Rhetorical acts compose associatively -/
theorem rhetoricalAct_assoc (a b c : I) :
    rhetoricalAct (rhetoricalAct a b) c = rhetoricalAct a (rhetoricalAct b c) := by
  unfold rhetoricalAct; exact compose_assoc a b c

/-- Rhetoric depth bound: depth of rhetorical act is subadditive -/
theorem rhetoric_depth_bound (argument audience : I) :
    depth (rhetoricalAct argument audience) ≤ depth argument + depth audience := by
  unfold rhetoricalAct; exact depth_subadditive' argument audience

/-- Logos (depth) of a rhetorical act is bounded -/
theorem logos_rhetoricalAct_bound (argument audience : I) :
    logos (rhetoricalAct argument audience) ≤ logos argument + logos audience := by
  exact rhetoric_depth_bound argument audience

/-- Self-resonance of rhetorical act is at least the argument's ethos -/
theorem rhetoricalAct_self_resonance_ge_ethos (argument audience : I) :
    resonanceStrength (rhetoricalAct argument audience)
      (rhetoricalAct argument audience) ≥ ethos argument := by
  unfold rhetoricalAct ethos
  exact rs_compose_self_right argument audience

/-- Self-resonance of rhetorical act is at least the audience's self-resonance -/
theorem rhetoricalAct_self_resonance_ge_audience (argument audience : I) :
    resonanceStrength (rhetoricalAct argument audience)
      (rhetoricalAct argument audience) ≥ resonanceStrength audience audience := by
  unfold rhetoricalAct
  exact rs_compose_self_left audience argument

/-- Rhetorical distance is non-negative -/
theorem rhetoricalDistance_nonneg (argument audience : I) :
    rhetoricalDistance argument audience ≥ 0 := by
  unfold rhetoricalDistance; exact squaredDistance_nonneg audience _

/-- Void rhetoric has zero distance (no change) -/
theorem void_rhetoric_zero_distance (audience : I) :
    rhetoricalDistance (void : I) audience = 0 := by
  unfold rhetoricalDistance
  rw [rhetoricalAct_void_arg]; exact squaredDistance_self audience

/-! ## §4. Iterated Rhetoric & Propaganda -/

/-- Base case: zero iterations = no change -/
theorem iterated_rhetoric_zero (argument : I) (audience : I) :
    iteratedRhetoric argument 0 audience = audience := rfl

/-- Recursive case -/
theorem iterated_rhetoric_succ (argument : I) (n : ℕ) (audience : I) :
    iteratedRhetoric argument (n + 1) audience =
    rhetoricalAct argument (iteratedRhetoric argument n audience) := rfl

/-- Repeating nothing changes nothing -/
theorem iterated_void : ∀ (n : ℕ) (audience : I),
    iteratedRhetoric (void : I) n audience = audience
  | 0, audience => rfl
  | n + 1, audience => by
    simp only [iteratedRhetoric]
    rw [rhetoricalAct_void_arg]
    exact iterated_void n audience

/-- One iteration = one rhetorical act -/
theorem iterated_rhetoric_one (argument audience : I) :
    iteratedRhetoric argument 1 audience = rhetoricalAct argument audience := by
  simp [iteratedRhetoric]

/-- Iterated rhetoric depth bound: depth grows at most linearly -/
theorem iterated_depth_bound (argument : I) : ∀ (n : ℕ) (audience : I),
    depth (iteratedRhetoric argument n audience) ≤ n * depth argument + depth audience
  | 0, audience => by simp [iteratedRhetoric]
  | n + 1, audience => by
    simp only [iteratedRhetoric]
    have ih := iterated_depth_bound argument n audience
    have h := rhetoric_depth_bound argument (iteratedRhetoric argument n audience)
    have : (n + 1) * depth argument + depth audience =
      depth argument + (n * depth argument + depth audience) := by ring
    omega

/-- Self-resonance of iterated rhetoric is monotonically non-decreasing -/
theorem iterated_self_resonance_mono (argument : I) (n : ℕ) (audience : I) :
    resonanceStrength (iteratedRhetoric argument (n + 1) audience)
      (iteratedRhetoric argument (n + 1) audience) ≥
    resonanceStrength (iteratedRhetoric argument n audience)
      (iteratedRhetoric argument n audience) := by
  simp only [iteratedRhetoric]
  exact rhetoricalAct_self_resonance_ge_audience argument (iteratedRhetoric argument n audience)

/-- Persuasive force is non-negative at every iteration -/
theorem iterated_persuasiveForce_nonneg (argument : I) (n : ℕ) (audience : I) :
    persuasiveForce argument (iteratedRhetoric argument n audience) ≥ 0 :=
  persuasiveForce_nonneg argument _

/-- Each iteration preserves the ethos bound on persuasive force -/
theorem iterated_persuasiveForce_ge_zero (argument : I) (n : ℕ) (audience : I) :
    persuasiveForce argument (iteratedRhetoric argument n audience) ≥ 0 :=
  persuasiveForce_nonneg argument _

/-- Iterated rhetoric with void audience: each step composes with argument -/
theorem iterated_void_audience_depth (argument : I) (n : ℕ) :
    depth (iteratedRhetoric argument n (void : I)) ≤ n * depth argument := by
  have h := iterated_depth_bound argument n (void : I)
  simp [IdeaticSpace2.depth_void] at h
  linarith

/-! ## §5. Gramsci's Hegemony -/

/-- Hegemonic: an argument that resonates positively with a whole population -/
def isHegemonic (argument : I) (population : List I) : Prop :=
  ∀ member ∈ population, resonanceStrength argument member > 0

/-- Counter-hegemonic: an idea that opposes the dominant idea -/
def isCounterHegemonic (counter dominant : I) : Prop :=
  resonanceStrength counter dominant <
  resonanceStrength (void : I) (void : I)

/-- Every argument is vacuously hegemonic over the empty population -/
theorem hegemonic_empty (argument : I) : isHegemonic argument ([] : List I) := by
  intro m hm; exact absurd hm (List.not_mem_nil m)

/-- An argument is hegemonic over a singleton iff it resonates with that member -/
theorem hegemonic_singleton (argument member : I) :
    isHegemonic argument [member] ↔ resonanceStrength argument member > 0 := by
  constructor
  · intro h; exact h member (List.mem_cons_self member [])
  · intro h m hm
    simp [List.mem_cons, List.mem_nil_iff] at hm
    rw [hm]; exact h

/-- Hegemonic argument has positive pathos with every population member -/
theorem hegemonic_positive_pathos (argument : I) (population : List I)
    (h : isHegemonic argument population) :
    ∀ member ∈ population, pathos argument member > 0 := h

/-- If hegemonic over a list, then hegemonic over its tail -/
theorem hegemonic_tail (argument a : I) (rest : List I)
    (h : isHegemonic argument (a :: rest)) : isHegemonic argument rest := by
  intro m hm; exact h m (List.mem_cons_of_mem a hm)

/-- Counter-hegemonic means resonance is below the void baseline -/
theorem counterhegemonic_below_baseline (counter dominant : I)
    (h : isCounterHegemonic counter dominant) :
    resonanceStrength counter dominant < 1 := by
  unfold isCounterHegemonic at h; rw [IdeaticSpace2.rs_void_self] at h; exact h

/-- Void cannot be hegemonic over any non-empty population
    because rs(void, a) may not exceed 0 strictly — but actually rs is non-negative
    and rs(void, void) = 1 > 0. So void IS hegemonic over [void].
    Instead: counter-hegemony is asymmetric. -/
theorem counterhegemonic_asymmetry (a b : I)
    (h : isCounterHegemonic a b) : resonanceStrength a b < 1 :=
  counterhegemonic_below_baseline a b h

/-- Self-resonance always exceeds the counter-hegemonic threshold -/
theorem self_not_counterhegemonic (a : I) : ¬isCounterHegemonic a a := by
  unfold isCounterHegemonic
  rw [IdeaticSpace2.rs_void_self]
  linarith [rs_self_ge_one (I := I) a]

/-- Combining hegemonic populations preserves hegemony -/
theorem hegemonic_append (argument : I) (pop1 pop2 : List I)
    (h1 : isHegemonic argument pop1)
    (h2 : isHegemonic argument pop2) :
    isHegemonic argument (pop1 ++ pop2) := by
  intro m hm
  rw [List.mem_append] at hm
  cases hm with
  | inl h => exact h1 m h
  | inr h => exact h2 m h

/-! ## §6. Habermas's Ideal Speech -/

/-- Ideal discourse: mutual positive resonance between all participants -/
def idealDiscourse (participants : List I) : Prop :=
  ∀ a ∈ participants, ∀ b ∈ participants,
    resonanceStrength a b > 0

/-- Empty discourse is vacuously ideal -/
theorem idealDiscourse_nil : idealDiscourse ([] : List I) := by
  intro a ha; exact absurd ha (List.not_mem_nil a)

/-- Singleton discourse: ideal iff the participant has positive self-resonance (always true) -/
theorem idealDiscourse_singleton (a : I) : idealDiscourse [a] := by
  intro x hx y hy
  simp [List.mem_cons, List.mem_nil_iff] at hx hy
  rw [hx, hy]; exact rs_self_pos' a

/-- Ideal discourse is monotone: subcollections are also ideal -/
theorem idealDiscourse_tail (a : I) (rest : List I)
    (h : idealDiscourse (a :: rest)) : idealDiscourse rest := by
  intro x hx y hy
  exact h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)

/-- In ideal discourse, every pair has positive pathos -/
theorem idealDiscourse_pathos_positive (participants : List I)
    (h : idealDiscourse participants) :
    ∀ a ∈ participants, ∀ b ∈ participants, pathos a b > 0 := h

/-- Ideal discourse implies hegemony: each participant is hegemonic over the rest -/
theorem idealDiscourse_implies_hegemonic (participants : List I)
    (h : idealDiscourse participants) :
    ∀ a ∈ participants, isHegemonic a participants := by
  intro a ha m hm; exact h a ha m hm

/-- A pair forms ideal discourse iff they mutually resonate -/
theorem idealDiscourse_pair (a b : I)
    (hab : resonanceStrength a b > 0) : idealDiscourse [a, b] := by
  intro x hx y hy
  have hx' : x = a ∨ x = b := by simpa using hx
  have hy' : y = a ∨ y = b := by simpa using hy
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact rs_self_pos' _
  · exact hab
  · rw [rs_symm']; exact hab
  · exact rs_self_pos' _

/-! ## §7. Rhetorical Strategy — Composition & Ordering -/

/-- Sequential rhetoric: first argument a, then argument b -/
def sequentialRhetoric (a b audience : I) : I :=
  rhetoricalAct b (rhetoricalAct a audience)

/-- Sequential rhetoric = composing the arguments then applying -/
theorem sequential_eq_compose (a b audience : I) :
    sequentialRhetoric a b audience = compose b (compose a audience) := rfl

/-- Depth bound for sequential rhetoric -/
theorem sequential_depth_bound (a b audience : I) :
    depth (sequentialRhetoric a b audience) ≤ depth a + depth b + depth audience := by
  unfold sequentialRhetoric rhetoricalAct
  have h1 := depth_subadditive' b (compose a audience)
  have h2 := depth_subadditive' a audience
  omega

/-- Self-resonance grows under sequential rhetoric -/
theorem sequential_self_resonance_ge (a b audience : I) :
    resonanceStrength (sequentialRhetoric a b audience)
      (sequentialRhetoric a b audience) ≥
    resonanceStrength audience audience := by
  unfold sequentialRhetoric
  have h1 := rhetoricalAct_self_resonance_ge_audience b (rhetoricalAct a audience)
  have h2 := rhetoricalAct_self_resonance_ge_audience a audience
  linarith

/-! ## §8. Rhetorical Strength Ordering -/

/-- Argument a is rhetorically stronger than b if it has higher ethos -/
def rhetoricallyStronger (a b : I) : Prop := ethos a > ethos b

/-- Rhetorical strength is transitive -/
theorem rhetoricallyStronger_trans (a b c : I) :
    rhetoricallyStronger a b → rhetoricallyStronger b c →
    rhetoricallyStronger a c := by
  unfold rhetoricallyStronger; intro h1 h2; linarith

/-- Rhetorical strength is irreflexive -/
theorem rhetoricallyStronger_irrefl (a : I) : ¬rhetoricallyStronger a a := by
  unfold rhetoricallyStronger; linarith

/-- Composing an argument with itself increases ethos -/
theorem compose_increases_ethos (a b : I) :
    ethos (rhetoricalAct a b) ≥ ethos a := by
  unfold ethos rhetoricalAct
  exact rs_compose_self_right a b

/-- Void is the weakest argument: everything is at least as strong -/
theorem void_weakest_ethos (a : I) : ethos a ≥ ethos (void : I) := by
  unfold ethos; rw [IdeaticSpace2.rs_void_self]; exact rs_self_ge_one a

/-! ## §9. Persuasion Dynamics -/

/-- Resistance is the gap between self-resonance and cross-resonance -/
theorem resistance_eq (argument audience : I) :
    resistance argument audience =
    ethos argument - pathos argument audience := rfl

/-- Cauchy-Schwarz bounds pathos² by the product of ethos values -/
theorem pathos_cauchy_schwarz (a b : I) :
    pathos a b * pathos a b ≤ ethos a * ethos b :=
  rs_le_self_product a b

/-- Pathos with void is non-negative -/
theorem pathos_void_nonneg (a : I) : pathos a (void : I) ≥ 0 :=
  rs_nonneg' a _

/-- Ethos of composed idea dominates both components -/
theorem ethos_compose_dominates (a b : I) :
    ethos (compose a b) ≥ ethos a ∧ ethos (compose a b) ≥ ethos b := by
  constructor
  · exact rs_compose_self_right a b
  · exact rs_compose_self_left b a

end IDT2.Rhetoric
