/-
# Fixed Point Structure in Ideogenetic Systems

From FORMAL_ANTHROPOLOGY++ Chapter 6: Core Theorems of Generation, Section 6.3

**Theorem 6.10 (Cyclic Fixed Points)**: If `a ∈ gen^k(a)` for some `k > 0`, then the orbit 
`{a, gen(a), gen²(a), ..., gen^(k-1)(a)}` is closed under `gen`.

## Key Insight:
Ideas can exhibit cyclic behavior - an idea that eventually generates itself creates a 
fixed orbit in conceptual space. This captures phenomena like:
- Reflexive concepts ("this statement")
- Dialectical processes (thesis → antithesis → synthesis → thesis')
- Circular reasoning patterns
- Self-validating belief systems

## Mathematical Content:
This theorem establishes that cycles in generation create closed subsystems. Unlike
standard fixed points where `a ∈ gen(a)`, cyclic fixed points have period `k > 1`.

The proof uses:
1. Orbit construction  
2. Functional iteration properties
3. Closure under generation

This is a **positive existence result** showing rich structure in ideogenetic dynamics.
-/

import FormalAnthropology.SingleAgent_Basic
import FormalAnthropology.SingleAgent_Closure
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace SingleAgentIdeogenesis

open Set

/-! ## Section 1: Orbit Definition -/

/-- The forward orbit of an idea under k iterations of generation.
    This is the set {a, gen(a), gen²(a), ..., gen^(k-1)(a)} -/
def orbit (sys : IdeogeneticSystem) (a : sys.Idea) (k : ℕ) : Set sys.Idea :=
  {b | ∃ i : ℕ, i < k ∧ b ∈ genIter sys i {a}}

/-- The orbit contains the seed -/
theorem mem_orbit_self (sys : IdeogeneticSystem) (a : sys.Idea) (k : ℕ) (h : 0 < k) :
    a ∈ orbit sys a k := by
  use 0
  constructor
  · exact h
  · simp [genIter]

/-- If k > 0, the orbit is nonempty -/
theorem orbit_nonempty (sys : IdeogeneticSystem) (a : sys.Idea) (k : ℕ) (h : 0 < k) :
    (orbit sys a k).Nonempty :=
  ⟨a, mem_orbit_self sys a k h⟩

/-! ## Section 2: Cyclic Ideas -/

/-- An idea is k-cyclic if it returns to itself after k generation steps -/
def is_kcyclic (sys : IdeogeneticSystem) (a : sys.Idea) (k : ℕ) : Prop :=
  a ∈ genIter sys k {a}

/-- An idea is cyclic if it's k-cyclic for some k > 0 -/
def is_cyclic (sys : IdeogeneticSystem) (a : sys.Idea) : Prop :=
  ∃ k > 0, is_kcyclic sys a k

/-- The minimal period of a cyclic idea -/
noncomputable def minimal_period (sys : IdeogeneticSystem) (a : sys.Idea) 
    (h : is_cyclic sys a) : ℕ :=
  @Nat.find _ (Classical.decPred _) ⟨1, h.choose_spec.choose_spec⟩

/-! ## Section 3: Orbit Closure Properties -/

/-- Helper: extending orbit by one more iteration -/
theorem orbit_succ (sys : IdeogeneticSystem) (a : sys.Idea) (k : ℕ) :
    orbit sys a (k + 1) = orbit sys a k ∪ {b | b ∈ genIter sys k {a}} := by
  ext b
  constructor
  · intro ⟨i, hi, hb⟩
    by_cases h : i < k
    · left
      exact ⟨i, h, hb⟩
    · right
      push_neg at h
      have : i = k := Nat.lt_succ_iff_lt_or_eq.mp hi |>.resolve_left h
      rw [this] at hb
      exact hb
  · intro h
    cases h with
    | inl hl =>
      obtain ⟨i, hi, hb⟩ := hl
      use i
      constructor
      · exact Nat.lt_succ_of_lt hi
      · exact hb
    | inr hr =>
      use k
      constructor
      · exact Nat.lt_succ_self k
      · exact hr

/-- For a DETERMINISTIC generator (each idea has exactly one successor),
    we define the unique successor function. -/
noncomputable def detSucc (sys : IdeogeneticSystem) 
    (h_det : ∀ b : sys.Idea, ∃! c, c ∈ sys.generate b) (a : sys.Idea) : sys.Idea :=
  (h_det a).choose

/-- The deterministic successor is in the generate set -/
theorem detSucc_mem (sys : IdeogeneticSystem) 
    (h_det : ∀ b : sys.Idea, ∃! c, c ∈ sys.generate b) (a : sys.Idea) :
    detSucc sys h_det a ∈ sys.generate a :=
  (h_det a).choose_spec.1

/-- For deterministic systems, genIter sys n {a} = {detSucc^n a} -/
theorem genIter_det_singleton (sys : IdeogeneticSystem)
    (h_det : ∀ b : sys.Idea, ∃! c, c ∈ sys.generate b) (a : sys.Idea) (n : ℕ) :
    genIter sys n {a} = {(detSucc sys h_det)^[n] a} := by
  induction n with
  | zero => simp [genIter, Function.iterate_zero]
  | succ n ih =>
    simp only [genIter, genStep, Set.mem_iUnion, Set.mem_singleton_iff]
    ext x
    constructor
    · intro ⟨b, hb, hx⟩
      rw [ih, Set.mem_singleton_iff] at hb
      rw [hb] at hx
      have := (h_det _).unique hx (detSucc_mem sys h_det _)
      simp only [Set.mem_singleton_iff, Function.iterate_succ', Function.comp_apply]
      exact this
    · intro hx
      simp only [Set.mem_singleton_iff, Function.iterate_succ', Function.comp_apply] at hx
      use (detSucc sys h_det)^[n] a
      constructor
      · rw [ih]; rfl
      · rw [hx]; exact detSucc_mem sys h_det _

/-- The key property: for DETERMINISTIC systems, if the idea is k-cyclic, 
    applying generation to the orbit stays in the orbit. -/
theorem orbit_closed_under_gen (sys : IdeogeneticSystem) (a : sys.Idea) (k : ℕ)
    (hk : k > 0) (h_det : ∀ b : sys.Idea, ∃! c, c ∈ sys.generate b)
    (h_cyclic : is_kcyclic sys a k) :
    ∀ b ∈ orbit sys a k, sys.generate b ⊆ orbit sys a k := by
  intro b ⟨i, hi, hb⟩ c hc
  -- For deterministic systems, b = detSucc^i(a) and c = detSucc^(i+1)(a)
  rw [genIter_det_singleton sys h_det] at hb
  simp only [Set.mem_singleton_iff] at hb
  have hc_eq : c = detSucc sys h_det b := (h_det b).unique hc (detSucc_mem sys h_det b)
  rw [hb, hc_eq]
  -- Now we need detSucc^(i+1)(a) ∈ orbit sys a k
  use (i + 1) % k
  constructor
  · exact Nat.mod_lt (i + 1) hk
  · rw [genIter_det_singleton sys h_det]
    simp only [Set.mem_singleton_iff]
    -- We need detSucc^((i+1) mod k)(a) = detSucc^(i+1)(a)
    -- This uses h_cyclic: detSucc^k(a) = a
    rw [genIter_det_singleton sys h_det, Set.mem_singleton_iff] at h_cyclic
    -- h_cyclic : detSucc^k(a) = a
    -- We need to show detSucc^((i+1) mod k)(a) = detSucc^(i+1)(a)
    have h_period : ∀ m, (detSucc sys h_det)^[m + k] a = (detSucc sys h_det)^[m] a := by
      intro m
      rw [Function.iterate_add]
      simp only [Function.comp_apply, h_cyclic]
    -- Use that (i+1) = (i+1) mod k + ((i+1) / k) * k
    have := Nat.div_add_mod (i + 1) k
    conv_rhs => rw [← this]
    clear this
    induction (i + 1) / k with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc]
      rw [Function.iterate_add, Function.comp_apply, h_period]
      rw [Nat.add_comm ((i + 1) % k) (n * k), Function.iterate_add] at ih
      simp only [Function.comp_apply] at ih ⊢
      rw [Nat.add_comm (n * k) ((i + 1) % k)]
      rw [Function.iterate_add, Function.comp_apply]
      rfl

/-! ## Section 4: The Main Theorem -/

/-- **Theorem 6.10: Cyclic Fixed Points (Deterministic Case)**

If an idea `a` is k-cyclic (returns to itself after k steps) in a DETERMINISTIC system,
then its orbit {a, gen(a), gen²(a), ..., gen^(k-1)(a)} is closed under the generation operator.

This establishes that cycles create invariant subsystems in the ideogenetic space.

NOTE: For non-deterministic systems, a different orbit definition is needed
(the closure under all possible generation paths, not just forward iterates).
-/
theorem cyclic_orbit_closed (sys : IdeogeneticSystem) (a : sys.Idea) (k : ℕ)
    (hk : k > 0) (h_det : ∀ b : sys.Idea, ∃! c, c ∈ sys.generate b)
    (h_cyclic : is_kcyclic sys a k) :
    ∀ b ∈ orbit sys a k, sys.generate b ⊆ orbit sys a k :=
  orbit_closed_under_gen sys a k hk h_det h_cyclic

/-! ## Section 5: Corollaries and Applications -/

/-- A 1-cyclic idea is a standard fixed point -/
theorem one_cyclic_is_fixed_point (sys : IdeogeneticSystem) (a : sys.Idea)
    (h : is_kcyclic sys a 1) :
    a ∈ sys.generate a := by
  unfold is_kcyclic at h
  simp only [genIter, genStep, Set.mem_iUnion, Set.mem_singleton_iff, exists_eq_left] at h
  exact h

/-- Fixed points are 1-cyclic -/
theorem fixed_point_is_one_cyclic (sys : IdeogeneticSystem) (a : sys.Idea)
    (h : a ∈ sys.generate a) :
    is_kcyclic sys a 1 := by
  unfold is_kcyclic
  simp only [genIter, genStep, Set.mem_iUnion, Set.mem_singleton_iff, exists_eq_left]
  exact h

/-- The orbit of a 1-cyclic idea is just the singleton -/
theorem orbit_one_cyclic (sys : IdeogeneticSystem) (a : sys.Idea)
    (h : is_kcyclic sys a 1) :
    orbit sys a 1 = {a} := by
  ext b
  constructor
  · intro ⟨i, hi, hb⟩
    have : i = 0 := Nat.lt_one_iff.mp hi
    rw [this] at hb
    simp [genIter] at hb
    exact hb
  · intro hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact mem_orbit_self sys a 1 (by norm_num)

/-- If an idea is k-cyclic, it is also (k*m)-cyclic for any m ≥ 1.
    
    This is the CORRECT direction: smaller period → larger period is a multiple.
    The converse (larger period implies smaller period divides it) is FALSE in general;
    it only holds when the smaller number is the MINIMAL period. -/
theorem kcyclic_multiple (sys : IdeogeneticSystem) (a : sys.Idea) (k m : ℕ)
    (hk : k > 0) (hm : m > 0)
    (h_det : ∀ b : sys.Idea, ∃! c, c ∈ sys.generate b)
    (h : is_kcyclic sys a k) :
    is_kcyclic sys a (k * m) := by
  -- If f^k(a) = a, then f^(k*m)(a) = (f^k)^m(a) = a
  rw [genIter_det_singleton sys h_det, Set.mem_singleton_iff] at h ⊢
  rw [mul_comm, Function.iterate_mul]
  induction m with
  | zero => omega
  | succ m' ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    cases m' with
    | zero => simp [h]
    | succ m'' => 
      rw [ih (by omega), h]

/-- CORRECTED THEOREM: If k-cyclic and k | n, then n-cyclic.
    
    NOTE: The original `kcyclic_of_divisor` had the divisibility backwards and was FALSE.
    This is the correct version: if the period divides n, then n is also a period. -/
theorem kcyclic_of_multiple (sys : IdeogeneticSystem) (a : sys.Idea) (k n : ℕ)
    (hk : k > 0) (hn : n > 0)
    (h_det : ∀ b : sys.Idea, ∃! c, c ∈ sys.generate b)
    (hdiv : k ∣ n) (h : is_kcyclic sys a k) :
    is_kcyclic sys a n := by
  obtain ⟨m, rfl⟩ := hdiv
  have hm : m > 0 := by
    by_contra hm_zero
    push_neg at hm_zero
    interval_cases m
    simp at hn
  exact kcyclic_multiple sys a k m hk hm h_det h

/-- The minimal period divides any period (DETERMINISTIC SYSTEMS ONLY).
    
    This is the key theorem that makes cycle analysis work. For deterministic systems,
    if f^m(a) = a (minimal period m) and f^n(a) = a, then m | n by the division algorithm:
    n = q*m + r with 0 ≤ r < m, and f^r(a) = a contradicts minimality unless r = 0. -/
theorem minimal_period_divides (sys : IdeogeneticSystem) (a : sys.Idea)
    (h_det : ∀ b : sys.Idea, ∃! c, c ∈ sys.generate b)
    (h_cyc : is_cyclic sys a) (n : ℕ) (hn : n > 0) (h_n : is_kcyclic sys a n) :
    minimal_period sys a h_cyc ∣ n := by
  -- Let m = minimal_period sys a h_cyc
  -- We know m > 0 and f^m(a) = a where f = detSucc sys h_det
  -- We have h_n : f^n(a) = a with n > 0
  -- 
  -- Proof by contradiction: suppose m ∤ n
  -- By division algorithm: n = q*m + r with 0 < r < m
  -- Then f^n(a) = f^(q*m + r)(a) = f^r(f^(q*m)(a)) = f^r((f^m)^q(a)) = f^r(a)
  -- So f^r(a) = a with 0 < r < m, contradicting minimality of m
  -- 
  -- Implementation using Nat.mod:
  by_contra h_ndiv
  have m := minimal_period sys a h_cyc
  have hm_pos : m > 0 := Nat.find_pos ⟨1, h_cyc.choose_spec.choose_spec⟩
  have hm_spec : is_kcyclic sys a m := Nat.find_spec ⟨1, h_cyc.choose_spec.choose_spec⟩
  have hm_min : ∀ k, k > 0 → k < m → ¬is_kcyclic sys a k := by
    intro k hk_pos hk_lt hk_cyc
    exact Nat.find_min ⟨1, h_cyc.choose_spec.choose_spec⟩ hk_lt ⟨hk_pos, hk_cyc⟩
  -- r = n % m, with 0 ≤ r < m
  let r := n % m
  have hr_lt : r < m := Nat.mod_lt n hm_pos
  have hr_eq : n = (n / m) * m + r := (Nat.div_add_mod n m).symm
  -- If r = 0, then m | n, contradiction
  have hr_pos : r > 0 := by
    by_contra hr_zero
    push_neg at hr_zero
    interval_cases r
    · simp at h_ndiv
      have : m ∣ n := ⟨n / m, by omega⟩
      exact h_ndiv this
  -- Now 0 < r < m, and we show f^r(a) = a, contradicting minimality
  -- f^n(a) = a and f^(q*m)(a) = a, so f^r(a) = f^(n - q*m)(a) = ?
  -- We need: f^n = f^r ∘ f^(q*m), and f^(q*m)(a) = (f^m)^q(a) = a
  have hqm : (detSucc sys h_det)^[n / m * m] a = a := by
    rw [mul_comm, Function.iterate_mul]
    -- (f^m)^(n/m)(a) = a since f^m(a) = a
    unfold is_kcyclic at hm_spec
    rw [genIter_det_eq] at hm_spec
    simp at hm_spec
    induction (n / m) with
    | zero => simp
    | succ q' ih => 
      rw [Function.iterate_succ', Function.comp_apply, ih, hm_spec]
  have hr_cyc : (detSucc sys h_det)^[r] a = a := by
    have h_split : (detSucc sys h_det)^[n] a = (detSucc sys h_det)^[r] ((detSucc sys h_det)^[n / m * m] a) := by
      rw [← Function.iterate_add]
      congr 1
      omega
    unfold is_kcyclic at h_n
    rw [genIter_det_eq] at h_n
    simp at h_n
    rw [hqm] at h_split
    rw [← h_n, h_split]
  -- Now we have f^r(a) = a with 0 < r < m, contradicting minimality
  exact hm_min r hr_pos hr_lt (by unfold is_kcyclic; rw [genIter_det_eq]; simp [hr_cyc])

/-! ## Section 6: Examples and Non-Examples -/

/-- Example: Self-referential concepts are fixed points -/
example : ∃ (sys : IdeogeneticSystem), ∃ (a : sys.Idea), a ∈ sys.generate a := by
  -- We can construct such a system
  use {
    Idea := Bool
    generate := fun b => if b then {true, false} else {false}
    primordial := true
  }
  use true
  simp

/-- Non-example: Not all ideas are cyclic -/
theorem exists_noncyclic : ∃ (sys : IdeogeneticSystem), ∃ (a : sys.Idea), ¬is_cyclic sys a := by
  -- Natural numbers with successor is a non-cyclic system
  let succSys : IdeogeneticSystem := {
    Idea := ℕ
    generate := fun n => {n + 1}
    primordial := 0
  }
  use succSys
  use 0
  intro ⟨k, hk, h_cyc⟩
  -- h_cyc : 0 ∈ genIter succSys k {0}
  -- For this system, genIter k {0} = {k} (successor applied k times)
  -- So 0 ∈ {k} means 0 = k, contradicting k > 0
  unfold is_kcyclic at h_cyc
  -- We prove by induction that genIter succSys k {0} = {k}
  have genIter_succ : ∀ n : ℕ, genIter succSys n {0} = {n} := by
    intro n
    induction n with
    | zero => simp [genIter]
    | succ m ih =>
      simp only [genIter, genStep, Set.mem_iUnion, Set.mem_singleton_iff]
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_iUnion, exists_prop]
      constructor
      · intro ⟨y, hy, hx⟩
        rw [ih] at hy
        simp at hy hx
        rw [hy] at hx
        simp at hx
        exact hx
      · intro hx
        use m
        rw [ih]
        simp [hx]
  rw [genIter_succ k] at h_cyc
  simp at h_cyc
  omega

/-! ## Section 7: Orbit Size Bounds -/

/-- The orbit has at most k elements.
    
    This follows from the definition: orbit sys a k = {b | ∃ i < k, b ∈ genIter i {a}}.
    Each element comes from some i < k, so there are at most k source indices.
    However, different indices may give the same element, so |orbit| ≤ k. -/
theorem orbit_card_le (sys : IdeogeneticSystem) (a : sys.Idea) (k : ℕ)
    (h_det : ∀ b : sys.Idea, ∃! c, c ∈ sys.generate b)
    [Fintype (orbit sys a k)] :
    Fintype.card (orbit sys a k) ≤ k := by
  -- For a deterministic system, genIter sys i {a} = {f^i(a)} where f is the successor
  -- So orbit sys a k = {f^0(a), f^1(a), ..., f^(k-1)(a)} which has at most k elements
  -- The finiteness follows from k being finite
  classical
  -- Map each orbit element to its first occurrence index
  have h_inj : ∀ b ∈ orbit sys a k, ∃ i : Fin k, (detSucc sys h_det)^[i.val] a = b := by
    intro b ⟨i, hi, hb⟩
    use ⟨i, hi⟩
    -- b ∈ genIter sys i {a} = {(detSucc sys h_det)^[i] a} for deterministic systems
    have : genIter sys i {a} = {(detSucc sys h_det)^[i] a} := genIter_det_eq sys h_det a i
    rw [this] at hb
    simp at hb
    exact hb.symm
  -- The orbit injects into Fin k
  calc Fintype.card (orbit sys a k) 
      ≤ Fintype.card (Fin k) := Fintype.card_le_of_surjective 
          (fun i => ⟨(detSucc sys h_det)^[i.val] a, by
            use i.val, i.isLt
            rw [genIter_det_eq sys h_det a i.val]
            simp⟩)
          (by
            intro ⟨b, hb⟩
            obtain ⟨i, hi⟩ := h_inj b hb
            use i
            simp [hi])
    _ = k := Fintype.card_fin k

/-- For a deterministic generator, orbit has exactly k elements
    if the idea is k-cyclic with minimal period k -/
theorem orbit_card_eq_period (sys : IdeogeneticSystem) (a : sys.Idea) (k : ℕ)
    (hk : k > 0)
    (h_det : ∀ b, ∃! c, c ∈ sys.generate b)
    (h_cyc : is_kcyclic sys a k)
    (h_min : ∀ j, 0 < j → j < k → ¬is_kcyclic sys a j)
    [Fintype (orbit sys a k)] :
    Fintype.card (orbit sys a k) = k := by
  -- For deterministic systems with minimal period k:
  -- - All iterates f^0(a), f^1(a), ..., f^(k-1)(a) are distinct
  --   (if f^i(a) = f^j(a) with i < j < k, then f^(j-i)(a) = a, contradicting minimality)
  -- - So the orbit has exactly k distinct elements
  apply le_antisymm
  · exact orbit_card_le sys a k h_det
  · -- Need to show k ≤ card(orbit)
    -- This requires showing all iterates are distinct
    -- If f^i(a) = f^j(a) for i < j < k, then f^(j-i)(a) = a with 0 < j-i < k
    -- contradicting h_min
    by_contra h_lt
    push_neg at h_lt
    -- If card < k, by pigeonhole, two distinct i, j < k have f^i(a) = f^j(a)
    -- Then f^|i-j|(a) = a with 0 < |i-j| < k, contradicting h_min
    have h_not_inj : ¬Function.Injective (fun i : Fin k => (detSucc sys h_det)^[i.val] a) := by
      intro h_inj
      have : Fintype.card (Fin k) ≤ Fintype.card (orbit sys a k) := by
        apply Fintype.card_le_of_injective
        intro i
        exact ⟨(detSucc sys h_det)^[i.val] a, by
          use i.val, i.isLt
          rw [genIter_det_eq]
          simp⟩
        intro i j hij
        simp at hij
        exact Fin.ext (h_inj (Subtype.mk_eq_mk.mpr hij))
      simp at this
      omega
    push_neg at h_not_inj
    obtain ⟨i, j, hij, hne⟩ := h_not_inj
    wlog h_lt_ij : i < j generalizing i j
    · cases (Ne.lt_or_lt hne) with
      | inl h => exact this j i hij.symm (Ne.symm hne) h
      | inr h => 
        push_neg at h_lt_ij
        exact this j i hij.symm (Ne.symm hne) (lt_of_le_of_ne h_lt_ij (Ne.symm hne))
    -- Now i < j and f^i(a) = f^j(a)
    -- So f^(j-i)(a) = a with 0 < j - i < k
    have h_period : (detSucc sys h_det)^[j.val - i.val] a = a := by
      have : (detSucc sys h_det)^[j.val] a = (detSucc sys h_det)^[i.val + (j.val - i.val)] a := by
        congr 1; omega
      rw [Function.iterate_add] at this
      simp only [Function.comp_apply] at this
      rw [hij] at this
      exact this
    have h_pos : 0 < j.val - i.val := Nat.sub_pos_of_lt h_lt_ij
    have h_bound : j.val - i.val < k := by omega
    -- This contradicts minimality
    apply h_min (j.val - i.val) h_pos h_bound
    unfold is_kcyclic
    rw [genIter_det_eq]
    simp [h_period]

/-! ## Section 8: Philosophical Implications -/

/-- Reflexive concepts (ideas that refer to themselves) form fixed points -/
def is_reflexive (sys : IdeogeneticSystem) (a : sys.Idea) : Prop :=
  a ∈ sys.generate a

theorem reflexive_iff_one_cyclic (sys : IdeogeneticSystem) (a : sys.Idea) :
    is_reflexive sys a ↔ is_kcyclic sys a 1 := by
  constructor
  · exact fixed_point_is_one_cyclic sys a
  · exact one_cyclic_is_fixed_point sys a

/-- Dialectical processes can be modeled as 3-cycles -/
def is_dialectical (sys : IdeogeneticSystem) (thesis antithesis synthesis : sys.Idea) : Prop :=
  antithesis ∈ sys.generate thesis ∧
  synthesis ∈ sys.generate antithesis ∧
  thesis ∈ sys.generate synthesis

theorem dialectical_is_three_cyclic (sys : IdeogeneticSystem) 
    (thesis antithesis synthesis : sys.Idea)
    (h_dial : is_dialectical sys thesis antithesis synthesis) :
    is_kcyclic sys thesis 3 := by
  -- h_dial gives us: antithesis ∈ gen(thesis), synthesis ∈ gen(antithesis), thesis ∈ gen(synthesis)
  -- We need to show: thesis ∈ genIter sys 3 {thesis}
  -- genIter 3 {thesis} = genStep (genStep (genStep {thesis}))
  --                    = genStep (genStep (⋃ x ∈ {thesis}, gen x))
  --                    = genStep (genStep (gen thesis))
  --                    ⊇ genStep (genStep {antithesis})  [since antithesis ∈ gen thesis]
  --                    = genStep (gen antithesis)
  --                    ⊇ genStep {synthesis}  [since synthesis ∈ gen antithesis]
  --                    = gen synthesis
  --                    ∋ thesis  [by h_dial]
  unfold is_kcyclic
  simp only [genIter, genStep]
  obtain ⟨h1, h2, h3⟩ := h_dial
  -- thesis ∈ gen(synthesis)
  -- synthesis ∈ gen(antithesis) ⊆ ⋃ y ∈ gen(thesis), gen(y)
  -- antithesis ∈ gen(thesis) ⊆ ⋃ x ∈ {thesis}, gen(x)
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, exists_eq_left]
  -- Goal: thesis ∈ ⋃ z ∈ (⋃ y ∈ gen(thesis), gen(y)), gen(z)
  use synthesis
  constructor
  · use antithesis
    exact ⟨h1, h2⟩
  · exact h3

end SingleAgentIdeogenesis
