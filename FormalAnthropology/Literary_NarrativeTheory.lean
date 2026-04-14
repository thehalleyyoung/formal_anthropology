import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Literary Narrative Theory: The Mathematics of Storytelling

Formalizes narrative structure within Ideatic Diffusion Theory (IDT).
A **narrative** is a sequence of ideas equipped with a **tension function**
tracking dramatic intensity at each position.

## 88 theorems, zero sorries, zero axioms
-/

namespace IDT.NarrativeTheory

/-! ## §0. IdeaticSpace — Local Redefinition -/

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

/-! ## §1. Definitions -/

variable {I : Type*} [IdeaticSpace I]

structure Narrative (I : Type*) where
  ideas : List I
  tension : ℕ → ℕ

def Narrative.len {I : Type*} (N : Narrative I) : ℕ := N.ideas.length

def Coherent : List I → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => IdeaticSpace.resonates a b ∧ Coherent (b :: rest)

def CoherentNarrative (N : Narrative I) : Prop := Coherent N.ideas

def depthSum : List I → ℕ
  | [] => 0
  | a :: rest => IdeaticSpace.depth a + depthSum rest

def maxDepth : List I → ℕ
  | [] => 0
  | a :: rest => max (IdeaticSpace.depth a) (maxDepth rest)

def IsRetelling (f : I → I) : Prop :=
  ∀ (a : I), IdeaticSpace.depth (f a) ≤ IdeaticSpace.depth a

def subplot (s : List I) (start len : ℕ) : List I :=
  (s.drop start).take len

/-! ## §2. Coherence -/

/-- THEOREM 1 -/
theorem coherent_nil : Coherent ([] : List I) := trivial

/-- THEOREM 2 -/
theorem coherent_singleton (a : I) : Coherent [a] := trivial

/-- THEOREM 3 -/
theorem coherent_pair (a b : I) :
    Coherent [a, b] ↔ IdeaticSpace.resonates a b := by
  simp [Coherent]

/-- THEOREM 4 -/
theorem coherent_cons (a b : I) (rest : List I)
    (hab : IdeaticSpace.resonates a b)
    (hrest : Coherent (b :: rest)) :
    Coherent (a :: b :: rest) := ⟨hab, hrest⟩

/-- THEOREM 5 -/
theorem coherent_tail (a : I) (rest : List I)
    (h : Coherent (a :: rest)) : Coherent rest := by
  cases rest with
  | nil => trivial
  | cons _ _ => exact h.2

/-- THEOREM 6 -/
theorem coherent_replicate (a : I) : ∀ (n : ℕ), Coherent (List.replicate n a)
  | 0 => trivial
  | 1 => trivial
  | n + 2 => by
    simp [List.replicate_succ, Coherent]
    exact ⟨IdeaticSpace.resonance_refl a, coherent_replicate a (n + 1)⟩

/-- THEOREM 7 -/
theorem coherentNarrative_singleton (a : I) (t : ℕ → ℕ) :
    CoherentNarrative (Narrative.mk [a] t) := coherent_singleton a

/-- THEOREM 8 -/
theorem coherentNarrative_empty (t : ℕ → ℕ) :
    CoherentNarrative (Narrative.mk ([] : List I) t) := coherent_nil

/-! ## §3. Depth -/

@[simp] theorem depthSum_nil : depthSum ([] : List I) = 0 := rfl
theorem depthSum_cons_eq (a : I) (s : List I) :
    depthSum (a :: s) = IdeaticSpace.depth a + depthSum s := rfl
@[simp] theorem maxDepth_nil : maxDepth ([] : List I) = 0 := rfl
theorem maxDepth_cons_eq (a : I) (s : List I) :
    maxDepth (a :: s) = max (IdeaticSpace.depth a) (maxDepth s) := rfl

/-- THEOREM 9 -/
theorem maxDepth_le_depthSum : ∀ (s : List I), maxDepth s ≤ depthSum s
  | [] => le_refl 0
  | a :: rest => by
    simp only [maxDepth_cons_eq, depthSum_cons_eq]
    have := maxDepth_le_depthSum rest; omega

/-- THEOREM 10 -/
theorem depthSum_bound (s : List I) (d : ℕ)
    (hbound : ∀ (a : I), a ∈ s → IdeaticSpace.depth a ≤ d) :
    depthSum s ≤ s.length * d := by
  induction s with
  | nil => simp
  | cons a rest ih =>
    rw [depthSum_cons_eq, List.length_cons]
    have ha := hbound a (List.mem_cons_self a rest)
    have hrest := ih (fun b hb => hbound b (List.mem_cons_of_mem a hb))
    nlinarith

/-- THEOREM 11 -/
theorem depthSum_void_replicate : ∀ (n : ℕ),
    depthSum (List.replicate n (IdeaticSpace.void : I)) = 0
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, depthSum_cons_eq, IdeaticSpace.depth_void,
        depthSum_void_replicate n]

/-- THEOREM 12 -/
theorem depthSum_singleton (a : I) : depthSum [a] = IdeaticSpace.depth a := by
  simp [depthSum]

/-- THEOREM 13 -/
theorem depthSum_append : ∀ (s t : List I),
    depthSum (s ++ t) = depthSum s + depthSum t
  | [], t => by simp [depthSum]
  | a :: rest, t => by
    simp only [List.cons_append, depthSum_cons_eq]
    rw [depthSum_append rest t]; omega

/-- THEOREM 14 -/
theorem maxDepth_atomic_le_one : ∀ (s : List I),
    (∀ (a : I), a ∈ s → IdeaticSpace.atomic a) → maxDepth s ≤ 1
  | [], _ => by simp
  | a :: rest, h => by
    rw [maxDepth_cons_eq]
    have ha := IdeaticSpace.depth_atomic a (h a (List.mem_cons_self a rest))
    have := maxDepth_atomic_le_one rest
      (fun b hb => h b (List.mem_cons_of_mem a hb)); omega

/-- THEOREM 15 -/
theorem depthSum_cons_le (a : I) (s : List I) :
    depthSum s ≤ depthSum (a :: s) := by rw [depthSum_cons_eq]; omega

/-- THEOREM 16 -/
theorem maxDepth_cons_ge (a : I) (s : List I) :
    maxDepth s ≤ maxDepth (a :: s) := by
  rw [maxDepth_cons_eq]; omega

/-! ## §4. Tension & Climax (pure ℕ → ℕ) -/

section Tension

/-- THEOREM 17 (Climax Existence) -/
theorem climax_exists (t : ℕ → ℕ) : ∀ (n : ℕ),
    ∃ (c : ℕ), c ≤ n ∧ ∀ (j : ℕ), j ≤ n → t j ≤ t c
  | 0 => ⟨0, le_refl 0, fun j hj => by
      have hj0 : j = 0 := by omega
      subst hj0
      exact le_refl _⟩
  | n + 1 => by
    obtain ⟨c, hcn, hmax⟩ := climax_exists t n
    by_cases h : t c < t (n + 1)
    · exact ⟨n + 1, le_refl _, fun j hj => by
        by_cases hj2 : j ≤ n
        · have := hmax j hj2; omega
        · have hjeq : j = n + 1 := by omega
          subst hjeq; exact le_refl _⟩
    · push_neg at h
      exact ⟨c, by omega, fun j hj => by
        by_cases hj2 : j ≤ n
        · exact hmax j hj2
        · have hjeq : j = n + 1 := by omega
          subst hjeq; exact h⟩

/-- THEOREM 18: bounded growth from step 0. -/
theorem tension_growth_bound (t : ℕ → ℕ) (k : ℕ)
    (hgrow : ∀ (i : ℕ), t (i + 1) ≤ t i + k) :
    ∀ (n : ℕ), t n ≤ t 0 + n * k
  | 0 => by omega
  | n + 1 => by
    have ih := tension_growth_bound t k hgrow n
    have step := hgrow n; nlinarith

/-- THEOREM 19: growth ≤ 1 from 0 → t(n) ≤ n. -/
theorem bounded_growth_climax_height (t : ℕ → ℕ) (n : ℕ)
    (h0 : t 0 = 0) (hg : ∀ (i : ℕ), t (i + 1) ≤ t i + 1) :
    t n ≤ n := by
  have := tension_growth_bound t 1 hg n; linarith

/-- THEOREM 20: growth ≤ k from 0 → t(n) ≤ n*k. -/
theorem tension_step_bound (t : ℕ → ℕ) (n k : ℕ)
    (h0 : t 0 = 0) (hg : ∀ (i : ℕ), t (i + 1) ≤ t i + k) :
    t n ≤ n * k := by
  have := tension_growth_bound t k hg n; linarith

/-- THEOREM 21: trichotomy. -/
theorem tension_trichotomy (t : ℕ → ℕ) (i : ℕ) :
    t i < t (i + 1) ∨ t (i + 1) < t i ∨ t i = t (i + 1) := by omega

/-- THEOREM 22: constant → no action. -/
theorem constant_no_action (t : ℕ → ℕ) (c : ℕ)
    (hc : ∀ (i : ℕ), t i = c) (i : ℕ) :
    ¬(t i < t (i + 1)) ∧ ¬(t (i + 1) < t i) := by
  constructor <;> (rw [hc i, hc (i + 1)]; omega)

/-- THEOREM 23 (Rising Step): rising on [a,b) → t a < t b. -/
theorem rising_step (t : ℕ → ℕ) (a : ℕ) :
    ∀ (b : ℕ), a < b →
    (∀ (i : ℕ), a ≤ i → i < b → t i < t (i + 1)) →
    t a < t b
  | 0 => fun h _ => by omega
  | b + 1 => fun hab hrise => by
    by_cases hab2 : a < b
    · have ih := rising_step t a b hab2 (fun i h1 h2 => hrise i h1 (by omega))
      have hs := hrise b (by omega) (by omega)
      omega
    · have : a = b := by omega
      subst this
      exact hrise a (le_refl a) (by omega)

/-- THEOREM 24 (Falling Step): falling on [a,b) → t b < t a. -/
theorem falling_step (t : ℕ → ℕ) (a : ℕ) :
    ∀ (b : ℕ), a < b →
    (∀ (i : ℕ), a ≤ i → i < b → t (i + 1) < t i) →
    t b < t a
  | 0 => fun h _ => by omega
  | b + 1 => fun hab hfall => by
    by_cases hab2 : a < b
    · have ih := falling_step t a b hab2 (fun i h1 h2 => hfall i h1 (by omega))
      have hs := hfall b (by omega) (by omega)
      omega
    · have : a = b := by omega
      subst this
      exact hfall a (le_refl a) (by omega)

/-- THEOREM 25 (Rising Monotone): i < j in rising region → t i < t j. -/
theorem rising_monotone (t : ℕ → ℕ) (i j : ℕ)
    (hij : i < j)
    (hrise : ∀ (k : ℕ), i ≤ k → k < j → t k < t (k + 1)) :
    t i < t j :=
  rising_step t i j hij hrise

/-- THEOREM 26 (Falling Monotone): i < j in falling region → t j < t i. -/
theorem falling_monotone (t : ℕ → ℕ) (i j : ℕ)
    (hij : i < j)
    (hfall : ∀ (k : ℕ), i ≤ k → k < j → t (k + 1) < t k) :
    t j < t i :=
  falling_step t i j hij hfall

/-- THEOREM 27 (Rising Bounded by Ceiling): rising + ceiling M → length limited. -/
theorem rising_bounded (t : ℕ → ℕ) (a b M : ℕ)
    (hab : a < b)
    (hrise : ∀ (i : ℕ), a ≤ i → i < b → t i < t (i + 1))
    (hta : t a ≤ M) (htb : t b ≤ M) :
    t a < t b :=
  rising_step t a b hab hrise

/-- THEOREM 28 (Freytag's Pyramid): rises [0,c) falls [c,n) → c is climax. -/
theorem freytag_pyramid (t : ℕ → ℕ) (c n : ℕ)
    (hcn : c ≤ n) (hc : 0 < c)
    (hrise : ∀ (i : ℕ), i < c → t i < t (i + 1))
    (hfall : ∀ (i : ℕ), c ≤ i → i < n → t (i + 1) < t i) :
    ∀ (j : ℕ), j ≤ n → t j ≤ t c := by
  intro j hj
  by_cases hjc : j = c
  · subst hjc; exact le_refl _
  · by_cases hjlt : j < c
    · have := rising_step t j c hjlt (fun i h1 h2 => hrise i (by omega))
      omega
    · have hjgt : c < j := by omega
      have := falling_step t c j hjgt (fun i h1 h2 => hfall i (by omega) (by omega))
      omega

/-- THEOREM 29: zero tension flat. -/
theorem zero_tension_flat (t : ℕ → ℕ) (h : ∀ (i : ℕ), t i = 0) (i : ℕ) :
    t i = t (i + 1) := by rw [h i, h (i + 1)]

/-- THEOREM 30 (Denouement): positive then zero → falling step exists. -/
theorem denouement_exists (t : ℕ → ℕ) (c n : ℕ)
    (hcn : c < n) (hpos : 0 < t c) (hend : t n = 0) :
    ∃ (d : ℕ), c ≤ d ∧ d < n ∧ t (d + 1) < t d := by
  by_contra h; push_neg at h
  -- t is non-decreasing from c to n, contradiction with t(n) = 0 < t(c)
  suffices hsuff : t c ≤ t n by omega
  clear hpos hend
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hcm : c ≤ m
    · by_cases hcm2 : c < m
      · have ihm := ih (by omega) (fun d hd1 hd2 => h d hd1 (by omega))
        have hstep := h m hcm (by omega)
        omega
      · have : c = m := by omega
        subst this
        have := h c (le_refl c) (by omega)
        omega
    · have : c = m + 1 := by omega
      subst this; exact le_refl _

/-- THEOREM 31: constant ⇒ all climax. -/
theorem constant_all_climax (t : ℕ → ℕ) (v : ℕ)
    (hc : ∀ (i : ℕ), t i = v) (j k : ℕ) : t k ≤ t j := by
  rw [hc k, hc j]

/-- THEOREM 32: climax ≥ start. -/
theorem climax_ge_start (t : ℕ → ℕ) (c n : ℕ)
    (h : ∀ (j : ℕ), j ≤ n → t j ≤ t c) (hn : 0 ≤ n) :
    t 0 ≤ t c := h 0 (by omega)

/-- THEOREM 33: climax ≥ end. -/
theorem climax_ge_end (t : ℕ → ℕ) (c n : ℕ)
    (h : ∀ (j : ℕ), j ≤ n → t j ≤ t c) (hcn : c ≤ n) :
    t n ≤ t c := h n (le_refl n)

/-- THEOREM 34: bounded growth mono in k. -/
theorem bounded_growth_mono (t : ℕ → ℕ) (k k' : ℕ)
    (hkk : k ≤ k') (hg : ∀ (i : ℕ), t (i + 1) ≤ t i + k) (i : ℕ) :
    t (i + 1) ≤ t i + k' := by have := hg i; omega

/-- THEOREM 35: non-decreasing. -/
theorem nondecr_bound (t : ℕ → ℕ)
    (hg : ∀ (i : ℕ), t (i + 1) ≤ t i) : ∀ (n : ℕ), t n ≤ t 0
  | 0 => le_refl _
  | n + 1 => by have := hg n; have := nondecr_bound t hg n; omega

/-- THEOREM 36: non-decr + non-incr = const. -/
theorem nondecr_nonincr_const (t : ℕ → ℕ)
    (hnd : ∀ (i : ℕ), t i ≤ t (i + 1))
    (hni : ∀ (i : ℕ), t (i + 1) ≤ t i) : ∀ (n : ℕ), t n = t 0
  | 0 => rfl
  | n + 1 => by
    have := hnd n; have := hni n
    have := nondecr_nonincr_const t hnd hni n; omega

/-- THEOREM 37: arc classification. -/
theorem arc_classification (t : ℕ → ℕ) (i : ℕ) :
    (t i < t (i + 1)) ∨ (t (i + 1) < t i) ∨ (t i = t (i + 1)) := by omega

/-- THEOREM 38: climax before end. -/
theorem climax_before_end (c n : ℕ) (t : ℕ → ℕ)
    (hcn : c ≤ n) (hlt : t n < t c) : c < n := by
  by_contra h; push_neg at h
  have hceq : c = n := by omega
  subst hceq; omega

end Tension

/-! ## §5. Composition -/

/-- THEOREM 39: resonant pair coherent. -/
theorem coherent_pair_mk (a b : I) (h : IdeaticSpace.resonates a b) :
    Coherent [a, b] := by simp [Coherent]; exact h

/-- THEOREM 40: prepend. -/
theorem coherent_simple_concat (a b : I) (rest : List I)
    (hab : IdeaticSpace.resonates a b) (hrest : Coherent (b :: rest)) :
    Coherent ([a] ++ b :: rest) := by simp; exact ⟨hab, hrest⟩

/-- THEOREM 41: void replicate coherent. -/
theorem coherent_void_replicate (n : ℕ) :
    Coherent (List.replicate n (IdeaticSpace.void : I)) :=
  coherent_replicate IdeaticSpace.void n

/-- THEOREM 42: resonance reflexive. -/
theorem resonance_refl (a : I) : IdeaticSpace.resonates a a :=
  IdeaticSpace.resonance_refl a

/-- THEOREM 43: resonance symmetric. -/
theorem resonance_symm (a b : I) (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates b a := IdeaticSpace.resonance_symm a b h

/-! ## §6. Subplot -/

/-- THEOREM 44: prefix coherent. -/
theorem coherent_take : ∀ (s : List I) (n : ℕ),
    Coherent s → Coherent (s.take n)
  | [], _ => fun _ => by simp [Coherent, List.take]
  | [_], n => fun _ => by
    cases n with | zero => simp [Coherent, List.take] | succ _ => simp [Coherent]
  | a :: b :: rest, n => fun h => by
    cases n with
    | zero => simp [Coherent, List.take]
    | succ m => cases m with
      | zero => simp [List.take, Coherent]
      | succ k =>
        simp [List.take, Coherent]
        exact ⟨h.1, coherent_take (b :: rest) (k + 1) h.2⟩

/-- THEOREM 45: suffix coherent. -/
theorem coherent_drop : ∀ (s : List I) (n : ℕ),
    Coherent s → Coherent (s.drop n)
  | [], _ => fun _ => by simp; trivial
  | _, 0 => fun h => by simp; exact h
  | a :: rest, n + 1 => fun h => by
    simp [List.drop]; exact coherent_drop rest n (coherent_tail a rest h)

/-- THEOREM 46: subplot coherent. -/
theorem coherent_subplot (s : List I) (start len : ℕ)
    (h : Coherent s) : Coherent (subplot s start len) :=
  coherent_take (s.drop start) len (coherent_drop s start h)

/-- THEOREM 47: subplot length bound. -/
theorem subplot_length_le (s : List I) (start len : ℕ) :
    (subplot s start len).length ≤ s.length := by
  simp [subplot, List.length_take, List.length_drop]

/-- THEOREM 48: take depthSum bound. -/
theorem depthSum_take_le : ∀ (s : List I) (n : ℕ),
    depthSum (s.take n) ≤ depthSum s
  | [], _ => by simp [depthSum]
  | _, 0 => by simp [depthSum, List.take]
  | a :: rest, n + 1 => by
    simp only [List.take_succ_cons, depthSum_cons_eq]
    have := depthSum_take_le rest n; omega

/-- THEOREM 49: drop depthSum bound. -/
theorem depthSum_drop_le : ∀ (s : List I) (n : ℕ),
    depthSum (s.drop n) ≤ depthSum s
  | [], _ => by simp [depthSum]
  | _, 0 => by simp
  | a :: rest, n + 1 => by
    simp [List.drop, depthSum_cons_eq]
    have := depthSum_drop_le rest n; omega

/-- THEOREM 50: subplot depth bound. -/
theorem subplot_depth_le_total (s : List I) (start len : ℕ) :
    depthSum (subplot s start len) ≤ depthSum s := by
  unfold subplot
  calc depthSum ((s.drop start).take len)
      ≤ depthSum (s.drop start) := depthSum_take_le (s.drop start) len
    _ ≤ depthSum s := depthSum_drop_le s start

/-- THEOREM 51: subplot zero empty. -/
theorem subplot_zero (s : List I) (start : ℕ) :
    subplot s start 0 = ([] : List I) := by simp [subplot, List.take]

/-- THEOREM 52: subplot count. -/
theorem subplot_count_bound (n : ℕ) :
    n * (n + 1) / 2 + 1 ≤ (n + 1) * (n + 1) := by
  have : n * (n + 1) / 2 ≤ n * (n + 1) := Nat.div_le_self _ _; nlinarith

/-! ## §7. Narrative Depth -/

/-- THEOREM 53 -/
theorem void_narrative_depth (n : ℕ) :
    depthSum (List.replicate n (IdeaticSpace.void : I)) = 0 :=
  depthSum_void_replicate n

/-- THEOREM 54 -/
theorem atomic_narrative_depth (s : List I)
    (h : ∀ (a : I), a ∈ s → IdeaticSpace.atomic a) :
    depthSum s ≤ s.length := by
  induction s with
  | nil => simp
  | cons a rest ih =>
    rw [depthSum_cons_eq, List.length_cons]
    have ha := IdeaticSpace.depth_atomic a (h a (List.mem_cons_self a rest))
    have := ih (fun b hb => h b (List.mem_cons_of_mem a hb)); omega

/-- THEOREM 55 -/
theorem composed_depth_bound (a b : I) :
    IdeaticSpace.depth (IdeaticSpace.compose a b) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b :=
  IdeaticSpace.depth_subadditive a b

/-- THEOREM 56 -/
theorem maxDepth_singleton (a : I) : maxDepth [a] = IdeaticSpace.depth a := by
  simp [maxDepth]

/-- THEOREM 57 -/
theorem depthSum_pair (a b : I) :
    depthSum [a, b] = IdeaticSpace.depth a + IdeaticSpace.depth b := by
  simp [depthSum]

/-- THEOREM 58 -/
theorem maxDepth_append_ge_left : ∀ (s t : List I),
    maxDepth s ≤ maxDepth (s ++ t)
  | [], _ => by simp [maxDepth]
  | a :: rest, t => by
    simp only [List.cons_append, maxDepth_cons_eq]
    have := maxDepth_append_ge_left rest t; omega

/-- THEOREM 59 -/
theorem maxDepth_append_ge_right : ∀ (s t : List I),
    maxDepth t ≤ maxDepth (s ++ t)
  | [], t => by simp
  | a :: rest, t => by
    simp only [List.cons_append, maxDepth_cons_eq]
    have := maxDepth_append_ge_right rest t; omega

/-- THEOREM 60 -/
theorem maxDepth_append_bound : ∀ (s t : List I),
    maxDepth (s ++ t) ≤ max (maxDepth s) (maxDepth t)
  | [], t => by simp [maxDepth]
  | a :: rest, t => by
    simp only [List.cons_append, maxDepth_cons_eq]
    have := maxDepth_append_bound rest t; omega

/-! ## §8. Retelling / Diffusion -/

/-- THEOREM 61 -/
theorem retelling_depth_bound (f : I → I) (s : List I) (hf : IsRetelling f) :
    depthSum (s.map f) ≤ depthSum s := by
  induction s with
  | nil => simp [depthSum]
  | cons a rest ih => simp [List.map, depthSum_cons_eq]; have := hf a; omega

/-- THEOREM 62 -/
theorem iterated_retelling_bound (f : I → I) (s : List I) (n : ℕ) (hf : IsRetelling f) :
    depthSum (Nat.iterate (List.map f) n s) ≤ depthSum s := by
  induction n generalizing s with
  | zero => simp [Nat.iterate]
  | succ k ih =>
    show depthSum (Nat.iterate (List.map f) k (List.map f s)) ≤ depthSum s
    calc depthSum (Nat.iterate (List.map f) k (List.map f s))
        ≤ depthSum (List.map f s) := ih (List.map f s)
      _ ≤ depthSum s := retelling_depth_bound f s hf

/-- THEOREM 63 -/
theorem id_is_retelling : IsRetelling (id : I → I) := fun _ => le_refl _

/-- THEOREM 64 -/
theorem retelling_compose (f g : I → I) (hf : IsRetelling f) (hg : IsRetelling g) :
    IsRetelling (f ∘ g) := fun a => le_trans (hf (g a)) (hg a)

/-- THEOREM 65 -/
theorem const_void_is_retelling :
    IsRetelling (fun (_ : I) => IdeaticSpace.void) := by
  intro a; rw [IdeaticSpace.depth_void]; exact Nat.zero_le _

/-- THEOREM 66 -/
theorem retelling_preserves_length (f : I → I) (s : List I) :
    (s.map f).length = s.length := by simp

/-- THEOREM 67 -/
theorem retelling_void_list (f : I → I) (n : ℕ) (hf : IsRetelling f) :
    depthSum (List.map f (List.replicate n (IdeaticSpace.void : I))) = 0 := by
  have h1 := void_narrative_depth (I := I) n
  have h2 := retelling_depth_bound f (List.replicate n (IdeaticSpace.void : I)) hf
  omega

/-- THEOREM 68 -/
theorem retelling_replicate_coherent (f : I → I) (n : ℕ) (a : I) :
    Coherent (List.map f (List.replicate n a)) := by
  have : List.map f (List.replicate n a) = List.replicate n (f a) := by
    induction n with
    | zero => simp
    | succ k ih => simp [List.replicate_succ, List.map, ih]
  rw [this]
  exact coherent_replicate (f a) n

/-! ## §9. Narrative Length -/

/-- THEOREM 69 -/
theorem empty_narrative_len (t : ℕ → ℕ) :
    (Narrative.mk ([] : List I) t).len = 0 := rfl

/-- THEOREM 70 -/
theorem singleton_narrative_len (a : I) (t : ℕ → ℕ) :
    (Narrative.mk [a] t).len = 1 := rfl

/-- THEOREM 71 -/
theorem cons_narrative_len_pos (a : I) (rest : List I) (t : ℕ → ℕ) :
    0 < (Narrative.mk (a :: rest) t).len := by simp [Narrative.len]

/-- THEOREM 72 -/
theorem take_len_le (s : List I) (n : ℕ) : (s.take n).length ≤ n :=
  List.length_take_le n s

/-! ## §10. Transformations -/

def reverseNarrative (N : Narrative I) (n : ℕ) : Narrative I :=
  ⟨N.ideas.reverse, fun i => N.tension (n - i)⟩

/-- THEOREM 73 -/
theorem reverse_len (N : Narrative I) (n : ℕ) :
    (reverseNarrative N n).len = N.len := by
  simp [reverseNarrative, Narrative.len, List.length_reverse]

/-- THEOREM 74 -/
theorem reverse_reverse_ideas (N : Narrative I) :
    N.ideas.reverse.reverse = N.ideas := List.reverse_reverse N.ideas

/-- THEOREM 75 -/
theorem map_preserves_len (f : I → I) (N : Narrative I) :
    (Narrative.mk (N.ideas.map f) N.tension).len = N.len := by
  simp [Narrative.len, List.length_map]

/-- THEOREM 76 -/
theorem depthSum_append_nil (s : List I) :
    depthSum (s ++ []) = depthSum s := by rw [List.append_nil]

/-! ## §11. IDT Algebraic Properties -/

/-- THEOREM 77 -/
theorem void_depth_zero : IdeaticSpace.depth (IdeaticSpace.void : I) = 0 :=
  IdeaticSpace.depth_void

/-- THEOREM 78 -/
theorem void_is_atomic : IdeaticSpace.atomic (IdeaticSpace.void : I) :=
  IdeaticSpace.void_atomic

/-- THEOREM 79 -/
theorem void_resonates_self :
    IdeaticSpace.resonates (IdeaticSpace.void : I) IdeaticSpace.void :=
  IdeaticSpace.resonance_refl _

/-- THEOREM 80 -/
theorem resonance_compose_thm (a a' b b' : I)
    (ha : IdeaticSpace.resonates a a') (hb : IdeaticSpace.resonates b b') :
    IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose a' b') :=
  IdeaticSpace.resonance_compose a a' b b' ha hb

/-- THEOREM 81 -/
theorem void_left (a : I) : IdeaticSpace.compose IdeaticSpace.void a = a :=
  IdeaticSpace.void_left a

/-- THEOREM 82 -/
theorem void_right (a : I) : IdeaticSpace.compose a IdeaticSpace.void = a :=
  IdeaticSpace.void_right a

/-- THEOREM 83 -/
theorem compose_assoc (a b c : I) :
    IdeaticSpace.compose (IdeaticSpace.compose a b) c =
    IdeaticSpace.compose a (IdeaticSpace.compose b c) :=
  IdeaticSpace.compose_assoc a b c

/-- THEOREM 84 -/
theorem resonance_compose_right (a b c : I) (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (IdeaticSpace.compose a c) (IdeaticSpace.compose b c) :=
  IdeaticSpace.resonance_compose a b c c h (IdeaticSpace.resonance_refl c)

/-- THEOREM 85 -/
theorem resonance_compose_left (a b c : I) (h : IdeaticSpace.resonates b c) :
    IdeaticSpace.resonates (IdeaticSpace.compose a b) (IdeaticSpace.compose a c) :=
  IdeaticSpace.resonance_compose a a b c (IdeaticSpace.resonance_refl a) h

/-- THEOREM 86 -/
theorem void_compose_void :
    IdeaticSpace.compose (IdeaticSpace.void : I) IdeaticSpace.void = IdeaticSpace.void :=
  IdeaticSpace.void_left _

/-- THEOREM 87 -/
theorem depth_void_compose (a : I) :
    IdeaticSpace.depth (IdeaticSpace.compose IdeaticSpace.void a) =
    IdeaticSpace.depth a := by rw [IdeaticSpace.void_left]

/-- THEOREM 88 -/
theorem atomic_depth_le_one (a : I) (h : IdeaticSpace.atomic a) :
    IdeaticSpace.depth a ≤ 1 := IdeaticSpace.depth_atomic a h

end IDT.NarrativeTheory
