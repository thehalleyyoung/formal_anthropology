/-
# Theorem N3: Bounded-Macro Compression

If each macro can be simulated by at most L base-generator steps, then
macro-extended depth sits between ceil(depth/L) and depth.
-/

import FormalAnthropology.Learning_AdaptiveGenerators
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace MacroInvariance

open Set AdaptiveGenerators
attribute [local instance] Classical.propDecidable

/-! ## Monotonicity and helper lemmas -/

def isMonotone {Idea : Type*} (f : Set Idea -> Set Idea) : Prop :=
  ∀ A B, A ⊆ B → f A ⊆ f B

lemma genCumulativeWith_mono_seed {Idea : Type*} (g : Set Idea -> Set Idea)
    (hmono : isMonotone g) :
    ∀ n (A B : Set Idea), A ⊆ B →
      genCumulativeWith g n A ⊆ genCumulativeWith g n B := by
  intro n
  induction n with
  | zero =>
      intro A B hAB
      simpa [genCumulativeWith] using hAB
  | succ n ih =>
      intro A B hAB
      intro x hx
      simp [genCumulativeWith] at hx
      cases hx with
      | inl hmem =>
          exact Or.inl (ih _ _ hAB hmem)
      | inr hmem =>
          have hstep : g (genCumulativeWith g n A) ⊆ g (genCumulativeWith g n B) :=
            hmono _ _ (ih _ _ hAB)
          exact Or.inr (hstep hmem)

lemma genCumulativeWith_add {Idea : Type*} (g : Set Idea -> Set Idea)
    (n m : Nat) (A : Set Idea) :
    genCumulativeWith g (n + m) A =
      genCumulativeWith g m (genCumulativeWith g n A) := by
  induction m with
  | zero =>
      simp [genCumulativeWith]
  | succ m ih =>
      simp [Nat.add_assoc, genCumulativeWith, ih]

/-! ## Macro-union generator -/

/-- Union of a base generator with a finite set of macros. -/
def macroUnion {Idea : Type*} (g : Set Idea -> Set Idea)
    (M : Finset (Set Idea -> Set Idea)) : Set Idea -> Set Idea :=
  fun A => g A ∪ ⋃ m ∈ (M : Set (Set Idea -> Set Idea)), m A

/-- Macros are L-bounded if each macro step is simulated by L base steps. -/
def macroBound {Idea : Type*} (g : Set Idea -> Set Idea)
    (M : Finset (Set Idea -> Set Idea)) (L : Nat) : Prop :=
  ∀ m ∈ M, ∀ A, m A ⊆ genCumulativeWith g L A

/-- Monotonicity of the macro-union generator. -/
lemma macroUnion_monotone {Idea : Type*} (g : Set Idea -> Set Idea)
    (M : Finset (Set Idea -> Set Idea))
    (hmono_g : isMonotone g)
    (hmono_m : ∀ m ∈ M, isMonotone m) :
    isMonotone (macroUnion g M) := by
  intro A B hAB x hx
  simp [macroUnion] at hx
  cases hx with
  | inl hmem =>
      exact Or.inl (hmono_g _ _ hAB hmem)
  | inr hmem =>
      obtain ⟨m, hm, hmx⟩ := by
        simpa using hmem
      have hstep : m A ⊆ m B := hmono_m m hm _ _ hAB
      exact Or.inr (by
        refine ⟨m, hm, hstep hmx⟩)

/-- Base generator is always included in the macro-union generator. -/
lemma base_subset_macroUnion {Idea : Type*} (g : Set Idea -> Set Idea)
    (M : Finset (Set Idea -> Set Idea)) (A : Set Idea) :
    g A ⊆ macroUnion g M A := by
  intro x hx
  simp [macroUnion, hx]

/-! ## Simulation lemma: macro steps expand to L base steps -/

lemma macro_simulation {Idea : Type*} (g : Set Idea -> Set Idea)
    (M : Finset (Set Idea -> Set Idea)) (L : Nat) (A : Set Idea)
    (hL : 1 <= L)
    (hmono_g : isMonotone g)
    (hbound : macroBound g M L) :
    ∀ t, genCumulativeWith (macroUnion g M) t A ⊆ genCumulativeWith g (t * L) A := by
  intro t
  induction t with
  | zero =>
      simp [genCumulativeWith]
  | succ t ih =>
      intro x hx
      simp [genCumulativeWith] at hx
      cases hx with
      | inl hmem =>
          have : x ∈ genCumulativeWith g (t * L) A := ih hmem
          -- t * L <= (t+1) * L
          have hle : t * L <= (t + 1) * L := by
            calc
              t * L <= t * L + L := by exact Nat.le_add_right _ _
              _ = (t + 1) * L := by ring
          exact genCumulativeWith_mono g A (t * L) ((t + 1) * L) hle this
      | inr hmem =>
          -- Expand one macro-union step.
          have hstep : x ∈ macroUnion g M (genCumulativeWith (macroUnion g M) t A) := hmem
          simp [macroUnion] at hstep
          cases hstep with
          | inl hbase =>
              -- Base generator step.
              have hseed : genCumulativeWith (macroUnion g M) t A ⊆ genCumulativeWith g (t * L) A :=
                ih
              have hbase' : g (genCumulativeWith (macroUnion g M) t A) ⊆
                  g (genCumulativeWith g (t * L) A) :=
                hmono_g _ _ hseed
              have : x ∈ g (genCumulativeWith g (t * L) A) := hbase' hbase
              -- One more base step from stage t*L.
              have : x ∈ genCumulativeWith g (t * L + 1) A := by
                simp [genCumulativeWith, this]
              -- t*L + 1 <= (t+1)*L when L >= 1, but we only need inclusion by monotone in n.
              have hle : t * L + 1 <= (t + 1) * L := by
                calc
                  t * L + 1 <= t * L + L := by
                    exact Nat.add_le_add_left hL _
                  _ = (t + 1) * L := by ring
              exact genCumulativeWith_mono g A (t * L + 1) ((t + 1) * L) hle this
          | inr hmac =>
              obtain ⟨m, hm, hmx⟩ := by
                simpa using hmac
              have hseed : genCumulativeWith (macroUnion g M) t A ⊆ genCumulativeWith g (t * L) A :=
                ih
              have hmx' : x ∈ genCumulativeWith g L (genCumulativeWith (macroUnion g M) t A) :=
                (hbound m hm _) hmx
              have hmono_seed := genCumulativeWith_mono_seed g hmono_g L
              have hmx'' : x ∈ genCumulativeWith g L (genCumulativeWith g (t * L) A) :=
                hmono_seed _ _ hseed hmx'
              -- Use stage addition.
              have : x ∈ genCumulativeWith g (t * L + L) A := by
                have hAdd := (genCumulativeWith_add g (t * L) L A).symm
                simpa [hAdd] using hmx''
              have hmul : t * L + L = (t + 1) * L := by ring
              simpa [hmul] using this

/-! ## Ceil division helper -/

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

lemma ceilDiv_le_iff {a b t : Nat} (hb : 0 < b) :
    ceilDiv a b <= t ↔ a <= t * b := by
  unfold ceilDiv
  have hdiv : (a + b - 1) / b <= t ↔ a + b - 1 <= b * t + (b - 1) :=
    Nat.div_le_iff_le_mul_add_pred hb
  have hrewrite : a + b - 1 = a + (b - 1) := by
    cases b with
    | zero => cases hb
    | succ b =>
        simp
  have hcancel : a + (b - 1) <= b * t + (b - 1) ↔ a <= b * t := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_right_comm] using
      (Nat.add_le_add_iff_right (b - 1) (a := a) (b := b * t))
  -- Combine.
  have : (a + b - 1) / b <= t ↔ a + (b - 1) <= b * t + (b - 1) := by
    simpa [hrewrite] using hdiv
  exact this.trans hcancel

/-! ## Theorem N3: Bounded-Macro Compression -/

theorem bounded_macro_compression {Idea : Type*} (g : Set Idea -> Set Idea)
    (M : Finset (Set Idea -> Set Idea)) (A : Set Idea) (L : Nat)
    (hL : 1 <= L)
    (hmono_g : isMonotone g)
    (hmono_m : ∀ m ∈ M, isMonotone m)
    (hbound : macroBound g M L)
    (c : Idea) :
    ceilDiv (depthWith g A c) L <= depthWith (macroUnion g M) A c ∧
    depthWith (macroUnion g M) A c <= depthWith g A c := by
  -- Lower bound via simulation.
  have hmono_union : isMonotone (macroUnion g M) :=
    macroUnion_monotone g M hmono_g hmono_m
  have hsim : ∀ t, genCumulativeWith (macroUnion g M) t A ⊆ genCumulativeWith g (t * L) A :=
    macro_simulation g M L A hL hmono_g hbound
  have hlow : depthWith g A c <= depthWith (macroUnion g M) A c * L := by
    by_cases hreach : ∃ n, c ∈ genCumulativeWith (macroUnion g M) n A
    · have hc : c ∈ genCumulativeWith (macroUnion g M)
          (depthWith (macroUnion g M) A c) A := by
          have : c ∈ closureWith (macroUnion g M) A := by
            simpa [closureWith] using hreach
          exact mem_genCumulativeWith_depth (macroUnion g M) A c this
      have hc' : c ∈ genCumulativeWith g
          (depthWith (macroUnion g M) A c * L) A := hsim _ hc
      exact depthWith_le_of_mem g A c _ hc'
    · -- If not reachable under macroUnion, depth is 0 and inequality holds.
      have : depthWith (macroUnion g M) A c = 0 := by
        unfold depthWith
        rw [dif_neg hreach]
      simp [this]
  have hceil : ceilDiv (depthWith g A c) L <= depthWith (macroUnion g M) A c := by
    have hpos : 0 < L := by omega
    have := (ceilDiv_le_iff (a := depthWith g A c) (b := L)
      (t := depthWith (macroUnion g M) A c) hpos).2 hlow
    exact this
  -- Upper bound: base generator is included in macroUnion.
  have hsubset : ∀ t, genCumulativeWith g t A ⊆ genCumulativeWith (macroUnion g M) t A := by
    intro t
    exact genCumulativeWith_mono_gen g (macroUnion g M) hmono_union
      (base_subset_macroUnion g M) t A
  have hupper : depthWith (macroUnion g M) A c <= depthWith g A c := by
    by_cases hreach : ∃ n, c ∈ genCumulativeWith g n A
    · have hc : c ∈ genCumulativeWith g (depthWith g A c) A := by
        have : c ∈ closureWith g A := by
          simpa [closureWith] using hreach
        exact mem_genCumulativeWith_depth g A c this
      have hc' : c ∈ genCumulativeWith (macroUnion g M) (depthWith g A c) A :=
        hsubset _ hc
      exact depthWith_le_of_mem (macroUnion g M) A c _ hc'
    · -- If unreachable under g, then macroUnion cannot reach c either.
      have hreach' : ¬ ∃ n, c ∈ genCumulativeWith (macroUnion g M) n A := by
        intro h'
        obtain ⟨n, hn⟩ := h'
        have : c ∈ genCumulativeWith g (n * L) A := hsim _ hn
        exact hreach ⟨n * L, this⟩
      have h0g : depthWith g A c = 0 := by
        unfold depthWith
        rw [dif_neg hreach]
      have h0u : depthWith (macroUnion g M) A c = 0 := by
        unfold depthWith
        rw [dif_neg hreach']
      simp [h0g, h0u]
  exact ⟨hceil, hupper⟩

/-! ## Internal lemma: generator inclusion with monotone union -/

lemma genCumulativeWith_mono_gen {Idea : Type*} (g g' : Set Idea -> Set Idea)
    (hmono : isMonotone g') (hstep : ∀ B, g B ⊆ g' B)
    (n : Nat) (A : Set Idea) :
    genCumulativeWith g n A ⊆ genCumulativeWith g' n A := by
  induction n with
  | zero =>
      simp [genCumulativeWith]
  | succ n ih =>
      intro x hx
      simp [genCumulativeWith] at hx
      cases hx with
      | inl hmem =>
          exact Or.inl (ih hmem)
      | inr hmem =>
          have hstep' : g (genCumulativeWith g n A) ⊆
              g' (genCumulativeWith g n A) := hstep _
          have hmono' : g' (genCumulativeWith g n A) ⊆
              g' (genCumulativeWith g' n A) := hmono _ _ ih
          exact Or.inr (hmono' (hstep' hmem))

end MacroInvariance
