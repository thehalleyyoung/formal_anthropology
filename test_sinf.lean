import Mathlib

-- Test what lemmas exist for Nat.sInf
example : ∀ (s : Set ℕ), s.Nonempty → (∃ n ∈ s, ∀ m ∈ s, n ≤ m) → ∀ m ∈ s, sInf s ≤ m := by
  intro s hs h m hm
  exact Nat.sInf_le hm

-- Check if sInf satisfies its property
example : ∀ (P : ℕ → Prop), (∃ n, P n) → P (sInf {n | P n}) := by
  intro P h
  apply Nat.sInf_mem
  exact h

