import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import FormalAnthropology.IDT_Foundations_v2

/-!
# IDT v2: Intertextuality

Every text exists in relation to other texts (Kristeva, Barthes, Bloom).
In the quantitative resonance framework:
- **Intertextual resonance** = resonance strength between two texts' embeddings
- **Influence** = resonance of a precursor on a successor
- **Originality** = self-resonance minus total influence from a tradition
- **Anxiety of influence** (Bloom) = ratio of precursor influence to self-weight

Key results:
- Adding precursors to a tradition monotonically reduces originality
- Anxiety of self-influence is exactly 1 (maximum)
- Tradition composition is a monoid homomorphism
- Influence satisfies Cauchy-Schwarz bounds

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT2.Intertextuality

variable {I : Type*} [IdeaticSpace2 I]
open IdeaticSpace2

/-! ## §1. Intertextual Relations -/

/-- Intertextual resonance between two texts. -/
noncomputable def intertextualResonance (text1 text2 : I) : ℝ :=
  resonanceStrength text1 text2

/-- Influence of a precursor text on a successor text. -/
noncomputable def influence (precursor successor : I) : ℝ :=
  resonanceStrength precursor successor

/-- Two texts are minimally related when their resonance does not exceed the baseline. -/
def minimallyRelated (text1 text2 : I) : Prop :=
  resonanceStrength text1 text2 ≤ resonanceStrength (void : I) (void : I)

/-- Originality of a text relative to a tradition (list of precursors):
    self-resonance minus the sum of influences from each precursor. -/
noncomputable def originality (text : I) (tradition : List I) : ℝ :=
  resonanceStrength text text -
  (tradition.map (fun p => resonanceStrength text p)).sum

/-- The tradition composite: the composed idea of all precursor texts. -/
def traditionIdea : List I → I
  | [] => (void : I)
  | a :: rest => compose a (traditionIdea rest)

/-- Bloom's anxiety of influence: the ratio of a precursor's influence to the
    successor's self-resonance. A value of 1 means the successor is entirely
    "under the shadow" of the precursor. -/
noncomputable def anxietyOfInfluence (precursor successor : I) : ℝ :=
  resonanceStrength precursor successor / resonanceStrength successor successor

/-! ## §2. Influence Theorems -/

/-- Influence is symmetric: if A influences B, B influences A equally. -/
theorem influence_symmetric (a b : I) :
    influence a b = influence b a := by
  unfold influence; exact rs_symm' a b

/-- Self-influence equals self-resonance. -/
theorem self_influence (a : I) :
    influence a a = resonanceStrength a a := rfl

/-- Influence is always non-negative. -/
theorem influence_nonneg (a b : I) : influence a b ≥ 0 := by
  unfold influence; exact IdeaticSpace2.rs_nonneg a b

/-- Void-to-void influence equals the baseline resonance 1. -/
theorem influence_void : influence (void : I) (void : I) = 1 := by
  unfold influence; exact rs_void_unit

/-- **Cauchy-Schwarz for influence**: cross-influence squared is bounded by
    self-influences. -/
theorem influence_bounded (a b : I) :
    influence a b * influence a b ≤ influence a a * influence b b := by
  unfold influence; exact rs_le_self_product a b

/-- Influence grows under shared compositional context. -/
theorem influence_compose_mono_right (a b c : I) :
    influence (compose a c) (compose b c) ≥ influence a b := by
  unfold influence; exact IdeaticSpace2.rs_compose_right_mono a b c

/-- Influence grows under shared left context. -/
theorem influence_compose_mono_left (a b c : I) :
    influence (compose c a) (compose c b) ≥ influence a b := by
  unfold influence; exact IdeaticSpace2.rs_compose_left_mono a b c

/-! ## §3. Tradition -/

@[simp] theorem traditionIdea_nil :
    traditionIdea ([] : List I) = (void : I) := rfl

@[simp] theorem traditionIdea_cons (a : I) (rest : List I) :
    traditionIdea (a :: rest) = compose a (traditionIdea rest) := rfl

theorem traditionIdea_singleton (a : I) :
    traditionIdea [a] = a := by
  simp [IdeaticSpace2.void_right]

/-- Depth of a tradition composite is bounded by the sum of constituent depths. -/
theorem traditionIdea_depth_bound (t : List I) :
    depth (traditionIdea t) ≤ (t.map depth).sum := by
  induction t with
  | nil => simp [depth_void']
  | cons a rest ih =>
    simp only [traditionIdea_cons, List.map_cons, List.sum_cons]
    have h := depth_subadditive' a (traditionIdea rest)
    omega

/-- Tradition composition is a monoid homomorphism:
    merging two traditions = composing their ideas. -/
theorem tradition_merge (t1 t2 : List I) :
    traditionIdea (t1 ++ t2) =
    compose (traditionIdea (I := I) t1) (traditionIdea t2) := by
  induction t1 with
  | nil => simp [IdeaticSpace2.void_left]
  | cons a rest ih =>
    simp only [List.cons_append, traditionIdea_cons]
    rw [ih, ← IDT2.compose_assoc]

/-- Every tradition composite has self-resonance at least 1. -/
theorem tradition_weight_ge_one (t : List I) :
    resonanceStrength (traditionIdea t) (traditionIdea t) ≥ 1 :=
  rs_self_ge_one _

/-- Adding a text to a tradition increases the composite's self-resonance. -/
theorem tradition_weight_monotone (a : I) (rest : List I) :
    resonanceStrength (traditionIdea (a :: rest)) (traditionIdea (a :: rest)) ≥
    resonanceStrength (traditionIdea rest) (traditionIdea rest) := by
  simp only [traditionIdea_cons]
  exact rs_compose_self_left (traditionIdea rest) a

/-! ## §4. Originality -/

/-- With no tradition, originality equals pure self-resonance. -/
theorem originality_void_tradition (text : I) :
    originality text [] = resonanceStrength text text := by
  unfold originality; simp

/-- Originality against a single precursor. -/
theorem originality_singleton (text p : I) :
    originality text [p] = resonanceStrength text text - resonanceStrength text p := by
  unfold originality; simp

/-- With no tradition, originality is at least 1. -/
theorem originality_void_tradition_ge_one (text : I) :
    originality text [] ≥ 1 := by
  rw [originality_void_tradition]
  exact rs_self_ge_one text

/-- **Influence erodes originality**: adding a precursor to the tradition
    can only decrease originality. -/
theorem adding_precursor_reduces_originality (text p : I) (tradition : List I) :
    originality text (p :: tradition) ≤ originality text tradition := by
  unfold originality
  simp only [List.map_cons, List.sum_cons]
  linarith [IdeaticSpace2.rs_nonneg text p]

/-- Originality is at most self-resonance, regardless of tradition. -/
theorem originality_le_self_resonance (text : I) (tradition : List I) :
    originality text tradition ≤ resonanceStrength text text := by
  unfold originality
  have : 0 ≤ (tradition.map (fun p => resonanceStrength text p)).sum := by
    induction tradition with
    | nil => simp
    | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons]
      linarith [IdeaticSpace2.rs_nonneg text p]
  linarith

/-! ## §5. Anxiety of Influence -/

/-- Anxiety of influence is non-negative. -/
theorem anxiety_nonneg (p s : I) : anxietyOfInfluence p s ≥ 0 := by
  unfold anxietyOfInfluence
  exact div_nonneg (IdeaticSpace2.rs_nonneg p s) (le_of_lt (rs_self_pos' s))

/-- Self-anxiety is exactly 1: every text is maximally influenced by itself. -/
theorem anxiety_self (a : I) : anxietyOfInfluence a a = 1 := by
  unfold anxietyOfInfluence
  exact div_self (ne_of_gt (rs_self_pos' a))

/-- Product identity: anxiety times self-resonance recovers the raw influence. -/
theorem anxiety_product (p s : I) :
    anxietyOfInfluence p s * resonanceStrength s s = resonanceStrength p s := by
  unfold anxietyOfInfluence
  have hs : (resonanceStrength s s : ℝ) ≠ 0 := ne_of_gt (rs_self_pos' s)
  field_simp

/-- Anxiety is symmetric in a weighted sense:
    anxiety(p,s) · rs(s,s) = anxiety(s,p) · rs(p,p). -/
theorem anxiety_weighted_symmetry (p s : I) :
    anxietyOfInfluence p s * resonanceStrength s s =
    anxietyOfInfluence s p * resonanceStrength p p := by
  rw [anxiety_product, anxiety_product, rs_symm']

/-- When the precursor has at most the successor's self-resonance,
    anxiety of influence is at most 1. -/
theorem anxiety_le_one (p s : I)
    (h : resonanceStrength p p ≤ resonanceStrength s s) :
    anxietyOfInfluence p s ≤ 1 := by
  unfold anxietyOfInfluence
  rw [div_le_one (rs_self_pos' s), rs_symm']
  exact rs_le_self_when s p h

end IDT2.Intertextuality
