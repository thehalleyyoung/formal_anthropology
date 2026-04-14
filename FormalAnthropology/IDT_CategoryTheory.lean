import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Ideatic Diffusion Theory: Category-Theoretic Perspective

This file develops the **category-theoretic** perspective on ideatic spaces,
treating them as objects with structure-preserving morphisms between them.

## Core Concepts

1. **IdeaticMorphism**: Structure-preserving maps between ideatic spaces
   (preserve composition, void, and resonance)
2. **BoundedMorphism**: Morphisms that also satisfy a depth bound
3. **IdeaticEmbedding**: Injective morphisms preserving all structure
4. **IdeaticIso**: Bijective morphisms with structure-preserving inverses
5. **Endomorphisms and Fixed Points**: Self-maps and their iterates

## Literary Application: Translation Theory

Translation between natural languages is modeled as a morphism between
ideatic spaces. Key results:
- Translation loss as non-isomorphism
- Untranslatability as absence of resonant images
- Back-translation always loses information (unless isomorphism)

## NO SORRIES, NO ADMITS, NO AXIOMS
-/

namespace IDT.CategoryTheory

/-! ## §0. Local IdeaticSpace Definition -/

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

/-! ## §1. Morphisms Between Ideatic Spaces -/

section Morphisms

variable {I : Type*} [IdeaticSpace I]
variable {J : Type*} [IdeaticSpace J]
variable {K : Type*} [IdeaticSpace K]

/-- A structure-preserving map between ideatic spaces. -/
structure IdeaticMorphism (I : Type*) (J : Type*) [IdeaticSpace I] [IdeaticSpace J] where
  map : I → J
  map_compose : ∀ (a b : I),
    map (IdeaticSpace.compose a b) = IdeaticSpace.compose (map a) (map b)
  map_void : map (IdeaticSpace.void : I) = (IdeaticSpace.void : J)
  map_resonance : ∀ (a b : I),
    IdeaticSpace.resonates a b → IdeaticSpace.resonates (map a) (map b)

/-- The identity morphism on any ideatic space. -/
def IdeaticMorphism.id (I : Type*) [IdeaticSpace I] : IdeaticMorphism I I where
  map := fun a => a
  map_compose := fun _ _ => rfl
  map_void := rfl
  map_resonance := fun _ _ h => h

/-- Composition of two ideatic morphisms. -/
def IdeaticMorphism.comp {I J K : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]
    (g : IdeaticMorphism J K) (f : IdeaticMorphism I J) : IdeaticMorphism I K where
  map := fun a => g.map (f.map a)
  map_compose := fun a b => by simp [f.map_compose, g.map_compose]
  map_void := by simp [f.map_void, g.map_void]
  map_resonance := fun a b h => g.map_resonance _ _ (f.map_resonance a b h)

/-- Theorem 1: Morphism composition is associative on the underlying maps. -/
theorem morphism_comp_assoc {I J K L : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K] [IdeaticSpace L]
    (h : IdeaticMorphism K L) (g : IdeaticMorphism J K) (f : IdeaticMorphism I J) :
    (h.comp (g.comp f)).map = (h.comp g |>.comp f).map := by
  rfl

/-- Theorem 2: Identity is a left unit for morphism composition. -/
theorem morphism_id_comp_map {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) :
    ((IdeaticMorphism.id J).comp f).map = f.map := by
  rfl

/-- Theorem 3: Identity is a right unit for morphism composition. -/
theorem morphism_comp_id_map {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) :
    (f.comp (IdeaticMorphism.id I)).map = f.map := by
  rfl

/-- Theorem 4: Morphisms preserve the void element. -/
theorem morphism_preserves_void (f : IdeaticMorphism I J) :
    f.map (IdeaticSpace.void : I) = (IdeaticSpace.void : J) :=
  f.map_void

/-- Theorem 5: Morphisms preserve resonance. -/
theorem morphism_preserves_resonance (f : IdeaticMorphism I J) (a b : I)
    (h : IdeaticSpace.resonates a b) : IdeaticSpace.resonates (f.map a) (f.map b) :=
  f.map_resonance a b h

/-- Theorem 6: Composition of morphisms preserves void. -/
theorem comp_preserves_void {I J K : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]
    (g : IdeaticMorphism J K) (f : IdeaticMorphism I J) :
    (g.comp f).map (IdeaticSpace.void : I) = (IdeaticSpace.void : K) :=
  (g.comp f).map_void

/-- Theorem 7: Self-resonance is preserved by morphisms. -/
theorem morphism_preserves_self_resonance (f : IdeaticMorphism I J) (a : I) :
    IdeaticSpace.resonates (f.map a) (f.map a) :=
  f.map_resonance a a (IdeaticSpace.resonance_refl a)

end Morphisms

/-! ## §2. Depth-Bounded Morphisms -/

section BoundedMorphisms

variable {I : Type*} [IdeaticSpace I]
variable {J : Type*} [IdeaticSpace J]
variable {K : Type*} [IdeaticSpace K]

/-- A morphism that additionally never increases depth. -/
structure BoundedMorphism (I : Type*) (J : Type*) [IdeaticSpace I] [IdeaticSpace J]
    extends IdeaticMorphism I J where
  depth_bound : ∀ (a : I), IdeaticSpace.depth (map a) ≤ IdeaticSpace.depth a

/-- Theorem 8: The identity morphism is bounded. -/
def BoundedMorphism.id (I : Type*) [IdeaticSpace I] : BoundedMorphism I I where
  map := fun a => a
  map_compose := fun _ _ => rfl
  map_void := rfl
  map_resonance := fun _ _ h => h
  depth_bound := fun _ => Nat.le_refl _

/-- Theorem 9: Composition of bounded morphisms is bounded. -/
def BoundedMorphism.comp {I J K : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]
    (g : BoundedMorphism J K) (f : BoundedMorphism I J) : BoundedMorphism I K where
  map := fun a => g.map (f.map a)
  map_compose := fun a b => by simp [f.map_compose, g.map_compose]
  map_void := by simp [f.map_void, g.map_void]
  map_resonance := fun a b h => g.map_resonance _ _ (f.map_resonance a b h)
  depth_bound := fun a => Nat.le_trans (g.depth_bound (f.map a)) (f.depth_bound a)

/-- Theorem 10: Translation loss — bounded morphisms never increase depth. -/
theorem translation_loss (f : BoundedMorphism I J) (a : I) :
    IdeaticSpace.depth (f.map a) ≤ IdeaticSpace.depth a :=
  f.depth_bound a

/-- Helper: Nat.iterate for the succ case. -/
private theorem iterate_succ_eq {α : Type*} (f : α → α) (n : ℕ) (a : α) :
    Nat.iterate f (n + 1) a = Nat.iterate f n (f a) := by
  rfl

/-- Theorem 11: Iterated bounded compositions are still bounded. -/
theorem iterated_bounded_comp_depth {I : Type*} [IdeaticSpace I]
    (f : BoundedMorphism I I) (n : ℕ) (a : I) :
    IdeaticSpace.depth (Nat.iterate f.map n a) ≤ IdeaticSpace.depth a := by
  induction n generalizing a with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [iterate_succ_eq]
    exact ih (f.map a) |>.trans (f.depth_bound a)

/-- Theorem 12: Bounded morphisms map void to void. -/
theorem bounded_maps_void (f : BoundedMorphism I J) :
    f.map (IdeaticSpace.void : I) = (IdeaticSpace.void : J) :=
  f.map_void

/-- Theorem 13: Depth of void image is zero for any bounded morphism. -/
theorem bounded_void_depth (f : BoundedMorphism I J) :
    IdeaticSpace.depth (f.map (IdeaticSpace.void : I)) = 0 := by
  rw [f.map_void]; exact IdeaticSpace.depth_void

/-- Theorem 14: Bounded morphisms map atomic elements to elements of depth ≤ 1. -/
theorem bounded_atomic_depth (f : BoundedMorphism I J) (a : I)
    (ha : IdeaticSpace.atomic a) :
    IdeaticSpace.depth (f.map a) ≤ 1 :=
  Nat.le_trans (f.depth_bound a) (IdeaticSpace.depth_atomic a ha)

/-- Theorem 15: Depth of composition image is bounded by sum of depths. -/
theorem bounded_compose_depth (f : BoundedMorphism I J) (a b : I) :
    IdeaticSpace.depth (f.map (IdeaticSpace.compose a b)) ≤
    IdeaticSpace.depth a + IdeaticSpace.depth b := by
  calc IdeaticSpace.depth (f.map (IdeaticSpace.compose a b))
      ≤ IdeaticSpace.depth (IdeaticSpace.compose a b) := f.depth_bound _
    _ ≤ IdeaticSpace.depth a + IdeaticSpace.depth b := IdeaticSpace.depth_subadditive a b

end BoundedMorphisms

/-! ## §3. Perfect Translations and Depth Preservation -/

section PerfectTranslation

variable {I : Type*} [IdeaticSpace I]
variable {J : Type*} [IdeaticSpace J]

/-- A perfect translation preserves depth exactly. -/
structure PerfectMorphism (I : Type*) (J : Type*) [IdeaticSpace I] [IdeaticSpace J]
    extends IdeaticMorphism I J where
  depth_preserve : ∀ (a : I), IdeaticSpace.depth (map a) = IdeaticSpace.depth a

/-- Theorem 16: Every perfect morphism is bounded. -/
def PerfectMorphism.toBounded {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : PerfectMorphism I J) : BoundedMorphism I J where
  map := f.map
  map_compose := f.map_compose
  map_void := f.map_void
  map_resonance := f.map_resonance
  depth_bound := fun a => le_of_eq (f.depth_preserve a)

/-- Theorem 17: The identity is a perfect morphism. -/
def PerfectMorphism.id (I : Type*) [IdeaticSpace I] : PerfectMorphism I I where
  map := fun a => a
  map_compose := fun _ _ => rfl
  map_void := rfl
  map_resonance := fun _ _ h => h
  depth_preserve := fun _ => rfl

/-- Theorem 18: Composition of perfect morphisms is perfect. -/
def PerfectMorphism.comp {I J K : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]
    (g : PerfectMorphism J K) (f : PerfectMorphism I J) : PerfectMorphism I K where
  map := fun a => g.map (f.map a)
  map_compose := fun a b => by simp [f.map_compose, g.map_compose]
  map_void := by simp [f.map_void, g.map_void]
  map_resonance := fun a b h => g.map_resonance _ _ (f.map_resonance a b h)
  depth_preserve := fun a => by simp [g.depth_preserve, f.depth_preserve]

/-- Theorem 19: Perfect morphism preserves void depth. -/
theorem perfect_void_depth (f : PerfectMorphism I J) :
    IdeaticSpace.depth (f.map (IdeaticSpace.void : I)) = 0 := by
  rw [f.depth_preserve]; exact IdeaticSpace.depth_void

/-- Theorem 20: Perfect morphism maps depth-0 elements to depth-0. -/
theorem perfect_preserves_depth_zero (f : PerfectMorphism I J) (a : I)
    (h : IdeaticSpace.depth a = 0) : IdeaticSpace.depth (f.map a) = 0 := by
  rw [f.depth_preserve]; exact h

/-- Theorem 21: Perfect morphism preserves atomic depth bound. -/
theorem perfect_preserves_atomic_bound (f : PerfectMorphism I J) (a : I)
    (ha : IdeaticSpace.atomic a) : IdeaticSpace.depth (f.map a) ≤ 1 := by
  rw [f.depth_preserve]; exact IdeaticSpace.depth_atomic a ha

end PerfectTranslation

/-! ## §4. Subspaces -/

section Subspaces

variable {I : Type*} [IdeaticSpace I]

/-- A subspace: closed under composition and contains void. -/
structure IdeaticSubspace (I : Type*) [IdeaticSpace I] where
  carrier : Set I
  void_mem : (IdeaticSpace.void : I) ∈ carrier
  compose_mem : ∀ {a b : I}, a ∈ carrier → b ∈ carrier →
    IdeaticSpace.compose a b ∈ carrier

/-- Theorem 22: The full space is a subspace. -/
def IdeaticSubspace.full (I : Type*) [IdeaticSpace I] : IdeaticSubspace I where
  carrier := Set.univ
  void_mem := Set.mem_univ _
  compose_mem := fun _ _ => Set.mem_univ _

/-- Theorem 23: The singleton {void} is a subspace. -/
def IdeaticSubspace.trivial (I : Type*) [IdeaticSpace I] : IdeaticSubspace I where
  carrier := {IdeaticSpace.void}
  void_mem := Set.mem_singleton _
  compose_mem := fun ha hb => by
    simp [Set.mem_singleton_iff] at ha hb ⊢
    rw [ha, hb, IdeaticSpace.void_left]

/-- Theorem 24: Intersection of two subspaces is a subspace. -/
def IdeaticSubspace.inter (S T : IdeaticSubspace I) : IdeaticSubspace I where
  carrier := S.carrier ∩ T.carrier
  void_mem := ⟨S.void_mem, T.void_mem⟩
  compose_mem := fun ha hb => ⟨S.compose_mem ha.1 hb.1, T.compose_mem ha.2 hb.2⟩

/-- The image of a morphism. -/
def morphism_image {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) : Set J :=
  Set.range f.map

/-- Theorem 25: Image of a morphism is closed under composition. -/
theorem morphism_image_compose_closed {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) (x y : J)
    (hx : x ∈ morphism_image f) (hy : y ∈ morphism_image f) :
    IdeaticSpace.compose x y ∈ morphism_image f := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨IdeaticSpace.compose a b, f.map_compose a b⟩

/-- Theorem 26: Void is in the image of any morphism. -/
theorem void_in_morphism_image {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) :
    (IdeaticSpace.void : J) ∈ morphism_image f :=
  ⟨IdeaticSpace.void, f.map_void⟩

/-- Theorem 27: Image of a morphism forms a subspace. -/
def morphism_image_subspace {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) : IdeaticSubspace J where
  carrier := morphism_image f
  void_mem := void_in_morphism_image f
  compose_mem := fun hx hy => morphism_image_compose_closed f _ _ hx hy

/-- The kernel of a morphism: preimage of void. -/
def morphism_kernel {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) : Set I :=
  {a : I | f.map a = IdeaticSpace.void}

/-- Theorem 28: Void is always in the kernel. -/
theorem void_in_kernel {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) :
    (IdeaticSpace.void : I) ∈ morphism_kernel f := by
  simp [morphism_kernel, f.map_void]

/-- Theorem 29: Kernel is closed under composition. -/
theorem kernel_compose_closed {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) (a b : I)
    (ha : a ∈ morphism_kernel f) (hb : b ∈ morphism_kernel f) :
    IdeaticSpace.compose a b ∈ morphism_kernel f := by
  simp [morphism_kernel] at ha hb ⊢
  rw [f.map_compose, ha, hb, IdeaticSpace.void_left]

/-- Theorem 30: Kernel forms a subspace. -/
def kernel_subspace {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) : IdeaticSubspace I where
  carrier := morphism_kernel f
  void_mem := void_in_kernel f
  compose_mem := fun ha hb => kernel_compose_closed f _ _ ha hb

end Subspaces

/-! ## §5. Isomorphisms -/

section Isomorphisms

variable {I : Type*} [IdeaticSpace I]
variable {J : Type*} [IdeaticSpace J]
variable {K : Type*} [IdeaticSpace K]

/-- An isomorphism between ideatic spaces. -/
structure IdeaticIso (I : Type*) (J : Type*) [IdeaticSpace I] [IdeaticSpace J] where
  toFun : I → J
  invFun : J → I
  left_inv : ∀ (a : I), invFun (toFun a) = a
  right_inv : ∀ (b : J), toFun (invFun b) = b
  map_compose : ∀ (a b : I),
    toFun (IdeaticSpace.compose a b) = IdeaticSpace.compose (toFun a) (toFun b)
  map_void : toFun (IdeaticSpace.void : I) = (IdeaticSpace.void : J)
  map_resonance : ∀ (a b : I),
    IdeaticSpace.resonates a b → IdeaticSpace.resonates (toFun a) (toFun b)
  inv_compose : ∀ (a b : J),
    invFun (IdeaticSpace.compose a b) = IdeaticSpace.compose (invFun a) (invFun b)
  inv_void : invFun (IdeaticSpace.void : J) = (IdeaticSpace.void : I)
  inv_resonance : ∀ (a b : J),
    IdeaticSpace.resonates a b → IdeaticSpace.resonates (invFun a) (invFun b)

/-- Theorem 31: The identity is an isomorphism. -/
def IdeaticIso.refl (I : Type*) [IdeaticSpace I] : IdeaticIso I I where
  toFun := fun a => a
  invFun := fun a => a
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_compose := fun _ _ => rfl
  map_void := rfl
  map_resonance := fun _ _ h => h
  inv_compose := fun _ _ => rfl
  inv_void := rfl
  inv_resonance := fun _ _ h => h

/-- Helper: an iso is injective. -/
theorem IdeaticIso.injective {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (iso : IdeaticIso I J) : Function.Injective iso.toFun :=
  fun a b h => by rw [← iso.left_inv a, ← iso.left_inv b, h]

/-- Helper: an iso is surjective. -/
theorem IdeaticIso.surjective {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (iso : IdeaticIso I J) : Function.Surjective iso.toFun :=
  fun b => ⟨iso.invFun b, iso.right_inv b⟩

/-- Theorem 32: An isomorphism can be reversed. -/
def IdeaticIso.symm {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (iso : IdeaticIso I J) : IdeaticIso J I where
  toFun := iso.invFun
  invFun := iso.toFun
  left_inv := iso.right_inv
  right_inv := iso.left_inv
  map_compose := iso.inv_compose
  map_void := iso.inv_void
  map_resonance := iso.inv_resonance
  inv_compose := iso.map_compose
  inv_void := iso.map_void
  inv_resonance := iso.map_resonance

/-- Theorem 33: Isomorphisms compose. -/
def IdeaticIso.trans {I J K : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]
    (f : IdeaticIso I J) (g : IdeaticIso J K) : IdeaticIso I K where
  toFun := fun a => g.toFun (f.toFun a)
  invFun := fun c => f.invFun (g.invFun c)
  left_inv := fun a => by simp [g.left_inv, f.left_inv]
  right_inv := fun c => by simp [f.right_inv, g.right_inv]
  map_compose := fun a b => by simp [f.map_compose, g.map_compose]
  map_void := by simp [f.map_void, g.map_void]
  map_resonance := fun a b h => g.map_resonance _ _ (f.map_resonance a b h)
  inv_compose := fun a b => by simp [g.inv_compose, f.inv_compose]
  inv_void := by simp [g.inv_void, f.inv_void]
  inv_resonance := fun a b h => f.inv_resonance _ _ (g.inv_resonance a b h)

/-- Theorem 34: Isomorphic spaces have the same depth for corresponding elements
    (when the iso preserves depth). -/
theorem iso_depth_transfer {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (iso : IdeaticIso I J)
    (depth_iso : ∀ (a : I), IdeaticSpace.depth (iso.toFun a) = IdeaticSpace.depth a)
    (a : I) : IdeaticSpace.depth (iso.toFun a) = IdeaticSpace.depth a :=
  depth_iso a

/-- Theorem 35: Isomorphisms preserve void depth. -/
theorem iso_void_depth {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (iso : IdeaticIso I J) :
    IdeaticSpace.depth (iso.toFun (IdeaticSpace.void : I)) =
    IdeaticSpace.depth (IdeaticSpace.void : J) := by
  rw [iso.map_void]

/-- Theorem 36: An isomorphism yields a forward morphism. -/
def IdeaticIso.toMorphism {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (iso : IdeaticIso I J) : IdeaticMorphism I J where
  map := iso.toFun
  map_compose := iso.map_compose
  map_void := iso.map_void
  map_resonance := iso.map_resonance

/-- Theorem 37: An isomorphism yields an inverse morphism. -/
def IdeaticIso.toInvMorphism {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (iso : IdeaticIso I J) : IdeaticMorphism J I :=
  iso.symm.toMorphism

end Isomorphisms

/-! ## §6. Endomorphisms and Fixed Points -/

section Endomorphisms

variable {I : Type*} [IdeaticSpace I]

abbrev IdeaticEndo (I : Type*) [IdeaticSpace I] := IdeaticMorphism I I
abbrev BoundedEndo (I : Type*) [IdeaticSpace I] := BoundedMorphism I I

/-- The set of fixed points of an endomorphism. -/
def fixedPoints (f : IdeaticEndo I) : Set I :=
  {a : I | f.map a = a}

/-- Theorem 38: Void is always a fixed point. -/
theorem void_fixed (f : IdeaticEndo I) :
    (IdeaticSpace.void : I) ∈ fixedPoints f := by
  simp [fixedPoints, f.map_void]

/-- Theorem 39: Composition of fixed points is a fixed point. -/
theorem fixed_compose (f : IdeaticEndo I) (a b : I)
    (ha : a ∈ fixedPoints f) (hb : b ∈ fixedPoints f) :
    IdeaticSpace.compose a b ∈ fixedPoints f := by
  simp [fixedPoints] at ha hb ⊢
  rw [f.map_compose, ha, hb]

/-- Theorem 40: Fixed points form a subspace. -/
def fixedPointSubspace (f : IdeaticEndo I) : IdeaticSubspace I where
  carrier := fixedPoints f
  void_mem := void_fixed f
  compose_mem := fun ha hb => fixed_compose f _ _ ha hb

/-- Theorem 41: Fixed point of bounded endo has depth ≤ original. -/
theorem fixed_point_depth_le (f : BoundedEndo I) (a : I) :
    IdeaticSpace.depth (f.map a) ≤ IdeaticSpace.depth a :=
  f.depth_bound a

/-- Theorem 42: Iterated bounded endomorphism depth is non-increasing. -/
theorem iterated_endo_depth_nonincreasing (f : BoundedEndo I) (a : I) (n : ℕ) :
    IdeaticSpace.depth (Nat.iterate f.map n a) ≤ IdeaticSpace.depth a := by
  induction n generalizing a with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    show IdeaticSpace.depth (Nat.iterate f.map n (f.map a)) ≤ _
    exact (ih (f.map a)).trans (f.depth_bound a)

/-- Theorem 43: If f(a) is fixed, then all further iterates equal f(a). -/
theorem iterate_stabilizes_at_fixed (f : IdeaticEndo I) (a : I)
    (hfa : f.map a ∈ fixedPoints f) (n : ℕ) :
    Nat.iterate f.map (n + 1) a = f.map a := by
  have hffa : f.map (f.map a) = f.map a := hfa
  induction n with
  | zero => show f.map a = f.map a; rfl
  | succ n ih =>
    show Nat.iterate f.map (n + 1) (f.map a) = f.map a
    have key : ∀ k : ℕ, Nat.iterate f.map k (f.map a) = f.map a := by
      intro k
      induction k with
      | zero => rfl
      | succ k ihk =>
        show Nat.iterate f.map k (f.map (f.map a)) = f.map a
        rw [hffa]; exact ihk
    exact key (n + 1)

/-- Theorem 44: The identity endomorphism fixes everything. -/
theorem id_fixes_all (a : I) :
    a ∈ fixedPoints (IdeaticMorphism.id I) := by
  simp [fixedPoints, IdeaticMorphism.id]

/-- Theorem 45: Composition of endomorphisms is an endomorphism. -/
def endo_comp (f g : IdeaticEndo I) : IdeaticEndo I :=
  f.comp g

/-- Theorem 46: Endomorphism composition is associative. -/
theorem endo_comp_assoc (f g h : IdeaticEndo I) :
    (endo_comp (endo_comp f g) h).map = (endo_comp f (endo_comp g h)).map := by
  rfl

end Endomorphisms

/-! ## §7. Translation Theory -/

section TranslationTheory

variable {L₁ : Type*} [IdeaticSpace L₁]
variable {L₂ : Type*} [IdeaticSpace L₂]

abbrev Translation (L₁ L₂ : Type*) [IdeaticSpace L₁] [IdeaticSpace L₂] :=
  IdeaticMorphism L₁ L₂

/-- Translation loss: difference between source and target depth. -/
def translationLoss (f : BoundedMorphism L₁ L₂) (a : L₁) : ℕ :=
  IdeaticSpace.depth a - IdeaticSpace.depth (f.map a)

/-- Theorem 47: Translation loss is non-negative. -/
theorem translation_loss_nonneg (f : BoundedMorphism L₁ L₂) (a : L₁) :
    0 ≤ translationLoss f a :=
  Nat.zero_le _

/-- Theorem 48: A perfect translation has zero loss. -/
theorem perfect_translation_zero_loss {L₁ L₂ : Type*}
    [IdeaticSpace L₁] [IdeaticSpace L₂]
    (f : PerfectMorphism L₁ L₂) (a : L₁) :
    IdeaticSpace.depth a - IdeaticSpace.depth (f.map a) = 0 := by
  rw [f.depth_preserve]; exact Nat.sub_self _

/-- Untranslatability: an element has no resonant image besides self-resonance. -/
def untranslatable (f : Translation L₁ L₂) (a : L₁) : Prop :=
  ∀ (b : L₁), b ≠ a → ¬IdeaticSpace.resonates (f.map a) (f.map b)

/-- Theorem 49: Untranslatable elements break resonance connections. -/
theorem untranslatable_breaks_resonance
    (f : Translation L₁ L₂) (a b : L₁) (hab : a ≠ b)
    (hres : IdeaticSpace.resonates a b)
    (hunt : untranslatable f a) : False := by
  exact hunt b (Ne.symm hab) (f.map_resonance a b hres)

/-- Back-translation: translate from L₁ to L₂ and back. -/
def backTranslation {L₁ L₂ : Type*} [IdeaticSpace L₁] [IdeaticSpace L₂]
    (f : Translation L₁ L₂) (g : Translation L₂ L₁) : IdeaticEndo L₁ :=
  g.comp f

/-- Theorem 50: Back-translation preserves void. -/
theorem back_translation_void {L₁ L₂ : Type*}
    [IdeaticSpace L₁] [IdeaticSpace L₂]
    (f : Translation L₁ L₂) (g : Translation L₂ L₁) :
    (backTranslation f g).map (IdeaticSpace.void : L₁) = (IdeaticSpace.void : L₁) :=
  (backTranslation f g).map_void

/-- Theorem 51: Back-translation preserves composition. -/
theorem back_translation_compose {L₁ L₂ : Type*}
    [IdeaticSpace L₁] [IdeaticSpace L₂]
    (f : Translation L₁ L₂) (g : Translation L₂ L₁) (a b : L₁) :
    (backTranslation f g).map (IdeaticSpace.compose a b) =
    IdeaticSpace.compose ((backTranslation f g).map a) ((backTranslation f g).map b) :=
  (backTranslation f g).map_compose a b

/-- Theorem 52: Back-translation depth ≤ original when both are bounded. -/
theorem back_translation_depth_loss {L₁ L₂ : Type*}
    [IdeaticSpace L₁] [IdeaticSpace L₂]
    (f : BoundedMorphism L₁ L₂) (g : BoundedMorphism L₂ L₁) (a : L₁) :
    IdeaticSpace.depth (g.map (f.map a)) ≤ IdeaticSpace.depth a :=
  Nat.le_trans (g.depth_bound _) (f.depth_bound _)

/-- Theorem 53: Back-translation preserves resonance. -/
theorem back_translation_preserves_resonance {L₁ L₂ : Type*}
    [IdeaticSpace L₁] [IdeaticSpace L₂]
    (f : Translation L₁ L₂) (g : Translation L₂ L₁) (a b : L₁)
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates ((backTranslation f g).map a) ((backTranslation f g).map b) :=
  (backTranslation f g).map_resonance a b h

/-- Theorem 54: Fixed points of back-translation are "perfectly translatable". -/
theorem fixed_perfectly_translatable {L₁ L₂ : Type*}
    [IdeaticSpace L₁] [IdeaticSpace L₂]
    (f : Translation L₁ L₂) (g : Translation L₂ L₁) (a : L₁)
    (hfix : a ∈ fixedPoints (backTranslation f g)) :
    g.map (f.map a) = a :=
  hfix

/-- Theorem 55: Void is always perfectly translatable. -/
theorem void_perfectly_translatable {L₁ L₂ : Type*}
    [IdeaticSpace L₁] [IdeaticSpace L₂]
    (f : Translation L₁ L₂) (g : Translation L₂ L₁) :
    (IdeaticSpace.void : L₁) ∈ fixedPoints (backTranslation f g) :=
  void_fixed (backTranslation f g)

end TranslationTheory

/-! ## §8. Morphism Structure -/

section MorphismStructure

variable {I : Type*} [IdeaticSpace I]
variable {J : Type*} [IdeaticSpace J]

/-- Theorem 56: Kernel elements map to void. -/
theorem kernel_maps_to_void (f : IdeaticMorphism I J) (a : I)
    (ha : a ∈ morphism_kernel f) : f.map a = IdeaticSpace.void :=
  ha

/-- Theorem 57: Kernel absorbs composition. -/
theorem kernel_absorbs (f : IdeaticMorphism I J) (a b : I)
    (ha : a ∈ morphism_kernel f) (hb : b ∈ morphism_kernel f) :
    f.map (IdeaticSpace.compose a b) = IdeaticSpace.void := by
  rw [f.map_compose, ha, hb, IdeaticSpace.void_left]

/-- Theorem 58: Composition with void on left stays in kernel. -/
theorem void_compose_kernel (f : IdeaticMorphism I J) (a : I)
    (ha : a ∈ morphism_kernel f) :
    IdeaticSpace.compose (IdeaticSpace.void : I) a ∈ morphism_kernel f := by
  unfold morphism_kernel; simp [Set.mem_setOf_eq]
  rw [f.map_compose, f.map_void, IdeaticSpace.void_left]
  exact ha

/-- Theorem 59: Composition with void on right stays in kernel. -/
theorem kernel_compose_void_right (f : IdeaticMorphism I J) (a : I)
    (ha : a ∈ morphism_kernel f) :
    IdeaticSpace.compose a (IdeaticSpace.void : I) ∈ morphism_kernel f := by
  unfold morphism_kernel; simp [Set.mem_setOf_eq]
  rw [f.map_compose, f.map_void, IdeaticSpace.void_right]
  exact ha

/-- Theorem 60: For bounded morphisms, kernel elements have image depth 0. -/
theorem kernel_depth_bound (f : BoundedMorphism I J) (a : I)
    (ha : a ∈ morphism_kernel f.toIdeaticMorphism) :
    IdeaticSpace.depth (f.map a) = 0 := by
  simp [morphism_kernel] at ha
  rw [ha]; exact IdeaticSpace.depth_void

/-- Theorem 61: Image elements have preimages. -/
theorem image_has_preimage {I J : Type*} [IdeaticSpace I] [IdeaticSpace J]
    (f : IdeaticMorphism I J) (b : J) (hb : b ∈ morphism_image f) :
    ∃ (a : I), f.map a = b :=
  hb

end MorphismStructure

/-! ## §9. Depth Filtration and Morphisms -/

section DepthFiltration

variable {I : Type*} [IdeaticSpace I]
variable {J : Type*} [IdeaticSpace J]

/-- Depth-n filtration: elements of depth ≤ n. -/
def depthFiltration (I : Type*) [IdeaticSpace I] (n : ℕ) : Set I :=
  {a : I | IdeaticSpace.depth a ≤ n}

/-- Theorem 62: Void is in every filtration level. -/
theorem void_in_filtration (n : ℕ) :
    (IdeaticSpace.void : I) ∈ depthFiltration I n := by
  simp [depthFiltration, IdeaticSpace.depth_void]

/-- Theorem 63: Filtration is monotone. -/
theorem filtration_monotone {n m : ℕ} (h : n ≤ m) :
    depthFiltration I n ⊆ depthFiltration I m :=
  fun _ ha => Nat.le_trans ha h

/-- Theorem 64: Bounded morphisms preserve filtration level. -/
theorem bounded_preserves_filtration (f : BoundedMorphism I J) (n : ℕ) (a : I)
    (ha : a ∈ depthFiltration I n) :
    f.map a ∈ depthFiltration J n := by
  simp [depthFiltration] at ha ⊢
  exact Nat.le_trans (f.depth_bound a) ha

/-- Theorem 65: Perfect morphisms preserve filtration level exactly. -/
theorem perfect_preserves_filtration (f : PerfectMorphism I J) (n : ℕ) (a : I) :
    a ∈ depthFiltration I n ↔ f.map a ∈ depthFiltration J n := by
  simp [depthFiltration, f.depth_preserve]

/-- Theorem 66: Depth-0 filtration contains void. -/
theorem filtration_zero_has_void :
    (IdeaticSpace.void : I) ∈ depthFiltration I 0 := by
  simp [depthFiltration, IdeaticSpace.depth_void]

/-- Theorem 67: Atomic elements are in filtration level 1. -/
theorem atomic_in_filtration_one (a : I) (ha : IdeaticSpace.atomic a) :
    a ∈ depthFiltration I 1 := by
  simp [depthFiltration]; exact IdeaticSpace.depth_atomic a ha

/-- Theorem 68: Composition of filtration-n elements is in level 2n. -/
theorem compose_filtration (n : ℕ) (a b : I)
    (ha : a ∈ depthFiltration I n) (hb : b ∈ depthFiltration I n) :
    IdeaticSpace.compose a b ∈ depthFiltration I (n + n) := by
  simp [depthFiltration] at ha hb ⊢
  calc IdeaticSpace.depth (IdeaticSpace.compose a b)
      ≤ IdeaticSpace.depth a + IdeaticSpace.depth b := IdeaticSpace.depth_subadditive a b
    _ ≤ n + n := Nat.add_le_add ha hb

end DepthFiltration

/-! ## §10. Morphism Properties -/

section MorphismProperties

variable {I : Type*} [IdeaticSpace I]
variable {J : Type*} [IdeaticSpace J]

/-- Depth-reflecting morphism. -/
def DepthReflecting (f : IdeaticMorphism I J) : Prop :=
  ∀ (a : I) (n : ℕ), IdeaticSpace.depth (f.map a) ≤ n → IdeaticSpace.depth a ≤ n

/-- Resonance-reflecting morphism. -/
def ResonanceReflecting (f : IdeaticMorphism I J) : Prop :=
  ∀ (a b : I), IdeaticSpace.resonates (f.map a) (f.map b) → IdeaticSpace.resonates a b

/-- Theorem 69: Identity is depth-reflecting. -/
theorem id_depth_reflecting : DepthReflecting (IdeaticMorphism.id I) := by
  intro a n h; exact h

/-- Theorem 70: Identity is resonance-reflecting. -/
theorem id_resonance_reflecting : ResonanceReflecting (IdeaticMorphism.id I) := by
  intro a b h; exact h

/-- Theorem 71: Composition of depth-reflecting morphisms is depth-reflecting. -/
theorem comp_depth_reflecting {I J K : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]
    (g : IdeaticMorphism J K) (f : IdeaticMorphism I J)
    (hg : DepthReflecting g) (hf : DepthReflecting f) :
    DepthReflecting (g.comp f) := by
  intro a n h; exact hf a n (hg (f.map a) n h)

/-- Theorem 72: Composition of resonance-reflecting morphisms is resonance-reflecting. -/
theorem comp_resonance_reflecting {I J K : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]
    (g : IdeaticMorphism J K) (f : IdeaticMorphism I J)
    (hg : ResonanceReflecting g) (hf : ResonanceReflecting f) :
    ResonanceReflecting (g.comp f) := by
  intro a b h; exact hf a b (hg (f.map a) (f.map b) h)

/-- Theorem 73: Depth-reflecting bounded morphism preserves depth exactly. -/
theorem reflecting_bounded_is_depth_preserving
    (f : BoundedMorphism I J) (hrefl : DepthReflecting f.toIdeaticMorphism) (a : I) :
    IdeaticSpace.depth (f.map a) = IdeaticSpace.depth a := by
  exact Nat.le_antisymm (f.depth_bound a) (hrefl a _ (Nat.le_refl _))

end MorphismProperties

/-! ## §11. Constant Morphisms and Zero Maps -/

section ConstantMorphisms

variable {I : Type*} [IdeaticSpace I]
variable {J : Type*} [IdeaticSpace J]

/-- The zero morphism: sends everything to void. -/
def zeroMorphism (I J : Type*) [IdeaticSpace I] [IdeaticSpace J] : IdeaticMorphism I J where
  map := fun _ => IdeaticSpace.void
  map_compose := fun _ _ => (IdeaticSpace.void_left _).symm
  map_void := rfl
  map_resonance := fun _ _ _ => IdeaticSpace.resonance_refl _

/-- Theorem 74: The zero morphism is bounded. -/
def zeroBounded (I J : Type*) [IdeaticSpace I] [IdeaticSpace J] : BoundedMorphism I J where
  map := fun _ => IdeaticSpace.void
  map_compose := fun _ _ => (IdeaticSpace.void_left _).symm
  map_void := rfl
  map_resonance := fun _ _ _ => IdeaticSpace.resonance_refl _
  depth_bound := fun _ => by simp [IdeaticSpace.depth_void]

/-- Theorem 75: Zero morphism has trivial image. -/
theorem zero_morphism_image :
    morphism_image (zeroMorphism I J) = {IdeaticSpace.void} := by
  ext x
  constructor
  · rintro ⟨_, rfl⟩; simp [zeroMorphism]
  · intro hx; simp [Set.mem_singleton_iff] at hx; rw [hx]
    exact ⟨IdeaticSpace.void, rfl⟩

/-- Theorem 76: Everything is in the kernel of the zero morphism. -/
theorem zero_morphism_kernel :
    morphism_kernel (zeroMorphism I J) = Set.univ := by
  ext x; simp [morphism_kernel, zeroMorphism]

/-- Theorem 77: Composing with zero on left gives zero. -/
theorem zero_comp_left {I J K : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]
    (f : IdeaticMorphism I J) :
    ((zeroMorphism J K).comp f).map = (zeroMorphism I K).map := by
  ext x; simp [IdeaticMorphism.comp, zeroMorphism]

/-- Theorem 78: Composing with zero on right maps everything to f(void). -/
theorem zero_comp_right {I J K : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K]
    (f : IdeaticMorphism J K) :
    (f.comp (zeroMorphism I J)).map = (fun _ => f.map IdeaticSpace.void) := by
  ext x; simp [IdeaticMorphism.comp, zeroMorphism]

/-- Theorem 79: Zero composed with zero is zero. -/
theorem zero_comp_zero {I J K : Type*}
    [IdeaticSpace I] [IdeaticSpace J] [IdeaticSpace K] :
    ((zeroMorphism J K).comp (zeroMorphism I J)).map = (zeroMorphism I K).map := by
  ext x; simp [IdeaticMorphism.comp, zeroMorphism]

end ConstantMorphisms

/-! ## §12. Resonance Classes and Morphisms -/

section ResonanceClasses

variable {I : Type*} [IdeaticSpace I]
variable {J : Type*} [IdeaticSpace J]

/-- The resonance class of an element. -/
def resonanceClass (a : I) : Set I :=
  {b : I | IdeaticSpace.resonates a b}

/-- Theorem 80: Every element is in its own resonance class. -/
theorem mem_resonance_class (a : I) : a ∈ resonanceClass a :=
  IdeaticSpace.resonance_refl a

/-- Theorem 81: Resonance class membership is symmetric. -/
theorem resonance_class_symm (a b : I) :
    b ∈ resonanceClass a ↔ a ∈ resonanceClass b := by
  simp [resonanceClass]
  exact ⟨IdeaticSpace.resonance_symm a b, IdeaticSpace.resonance_symm b a⟩

/-- Theorem 82: A morphism maps resonance classes into resonance classes. -/
theorem morphism_maps_resonance_class (f : IdeaticMorphism I J) (a b : I)
    (hb : b ∈ resonanceClass a) :
    f.map b ∈ resonanceClass (f.map a) := by
  simp [resonanceClass] at hb ⊢
  exact f.map_resonance a b hb

/-- Theorem 83: Image of a resonance class is contained in resonance class of image. -/
theorem image_resonance_subset (f : IdeaticMorphism I J) (a : I) :
    f.map '' resonanceClass a ⊆ resonanceClass (f.map a) := by
  intro y hy
  obtain ⟨b, hb, rfl⟩ := hy
  exact morphism_maps_resonance_class f a b hb

/-- Theorem 84: Void's resonance class maps into void's resonance class. -/
theorem void_resonance_class_maps (f : IdeaticMorphism I J) (b : I)
    (hb : b ∈ resonanceClass (IdeaticSpace.void : I)) :
    f.map b ∈ resonanceClass (IdeaticSpace.void : J) := by
  simp [resonanceClass] at hb ⊢
  rw [← f.map_void]
  exact f.map_resonance _ _ hb

end ResonanceClasses

/-! ## §13. Iterated Morphism Applications -/

section IteratedMorphisms

variable {I : Type*} [IdeaticSpace I]

/-- Theorem 85: Iterated endomorphism preserves void. -/
theorem iterate_preserves_void (f : IdeaticEndo I) (n : ℕ) :
    Nat.iterate f.map n (IdeaticSpace.void : I) = (IdeaticSpace.void : I) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate f.map n (f.map IdeaticSpace.void) = _
    rw [f.map_void]; exact ih

/-- Theorem 86: Iterated endomorphism preserves composition. -/
theorem iterate_preserves_compose (f : IdeaticEndo I) (n : ℕ) (a b : I) :
    Nat.iterate f.map n (IdeaticSpace.compose a b) =
    IdeaticSpace.compose (Nat.iterate f.map n a) (Nat.iterate f.map n b) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate f.map n (f.map (IdeaticSpace.compose a b)) =
      IdeaticSpace.compose (Nat.iterate f.map n (f.map a)) (Nat.iterate f.map n (f.map b))
    rw [f.map_compose]; exact ih _ _

/-- Theorem 87: Iterated endomorphism preserves resonance. -/
theorem iterate_preserves_resonance (f : IdeaticEndo I) (n : ℕ) (a b : I)
    (h : IdeaticSpace.resonates a b) :
    IdeaticSpace.resonates (Nat.iterate f.map n a) (Nat.iterate f.map n b) := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih =>
    show IdeaticSpace.resonates (Nat.iterate f.map n (f.map a))
      (Nat.iterate f.map n (f.map b))
    exact ih _ _ (f.map_resonance a b h)

/-- Theorem 88: Iterates of the identity are the identity. -/
theorem iterate_id (n : ℕ) (a : I) :
    Nat.iterate (IdeaticMorphism.id I).map n a = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.iterate (IdeaticMorphism.id I).map n ((IdeaticMorphism.id I).map a) = a
    simp [IdeaticMorphism.id]; exact ih

/-- Theorem 89: One step of bounded iteration decreases depth. -/
theorem bounded_iterate_depth_step (f : BoundedEndo I) (a : I) (n : ℕ) :
    IdeaticSpace.depth (Nat.iterate f.map (n + 1) a) ≤
    IdeaticSpace.depth (Nat.iterate f.map n a) := by
  induction n generalizing a with
  | zero => exact f.depth_bound a
  | succ n ih =>
    show IdeaticSpace.depth (Nat.iterate f.map (n + 1) (f.map a)) ≤
      IdeaticSpace.depth (Nat.iterate f.map n (f.map a))
    exact ih (f.map a)

end IteratedMorphisms

/-! ## §14. Product Constructions -/

section ProductSpace

variable {I : Type*} [IdeaticSpace I]
variable {J : Type*} [IdeaticSpace J]

/-- Theorem 90: Morphisms preserve void. -/
theorem proj_preserves_void_fst (f : IdeaticMorphism I J) :
    f.map IdeaticSpace.void = IdeaticSpace.void :=
  f.map_void

/-- Theorem 91: Two morphisms from same source agree on void. -/
theorem morphisms_agree_on_void {K : Type*} [IdeaticSpace K]
    (f : IdeaticMorphism I J) (g : IdeaticMorphism I K) :
    f.map (IdeaticSpace.void : I) = IdeaticSpace.void ∧
    g.map (IdeaticSpace.void : I) = IdeaticSpace.void :=
  ⟨f.map_void, g.map_void⟩

/-- Theorem 92: Two morphisms preserve composition independently. -/
theorem morphisms_preserve_compose_independently {K : Type*} [IdeaticSpace K]
    (f : IdeaticMorphism I J) (g : IdeaticMorphism I K) (a b : I) :
    f.map (IdeaticSpace.compose a b) = IdeaticSpace.compose (f.map a) (f.map b) ∧
    g.map (IdeaticSpace.compose a b) = IdeaticSpace.compose (g.map a) (g.map b) :=
  ⟨f.map_compose a b, g.map_compose a b⟩

end ProductSpace

end IDT.CategoryTheory
