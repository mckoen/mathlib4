/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/

module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.CategoryTheory.DGCategory.HomotopyCategory

/-!
# Right DG modules and their homotopy category

This file develops right modules over a DG category from their enriched action. It includes the
signed tensor-cochain calculus, the DG enrichment by graded natural transformations, zero, shift,
tensor, and cone operations, and the quotient category of right modules by module homotopy.
-/

@[expose] public section

universe w u

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace DGCategory

variable {R : Type w} [CommRing R]

local notation "V" => CochainComplex (ModuleCat R) ℤ

variable (A : Type u) [DGCategory R A]

/-- A right DG module over `A`, presented by its contravariant enriched action. -/
structure RightModule where
  /-- The value of the module on an object of `A`. -/
  obj : A → V
  /-- A morphism `X ⟶ Y` acts on `M(Y)` to produce an element of `M(X)`. -/
  action : ∀ X Y : A, (X ⟶[V] Y) ⊗ obj Y ⟶ obj X
  /-- Acting by an identity is the identity. -/
  action_id : ∀ X : A,
    (λ_ (obj X)).inv ≫ eId V X ▷ obj X ≫ action X X = 𝟙 (obj X) := by
    cat_disch
  /-- Acting by a composite agrees with successive action. -/
  action_comp : ∀ X Y Z : A,
    eComp V X Y Z ▷ obj Z ≫ action X Z =
      (α_ (X ⟶[V] Y) (Y ⟶[V] Z) (obj Z)).hom ≫
        (X ⟶[V] Y) ◁ action Y Z ≫ action X Y := by
    cat_disch

namespace RightModule

/-- The representable right DG module `A(-, T)`. -/
def representable (T : A) : RightModule (R := R) A where
  obj X := X ⟶[V] T
  action X Y := eComp V X Y T
  action_id X := e_id_comp V X T
  action_comp X Y Z := (e_assoc' V X Y Z T).symm

/-- A closed degree-zero morphism of right DG modules, expressed as a pointwise morphism of
cochain complexes compatible with the module actions. -/
@[ext]
structure Hom (M N : RightModule (R := R) A) where
  /-- The component cochain map. -/
  app : ∀ X : A, M.obj X ⟶ N.obj X
  /-- Compatibility with the contravariant actions. -/
  naturality : ∀ X Y : A,
    M.action X Y ≫ app X = (X ⟶[V] Y) ◁ app Y ≫ N.action X Y := by
    cat_disch

instance : Category (RightModule (R := R) A) where
  Hom := Hom (R := R) A
  id M :=
    { app := fun _ ↦ 𝟙 _
      naturality := by simp }
  comp f g :=
    { app := fun X ↦ f.app X ≫ g.app X
      naturality := fun X Y ↦ by
        rw [← Category.assoc, f.naturality, Category.assoc, g.naturality,
          MonoidalCategory.whiskerLeft_comp, Category.assoc] }

@[simp]
lemma comp_app {M N P : RightModule (R := R) A} (f : M ⟶ N) (g : N ⟶ P) (X : A) :
    Hom.app (f ≫ g) X = f.app X ≫ g.app X := rfl

/-- Left whiskering of cochain maps is additive. -/
lemma complex_whiskerLeft_add (H : V) {K L : V} (f g : K ⟶ L) :
    H ◁ (f + g) = H ◁ f + H ◁ g := by
  rw [← id_tensorHom, DGCategory.tensor_add_right, id_tensorHom, id_tensorHom]

/-- Left whiskering of cochain maps commutes with scalar multiplication. -/
lemma complex_whiskerLeft_smul (H : V) {K L : V} (r : R) (f : K ⟶ L) :
    H ◁ (r • f) = r • (H ◁ f) := by
  rw [← id_tensorHom, DGCategory.tensor_smul_right, id_tensorHom]

/-- Left whiskering of the zero cochain map is zero. -/
lemma complex_whiskerLeft_zero (H : V) {K L : V} :
    H ◁ (0 : K ⟶ L) = 0 := by
  calc
    H ◁ (0 : K ⟶ L) = H ◁ ((0 : R) • (0 : K ⟶ L)) := by rw [zero_smul]
    _ = (0 : R) • (H ◁ (0 : K ⟶ L)) := complex_whiskerLeft_smul H 0 0
    _ = 0 := zero_smul _ _

/-- Left whiskering commutes with negation of cochain maps. -/
lemma complex_whiskerLeft_neg (H : V) {K L : V} (f : K ⟶ L) :
    H ◁ (-f) = -(H ◁ f) := by
  calc
    H ◁ (-f) = H ◁ ((-1 : R) • f) := by rw [neg_one_smul]
    _ = (-1 : R) • (H ◁ f) := complex_whiskerLeft_smul H (-1) f
    _ = -(H ◁ f) := neg_one_smul R _

/-- Left whiskering commutes with subtraction of cochain maps. -/
lemma complex_whiskerLeft_sub (H : V) {K L : V} (f g : K ⟶ L) :
    H ◁ (f - g) = H ◁ f - H ◁ g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, complex_whiskerLeft_add, complex_whiskerLeft_neg]

instance {M N : RightModule (R := R) A} : Zero (M ⟶ N) where
  zero :=
    { app := fun _ ↦ 0
      naturality := by simp [complex_whiskerLeft_zero] }

instance {M N : RightModule (R := R) A} : Add (M ⟶ N) where
  add f g :=
    { app := fun X ↦ f.app X + g.app X
      naturality := fun X Y ↦ by
        rw [Preadditive.comp_add, f.naturality, g.naturality,
          complex_whiskerLeft_add, Preadditive.add_comp] }

instance {M N : RightModule (R := R) A} : Neg (M ⟶ N) where
  neg f :=
    { app := fun X ↦ -f.app X
      naturality := fun X Y ↦ by
        rw [Preadditive.comp_neg, f.naturality, complex_whiskerLeft_neg,
          Preadditive.neg_comp] }

instance {M N : RightModule (R := R) A} : Sub (M ⟶ N) where
  sub f g :=
    { app := fun X ↦ f.app X - g.app X
      naturality := fun X Y ↦ by
        rw [Preadditive.comp_sub, f.naturality, g.naturality,
          complex_whiskerLeft_sub, Preadditive.sub_comp] }

instance {M N : RightModule (R := R) A} : SMul ℕ (M ⟶ N) where
  smul n f :=
    { app := fun X ↦ n • f.app X
      naturality := fun X Y ↦ by
        simp only [← Nat.cast_smul_eq_nsmul R]
        rw [Linear.comp_smul, f.naturality, complex_whiskerLeft_smul,
          Linear.smul_comp] }

instance {M N : RightModule (R := R) A} : SMul ℤ (M ⟶ N) where
  smul n f :=
    { app := fun X ↦ n • f.app X
      naturality := fun X Y ↦ by
        simp only [← Int.cast_smul_eq_zsmul R]
        rw [Linear.comp_smul, f.naturality, complex_whiskerLeft_smul,
          Linear.smul_comp] }

/-- Embed a module-morphism space into the family of its components. -/
def appEmbedding (M N : RightModule (R := R) A) :
    (M ⟶ N) → (∀ X, M.obj X ⟶ N.obj X) := fun f ↦ f.app

/-- A morphism of right DG modules is determined by all of its components. -/
lemma appEmbedding_injective (M N : RightModule (R := R) A) :
    Function.Injective (appEmbedding A M N) := by
  intro f g h
  apply Hom.ext
  exact h

noncomputable instance : Preadditive (RightModule (R := R) A) where
  homGroup M N := Function.Injective.addCommGroup
    (appEmbedding A M N) (appEmbedding_injective A M N)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  add_comp := by
    intro M N P f g h
    apply Hom.ext
    funext X
    change (f.app X + g.app X) ≫ h.app X =
      f.app X ≫ h.app X + g.app X ≫ h.app X
    exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by
    intro M N P f g h
    apply Hom.ext
    funext X
    change f.app X ≫ (g.app X + h.app X) =
      f.app X ≫ g.app X + f.app X ≫ h.app X
    exact Preadditive.comp_add _ _ _ _ _ _

/-- A homotopy between morphisms of right DG modules. In addition to a homotopy on every
value of the modules, the homotopy is required to commute with the DG action. The latter
condition is stated on the degreewise homotopy components; tensoring the component homotopy
uses the total-complex construction and therefore includes its Koszul signs. -/
structure Homotopy {M N : RightModule (R := R) A} (f g : M ⟶ N) where
  /-- The component homotopy at an object of the DG category. -/
  app : ∀ X : A, _root_.Homotopy (f.app X) (g.app X)
  /-- Compatibility of the homotopy components with the right module action. -/
  naturality : ∀ (X Y : A) (p q : ℤ),
    ((app X).compLeft (M.action X Y)).hom p q =
      ((HomologicalComplex.mapBifunctorMapHomotopy₂
        (𝟙 (X ⟶[V] Y)) (app Y) (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).compRight
          (N.action X Y)).hom p q := by
    cat_disch

/-- Tensoring the reflexive homotopy in the second variable produces the zero homotopy
component. -/
lemma tensorHomotopy₂_refl_hom (H : V) {K L : V} (f : K ⟶ L) (p q : ℤ) :
    (HomologicalComplex.mapBifunctorMapHomotopy₂
      (𝟙 H) (_root_.Homotopy.refl f)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q = 0 := by
  change HomologicalComplex.mapBifunctorMapHomotopy.hom₂
    (𝟙 H) (_root_.Homotopy.refl f)
      (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q = 0
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  dsimp [HomologicalComplex.mapBifunctorMapHomotopy.hom₂]
  erw [HomologicalComplex₂.ι_totalDesc]
  simp
  rfl

/-- Tensoring a symmetric homotopy in the second variable negates every homotopy
component. -/
lemma tensorHomotopy₂_symm_hom (H : V) {K L : V} {f g : K ⟶ L}
    (h : _root_.Homotopy f g) (p q : ℤ) :
    (HomologicalComplex.mapBifunctorMapHomotopy₂
      (𝟙 H) h.symm (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q =
      -(HomologicalComplex.mapBifunctorMapHomotopy₂
        (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q := by
  change HomologicalComplex.mapBifunctorMapHomotopy.hom₂
    (𝟙 H) h.symm (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q =
      -HomologicalComplex.mapBifunctorMapHomotopy.hom₂
        (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  dsimp [HomologicalComplex.mapBifunctorMapHomotopy.hom₂]
  erw [HomologicalComplex₂.ι_totalDesc]
  rw [Preadditive.comp_neg]
  erw [HomologicalComplex₂.ι_totalDesc]
  simp only [id_whiskerRight, _root_.Homotopy.symm_hom, Category.id_comp]
  rw [show -h.hom j ((ComplexShape.up ℤ).prev j) =
    (-1 : R) • h.hom j ((ComplexShape.up ℤ).prev j) by rw [neg_one_smul]]
  rw [MonoidalLinear.whiskerLeft_smul]
  simp
  rfl

/-- Tensoring a transitive composite of homotopies in the second variable adds their
homotopy components. -/
lemma tensorHomotopy₂_trans_hom (H : V) {K L : V} {f g k : K ⟶ L}
    (h₁ : _root_.Homotopy f g) (h₂ : _root_.Homotopy g k) (p q : ℤ) :
    (HomologicalComplex.mapBifunctorMapHomotopy₂
      (𝟙 H) (h₁.trans h₂) (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q =
      (HomologicalComplex.mapBifunctorMapHomotopy₂
          (𝟙 H) h₁ (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q +
        (HomologicalComplex.mapBifunctorMapHomotopy₂
          (𝟙 H) h₂ (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q := by
  change HomologicalComplex.mapBifunctorMapHomotopy.hom₂
    (𝟙 H) (h₁.trans h₂) (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q =
      HomologicalComplex.mapBifunctorMapHomotopy.hom₂
          (𝟙 H) h₁ (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q +
        HomologicalComplex.mapBifunctorMapHomotopy.hom₂
          (𝟙 H) h₂ (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  dsimp [HomologicalComplex.mapBifunctorMapHomotopy.hom₂]
  erw [HomologicalComplex₂.ι_totalDesc]
  rw [Preadditive.comp_add]
  erw [HomologicalComplex₂.ι_totalDesc, HomologicalComplex₂.ι_totalDesc]
  simp
  rfl

/-- Tensoring a sum of homotopies in the second variable adds their homotopy
components. -/
lemma tensorHomotopy₂_add_hom (H : V) {K L : V}
    {f₁ g₁ f₂ g₂ : K ⟶ L} (h₁ : _root_.Homotopy f₁ g₁)
    (h₂ : _root_.Homotopy f₂ g₂) (p q : ℤ) :
    (HomologicalComplex.mapBifunctorMapHomotopy₂
      (𝟙 H) (h₁.add h₂) (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q =
      (HomologicalComplex.mapBifunctorMapHomotopy₂
          (𝟙 H) h₁ (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q +
        (HomologicalComplex.mapBifunctorMapHomotopy₂
          (𝟙 H) h₂ (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q := by
  change HomologicalComplex.mapBifunctorMapHomotopy.hom₂
    (𝟙 H) (h₁.add h₂) (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q =
      HomologicalComplex.mapBifunctorMapHomotopy.hom₂
          (𝟙 H) h₁ (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q +
        HomologicalComplex.mapBifunctorMapHomotopy.hom₂
          (𝟙 H) h₂ (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  dsimp [HomologicalComplex.mapBifunctorMapHomotopy.hom₂]
  erw [HomologicalComplex₂.ι_totalDesc]
  rw [Preadditive.comp_add]
  erw [HomologicalComplex₂.ι_totalDesc, HomologicalComplex₂.ι_totalDesc]
  simp
  rfl

/-- Tensoring a homotopy precomposed in its second variable agrees, on homotopy
components, with precomposing the tensor homotopy. -/
lemma tensorHomotopy₂_compLeft_hom (H : V) {K L E : V} {f g : K ⟶ L}
    (h : _root_.Homotopy f g) (e : E ⟶ K) (p q : ℤ) :
    (HomologicalComplex.mapBifunctorMapHomotopy₂
      (𝟙 H) (h.compLeft e) (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q =
      (HomologicalComplex.mapBifunctorMap
          (𝟙 H) e (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f p ≫
        (HomologicalComplex.mapBifunctorMapHomotopy₂
          (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q := by
  change HomologicalComplex.mapBifunctorMapHomotopy.hom₂
    (𝟙 H) (h.compLeft e) (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q =
      (HomologicalComplex.mapBifunctorMap
          (𝟙 H) e (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f p ≫
        HomologicalComplex.mapBifunctorMapHomotopy.hom₂
          (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  dsimp [HomologicalComplex.mapBifunctorMapHomotopy.hom₂]
  erw [HomologicalComplex₂.ι_totalDesc]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  erw [HomologicalComplex₂.ι_totalDesc]
  simp [_root_.Homotopy.compLeft_hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensoring a homotopy postcomposed in its second variable agrees, on homotopy
components, with postcomposing the tensor homotopy. -/
lemma tensorHomotopy₂_compRight_hom (H : V) {K L E : V} {f g : K ⟶ L}
    (h : _root_.Homotopy f g) (e : L ⟶ E) (p q : ℤ) :
    (HomologicalComplex.mapBifunctorMapHomotopy₂
      (𝟙 H) (h.compRight e) (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q =
      (HomologicalComplex.mapBifunctorMapHomotopy₂
          (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).hom p q ≫
        (HomologicalComplex.mapBifunctorMap
          (𝟙 H) e (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f q := by
  change HomologicalComplex.mapBifunctorMapHomotopy.hom₂
    (𝟙 H) (h.compRight e) (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q =
      HomologicalComplex.mapBifunctorMapHomotopy.hom₂
          (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q ≫
        (HomologicalComplex.mapBifunctorMap
          (𝟙 H) e (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f q
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  dsimp [HomologicalComplex.mapBifunctorMapHomotopy.hom₂]
  erw [HomologicalComplex₂.ι_totalDesc, HomologicalComplex₂.ι_totalDesc_assoc]
  by_cases hq : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i, (ComplexShape.up ℤ).prev j) = q
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hq,
      HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hq]
    ext x
    simp [HomologicalComplex.ι_mapBifunctorMap]
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ hq,
      HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ hq]
    ext x
    simp

namespace Homotopy

/-- Every morphism of right DG modules is homotopic to itself. -/
noncomputable def refl {M N : RightModule (R := R) A} (f : M ⟶ N) : Homotopy A f f where
  app X := _root_.Homotopy.refl (f.app X)
  naturality X Y p q := by
    simp only [_root_.Homotopy.compLeft_hom, _root_.Homotopy.refl_hom,
      _root_.Homotopy.compRight_hom]
    simp [tensorHomotopy₂_refl_hom]

/-- Equal morphisms of right DG modules are homotopic. -/
noncomputable def ofEq {M N : RightModule (R := R) A} {f g : M ⟶ N}
    (h : f = g) : Homotopy A f g := by
  subst g
  exact refl A f

/-- A homotopy of right DG-module morphisms can be reversed. -/
noncomputable def symm {M N : RightModule (R := R) A} {f g : M ⟶ N}
    (h : Homotopy A f g) : Homotopy A g f where
  app X := (h.app X).symm
  naturality X Y p q := by
    simp only [_root_.Homotopy.compLeft_hom, _root_.Homotopy.symm_hom,
      _root_.Homotopy.compRight_hom, tensorHomotopy₂_symm_hom]
    rw [Preadditive.comp_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg (h.naturality X Y p q)

/-- Homotopies of right DG-module morphisms compose transitively. -/
noncomputable def trans {M N : RightModule (R := R) A} {f g k : M ⟶ N}
    (h₁ : Homotopy A f g) (h₂ : Homotopy A g k) : Homotopy A f k where
  app X := (h₁.app X).trans (h₂.app X)
  naturality X Y p q := by
    simp only [_root_.Homotopy.compLeft_hom, _root_.Homotopy.trans_hom,
      _root_.Homotopy.compRight_hom, tensorHomotopy₂_trans_hom]
    rw [Preadditive.comp_add, Preadditive.add_comp]
    simpa only [_root_.Homotopy.compLeft_hom, _root_.Homotopy.compRight_hom] using
      congrArg₂ (fun a b ↦ a + b) (h₁.naturality X Y p q) (h₂.naturality X Y p q)

/-- The pointwise sum of two homotopies of right DG-module morphisms. -/
noncomputable def add {M N : RightModule (R := R) A}
    {f₁ g₁ f₂ g₂ : M ⟶ N} (h₁ : Homotopy A f₁ g₁) (h₂ : Homotopy A f₂ g₂) :
    Homotopy A (f₁ + f₂) (g₁ + g₂) where
  app X := (h₁.app X).add (h₂.app X)
  naturality X Y p q := by
    simp only [_root_.Homotopy.compLeft_hom, _root_.Homotopy.add_hom,
      _root_.Homotopy.compRight_hom, tensorHomotopy₂_add_hom]
    rw [Preadditive.comp_add, Preadditive.add_comp]
    simpa only [_root_.Homotopy.compLeft_hom, _root_.Homotopy.compRight_hom] using
      congrArg₂ (fun a b ↦ a + b) (h₁.naturality X Y p q) (h₂.naturality X Y p q)

/-- A homotopy of right DG-module morphisms can be precomposed by a module morphism. -/
noncomputable def compLeft {L M N : RightModule (R := R) A} {f g : M ⟶ N}
    (h : Homotopy A f g) (e : L ⟶ M) : Homotopy A (e ≫ f) (e ≫ g) where
  app X := (h.app X).compLeft (e.app X)
  naturality X Y p q := by
    have he :
        (L.action X Y).f p ≫ (e.app X).f p =
          (HomologicalComplex.mapBifunctorMap
              (𝟙 (X ⟶[V] Y)) (e.app Y) (curriedTensor (ModuleCat R))
                (ComplexShape.up ℤ)).f p ≫ (M.action X Y).f p := by
      have he' := congrArg (fun k ↦ k.f p) (e.naturality X Y)
      simp only [HomologicalComplex.comp_f] at he'
      rw [← id_tensorHom] at he'
      change (L.action X Y).f p ≫ (e.app X).f p =
        (HomologicalComplex.mapBifunctorMap
            (𝟙 (X ⟶[V] Y)) (e.app Y) (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ)).f p ≫ (M.action X Y).f p at he'
      exact he'
    have hh :
        (M.action X Y).f p ≫ (h.app X).hom p q =
          (HomologicalComplex.mapBifunctorMapHomotopy₂
              (𝟙 (X ⟶[V] Y)) (h.app Y) (curriedTensor (ModuleCat R))
                (ComplexShape.up ℤ)).hom p q ≫ (N.action X Y).f q := by
      simpa only [_root_.Homotopy.compLeft_hom, _root_.Homotopy.compRight_hom] using
        h.naturality X Y p q
    simp only [_root_.Homotopy.compLeft_hom, _root_.Homotopy.compRight_hom,
      tensorHomotopy₂_compLeft_hom]
    rw [← Category.assoc, he, Category.assoc, hh, Category.assoc]

/-- A homotopy of right DG-module morphisms can be postcomposed by a module morphism. -/
noncomputable def compRight {M N P : RightModule (R := R) A} {f g : M ⟶ N}
    (h : Homotopy A f g) (e : N ⟶ P) : Homotopy A (f ≫ e) (g ≫ e) where
  app X := (h.app X).compRight (e.app X)
  naturality X Y p q := by
    have hh :
        (M.action X Y).f p ≫ (h.app X).hom p q =
          (HomologicalComplex.mapBifunctorMapHomotopy₂
              (𝟙 (X ⟶[V] Y)) (h.app Y) (curriedTensor (ModuleCat R))
                (ComplexShape.up ℤ)).hom p q ≫ (N.action X Y).f q := by
      simpa only [_root_.Homotopy.compLeft_hom, _root_.Homotopy.compRight_hom] using
        h.naturality X Y p q
    have he :
        (N.action X Y).f q ≫ (e.app X).f q =
          (HomologicalComplex.mapBifunctorMap
              (𝟙 (X ⟶[V] Y)) (e.app Y) (curriedTensor (ModuleCat R))
                (ComplexShape.up ℤ)).f q ≫ (P.action X Y).f q := by
      have he' := congrArg (fun k ↦ k.f q) (e.naturality X Y)
      simp only [HomologicalComplex.comp_f] at he'
      rw [← id_tensorHom] at he'
      change (N.action X Y).f q ≫ (e.app X).f q =
        (HomologicalComplex.mapBifunctorMap
            (𝟙 (X ⟶[V] Y)) (e.app Y) (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ)).f q ≫ (P.action X Y).f q at he'
      exact he'
    simp only [_root_.Homotopy.compLeft_hom, _root_.Homotopy.compRight_hom,
      tensorHomotopy₂_compRight_hom]
    rw [← Category.assoc, hh, Category.assoc, he, ← Category.assoc]

end Homotopy

/-- Two morphisms of right DG modules are homotopic when there exists a homotopy compatible
with the right DG actions. -/
def homotopic : HomRel (RightModule (R := R) A) := fun _ _ f g ↦ Nonempty (Homotopy A f g)

/-- Homotopy of right DG-module morphisms is an equivalence relation compatible with
composition. -/
noncomputable instance homotopy_congruence : Congruence (homotopic (R := R) A) where
  equivalence :=
    { refl := fun f ↦ ⟨Homotopy.refl A f⟩
      symm := fun ⟨h⟩ ↦ ⟨Homotopy.symm A h⟩
      trans := fun ⟨h₁⟩ ⟨h₂⟩ ↦ ⟨Homotopy.trans A h₁ h₂⟩ }
  comp_left := fun e _ _ ⟨h⟩ ↦ ⟨Homotopy.compLeft A h e⟩
  comp_right := fun e ⟨h⟩ ↦ ⟨Homotopy.compRight A h e⟩

/-- The homotopy category of right DG modules. -/
def HomotopyCategory := CategoryTheory.Quotient (homotopic (R := R) A)

instance : Category (HomotopyCategory (R := R) A) :=
  inferInstanceAs (Category (CategoryTheory.Quotient (homotopic (R := R) A)))

namespace HomotopyCategory

/-- The quotient functor from right DG modules to their homotopy category. -/
def quotient : RightModule (R := R) A ⥤ HomotopyCategory (R := R) A :=
  CategoryTheory.Quotient.functor (homotopic (R := R) A)

/-- The quotient functor identifies exactly the homotopic module morphisms. -/
lemma quotient_map_eq_iff {M N : RightModule (R := R) A} (f g : M ⟶ N) :
    (quotient (R := R) A).map f = (quotient (R := R) A).map g ↔
      homotopic (R := R) A f g :=
  CategoryTheory.Quotient.functor_map_eq_iff (homotopic (R := R) A) f g

/-- Homotopy of module morphisms is preserved by addition. -/
lemma homotopic_add {M N : RightModule (R := R) A}
    (f₁ f₂ g₁ g₂ : M ⟶ N) (hf : homotopic (R := R) A f₁ f₂)
    (hg : homotopic (R := R) A g₁ g₂) :
    homotopic (R := R) A (f₁ + g₁) (f₂ + g₂) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  exact ⟨Homotopy.add A hf hg⟩

/-- The homotopy category of right DG modules is preadditive. -/
noncomputable instance preadditiveQuotient :
    Preadditive (CategoryTheory.Quotient (homotopic (R := R) A)) :=
  CategoryTheory.Quotient.preadditive (homotopic (R := R) A) (by
    intro M N f₁ f₂ g₁ g₂ hf hg
    exact homotopic_add (R := R) A f₁ f₂ g₁ g₂ hf hg)

noncomputable instance : Preadditive (HomotopyCategory (R := R) A) :=
  inferInstanceAs (Preadditive (CategoryTheory.Quotient (homotopic (R := R) A)))

instance additiveQuotientFunctor :
    (CategoryTheory.Quotient.functor (homotopic (R := R) A)).Additive :=
  CategoryTheory.Quotient.functor_additive (homotopic (R := R) A) (by
    intro M N f₁ f₂ g₁ g₂ hf hg
    exact homotopic_add (R := R) A f₁ f₂ g₁ g₂ hf hg)

instance : (quotient (R := R) A).Additive :=
  inferInstanceAs ((CategoryTheory.Quotient.functor (homotopic (R := R) A)).Additive)

end HomotopyCategory

end RightModule

end DGCategory

namespace DGCategory.TensorCochain

variable {R : Type w} [CommRing R]
local notation "V" => CochainComplex (ModuleCat R) ℤ

open CochainComplex.HomComplex

lemma module_whiskerLeft_intUnits_smul (X : ModuleCat R) {Y Z : ModuleCat R}
    (r : ℤˣ) (f : Y ⟶ Z) : X ◁ (r • f) = r • (X ◁ f) := by
  simp only [Units.smul_def]
  exact Functor.map_zsmul (F := (tensoringLeft (ModuleCat R)).obj X)

lemma intUnits_smul_comp {C : Type*} [Category C] [Preadditive C]
    {X Y Z : C} (r : ℤˣ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (r • f) ≫ g = r • (f ≫ g) := by
  simp only [Units.smul_def, Preadditive.zsmul_comp]

lemma comp_intUnits_smul {C : Type*} [Category C] [Preadditive C]
    {X Y Z : C} (f : X ⟶ Y) (r : ℤˣ) (g : Y ⟶ Z) :
    f ≫ (r • g) = r • (f ≫ g) := by
  simp only [Units.smul_def, Preadditive.comp_zsmul]

/-- Tensor a homogeneous cochain in the second variable, with the Koszul sign from
moving it past the degree of the first complex. -/
noncomputable def right (H : V) {K L : V} {n : ℤ} (γ : Cochain K L n) :
    Cochain (H ⊗ K) (H ⊗ L) n :=
  Cochain.mk fun p q hpq =>
    HomologicalComplex.mapBifunctorDesc fun i j hij =>
      (i * n).negOnePow •
        (H.X i ◁ γ.v j (j + n) rfl) ≫
          HomologicalComplex.ιMapBifunctor H L (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) i (j + n) q (by dsimp at hij ⊢; omega)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma ι_right_v (H : V) {K L : V} {n : ℤ} (γ : Cochain K L n)
    (i j p q : ℤ) (hij : i + j = p) (hpq : p + n = q) :
    HomologicalComplex.ιMapBifunctor H K (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i j p hij ≫
      (right H γ).v p q hpq =
      (i * n).negOnePow •
        (H.X i ◁ γ.v j (j + n) rfl) ≫
          HomologicalComplex.ιMapBifunctor H L (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) i (j + n) q (by dsimp; omega) := by
  change HomologicalComplex.ιMapBifunctor H K (curriedTensor (ModuleCat R))
      (ComplexShape.up ℤ) i j p hij ≫
      HomologicalComplex.mapBifunctorDesc (fun i j hij =>
        (i * n).negOnePow •
          (H.X i ◁ γ.v j (j + n) rfl) ≫
            HomologicalComplex.ιMapBifunctor H L (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) i (j + n) q (by dsimp at hij ⊢; omega)) = _
  rw [HomologicalComplex.ι_mapBifunctorDesc]

@[simp]
lemma right_zero (H : V) {K L : V} (n : ℤ) :
    right H (0 : Cochain K L n) = 0 := by
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [ι_right_v H (0 : Cochain K L n) i j p q hij hpq]
  simp

@[simp]
lemma right_add (H : V) {K L : V} {n : ℤ} (γ γ' : Cochain K L n) :
    right H (γ + γ') = right H γ + right H γ' := by
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [ι_right_v H (γ + γ') i j p q hij hpq]
  simp only [Cochain.add_v, MonoidalPreadditive.whiskerLeft_add, smul_add,
    Preadditive.add_comp, Preadditive.comp_add]
  rw [ι_right_v H γ i j p q hij hpq, ι_right_v H γ' i j p q hij hpq]

@[simp]
lemma right_neg (H : V) {K L : V} {n : ℤ} (γ : Cochain K L n) :
    right H (-γ) = -right H γ := by
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [ι_right_v H (-γ) i j p q hij hpq]
  simp only [Cochain.neg_v]
  rw [show H.X i ◁ (-γ.v j (j + n) rfl) =
      -(H.X i ◁ γ.v j (j + n) rfl) by
    exact Functor.map_neg ((tensoringLeft (ModuleCat R)).obj (H.X i))]
  simp only [smul_neg, Preadditive.neg_comp, Preadditive.comp_neg]
  rw [ι_right_v H γ i j p q hij hpq]

@[simp]
lemma right_sub (H : V) {K L : V} {n : ℤ} (γ γ' : Cochain K L n) :
    right H (γ - γ') = right H γ - right H γ' := by
  rw [sub_eq_add_neg, sub_eq_add_neg, right_add, right_neg]

@[simp]
lemma right_smul (H : V) {K L : V} {n : ℤ} (r : R) (γ : Cochain K L n) :
    right H (r • γ) = r • right H γ := by
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [ι_right_v H (r • γ) i j p q hij hpq]
  simp only [Cochain.smul_v, MonoidalLinear.whiskerLeft_smul,
    Linear.smul_comp, Linear.comp_smul]
  rw [ι_right_v H γ i j p q hij hpq]
  exact SMulCommClass.smul_comm (i * n).negOnePow r
    ((H.X i ◁ γ.v j (j + n) rfl) ≫
      HomologicalComplex.ιMapBifunctor H L (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i (j + n) q (by dsimp at hij hpq ⊢; omega))

set_option backward.isDefEq.respectTransparency false in
/-- Signed tensoring of a homogeneous cochain is natural in the first complex. -/
lemma right_naturality_left {H H' K L : V} (a : H ⟶ H') {n : ℤ}
    (γ : Cochain K L n) :
    (Cochain.ofHom (a ▷ K)).comp (right H' γ) (zero_add n) =
      (right H γ).comp (Cochain.ofHom (a ▷ L)) (add_zero n) := by
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq]
  rw [Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q)]
  simp only [Cochain.ofHom_v]
  change _ ≫
      (HomologicalComplex.mapBifunctorMap a (𝟙 K)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f p ≫ _ = _
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  rw [ι_right_v H' γ i j p q hij hpq]
  rw [ι_right_v_assoc H γ i j p q hij hpq]
  simp only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul]
  congr 1
  simp only [HomologicalComplex.id_f]
  rw [show a ▷ L = HomologicalComplex.mapBifunctorMap a (𝟙 L)
    (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) by rfl]
  slice_rhs 2 3 => rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  rw [show ((curriedTensor (ModuleCat R)).obj (H'.X i)).map (𝟙 (K.X j)) = 𝟙 _ by simp]
  rw [show ((curriedTensor (ModuleCat R)).obj (H'.X i)).map (𝟙 (L.X (j + n))) = 𝟙 _ by simp]
  simp only [Category.id_comp]
  change (a.f i ▷ K.X j) ≫ (H'.X i ◁ γ.v j (j + n) rfl) ≫ _ =
    (H.X i ◁ γ.v j (j + n) rfl) ≫ (a.f i ▷ L.X (j + n)) ≫ _
  rw [MonoidalCategory.whisker_exchange_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Signed tensoring by the unit complex is compatible with the left unitor. -/
lemma leftUnitor_inv_right_v {K L : V} {n : ℤ} (γ : Cochain K L n)
    (p q : ℤ) (hpq : p + n = q) :
    (λ_ K).inv.f p ≫ (right (𝟙_ V) γ).v p q hpq =
      γ.v p q hpq ≫ (λ_ L).inv.f q := by
  subst q
  have hK : (λ_ K).inv.f p = (HomologicalComplex.leftUnitor' K).inv p := rfl
  have hL : (λ_ L).inv.f (p + n) =
      (HomologicalComplex.leftUnitor' L).inv (p + n) := rfl
  rw [hK, hL, HomologicalComplex.leftUnitor'_inv,
    HomologicalComplex.leftUnitor'_inv]
  simp only [Category.assoc]
  have hιK :
      (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)).ιTensorObj
          K 0 p p (zero_add p) =
        HomologicalComplex.ιMapBifunctor (𝟙_ V) K (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) 0 p p (zero_add p) := rfl
  have hιL :
      (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)).ιTensorObj
          L 0 (p + n) (p + n) (zero_add (p + n)) =
        HomologicalComplex.ιMapBifunctor (𝟙_ V) L (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) 0 (p + n) (p + n) (zero_add (p + n)) := rfl
  rw [hιK, hιL]
  slice_lhs 3 4 => rw [ι_right_v (𝟙_ V) γ 0 p p (p + n) (zero_add p) rfl]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  have hexchange :
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv ▷ K.X p) ≫
          ((𝟙_ V).X 0 ◁ γ.v p (p + n) rfl) =
        ((𝟙_ (ModuleCat R)) ◁ γ.v p (p + n) rfl) ≫
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (ModuleCat R))).inv ▷ L.X (p + n)) := by
    exact (MonoidalCategory.whisker_exchange
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv (γ.v p (p + n) rfl)).symm
  slice_lhs 2 3 => rw [hexchange]
  slice_lhs 1 2 => rw [← MonoidalCategory.leftUnitor_inv_naturality]
  simp only [Category.assoc]

/-- Cochain form of `leftUnitor_inv_right_v`. -/
lemma leftUnitor_inv_right {K L : V} {n : ℤ} (γ : Cochain K L n) :
    (Cochain.ofHom (λ_ K).inv).comp (right (𝟙_ V) γ) (zero_add n) =
      γ.comp (Cochain.ofHom (λ_ L).inv) (add_zero n) := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q), Cochain.ofHom_v]
  exact leftUnitor_inv_right_v γ p q hpq

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring a cochain in the second variable preserves composition. -/
lemma right_comp (H : V) {K L E : V} {n₁ n₂ n₁₂ : ℤ}
    (γ₁ : Cochain K L n₁) (γ₂ : Cochain L E n₂) (h : n₁ + n₂ = n₁₂) :
    right H (γ₁.comp γ₂ h) = (right H γ₁).comp (right H γ₂) h := by
  subst n₁₂
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [ι_right_v H (γ₁.comp γ₂ rfl) i j p q hij hpq]
  rw [Cochain.comp_v γ₁ γ₂ rfl j (j + n₁) (j + (n₁ + n₂)) rfl (by omega)]
  rw [Cochain.comp_v (right H γ₁) (right H γ₂) rfl
    p (p + n₁) q rfl (by omega)]
  rw [← Category.assoc]
  rw [ι_right_v H γ₁ i j p (p + n₁) hij rfl]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [ι_right_v H γ₂ i (j + n₁) (p + n₁) q
    (by dsimp at hij ⊢; omega) (by omega)]
  simp only [comp_intUnits_smul, smul_smul,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← Int.negOnePow_add]
  congr 1
  · congr 1
    ring
  · have aux (a b : ℤ) (hab : a = b)
        (ha : j + n₁ + n₂ = a) (hb : j + n₁ + n₂ = b)
        (hia : i + a = q) (hib : i + b = q) :
        (H.X i ◁ γ₁.v j (j + n₁) rfl) ≫
              (H.X i ◁ γ₂.v (j + n₁) a ha) ≫
                HomologicalComplex.ιMapBifunctor H E (curriedTensor (ModuleCat R))
                  (ComplexShape.up ℤ) i a q hia =
          (H.X i ◁ γ₁.v j (j + n₁) rfl) ≫
              (H.X i ◁ γ₂.v (j + n₁) b hb) ≫
                HomologicalComplex.ιMapBifunctor H E (curriedTensor (ModuleCat R))
                  (ComplexShape.up ℤ) i b q hib := by
      subst b
      rfl
    exact aux (j + (n₁ + n₂)) (j + n₁ + n₂) (by omega)
      (by omega) rfl (by dsimp at hij hpq ⊢; omega) (by dsimp at hij hpq ⊢; omega)

set_option backward.isDefEq.respectTransparency false in
/-- In degree zero, signed right tensoring is the ordinary tensor product of cochain maps. -/
lemma right_ofHom (H : V) {K L : V} (f : K ⟶ L) :
    right H (Cochain.ofHom f) = Cochain.ofHom (H ◁ f) := by
  apply Cochain.ext
  intro p q hpq
  obtain rfl : q = p := by omega
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [ι_right_v H (Cochain.ofHom f) i j q q hij (add_zero q)]
  simp only [Cochain.ofHom_v, mul_zero, Int.negOnePow_zero, one_smul]
  change _ = _ ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 H) f
      (curriedTensor (ModuleCat R)) (.up ℤ)).f q
  rw [HomologicalComplex.ι_mapBifunctorMap]
  change _ = ((𝟙 (H.X i)) ▷ K.X j) ≫ (H.X i ◁ f.f j) ≫ _
  simp only [MonoidalCategory.id_whiskerRight, Category.id_comp]
  have aux (a : ℤ) (ha : a = j) (hja : j + 0 = a) (hia : i + a = q) :
      (H.X i ◁ (Cochain.ofHom f).v j a hja) ≫
          HomologicalComplex.ιMapBifunctor H L (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) i a q hia =
        (H.X i ◁ f.f j) ≫
          HomologicalComplex.ιMapBifunctor H L (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) i j q hij := by
    subst a
    rfl
  exact aux (j + 0) (by omega) rfl (by dsimp at hij ⊢; omega)

set_option backward.isDefEq.respectTransparency false in
/-- Signed tensoring of the cochain attached to a homotopy is the cochain attached
to the usual tensor-product homotopy. -/
lemma right_ofHomotopy (H : V) {K L : V} {f g : K ⟶ L}
    (h : _root_.Homotopy f g) :
    right H (Cochain.ofHomotopy h) =
      Cochain.ofHomotopy (HomologicalComplex.mapBifunctorMapHomotopy₂
        (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)) := by
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [ι_right_v H (Cochain.ofHomotopy h) i j p q hij hpq]
  change _ = HomologicalComplex.ιMapBifunctor H K (curriedTensor (ModuleCat R))
      (ComplexShape.up ℤ) i j p hij ≫
        HomologicalComplex.mapBifunctorMapHomotopy.hom₂
          (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q
  rw [HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₂
    (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
      i (j + (-1)) j p q hij (by rw [CochainComplex.prev]; omega)]
  rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ (by
    dsimp at hij hpq ⊢
    omega)]
  simp only [Cochain.ofHomotopy, Cochain.mk_v, HomologicalComplex.id_f]
  rw [show ((curriedTensor (ModuleCat R)).map (𝟙 (H.X i))).app (K.X j) =
    𝟙 (H.X i ⊗ K.X j) by simp]
  have hs : (i * (-1)).negOnePow = i.negOnePow := by
    rw [mul_neg, mul_one, Int.negOnePow_neg]
  have hε : (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i, j + (-1)) = i.negOnePow := rfl
  rw [hs, hε]
  congr 1

lemma right_comp_ofHom (H : V) {K L E : V} {n : ℤ}
    (γ : Cochain K L n) (f : L ⟶ E) :
    right H (γ.comp (Cochain.ofHom f) (add_zero n)) =
      (right H γ).comp (Cochain.ofHom (H ◁ f)) (add_zero n) := by
  rw [right_comp, right_ofHom]

set_option backward.isDefEq.respectTransparency false in
lemma δ_right (H : V) {K L : V} (n m : ℤ) (hnm : n + 1 = m)
    (γ : Cochain K L n) :
    δ n m (right H γ) = right H (δ n m γ) := by
  subst m
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [δ_v n (n + 1) rfl (right H γ) p q hpq (q - 1) (p + 1) rfl rfl]
  simp only [Preadditive.comp_add, Linear.comp_units_smul]
  rw [← Category.assoc]
  rw [ι_right_v H γ i j p (q - 1) hij (by omega)]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [show (H ⊗ L).d (q - 1) q =
      (HomologicalComplex.mapBifunctor H L (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ)).d (q - 1) q by rfl]
  rw [show (H ⊗ K).d p (p + 1) =
      (HomologicalComplex.mapBifunctor H K (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ)).d p (p + 1) by rfl]
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add]
  rw [HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add, Preadditive.add_comp, smul_add]
  simp only [← Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := H) (K₂ := L) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel i (i + 1))
      (j + n) q (by dsimp at hij ⊢; omega),
    HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := H) (K₂ := L) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) i
      (by simp : (ComplexShape.up ℤ).Rel (j + n) (j + n + 1))
      q (by dsimp at hij ⊢; omega),
    HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := H) (K₂ := K) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel i (i + 1))
      j (p + 1) (by dsimp at hij ⊢; omega),
    HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := H) (K₂ := K) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) i
      (by simp : (ComplexShape.up ℤ).Rel j (j + 1))
      (p + 1) (by dsimp at hij ⊢; omega)]
  have hε₁ (a b : ℤ) :
      (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = 1 := rfl
  have hε₂ (a b : ℤ) :
      (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) =
        a.negOnePow := rfl
  simp only [hε₁, hε₂, one_smul, Linear.comp_units_smul,
    Linear.units_smul_comp, smul_smul, Category.assoc]
  rw [ι_right_v H γ (i + 1) j (p + 1) q (by dsimp at hij ⊢; omega) (by omega),
    ι_right_v H γ i (j + 1) (p + 1) q (by dsimp at hij ⊢; omega) (by omega),
    ι_right_v H (δ n (n + 1) γ) i j p q hij hpq]
  rw [δ_v n (n + 1) rfl γ j (j + (n + 1)) rfl (j + n) (j + 1) (by omega) rfl]
  simp only [MonoidalPreadditive.whiskerLeft_add, MonoidalCategory.whiskerLeft_comp,
    Preadditive.add_comp, Category.assoc]
  rw [show ((curriedTensor (ModuleCat R)).map (H.d i (i + 1))).app (L.X (j + n)) =
      H.d i (i + 1) ▷ L.X (j + n) by rfl]
  rw [show ((curriedTensor (ModuleCat R)).map (H.d i (i + 1))).app (K.X j) =
      H.d i (i + 1) ▷ K.X j by rfl]
  rw [MonoidalCategory.whisker_exchange_assoc]
  have hK :
      H.X i ◁ ((n + 1).negOnePow • K.d j (j + 1) ≫
        γ.v (j + 1) (j + (n + 1)) (by omega)) =
        (n + 1).negOnePow •
          ((H.X i ◁ K.d j (j + 1)) ≫
            H.X i ◁ γ.v (j + 1) (j + (n + 1)) (by omega)) := by
    change H.X i ◁ ((n + 1).negOnePow •
      (K.d j (j + 1) ≫ γ.v (j + 1) (j + (n + 1)) (by omega))) =
        (n + 1).negOnePow •
          ((H.X i ◁ K.d j (j + 1)) ≫
            H.X i ◁ γ.v (j + 1) (j + (n + 1)) (by omega))
    rw [module_whiskerLeft_intUnits_smul, MonoidalCategory.whiskerLeft_comp]
  rw [hK]
  simp only [Linear.comp_units_smul, smul_smul, smul_add]
  rw [show ((curriedTensor (ModuleCat R)).obj (H.X i)).map
      (L.d (j + n) (j + n + 1)) = H.X i ◁ L.d (j + n) (j + n + 1) by rfl]
  rw [show ((curriedTensor (ModuleCat R)).obj (H.X i)).map
      (K.d j (j + 1)) = H.X i ◁ K.d j (j + 1) by rfl]
  have hsH :
      (n + 1).negOnePow * ((i + 1) * n).negOnePow = -(i * n).negOnePow := by
    calc
      (n + 1).negOnePow * ((i + 1) * n).negOnePow =
          ((n + 1) + (i + 1) * n).negOnePow :=
        (Int.negOnePow_add _ _).symm
      _ = (2 * n + (i * n + 1)).negOnePow := by congr 1; ring
      _ = (2 * n).negOnePow * (i * n + 1).negOnePow := Int.negOnePow_add _ _
      _ = (i * n + 1).negOnePow := by rw [Int.negOnePow_two_mul, one_mul]
      _ = (i * n).negOnePow * Int.negOnePow 1 := Int.negOnePow_add _ _
      _ = -(i * n).negOnePow := by
        rw [Int.negOnePow_one, mul_neg, mul_one]
  have hsL :
      (i * n).negOnePow * i.negOnePow = (i * (n + 1)).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    ring
  have hsK :
      ((n + 1).negOnePow * i.negOnePow) * (i * n).negOnePow =
        (i * (n + 1)).negOnePow * (n + 1).negOnePow := by
    simp only [mul_add, Int.negOnePow_add]
    ac_rfl
  rw [hsH, hsL, hsK]
  simp only [intUnits_smul_comp, smul_smul, Units.neg_smul]
  abel_nf
  simp only [Category.assoc]
  congr 1
  · congr 1
    congr 1
    congr 1
    · change H.X i ⊗ L.X (j + n + 1) = H.X i ⊗ L.X (j + (n + 1))
      exact congrArg (fun a ↦ H.X i ⊗ L.X a) (by omega)
    · have aux (a b : ℤ) (h : a = b) :
          HEq (H.X i ◁ L.d (j + n) a) (H.X i ◁ L.d (j + n) b) := by
        subst b
        rfl
      exact aux _ _ (by omega)
    · have aux (a b : ℤ) (h : a = b) (ha : i + a = q) (hb : i + b = q) :
          HEq
            (HomologicalComplex.ιMapBifunctor H L (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) i a q ha)
            (HomologicalComplex.ιMapBifunctor H L (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) i b q hb) := by
        subst b
        rfl
      exact aux _ _ (by omega) _ _
  · congr 1
    congr 1
    congr 1
    · exact congrArg (fun a ↦ H.X i ⊗ L.X a) (by omega)
    · have aux (a b : ℤ) (h : a = b)
          (ha : j + 1 + n = a) (hb : j + 1 + n = b) :
          HEq (H.X i ◁ γ.v (j + 1) a ha) (H.X i ◁ γ.v (j + 1) b hb) := by
        subst b
        rfl
      exact aux _ _ (by omega) _ _
    · have aux (a b : ℤ) (h : a = b) (ha : i + a = q) (hb : i + b = q) :
          HEq
            (HomologicalComplex.ιMapBifunctor H L (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) i a q ha)
            (HomologicalComplex.ιMapBifunctor H L (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) i b q hb) := by
        subst b
        rfl
      exact aux _ _ (by omega) _ _

end DGCategory.TensorCochain

namespace DGCategory.TensorCochain

variable {R : Type w} [CommRing R]
local notation "V" => CochainComplex (ModuleCat R) ℤ

open CochainComplex.HomComplex

/-!
## Signed tensor cochains and shifts

Signed tensoring in the second variable commutes with the standard shift comparison for
cochain complexes.
-/

/-- The signed tensor of a shifted cochain commutes with the canonical comparison
`H ⊗ K[n] ≅ (H ⊗ K)[n]`. -/
lemma right_shift_comm (H : V) {K L : V} {d : ℤ} (γ : Cochain K L d) (n : ℤ) :
    (Cochain.ofHom (CochainComplex.mapBifunctorShift₂Iso H K
        (curriedTensor (ModuleCat R)) n).hom).comp
          ((right H γ).shift n) (zero_add d) =
      (right H (γ.shift n)).comp
        (Cochain.ofHom (CochainComplex.mapBifunctorShift₂Iso H L
          (curriedTensor (ModuleCat R)) n).hom) (add_zero d) := by
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [Cochain.comp_zero_cochain_v]
  rw [Cochain.zero_cochain_comp_v]
  simp only [Cochain.ofHom_v]
  rw [← Category.assoc]
  erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
    H K (curriedTensor (ModuleCat R)) n i j p hij
      (j + n) (p + n) rfl rfl]
  rw [Cochain.shift_v (right H γ) n p q hpq
    (p + n) (q + n) rfl rfl]
  have hsrc :
      (CochainComplex.shiftFunctorObjXIso
        (HomologicalComplex.mapBifunctor H K (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ)) n p (p + n) rfl) =
        CochainComplex.shiftFunctorObjXIso (H ⊗ K) n p (p + n) rfl := rfl
  rw [hsrc, Linear.units_smul_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 3 4 =>
    rw [ι_right_v H γ i (j + n) (p + n) (q + n)
      (by dsimp at hij ⊢; omega) (by omega)]
  slice_rhs 1 2 =>
    rw [ι_right_v H (γ.shift n) i j p q hij hpq]
  rw [Cochain.shift_v γ n j (j + d) (by omega)
    (j + n) (j + n + d) rfl (by omega)]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Linear.units_smul_comp]
  slice_rhs 5 6 =>
    erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
      H L (curriedTensor (ModuleCat R)) n i (j + d) q
        (by dsimp at hij hpq ⊢; omega)
        (j + n + d) (q + n) (by omega) rfl]
  rw [show ((curriedTensor (ModuleCat R)).obj (H.X i)).map
      (CochainComplex.shiftFunctorObjXIso K n j (j + n) rfl).hom =
        H.X i ◁ (CochainComplex.shiftFunctorObjXIso K n j (j + n) rfl).hom
    by rfl]
  rw [show ((curriedTensor (ModuleCat R)).obj (H.X i)).map
      (CochainComplex.shiftFunctorObjXIso L n (j + d) (j + n + d) (by omega)).hom =
        H.X i ◁
          (CochainComplex.shiftFunctorObjXIso L n (j + d) (j + n + d) (by omega)).hom
    by rfl]
  simp only [Linear.comp_units_smul]
  slice_rhs 5 6 =>
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id]
  have htgt :
      (CochainComplex.shiftFunctorObjXIso
        (HomologicalComplex.mapBifunctor H L (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ)) n q (q + n) rfl) =
        CochainComplex.shiftFunctorObjXIso (H ⊗ L) n q (q + n) rfl := rfl
  rw [htgt]
  simp only [Category.id_comp]
  rw [smul_comm (i * n).negOnePow (i * d).negOnePow]

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring a right-shifted cochain agrees with right-shifting the tensor cochain,
after applying the signed tensor/shift comparison on the target. -/
lemma right_rightShift (H : V) {K L : V} {d d' n : ℤ} (γ : Cochain K L d)
    (h : d' + n = d) :
    (right H (γ.rightShift n d' h)).comp
        (Cochain.ofHom (CochainComplex.mapBifunctorShift₂Iso H L
          (curriedTensor (ModuleCat R)) n).hom) (add_zero d') =
      (right H γ).rightShift n d' h := by
  subst d
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [Cochain.comp_v _ _ (add_zero d') p q q hpq (add_zero q)]
  simp only [Cochain.ofHom_v]
  rw [ι_right_v_assoc H (γ.rightShift n d' rfl) i j p q hij hpq]
  rw [γ.rightShift_v n d' rfl j (j + d') rfl (j + (d' + n)) (by omega)]
  simp only [MonoidalCategory.whiskerLeft_comp, Linear.units_smul_comp,
    Category.assoc]
  rw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
    H L (curriedTensor (ModuleCat R)) n i (j + d') q
      (by dsimp at hij hpq ⊢; omega)
      (j + (d' + n)) (q + n) (by omega) rfl]
  simp only [Linear.comp_units_smul, smul_smul]
  rw [← Int.negOnePow_add]
  have hsign : i * d' + i * n = i * (d' + n) := by ring
  rw [hsign]
  rw [show ((curriedTensor (ModuleCat R)).obj (H.X i)).map
      (CochainComplex.shiftFunctorObjXIso L n (j + d') (j + (d' + n)) (by omega)).hom =
        H.X i ◁
          (CochainComplex.shiftFunctorObjXIso L n (j + d') (j + (d' + n)) (by omega)).hom
    by rfl]
  slice_lhs 3 4 =>
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id]
  simp only [Category.id_comp]
  rw [(right H γ).rightShift_v n d' rfl p q hpq (q + n) (by omega)]
  rw [ι_right_v_assoc H γ i j p (q + n) hij (by omega)]
  simp only [Linear.units_smul_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Right-shifting the target of a composite whose first cochain has degree zero
amounts to right-shifting its second cochain. -/
lemma zero_cochain_comp_rightShift {K L M : V} (α : Cochain K L 0)
    {d d' n : ℤ} (β : Cochain L M d) (h : d' + n = d) :
    (α.comp β (zero_add d)).rightShift n d' h =
      α.comp (β.rightShift n d' h) (zero_add d') := by
  subst d
  apply Cochain.ext
  intro p q hpq
  rw [( α.comp β (zero_add (d' + n))).rightShift_v
    n d' rfl p q hpq (q + n) (by omega)]
  rw [Cochain.comp_v _ _ (zero_add (d' + n)) p p (q + n)
    (add_zero p) (by omega)]
  rw [Cochain.comp_v _ _ (zero_add d') p p q (add_zero p) hpq]
  rw [β.rightShift_v n d' rfl p q hpq (q + n) (by omega)]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Right-shifting a composite with a degree-zero map is composition of the
right-shifted cochain with the shifted map. -/
lemma rightShift_comp_ofHom {K L M : V} {d d' n : ℤ} (γ : Cochain K L d)
    (f : L ⟶ M) (h : d' + n = d) :
    (γ.comp (Cochain.ofHom f) (add_zero d)).rightShift n d' h =
      (γ.rightShift n d' h).comp (Cochain.ofHom (f⟦n⟧')) (add_zero d') := by
  subst d
  apply Cochain.ext
  intro p q hpq
  rw [( γ.comp (Cochain.ofHom f) (add_zero (d' + n))).rightShift_v
    n d' rfl p q hpq (q + n) (by omega)]
  rw [Cochain.comp_v _ _ (add_zero (d' + n)) p (q + n) (q + n)
    (by omega) (add_zero (q + n))]
  rw [Cochain.comp_v _ _ (add_zero d') p q q hpq (add_zero q)]
  rw [γ.rightShift_v n d' rfl p q hpq (q + n) (by omega)]
  simp only [Cochain.ofHom_v, CochainComplex.shiftFunctor_map_f',
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]

end DGCategory.TensorCochain

namespace DGCategory.TensorCochain

variable {R : Type w} [CommRing R]
local notation "V" => CochainComplex (ModuleCat R) ℤ

open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false in
lemma associator_hom_right (H₁ H₂ : V) {K L : V} {n : ℤ}
    (γ : Cochain K L n) :
    (Cochain.ofHom (α_ H₁ H₂ K).hom).comp (right H₁ (right H₂ γ)) (zero_add n) =
      (right (H₁ ⊗ H₂) γ).comp (Cochain.ofHom (α_ H₁ H₂ L).hom) (add_zero n) := by
  apply Cochain.ext
  intro p q hpq
  rw [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq]
  rw [Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q)]
  simp only [Cochain.ofHom_v]
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro i₁ i₂ i₃ hp
  have hp₁₂ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁ + i₂, i₃) = p := hp
  have hp₂₃ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁, i₂ + i₃) = p := by
    change (i₁ + i₂) + i₃ = p at hp
    change i₁ + (i₂ + i₃) = p
    omega
  erw [HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc
    (curriedAssociatorNatIso (ModuleCat R)) H₁ H₂ K
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        i₁ i₂ i₃ p hp]
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq
    (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R)) H₁ H₂ K
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        i₁ i₂ i₃ (i₂ + i₃) p rfl hp₂₃]
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    change HomologicalComplex.ιMapBifunctor H₁ (H₂ ⊗ K)
      (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) i₁ (i₂ + i₃) p hp₂₃ ≫
        (right H₁ (right H₂ γ)).v p q hpq
    rw [ι_right_v H₁ (right H₂ γ) i₁ (i₂ + i₃) p q hp₂₃ hpq]
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq
    (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R)) H₁ H₂ K
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) i₁ i₂ i₃ (i₁ + i₂) p rfl hp₁₂]
  simp only [Category.assoc]
  slice_rhs 2 3 =>
    change HomologicalComplex.ιMapBifunctor (H₁ ⊗ H₂) K
      (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) (i₁ + i₂) i₃ p hp₁₂ ≫
        (right (H₁ ⊗ H₂) γ).v p q hpq
    rw [ι_right_v (H₁ ⊗ H₂) γ (i₁ + i₂) i₃ p q hp₁₂ hpq]
  have hInner := ι_right_v H₂ γ i₂ i₃ (i₂ + i₃) (i₂ + i₃ + n) rfl rfl
  have hmapK :
      ((curriedTensor (ModuleCat R)).obj (H₁.X i₁)).map
          (HomologicalComplex.ιMapBifunctor H₂ K (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) i₂ i₃ (i₂ + i₃) rfl) =
        H₁.X i₁ ◁
          HomologicalComplex.ιMapBifunctor H₂ K (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) i₂ i₃ (i₂ + i₃) rfl := rfl
  rw [hmapK]
  simp only [Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [hInner]
  rw [module_whiskerLeft_intUnits_smul]
  rw [MonoidalCategory.whiskerLeft_comp]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul,
    Category.assoc]
  rw [← Int.negOnePow_add]
  congr 1
  · congr 1
    ring
  · slice_lhs 1 2 =>
      change ( α_ (H₁.X i₁) (H₂.X i₂) (K.X i₃)).hom ≫
        H₁.X i₁ ◁ H₂.X i₂ ◁ γ.v i₃ (i₃ + n) rfl
      rw [← MonoidalCategory.associator_naturality_right]
    simp only [Category.assoc]
    have hq : (i₁ + i₂) + (i₃ + n) = q := by
      change (i₁ + i₂) + i₃ = p at hp
      omega
    have hqTriple :
        (ComplexShape.up ℤ).r (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i₁, i₂, i₃ + n) = q := hq
    have hq₂₃ :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (i₁, i₂ + i₃ + n) = q := by
      change i₁ + (i₂ + i₃ + n) = q
      omega
    have hi₂₃ :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (i₂, i₃ + n) = i₂ + i₃ + n := by
      change i₂ + (i₃ + n) = i₂ + i₃ + n
      omega
    have hmapL :
        H₁.X i₁ ◁
            HomologicalComplex.ιMapBifunctor H₂ L (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) i₂ (i₃ + n) (i₂ + i₃ + n)
                hi₂₃ =
          ((curriedTensor (ModuleCat R)).obj (H₁.X i₁)).map
            (HomologicalComplex.ιMapBifunctor H₂ L (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) i₂ (i₃ + n) (i₂ + i₃ + n)
                hi₂₃) := rfl
    rw [hmapL]
    slice_lhs 3 4 =>
      change
        ((curriedTensor (ModuleCat R)).obj (H₁.X i₁)).map
            (HomologicalComplex.ιMapBifunctor H₂ L (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) i₂ (i₃ + n) (i₂ + i₃ + n) hi₂₃) ≫
          HomologicalComplex.ιMapBifunctor H₁
            (HomologicalComplex.mapBifunctor H₂ L (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ)) (curriedTensor (ModuleCat R))
                (ComplexShape.up ℤ) i₁ (i₂ + i₃ + n) q hq₂₃
      rw [← HomologicalComplex.mapBifunctor₂₃.ι_eq
        (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R)) H₁ H₂ L
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            i₁ i₂ (i₃ + n) (i₂ + i₃ + n) q hi₂₃ hq₂₃]
    slice_lhs 2 3 =>
      erw [← HomologicalComplex.ι_mapBifunctorAssociatorX_hom
        (curriedAssociatorNatIso (ModuleCat R)) H₁ H₂ L
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            i₁ i₂ (i₃ + n) q hqTriple]
    have hq₁₂ :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (i₁ + i₂, i₃ + n) = q := hq
    let j : H₁.X i₁ ⊗ H₂.X i₂ ⟶ (H₁ ⊗ H₂).X (i₁ + i₂) :=
      HomologicalComplex.ιMapBifunctor H₁ H₂ (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ (i₁ + i₂) rfl
    have hjK :
        ((curriedTensor (ModuleCat R)).map j).app (K.X i₃) = j ▷ K.X i₃ := rfl
    have hjL :
        j ▷ L.X (i₃ + n) =
          ((curriedTensor (ModuleCat R)).map j).app (L.X (i₃ + n)) := rfl
    change _ =
      ((curriedTensor (ModuleCat R)).map j).app (K.X i₃) ≫
        (H₁ ⊗ H₂).X (i₁ + i₂) ◁ γ.v i₃ (i₃ + n) rfl ≫ _
    rw [hjK]
    slice_rhs 1 2 =>
      rw [← MonoidalCategory.whisker_exchange]
    rw [hjL]
    slice_rhs 2 3 =>
      dsimp only [j]
      change
        ((curriedTensor (ModuleCat R)).map
            (HomologicalComplex.ιMapBifunctor H₁ H₂ (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) i₁ i₂ (i₁ + i₂) rfl)).app (L.X (i₃ + n)) ≫
          HomologicalComplex.ιMapBifunctor
            (HomologicalComplex.mapBifunctor H₁ H₂ (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ)) L (curriedTensor (ModuleCat R))
                (ComplexShape.up ℤ) (i₁ + i₂) (i₃ + n) q hq₁₂
      rw [← HomologicalComplex.mapBifunctor₁₂.ι_eq
        (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R)) H₁ H₂ L
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            i₁ i₂ (i₃ + n) (i₁ + i₂) q rfl hq₁₂]
    rfl

end DGCategory.TensorCochain
namespace DGCategory.HomComplex

variable (R : Type w) [CommRing R]

open CochainComplex.HomComplex

/-- Composition of homogeneous cochains, with the Koszul factor required by the
`Hom X Y ⊗ Hom Y Z` convention used by `EnrichedCategory.comp`. -/
def signedComp {F G K : CochainComplex (ModuleCat.{w} R) ℤ}
    (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂) :
    Cochain F G n₁ →ₗ[R] Cochain G K n₂ →ₗ[R] Cochain F K n₁₂ :=
  LinearMap.mk₂ R
    (fun z₁ z₂ ↦ (n₁ * n₂).negOnePow • z₁.comp z₂ h)
    (fun z₁ z₁' z₂ ↦ by simp)
    (fun r z₁ z₂ ↦ by simp [smul_comm r (n₁ * n₂).negOnePow])
    (fun z₁ z₂ z₂' ↦ by simp)
    (fun r z₁ z₂ ↦ by simp [smul_comm r (n₁ * n₂).negOnePow])

set_option backward.isDefEq.respectTransparency false in
/-- Signed composition obeys the Leibniz rule for the tensor-product differential. -/
lemma δ_signedComp {F G K : CochainComplex (ModuleCat.{w} R) ℤ}
    (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂)
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) :
    δ n₁₂ (n₁₂ + 1) (signedComp R n₁ n₂ n₁₂ h z₁ z₂) =
      signedComp R (n₁ + 1) n₂ (n₁₂ + 1) (by omega)
          (δ n₁ (n₁ + 1) z₁) z₂ +
        n₁.negOnePow •
          signedComp R n₁ (n₂ + 1) (n₁₂ + 1) (by omega)
            z₁ (δ n₂ (n₂ + 1) z₂) := by
  change δ n₁₂ (n₁₂ + 1) ((n₁ * n₂).negOnePow • z₁.comp z₂ h) = _
  rw [δ_units_smul, δ_comp z₁ z₂ h (n₁ + 1) (n₂ + 1) (n₁₂ + 1)
    (by omega) rfl rfl]
  simp only [smul_add, signedComp, LinearMap.mk₂_apply, add_mul, mul_add,
    Int.negOnePow_add, smul_smul, one_mul, mul_one]
  rw [mul_comm (n₁ * n₂).negOnePow n₁.negOnePow, ← mul_assoc,
    Int.units_mul_self, one_mul]
  abel

end DGCategory.HomComplex

namespace DGCategory.RightModule

variable {R : Type w} [CommRing R]

local notation "V" => CochainComplex (ModuleCat R) ℤ

open CochainComplex.HomComplex

section General

variable (A : Type u) [DGCategory R A]

/-- A degree-`n` graded natural transformation between right DG modules.  On an
element of degree `i` in an enriched Hom complex, `TensorCochain.right` contributes
the sign `(-1)^(i*n)` required by DG naturality. -/
@[ext]
structure GradedHom (M N : RightModule (R := R) A) (n : ℤ) where
  /-- The homogeneous cochain at each object. -/
  app : ∀ X : A, Cochain (M.obj X) (N.obj X) n
  /-- Signed compatibility with the right actions. -/
  naturality : ∀ X Y : A,
    (Cochain.ofHom (M.action X Y)).comp (app X) (zero_add n) =
      (TensorCochain.right (X ⟶[V] Y) (app Y)).comp
        (Cochain.ofHom (N.action X Y)) (add_zero n) := by
    cat_disch

instance {M N : RightModule (R := R) A} {n : ℤ} : Zero (GradedHom A M N n) where
  zero :=
    { app := fun _ ↦ 0
      naturality := by simp }

instance {M N : RightModule (R := R) A} {n : ℤ} : Add (GradedHom A M N n) where
  add f g :=
    { app := fun X ↦ f.app X + g.app X
      naturality := fun X Y ↦ by
        simp only [Cochain.comp_add, TensorCochain.right_add, Cochain.add_comp]
        rw [f.naturality, g.naturality] }

instance {M N : RightModule (R := R) A} {n : ℤ} : Neg (GradedHom A M N n) where
  neg f :=
    { app := fun X ↦ -f.app X
      naturality := fun X Y ↦ by
        simp only [Cochain.comp_neg, TensorCochain.right_neg, Cochain.neg_comp]
        rw [f.naturality] }

instance {M N : RightModule (R := R) A} {n : ℤ} : Sub (GradedHom A M N n) where
  sub f g :=
    { app := fun X ↦ f.app X - g.app X
      naturality := fun X Y ↦ by
        simp only [Cochain.comp_sub, TensorCochain.right_sub, Cochain.sub_comp]
        rw [f.naturality, g.naturality] }

instance {M N : RightModule (R := R) A} {n : ℤ} : SMul R (GradedHom A M N n) where
  smul r f :=
    { app := fun X ↦ r • f.app X
      naturality := fun X Y ↦ by
        simp only [Cochain.comp_smul, TensorCochain.right_smul, Cochain.smul_comp]
        rw [f.naturality] }

instance {M N : RightModule (R := R) A} {n : ℤ} : SMul ℕ (GradedHom A M N n) where
  smul r f :=
    { app := fun X ↦ r • f.app X
      naturality := fun X Y ↦ by
        simp only [← Nat.cast_smul_eq_nsmul R]
        simp only [Cochain.comp_smul, TensorCochain.right_smul, Cochain.smul_comp]
        rw [f.naturality] }

instance {M N : RightModule (R := R) A} {n : ℤ} : SMul ℤ (GradedHom A M N n) where
  smul r f :=
    { app := fun X ↦ r • f.app X
      naturality := fun X Y ↦ by
        simp only [← Int.cast_smul_eq_zsmul R]
        simp only [Cochain.comp_smul, TensorCochain.right_smul, Cochain.smul_comp]
        rw [f.naturality] }

/-- Embed a graded module transformation into its family of component cochains. -/
def gradedAppEmbedding (M N : RightModule (R := R) A) (n : ℤ) :
    GradedHom A M N n → (∀ X, Cochain (M.obj X) (N.obj X) n) := fun f ↦ f.app

lemma gradedAppEmbedding_injective (M N : RightModule (R := R) A) (n : ℤ) :
    Function.Injective (gradedAppEmbedding A M N n) := by
  intro f g h
  apply GradedHom.ext
  exact h

noncomputable instance {M N : RightModule (R := R) A} {n : ℤ} :
    AddCommGroup (GradedHom A M N n) :=
  Function.Injective.addCommGroup (gradedAppEmbedding A M N n)
    (gradedAppEmbedding_injective A M N n) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The additive map given by evaluation of a graded module transformation. -/
def gradedAppAddHom (M N : RightModule (R := R) A) (n : ℤ) :
    GradedHom A M N n →+ (∀ X, Cochain (M.obj X) (N.obj X) n) where
  toFun := gradedAppEmbedding A M N n
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance {M N : RightModule (R := R) A} {n : ℤ} :
    Module R (GradedHom A M N n) :=
  Function.Injective.module R (gradedAppAddHom A M N n)
    (gradedAppEmbedding_injective A M N n) (fun _ _ ↦ rfl)

/-- The differential of a graded module-natural transformation, computed pointwise. -/
def differential {M N : RightModule (R := R) A} (n m : ℤ) (f : GradedHom A M N n) :
    GradedHom A M N m where
  app X := δ n m (f.app X)
  naturality X Y := by
    by_cases hnm : n + 1 = m
    · rw [← δ_ofHom_comp, f.naturality, δ_comp_ofHom,
        TensorCochain.δ_right (X ⟶[V] Y) n m hnm]
    · simp only [δ_shape n m hnm, TensorCochain.right_zero, Cochain.comp_zero,
        Cochain.zero_comp]

/-- The differential as an `R`-linear map. -/
def differentialLinear {M N : RightModule (R := R) A} (n m : ℤ) :
    GradedHom A M N n →ₗ[R] GradedHom A M N m where
  toFun := differential A n m
  map_add' f g := by
    apply GradedHom.ext
    funext X
    exact (δ_hom R (M.obj X) (N.obj X) n m).map_add (f.app X) (g.app X)
  map_smul' r f := by
    apply GradedHom.ext
    funext X
    exact (δ_hom R (M.obj X) (N.obj X) n m).map_smul r (f.app X)

end General

section FixedUniverse

variable (A : Type w) [DGCategory R A]

/-- The genuine Hom complex of graded natural transformations between two right DG modules. -/
def homComplex (M N : RightModule (R := R) A) : V where
  X n := ModuleCat.of R (GradedHom A M N n)
  d n m := ModuleCat.ofHom (differentialLinear A n m)
  shape n m hnm := by
    apply ModuleCat.Hom.ext
    apply LinearMap.ext
    intro f
    apply GradedHom.ext
    funext X
    exact δ_shape n m hnm (f.app X)
  d_comp_d' n m p _ _ := by
    apply ModuleCat.Hom.ext
    apply LinearMap.ext
    intro f
    apply GradedHom.ext
    funext X
    exact δ_δ n m p (f.app X)

set_option backward.isDefEq.respectTransparency false in
/-- The signed tensor of the cochain attached to a homotopy is exactly the cochain
attached to the tensor-product homotopy used by `RightModule.Homotopy`. -/
lemma tensorCochain_right_ofHomotopy (H : V) {K L : V} {f g : K ⟶ L}
    (h : _root_.Homotopy f g) :
    TensorCochain.right H (Cochain.ofHomotopy h) =
      Cochain.ofHomotopy (HomologicalComplex.mapBifunctorMapHomotopy₂
        (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)) := by
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [TensorCochain.ι_right_v H (Cochain.ofHomotopy h) i j p q hij hpq]
  change _ = HomologicalComplex.ιMapBifunctor H K (curriedTensor (ModuleCat R))
      (ComplexShape.up ℤ) i j p hij ≫
        HomologicalComplex.mapBifunctorMapHomotopy.hom₂
          (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p q
  rw [HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₂
    (𝟙 H) h (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
      i (j + (-1)) j p q hij (by rw [CochainComplex.prev]; omega)]
  rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ (by
    dsimp at hij hpq ⊢
    omega)]
  simp only [Cochain.ofHomotopy, Cochain.mk_v, HomologicalComplex.id_f]
  rw [show ((curriedTensor (ModuleCat R)).map (𝟙 (H.X i))).app (K.X j) =
    𝟙 (H.X i ⊗ K.X j) by simp]
  have hs : (i * (-1)).negOnePow = i.negOnePow := by
    rw [mul_neg, mul_one, Int.negOnePow_neg]
  have hε : (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i, j + (-1)) = i.negOnePow := rfl
  rw [hs, hε]
  congr 1

/-- A closed degree-zero module morphism, regarded as a graded natural transformation. -/
def ofHom {M N : RightModule (R := R) A} (f : M ⟶ N) : GradedHom A M N 0 where
  app X := Cochain.ofHom (f.app X)
  naturality X Y := by
    rw [← Cochain.ofHom_comp, TensorCochain.right_ofHom, ← Cochain.ofHom_comp,
      f.naturality]

@[simp]
lemma ofHom_add {M N : RightModule (R := R) A} (f g : M ⟶ N) :
    ofHom A (f + g) = ofHom A f + ofHom A g := by
  apply GradedHom.ext
  funext X
  change Cochain.ofHom (f.app X + g.app X) =
    Cochain.ofHom (f.app X) + Cochain.ofHom (g.app X)
  exact Cochain.ofHom_add (f.app X) (g.app X)

@[simp]
lemma differential_ofHom {M N : RightModule (R := R) A} (f : M ⟶ N) (m : ℤ) :
    differential A 0 m (ofHom A f) = 0 := by
  apply GradedHom.ext
  funext X
  exact δ_ofHom (p := m) (f.app X)

/-- Pointwise (unsigned) composition of graded module-natural transformations. -/
def compRaw {M N P : RightModule (R := R) A} {n₁ n₂ n₁₂ : ℤ}
    (f : GradedHom A M N n₁) (g : GradedHom A N P n₂) (h : n₁ + n₂ = n₁₂) :
    GradedHom A M P n₁₂ where
  app X := (f.app X).comp (g.app X) h
  naturality X Y := by
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
    rw [f.naturality]
    rw [Cochain.comp_assoc_of_second_is_zero_cochain]
    rw [g.naturality]
    rw [← Cochain.comp_assoc_of_third_is_zero_cochain]
    rw [← TensorCochain.right_comp]

/-- Signed composition, in the convention where enriched composition receives
`Hom(M,N) ⊗ Hom(N,P)`. -/
def signedComp {M N P : RightModule (R := R) A} (n₁ n₂ n₁₂ : ℤ)
    (h : n₁ + n₂ = n₁₂) :
    GradedHom A M N n₁ →ₗ[R] GradedHom A N P n₂ →ₗ[R] GradedHom A M P n₁₂ :=
  LinearMap.mk₂ R
    (fun f g ↦ (n₁ * n₂).negOnePow • compRaw A f g h)
    (fun f f' g ↦ by
      apply GradedHom.ext
      funext X
      change (n₁ * n₂).negOnePow • ((f.app X + f'.app X).comp (g.app X) h) =
        (n₁ * n₂).negOnePow • (f.app X).comp (g.app X) h +
          (n₁ * n₂).negOnePow • (f'.app X).comp (g.app X) h
      simp)
    (fun r f g ↦ by
      apply GradedHom.ext
      funext X
      change (n₁ * n₂).negOnePow • ((r • f.app X).comp (g.app X) h) =
        r • (n₁ * n₂).negOnePow • (f.app X).comp (g.app X) h
      simp [smul_comm r (n₁ * n₂).negOnePow])
    (fun f g g' ↦ by
      apply GradedHom.ext
      funext X
      change (n₁ * n₂).negOnePow • ((f.app X).comp (g.app X + g'.app X) h) =
        (n₁ * n₂).negOnePow • (f.app X).comp (g.app X) h +
          (n₁ * n₂).negOnePow • (f.app X).comp (g'.app X) h
      simp)
    (fun r f g ↦ by
      apply GradedHom.ext
      funext X
      change (n₁ * n₂).negOnePow • ((f.app X).comp (r • g.app X) h) =
        r • (n₁ * n₂).negOnePow • (f.app X).comp (g.app X) h
      simp [smul_comm r (n₁ * n₂).negOnePow])

set_option backward.isDefEq.respectTransparency false in
/-- Signed module composition satisfies the DG Leibniz rule. -/
lemma differential_signedComp {M N P : RightModule (R := R) A}
    (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂)
    (f : GradedHom A M N n₁) (g : GradedHom A N P n₂) :
    differential A n₁₂ (n₁₂ + 1) (signedComp A n₁ n₂ n₁₂ h f g) =
      signedComp A (n₁ + 1) n₂ (n₁₂ + 1) (by omega)
          (differential A n₁ (n₁ + 1) f) g +
        n₁.negOnePow •
          signedComp A n₁ (n₂ + 1) (n₁₂ + 1) (by omega)
            f (differential A n₂ (n₂ + 1) g) := by
  apply GradedHom.ext
  funext X
  exact HomComplex.δ_signedComp R n₁ n₂ n₁₂ h (f.app X) (g.app X)

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of signed composition on homogeneous module maps. -/
lemma signedComp_assoc {M N P Q : RightModule (R := R) A}
    (n₁ n₂ n₃ : ℤ) (f : GradedHom A M N n₁) (g : GradedHom A N P n₂)
    (k : GradedHom A P Q n₃) :
    signedComp A (n₁ + n₂) n₃ (n₁ + n₂ + n₃) rfl
        (signedComp A n₁ n₂ (n₁ + n₂) rfl f g) k =
      signedComp A n₁ (n₂ + n₃) (n₁ + n₂ + n₃) (by omega) f
        (signedComp A n₂ n₃ (n₂ + n₃) rfl g k) := by
  apply GradedHom.ext
  funext X
  change ((n₁ + n₂) * n₃).negOnePow •
      (((n₁ * n₂).negOnePow • (f.app X).comp (g.app X) rfl).comp
        (k.app X) rfl) =
    (n₁ * (n₂ + n₃)).negOnePow •
      ((f.app X).comp
        ((n₂ * n₃).negOnePow • (g.app X).comp (k.app X) rfl) (by omega))
  simp only [Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul]
  rw [Cochain.comp_assoc]
  · have hs : ((n₁ + n₂) * n₃).negOnePow * (n₁ * n₂).negOnePow =
        (n₁ * (n₂ + n₃)).negOnePow * (n₂ * n₃).negOnePow := by
      rw [← Int.negOnePow_add, ← Int.negOnePow_add]
      apply congrArg
      ring
    rw [hs]
  · rfl

/-- The bidegree component of composition in the DG category of right modules. -/
def compComponent {M N P : RightModule (R := R) A}
    (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂) :
    ((homComplex A M N).X n₁ ⊗ (homComplex A N P).X n₂) ⟶
      (homComplex A M P).X n₁₂ :=
  ModuleCat.ofHom <| TensorProduct.lift (signedComp A n₁ n₂ n₁₂ h)

set_option backward.isDefEq.respectTransparency false in
/-- Composition on the Hom complexes of right DG modules. -/
noncomputable def comp {M N P : RightModule (R := R) A} :
    homComplex A M N ⊗ homComplex A N P ⟶ homComplex A M P where
  f n := HomologicalComplex.mapBifunctorDesc
    (fun n₁ n₂ h ↦ compComponent A n₁ n₂ n h)
  comm' n m hnm := by
    simp only [ComplexShape.up_Rel] at hnm
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro n₁ n₂ hn
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    change _ = _ ≫
      (HomologicalComplex.mapBifunctor (homComplex A M N) (homComplex A N P)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).d n m ≫ _
    rw [HomologicalComplex.mapBifunctor.d_eq, ← Category.assoc,
      Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂]
    rw [HomologicalComplex.mapBifunctor.d₁_eq
        (K₁ := homComplex A M N) (K₂ := homComplex A N P)
        (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ)
        (by simp : (ComplexShape.up ℤ).Rel n₁ (n₁ + 1)) n₂ m
        (by dsimp at hn ⊢; omega),
      HomologicalComplex.mapBifunctor.d₂_eq
        (K₁ := homComplex A M N) (K₂ := homComplex A N P)
        (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ) n₁
        (by simp : (ComplexShape.up ℤ).Rel n₂ (n₂ + 1)) m
        (by dsimp at hn ⊢; omega)]
    simp only [Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro f g
    change GradedHom A M N n₁ at f
    change GradedHom A N P n₂ at g
    unfold compComponent homComplex
    rw [ModuleCat.hom_comp]
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [ModuleCat.hom_add, LinearMap.add_apply]
    simp only [ModuleCat.hom_smul, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.smul_apply, LinearMap.comp_apply, curriedTensor,
      ModuleCat.hom_whiskerRight, ModuleCat.hom_whiskerLeft]
    have hε₁ : (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (n₁, n₂) = 1 := rfl
    have hε₂ : (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (n₁, n₂) = n₁.negOnePow := rfl
    rw [hε₁, hε₂, one_smul]
    change differential A n m (signedComp A n₁ n₂ n hn f g) =
      signedComp A (n₁ + 1) n₂ m (by dsimp at hn ⊢; omega)
          (differential A n₁ (n₁ + 1) f) g +
        n₁.negOnePow • signedComp A n₁ (n₂ + 1) m
          (by dsimp at hn ⊢; omega) f (differential A n₂ (n₂ + 1) g)
    subst m
    exact differential_signedComp A n₁ n₂ n hn f g

/-- The degree-zero graded identity of a right module. -/
def gradedId (M : RightModule (R := R) A) : GradedHom A M M 0 := ofHom A (𝟙 M)

/-- The degree-zero component of the enriched identity. -/
def idComponent (M : RightModule (R := R) A) :
    𝟙_ (ModuleCat R) ⟶ (homComplex A M M).X 0 :=
  ModuleCat.ofHom
    { toFun := fun r ↦ r • gradedId A M
      map_add' := fun r s ↦ by rw [add_smul]
      map_smul' := fun r s ↦ by simp [smul_smul] }

@[simp]
lemma idComponent_one (M : RightModule (R := R) A) :
    (idComponent A M).hom' 1 = gradedId A M := by
  change (1 : R) • gradedId A M = gradedId A M
  exact one_smul R _

/-- The identity morphism for the DG enrichment of right modules. -/
noncomputable def enrichedId (M : RightModule (R := R) A) :
    𝟙_ V ⟶ homComplex A M M :=
  HomologicalComplex.mkHomFromSingle (idComponent A M) (fun k hk ↦ by
    simp only [ComplexShape.up_Rel] at hk
    subst k
    apply ModuleCat.Hom.ext
    apply LinearMap.ext
    intro r
    apply GradedHom.ext
    funext X
    change δ 0 1 (r • Cochain.ofHom (𝟙 (M.obj X))) = 0
    rw [δ_smul]
    simp)

set_option backward.isDefEq.respectTransparency false in
/-- Left unitality of enriched module composition. -/
lemma enriched_id_comp (M N : RightModule (R := R) A) :
    (λ_ (homComplex A M N)).inv ≫ enrichedId A M ▷ homComplex A M N ≫ comp A =
      𝟙 (homComplex A M N) := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  have hleft : (λ_ (homComplex A M N)).inv.f n =
      (HomologicalComplex.leftUnitor' (homComplex A M N)).inv n := rfl
  rw [hleft, HomologicalComplex.leftUnitor'_inv]
  have hwhisk : (enrichedId A M ▷ homComplex A M N).f n =
      (HomologicalComplex.mapBifunctorMap (enrichedId A M) (𝟙 (homComplex A M N))
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f n := rfl
  rw [hwhisk]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap_assoc]
  rw [show (enrichedId A M).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ≫ idComponent A M by
    apply HomologicalComplex.mkHomFromSingle_f]
  simp only [Functor.map_comp, NatTrans.comp_app, HomologicalComplex.id_f,
    Category.assoc]
  unfold comp
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  rw [show ((curriedTensor (ModuleCat R)).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom).app ((homComplex A M N).X n) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ▷ (homComplex A M N).X n by rfl]
  rw [show ((curriedTensor (ModuleCat R)).map (idComponent A M)).app
      ((homComplex A M N).X n) = idComponent A M ▷ (homComplex A M N).X n by rfl]
  rw [show ((curriedTensor (ModuleCat R)).obj ((homComplex A M M).X 0)).map
      (𝟙 ((homComplex A M N).X n)) = (homComplex A M M).X 0 ◁
        𝟙 ((homComplex A M N).X n) by rfl]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id_assoc,
    MonoidalCategory.whiskerLeft_id]
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro f
  change GradedHom A M N n at f
  change (compComponent A 0 n n (zero_add n)).hom'
      ((idComponent A M ▷ (homComplex A M N).X n).hom'
        ((λ_ ((homComplex A M N).X n)).inv.hom' f)) = f
  rw [show (λ_ ((homComplex A M N).X n)).inv.hom' f = 1 ⊗ₜ[R] f by
    exact ModuleCat.MonoidalCategory.leftUnitor_inv_apply
      (M := (homComplex A M N).X n) f]
  rw [show (idComponent A M ▷ (homComplex A M N).X n).hom' (1 ⊗ₜ[R] f) =
      (idComponent A M).hom' 1 ⊗ₜ[R] f by
    exact ModuleCat.MonoidalCategory.whiskerRight_apply
      (idComponent A M) ((homComplex A M N).X n) 1 f]
  unfold compComponent homComplex
  change signedComp A 0 n n (zero_add n) ((idComponent A M).hom' 1) f = f
  rw [idComponent_one]
  apply GradedHom.ext
  funext X
  change HomComplex.signedComp R 0 n n (zero_add n)
    (Cochain.ofHom (𝟙 (M.obj X))) (f.app X) = f.app X
  simp [HomComplex.signedComp]

set_option backward.isDefEq.respectTransparency false in
/-- Right unitality of enriched module composition. -/
lemma enriched_comp_id (M N : RightModule (R := R) A) :
    (ρ_ (homComplex A M N)).inv ≫ homComplex A M N ◁ enrichedId A N ≫ comp A =
      𝟙 (homComplex A M N) := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  have hright : (ρ_ (homComplex A M N)).inv.f n =
      (HomologicalComplex.rightUnitor' (homComplex A M N)).inv n := rfl
  rw [hright, HomologicalComplex.rightUnitor'_inv]
  have hwhisk : (homComplex A M N ◁ enrichedId A N).f n =
      (HomologicalComplex.mapBifunctorMap (𝟙 (homComplex A M N)) (enrichedId A N)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f n := rfl
  rw [hwhisk]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap_assoc]
  rw [show (enrichedId A N).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ≫ idComponent A N by
    apply HomologicalComplex.mkHomFromSingle_f]
  simp only [Functor.map_comp, HomologicalComplex.id_f,
    Category.assoc]
  unfold comp
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro f
  change GradedHom A M N n at f
  change (compComponent A n 0 n (add_zero n)).hom'
      (((homComplex A M N).X n ◁ idComponent A N).hom'
        ((ρ_ ((homComplex A M N).X n)).inv.hom' f)) = f
  rw [show (ρ_ ((homComplex A M N).X n)).inv.hom' f = f ⊗ₜ[R] 1 by
    exact ModuleCat.MonoidalCategory.rightUnitor_inv_apply
      (M := (homComplex A M N).X n) f]
  rw [show ((homComplex A M N).X n ◁ idComponent A N).hom' (f ⊗ₜ[R] 1) =
      f ⊗ₜ[R] (idComponent A N).hom' 1 by
    exact ModuleCat.MonoidalCategory.whiskerLeft_apply
      ((homComplex A M N).X n) (idComponent A N) f 1]
  unfold compComponent homComplex
  change signedComp A n 0 n (add_zero n) f ((idComponent A N).hom' 1) = f
  rw [idComponent_one]
  apply GradedHom.ext
  funext X
  change HomComplex.signedComp R n 0 n (add_zero n)
    (f.app X) (Cochain.ofHom (𝟙 (N.obj X))) = f.app X
  simp [HomComplex.signedComp]

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of enriched composition for right DG modules. -/
lemma enriched_assoc (M N P Q : RightModule (R := R) A) :
    (α_ (homComplex A M N) (homComplex A N P) (homComplex A P Q)).inv ≫
        comp A ▷ homComplex A P Q ≫ comp A =
      homComplex A M N ◁ comp A ≫ comp A := by
  ext n : 1
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex.mapBifunctor₂₃.hom_ext (c₁₂ := ComplexShape.up ℤ)
  intro n₁ n₂ n₃ hn
  have hAssoc := HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (curriedAssociatorNatIso (ModuleCat R))
      (homComplex A M N) (homComplex A N P) (homComplex A P Q)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      n₁ n₂ n₃ n hn
  have hAssocInv :
      HomologicalComplex.mapBifunctor₂₃.ι
          (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
          (homComplex A M N) (homComplex A N P) (homComplex A P Q)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          n₁ n₂ n₃ n hn ≫
        (α_ (homComplex A M N) (homComplex A N P) (homComplex A P Q)).inv.f n =
      (α_ ((homComplex A M N).X n₁) ((homComplex A N P).X n₂)
        ((homComplex A P Q).X n₃)).inv ≫
        HomologicalComplex.mapBifunctor₁₂.ι
          (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
          (homComplex A M N) (homComplex A N P) (homComplex A P Q)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) n₁ n₂ n₃ n hn := by
    rw [← cancel_mono
      ((α_ (homComplex A M N) (homComplex A N P) (homComplex A P Q)).hom.f n)]
    have hi := (α_ (homComplex A M N) (homComplex A N P)
      (homComplex A P Q)).inv_hom_id
    have hi_n := congrFun (congrArg HomologicalComplex.Hom.f hi) n
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hi_n
    rw [Category.assoc, hi_n]
    rw [Category.assoc]
    erw [hAssoc]
    change _ ≫ 𝟙 _ =
      (α_ ((homComplex A M N).X n₁) ((homComplex A N P).X n₂)
        ((homComplex A P Q).X n₃)).inv ≫
        (α_ ((homComplex A M N).X n₁) ((homComplex A N P).X n₂)
          ((homComplex A P Q).X n₃)).hom ≫ _
    simp
  rw [← Category.assoc, hAssocInv]
  have hn₁₂ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (n₁ + n₂, n₃) = n := hn
  have hn₂₃ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (n₁, n₂ + n₃) = n := by
    change (n₁ + n₂) + n₃ = n at hn
    change n₁ + (n₂ + n₃) = n
    omega
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq
    (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
    (homComplex A M N) (homComplex A N P) (homComplex A P Q)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    n₁ n₂ n₃ (n₁ + n₂) n rfl hn₁₂]
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq
    (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
    (homComplex A M N) (homComplex A N P) (homComplex A P Q)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    n₁ n₂ n₃ (n₂ + n₃) n rfl hn₂₃]
  have hwhiskL :
      (comp (M := M) (N := N) (P := P) A ▷ homComplex A P Q).f n =
      (HomologicalComplex.mapBifunctorMap
        (comp (M := M) (N := N) (P := P) A) (𝟙 (homComplex A P Q))
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f n := rfl
  have hwhiskR :
      (homComplex A M N ◁ comp (M := N) (N := P) (P := Q) A).f n =
      (HomologicalComplex.mapBifunctorMap (𝟙 (homComplex A M N))
        (comp (M := N) (N := P) (P := Q) A)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f n := rfl
  rw [hwhiskL, hwhiskR]
  simp only [Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f]
  unfold comp
  dsimp only
  simp only [HomologicalComplex.ι_mapBifunctorDesc]
  rw [show ((curriedTensor (ModuleCat R)).map
      (HomologicalComplex.ιMapBifunctor (homComplex A M N) (homComplex A N P)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
        n₁ n₂ (n₁ + n₂) rfl)).app ((homComplex A P Q).X n₃) =
      HomologicalComplex.ιMapBifunctor (homComplex A M N) (homComplex A N P)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
        n₁ n₂ (n₁ + n₂) rfl ▷ (homComplex A P Q).X n₃ by rfl]
  change ( α_ ((homComplex A M N).X n₁) ((homComplex A N P).X n₂)
          ((homComplex A P Q).X n₃)).inv ≫
        HomologicalComplex.ιMapBifunctor (homComplex A M N) (homComplex A N P)
            (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
            n₁ n₂ (n₁ + n₂) rfl ▷ (homComplex A P Q).X n₃ ≫
          HomologicalComplex.mapBifunctorDesc
              (fun i j h ↦ compComponent A i j (n₁ + n₂) h) ▷
                (homComplex A P Q).X n₃ ≫
            (homComplex A M P).X (n₁ + n₂) ◁ 𝟙 ((homComplex A P Q).X n₃) ≫
              compComponent A (n₁ + n₂) n₃ n hn₁₂ =
      (homComplex A M N).X n₁ ◁
          HomologicalComplex.ιMapBifunctor (homComplex A N P) (homComplex A P Q)
            (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
            n₂ n₃ (n₂ + n₃) rfl ≫
        𝟙 ((homComplex A M N).X n₁) ▷
            (HomologicalComplex.mapBifunctor (homComplex A N P) (homComplex A P Q)
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).X (n₂ + n₃) ≫
          (homComplex A M N).X n₁ ◁
              HomologicalComplex.mapBifunctorDesc
                (fun i j h ↦ compComponent A i j (n₂ + n₃) h) ≫
            compComponent A n₁ (n₂ + n₃) n hn₂₃
  simp only [MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight,
    Category.id_comp]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro f gk
  induction gk using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [TensorProduct.tmul_add]
    simp only [map_add]
    rw [hx, hy]
  | tmul g k =>
    change GradedHom A M N n₁ at f
    change GradedHom A N P n₂ at g
    change GradedHom A P Q n₃ at k
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [ModuleCat.MonoidalCategory.associator_inv_apply]
    change (compComponent A (n₁ + n₂) n₃ n hn₁₂).hom'
        ((HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₁ + n₂) h) ▷
            (homComplex A P Q).X n₃).hom'
          ((HomologicalComplex.ιMapBifunctor
            (homComplex A M N) (homComplex A N P) (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) n₁ n₂ (n₁ + n₂) rfl ▷
              (homComplex A P Q).X n₃).hom' ((f ⊗ₜ[R] g) ⊗ₜ[R] k))) =
      (compComponent A n₁ (n₂ + n₃) n hn₂₃).hom'
        (((homComplex A M N).X n₁ ◁ HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₂ + n₃) h)).hom'
          (((homComplex A M N).X n₁ ◁ HomologicalComplex.ιMapBifunctor
            (homComplex A N P) (homComplex A P Q) (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) n₂ n₃ (n₂ + n₃) rfl).hom'
              (f ⊗ₜ[R] (g ⊗ₜ[R] k))))
    rw [show (HomologicalComplex.ιMapBifunctor
          (homComplex A M N) (homComplex A N P) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) n₁ n₂ (n₁ + n₂) rfl ▷
            (homComplex A P Q).X n₃).hom' ((f ⊗ₜ[R] g) ⊗ₜ[R] k) =
        (HomologicalComplex.ιMapBifunctor
          (homComplex A M N) (homComplex A N P) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) n₁ n₂ (n₁ + n₂) rfl).hom' (f ⊗ₜ[R] g) ⊗ₜ[R] k by
      exact ModuleCat.MonoidalCategory.whiskerRight_apply
        (HomologicalComplex.ιMapBifunctor
          (homComplex A M N) (homComplex A N P) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) n₁ n₂ (n₁ + n₂) rfl)
        ((homComplex A P Q).X n₃) (f ⊗ₜ[R] g) k]
    rw [show (HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₁ + n₂) h) ▷
            (homComplex A P Q).X n₃).hom'
          ((HomologicalComplex.ιMapBifunctor
            (homComplex A M N) (homComplex A N P) (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) n₁ n₂ (n₁ + n₂) rfl).hom' (f ⊗ₜ[R] g) ⊗ₜ[R] k) =
        ((HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₁ + n₂) h) :
            (HomologicalComplex.mapBifunctor (homComplex A M N) (homComplex A N P)
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).X (n₁ + n₂) ⟶
                (homComplex A M P).X (n₁ + n₂))).hom'
            ((HomologicalComplex.ιMapBifunctor
              (homComplex A M N) (homComplex A N P) (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) n₁ n₂ (n₁ + n₂) rfl).hom' (f ⊗ₜ[R] g)) ⊗ₜ[R] k by
      exact ModuleCat.MonoidalCategory.whiskerRight_apply
        (HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₁ + n₂) h) :
            (HomologicalComplex.mapBifunctor (homComplex A M N) (homComplex A N P)
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).X (n₁ + n₂) ⟶
                (homComplex A M P).X (n₁ + n₂))
        ((homComplex A P Q).X n₃)
        ((HomologicalComplex.ιMapBifunctor
          (homComplex A M N) (homComplex A N P) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) n₁ n₂ (n₁ + n₂) rfl).hom' (f ⊗ₜ[R] g)) k]
    rw [show ((homComplex A M N).X n₁ ◁ HomologicalComplex.ιMapBifunctor
          (homComplex A N P) (homComplex A P Q) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) n₂ n₃ (n₂ + n₃) rfl).hom'
          (f ⊗ₜ[R] (g ⊗ₜ[R] k)) =
        f ⊗ₜ[R] (HomologicalComplex.ιMapBifunctor
          (homComplex A N P) (homComplex A P Q) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) n₂ n₃ (n₂ + n₃) rfl).hom' (g ⊗ₜ[R] k) by
      exact ModuleCat.MonoidalCategory.whiskerLeft_apply
        ((homComplex A M N).X n₁)
        (HomologicalComplex.ιMapBifunctor
          (homComplex A N P) (homComplex A P Q) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) n₂ n₃ (n₂ + n₃) rfl) f (g ⊗ₜ[R] k)]
    rw [show ((homComplex A M N).X n₁ ◁ HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₂ + n₃) h)).hom'
          (f ⊗ₜ[R] (HomologicalComplex.ιMapBifunctor
            (homComplex A N P) (homComplex A P Q) (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) n₂ n₃ (n₂ + n₃) rfl).hom' (g ⊗ₜ[R] k)) =
        f ⊗ₜ[R] ((HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₂ + n₃) h) :
            (HomologicalComplex.mapBifunctor (homComplex A N P) (homComplex A P Q)
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).X (n₂ + n₃) ⟶
                (homComplex A N Q).X (n₂ + n₃))).hom'
            ((HomologicalComplex.ιMapBifunctor
              (homComplex A N P) (homComplex A P Q) (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) n₂ n₃ (n₂ + n₃) rfl).hom' (g ⊗ₜ[R] k)) by
      exact ModuleCat.MonoidalCategory.whiskerLeft_apply
        ((homComplex A M N).X n₁)
        (HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₂ + n₃) h) :
            (HomologicalComplex.mapBifunctor (homComplex A N P) (homComplex A P Q)
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).X (n₂ + n₃) ⟶
                (homComplex A N Q).X (n₂ + n₃)) f
        ((HomologicalComplex.ιMapBifunctor
          (homComplex A N P) (homComplex A P Q) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) n₂ n₃ (n₂ + n₃) rfl).hom' (g ⊗ₜ[R] k))]
    have hc₁₂ := congrArg
      (fun e : (homComplex A M N).X n₁ ⊗ (homComplex A N P).X n₂ ⟶
          (homComplex A M P).X (n₁ + n₂) ↦ e.hom' (f ⊗ₜ[R] g))
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := homComplex A M N) (K₂ := homComplex A N P)
        (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ)
        (A := (homComplex A M P).X (n₁ + n₂)) (j := n₁ + n₂)
        (fun i j h ↦ compComponent A i j (n₁ + n₂) h) n₁ n₂ rfl)
    have hc₂₃ := congrArg
      (fun e : (homComplex A N P).X n₂ ⊗ (homComplex A P Q).X n₃ ⟶
          (homComplex A N Q).X (n₂ + n₃) ↦ e.hom' (g ⊗ₜ[R] k))
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := homComplex A N P) (K₂ := homComplex A P Q)
        (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ)
        (A := (homComplex A N Q).X (n₂ + n₃)) (j := n₂ + n₃)
        (fun i j h ↦ compComponent A i j (n₂ + n₃) h) n₂ n₃ rfl)
    have hc₁₂' :
        ((HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₁ + n₂) h) :
            (HomologicalComplex.mapBifunctor (homComplex A M N) (homComplex A N P)
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).X (n₁ + n₂) ⟶
                (homComplex A M P).X (n₁ + n₂))).hom'
            ((HomologicalComplex.ιMapBifunctor
              (homComplex A M N) (homComplex A N P) (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) n₁ n₂ (n₁ + n₂) rfl).hom' (f ⊗ₜ[R] g)) =
          (compComponent A n₁ n₂ (n₁ + n₂) rfl).hom' (f ⊗ₜ[R] g) := by
      change (HomologicalComplex.ιMapBifunctor
          (homComplex A M N) (homComplex A N P) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) n₁ n₂ (n₁ + n₂) rfl ≫
        HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₁ + n₂) h)).hom' (f ⊗ₜ[R] g) = _
      exact hc₁₂
    have hc₂₃' :
        ((HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₂ + n₃) h) :
            (HomologicalComplex.mapBifunctor (homComplex A N P) (homComplex A P Q)
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).X (n₂ + n₃) ⟶
                (homComplex A N Q).X (n₂ + n₃))).hom'
            ((HomologicalComplex.ιMapBifunctor
              (homComplex A N P) (homComplex A P Q) (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) n₂ n₃ (n₂ + n₃) rfl).hom' (g ⊗ₜ[R] k)) =
          (compComponent A n₂ n₃ (n₂ + n₃) rfl).hom' (g ⊗ₜ[R] k) := by
      change (HomologicalComplex.ιMapBifunctor
          (homComplex A N P) (homComplex A P Q) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) n₂ n₃ (n₂ + n₃) rfl ≫
        HomologicalComplex.mapBifunctorDesc
          (fun i j h ↦ compComponent A i j (n₂ + n₃) h)).hom' (g ⊗ₜ[R] k) = _
      exact hc₂₃
    rw [hc₁₂', hc₂₃']
    unfold compComponent homComplex
    change signedComp A (n₁ + n₂) n₃ n hn₁₂
        (signedComp A n₁ n₂ (n₁ + n₂) rfl f g) k =
      signedComp A n₁ (n₂ + n₃) n hn₂₃ f
        (signedComp A n₂ n₃ (n₂ + n₃) rfl g k)
    subst n
    exact signedComp_assoc A n₁ n₂ n₃ f g k

/-- Right DG modules form a DG category whose Hom objects are the complexes of graded
module-natural transformations. -/
noncomputable instance dgCategory : DGCategory R (RightModule (R := R) A) where
  Hom := homComplex A
  id := enrichedId A
  comp := fun _ _ _ ↦ comp A
  id_comp := enriched_id_comp A
  comp_id := enriched_comp_id A
  assoc := enriched_assoc A

/-- Passing from a precomposed homotopy to its degree `-1` cochain is composition
with the corresponding degree-zero cochain. -/
lemma cochain_ofHomotopy_compLeft {K L E : V} {f g : K ⟶ L}
    (h : _root_.Homotopy f g) (e : E ⟶ K) :
    Cochain.ofHomotopy (h.compLeft e) =
      (Cochain.ofHom e).comp (Cochain.ofHomotopy h) (zero_add (-1)) := by
  apply Cochain.ext
  intro p q hpq
  rw [Cochain.zero_cochain_comp_v]
  simp only [Cochain.ofHomotopy, Cochain.mk_v, Cochain.ofHom_v,
    _root_.Homotopy.compLeft_hom]

/-- Passing from a postcomposed homotopy to its degree `-1` cochain is composition
with the corresponding degree-zero cochain. -/
lemma cochain_ofHomotopy_compRight {K L E : V} {f g : K ⟶ L}
    (h : _root_.Homotopy f g) (e : L ⟶ E) :
    Cochain.ofHomotopy (h.compRight e) =
      (Cochain.ofHomotopy h).comp (Cochain.ofHom e) (add_zero (-1)) := by
  apply Cochain.ext
  intro p q hpq
  rw [Cochain.comp_zero_cochain_v]
  simp only [Cochain.ofHomotopy, Cochain.mk_v, Cochain.ofHom_v,
    _root_.Homotopy.compRight_hom]

end FixedUniverse

end DGCategory.RightModule
namespace DGCategory

variable {R : Type w} [CommRing R]

local notation "V" => CochainComplex (ModuleCat R) ℤ

variable (A : Type u) [DGCategory R A]

namespace RightModule

/-- The strict zero right DG module. -/
noncomputable def zero : RightModule (R := R) A where
  obj _ := HomologicalComplex.zero
  action _ _ := 0
  action_id _ := HomologicalComplex.isZero_zero.eq_of_tgt _ _
  action_comp _ _ _ := HomologicalComplex.isZero_zero.eq_of_tgt _ _

/-- The strict zero right DG module is a zero object. -/
lemma isZero_zero : IsZero (zero (R := R) A) :=
  IsZero.mk
    (fun M ↦ ⟨
      { default := 0
        uniq := by
          intro f
          apply Hom.ext
          funext X
          exact HomologicalComplex.isZero_zero.eq_of_src _ _ }⟩)
    (fun M ↦ ⟨
      { default := 0
        uniq := by
          intro f
          apply Hom.ext
          funext X
          exact HomologicalComplex.isZero_zero.eq_of_tgt _ _ }⟩)

noncomputable instance : HasZeroObject (RightModule (R := R) A) :=
  HasZeroObject.mk ⟨zero (R := R) A, isZero_zero A⟩

/-- Naturality of the signed second-variable tensor-shift comparison in its first variable. -/
@[reassoc]
lemma mapBifunctorShift₂Iso_hom_naturality₁ {K L T : V} (f : K ⟶ L) (n : ℤ) :
    f ▷ T⟦n⟧ ≫
        (CochainComplex.mapBifunctorShift₂Iso L T (curriedTensor (ModuleCat R)) n).hom =
      (CochainComplex.mapBifunctorShift₂Iso K T (curriedTensor (ModuleCat R)) n).hom ≫
        (f ▷ T)⟦n⟧' := by
  have h := CategoryTheory.NatTrans.shift_app_comm
    ((curriedTensor (ModuleCat R)).map₂CochainComplex.map f) n T
  change (CochainComplex.mapBifunctorShift₂Iso K T
      (curriedTensor (ModuleCat R)) n).hom ≫ (f ▷ T)⟦n⟧' =
    f ▷ T⟦n⟧ ≫ (CochainComplex.mapBifunctorShift₂Iso L T
      (curriedTensor (ModuleCat R)) n).hom at h
  exact h.symm

/-- The action map of the objectwise shift of a right DG module.  The first map is the
canonical signed comparison `K ⊗ L[n] ≅ (K ⊗ L)[n]`. -/
noncomputable def shiftAction (M : RightModule (R := R) A) (n : ℤ) (X Y : A) :
    (X ⟶[V] Y) ⊗ (M.obj Y)⟦n⟧ ⟶ (M.obj X)⟦n⟧ :=
  (CochainComplex.mapBifunctorShift₂Iso (X ⟶[V] Y) (M.obj Y)
      (curriedTensor (ModuleCat R)) n).hom ≫
    (M.action X Y)⟦n⟧'

/-- Tensor a right DG module on the right by a cochain complex. -/
noncomputable def tensorRight (M : RightModule (R := R) A) (K : V) :
    RightModule (R := R) A where
  obj X := M.obj X ⊗ K
  action X Y := (α_ (X ⟶[V] Y) (M.obj Y) K).inv ≫ M.action X Y ▷ K
  action_id X := by
    rw [MonoidalCategory.leftUnitor_tensor_inv]
    simp only [Category.assoc]
    rw [← MonoidalCategory.associator_naturality_left_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.comp_whiskerRight]
    rw [← MonoidalCategory.comp_whiskerRight, M.action_id]
    simp
  action_comp X Y Z := by
    rw [← cancel_epi (α_ ((X ⟶[V] Y) ⊗ (Y ⟶[V] Z)) (M.obj Z) K).hom]
    rw [← MonoidalCategory.associator_naturality_left_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.comp_whiskerRight]
    rw [M.action_comp]
    simp

/-- Tensor a morphism of right DG modules on the right by a cochain complex. -/
noncomputable def tensorRightMap {M N : RightModule (R := R) A} (f : M ⟶ N) (K : V) :
    tensorRight A M K ⟶ tensorRight A N K where
  app X := f.app X ▷ K
  naturality X Y := by
    simp only [tensorRight, Category.assoc]
    slice_lhs 2 3 => rw [← MonoidalCategory.comp_whiskerRight]
    rw [MonoidalCategory.associator_inv_naturality_middle_assoc]
    slice_rhs 2 3 => rw [← MonoidalCategory.comp_whiskerRight]
    rw [f.naturality]

/-- Functoriality of right tensoring in the cochain-complex factor. -/
noncomputable def tensorRightMap₂ (M : RightModule (R := R) A) {K L : V} (f : K ⟶ L) :
    tensorRight A M K ⟶ tensorRight A M L where
  app X := M.obj X ◁ f
  naturality X Y := by
    simp only [tensorRight, Category.assoc]
    rw [MonoidalCategory.associator_inv_naturality_right_assoc]
    rw [MonoidalCategory.whisker_exchange]

/-- Right tensoring by a fixed cochain complex, as a functor on right DG modules. -/
noncomputable def tensorRightFunctor (K : V) :
    CategoryTheory.Functor (RightModule (R := R) A) (RightModule (R := R) A) where
  obj M := tensorRight A M K
  map f := tensorRightMap A f K
  map_id M := by
    apply Hom.ext
    funext X
    change (𝟙 (M.obj X)) ▷ K = 𝟙 (M.obj X ⊗ K)
    simp
  map_comp f g := by
    apply Hom.ext
    funext X
    change (f.app X ≫ g.app X) ▷ K = f.app X ▷ K ≫ g.app X ▷ K
    exact MonoidalCategory.comp_whiskerRight _ _ _

/-- An isomorphism in the second tensor factor induces an isomorphism of right DG modules. -/
noncomputable def tensorRightIso₂ (M : RightModule (R := R) A) {K L : V} (e : K ≅ L) :
    tensorRight A M K ≅ tensorRight A M L where
  hom := tensorRightMap₂ A M e.hom
  inv := tensorRightMap₂ A M e.inv
  hom_inv_id := by
    apply Hom.ext
    funext X
    change (M.obj X ◁ e.hom) ≫ (M.obj X ◁ e.inv) = 𝟙 (M.obj X ⊗ K)
    rw [← MonoidalCategory.whiskerLeft_comp]
    simp
  inv_hom_id := by
    apply Hom.ext
    funext X
    change (M.obj X ◁ e.inv) ≫ (M.obj X ◁ e.hom) = 𝟙 (M.obj X ⊗ L)
    rw [← MonoidalCategory.whiskerLeft_comp]
    simp

/-- Tensoring a right DG module by the monoidal unit does not change it. -/
noncomputable def tensorRightUnitIso (M : RightModule (R := R) A) :
    tensorRight A M (𝟙_ V) ≅ M where
  hom :=
    { app X := (ρ_ (M.obj X)).hom
      naturality X Y := by simp [tensorRight] }
  inv :=
    { app X := (ρ_ (M.obj X)).inv
      naturality X Y := by simp [tensorRight] }
  hom_inv_id := by
    apply Hom.ext
    funext X
    change (ρ_ (M.obj X)).hom ≫ (ρ_ (M.obj X)).inv = 𝟙 (M.obj X ⊗ (𝟙_ V))
    simp
  inv_hom_id := by
    apply Hom.ext
    funext X
    change (ρ_ (M.obj X)).inv ≫ (ρ_ (M.obj X)).hom = 𝟙 (M.obj X)
    simp

/-- Transport the action of a right DG module across objectwise isomorphisms. -/
noncomputable def ofObjIso (M : RightModule (R := R) A) (N : A → V)
    (e : ∀ X, M.obj X ≅ N X) : RightModule (R := R) A where
  obj := N
  action X Y := (X ⟶[V] Y) ◁ (e Y).inv ≫ M.action X Y ≫ (e X).hom
  action_id X := by
    rw [← cancel_mono (e X).inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    rw [← MonoidalCategory.leftUnitor_inv_naturality_assoc]
    rw [M.action_id]
    simp
  action_comp X Y Z := by
    rw [← cancel_mono (e X).inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    rw [← MonoidalCategory.associator_naturality_right_assoc]
    rw [M.action_comp]
    simp

/-- Transport a module morphism across the objectwise isomorphisms used by `ofObjIso`. -/
noncomputable def ofObjIsoMap {M M' : RightModule (R := R) A} (f : M ⟶ M')
    {N N' : A → V} (e : ∀ X, M.obj X ≅ N X) (e' : ∀ X, M'.obj X ≅ N' X) :
    ofObjIso A M N e ⟶ ofObjIso A M' N' e' where
  app X := (e X).inv ≫ f.app X ≫ (e' X).hom
  naturality X Y := by
    simp only [ofObjIso, Category.assoc, Iso.hom_inv_id_assoc,
      MonoidalCategory.whiskerLeft_comp]
    slice_rhs 3 4 =>
      rw [← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
        MonoidalCategory.whiskerLeft_id]
    slice_lhs 2 3 => rw [f.naturality]
    simp only [Category.id_comp, Category.assoc]

/-- The module with transported action is canonically isomorphic to the original module. -/
noncomputable def ofObjIsoIso (M : RightModule (R := R) A) (N : A → V)
    (e : ∀ X, M.obj X ≅ N X) : M ≅ ofObjIso A M N e where
  hom :=
    { app X := (e X).hom
      naturality X Y := by simp [ofObjIso] }
  inv :=
    { app X := (e X).inv
      naturality X Y := by simp [ofObjIso] }
  hom_inv_id := by
    apply Hom.ext
    funext X
    change (e X).hom ≫ (e X).inv = 𝟙 (M.obj X)
    simp
  inv_hom_id := by
    apply Hom.ext
    funext X
    change (e X).inv ≫ (e X).hom = 𝟙 (N X)
    simp

set_option maxHeartbeats 800000 in
-- The componentwise total-complex calculation needs additional elaboration time.
set_option backward.isDefEq.respectTransparency false in
/-- Moving a shift through the second variable of a triple tensor product is compatible
with the associator. -/
lemma mapBifunctorShift₂Iso_associator (H K L : V) (n : ℤ) :
    (α_ H K (L⟦n⟧)).inv ≫
        (CochainComplex.mapBifunctorShift₂Iso (H ⊗ K) L
          (curriedTensor (ModuleCat R)) n).hom =
      H ◁ (CochainComplex.mapBifunctorShift₂Iso K L
          (curriedTensor (ModuleCat R)) n).hom ≫
        (CochainComplex.mapBifunctorShift₂Iso H (K ⊗ L)
          (curriedTensor (ModuleCat R)) n).hom ≫
            ((α_ H K L).inv)⟦n⟧' := by
  rw [← cancel_epi (α_ H K (L⟦n⟧)).hom]
  simp only [Iso.hom_inv_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro i j k hp
  have hp₁₂ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i + j, k) = p := hp
  have hp₂₃ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i, j + k) = p := by
    change (i + j) + k = p at hp
    change i + (j + k) = p
    omega
  simp only [HomologicalComplex.comp_f]
  slice_rhs 1 2 =>
    erw [HomologicalComplex.ι_mapBifunctorAssociatorX_hom
      (curriedAssociatorNatIso (ModuleCat R)) H K (L⟦n⟧)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          i j k p hp]
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq
    (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R)) H K (L⟦n⟧)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        i j k (j + k) p rfl hp₂₃]
  slice_lhs 1 2 =>
    rw [HomologicalComplex.mapBifunctor₁₂.ι_eq
      (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R)) H K (L⟦n⟧)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) i j k (i + j) p rfl hp₁₂]
  slice_lhs 2 3 =>
    erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
      (H ⊗ K) L (curriedTensor (ModuleCat R)) n (i + j) k p hp₁₂
        (k + n) (p + n) rfl rfl]
  have hOuter :
      HomologicalComplex.ιMapBifunctor H
          (HomologicalComplex.mapBifunctor K (L⟦n⟧)
            (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ))
          (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) i (j + k) p hp₂₃ ≫
        (H ◁ (CochainComplex.mapBifunctorShift₂Iso K L
          (curriedTensor (ModuleCat R)) n).hom).f p =
      (H.X i ◁ (CochainComplex.mapBifunctorShift₂Iso K L
          (curriedTensor (ModuleCat R)) n).hom.f (j + k)) ≫
        HomologicalComplex.ιMapBifunctor H
          ((CategoryTheory.shiftFunctor V n).obj
            (HomologicalComplex.mapBifunctor K L
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)))
          (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) i (j + k) p hp₂₃ := by
    change _ ≫ (HomologicalComplex.mapBifunctorMap (𝟙 H)
        (CochainComplex.mapBifunctorShift₂Iso K L
          (curriedTensor (ModuleCat R)) n).hom
          (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f p = _
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp
  slice_rhs 3 4 => rw [hOuter]
  have hInner := CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
    K L (curriedTensor (ModuleCat R)) n j k (j + k) rfl
      (k + n) (j + k + n) rfl (by omega)
  have hInnerMap := congrArg
    (fun f ↦ ((curriedTensor (ModuleCat R)).obj (H.X i)).map f) hInner
  simp only [Functor.map_comp, Functor.map_units_smul] at hInnerMap
  simp only [Category.assoc]
  slice_rhs 2 3 =>
    change ((curriedTensor (ModuleCat R)).obj (H.X i)).map
        (HomologicalComplex.ιMapBifunctor K (L⟦n⟧)
          (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
            j k (j + k) rfl) ≫
      ((curriedTensor (ModuleCat R)).obj (H.X i)).map
        ((CochainComplex.mapBifunctorShift₂Iso K L
          (curriedTensor (ModuleCat R)) n).hom.f (j + k))
    rw [hInnerMap]
  have hOuterShift := CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
    H (K ⊗ L) (curriedTensor (ModuleCat R)) n i (j + k) p hp₂₃
      (j + k + n) (p + n) rfl rfl
  change
    HomologicalComplex.ιMapBifunctor H
        ((CategoryTheory.shiftFunctor V n).obj
          (HomologicalComplex.mapBifunctor K L
            (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)))
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
          i (j + k) p hp₂₃ ≫
      (CochainComplex.mapBifunctorShift₂Iso H (K ⊗ L)
        (curriedTensor (ModuleCat R)) n).hom.f p = _ at hOuterShift
  have hOuterShiftAssoc := congrArg
    (fun f ↦ f ≫ (((α_ H K L).inv)⟦n⟧').f p) hOuterShift
  simp only [Category.assoc] at hOuterShiftAssoc ⊢
  rw [hOuterShiftAssoc]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul,
    Category.assoc, ← Int.negOnePow_add]
  slice_rhs 5 6 =>
    rw [← Functor.map_comp]
    change ((curriedTensor (ModuleCat R)).obj (H.X i)).map
      (((K ⊗ L).shiftFunctorObjXIso n (j + k) (j + k + n) rfl).inv ≫
        ((K ⊗ L).shiftFunctorObjXIso n (j + k) (j + k + n) rfl).hom)
    simp only [Iso.inv_hom_id, Functor.map_id,
      MonoidalCategory.whiskerLeft_id]
  have hMapId :=
    ((curriedTensor (ModuleCat R)).obj (H.X i)).map_id
      ((HomologicalComplex.mapBifunctor K L
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).X (j + k + n))
  rw [hMapId, Category.id_comp]
  congr 1
  · congr 1
    ring
  · simp only [CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
      CochainComplex.shiftFunctor_map_f', Category.comp_id]
    dsimp only [CochainComplex.shiftFunctor]
    have hMapIdHK :=
      ((curriedTensor (ModuleCat R)).obj ((H ⊗ K).X (i + j))).map_id
        (L.X (k + n))
    rw [hMapIdHK, Category.id_comp]
    have hMapIdK :=
      ((curriedTensor (ModuleCat R)).obj (K.X j)).map_id (L.X (k + n))
    rw [hMapIdK]
    have hMapIdH :=
      ((curriedTensor (ModuleCat R)).obj (H.X i)).map_id
        (((curriedTensor (ModuleCat R)).obj (K.X j)).obj (L.X (k + n)))
    rw [hMapIdH]
    change
      ((curriedTensor (ModuleCat R)).map
          (HomologicalComplex.ιMapBifunctor H K (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) i j (i + j) rfl)).app (L.X (k + n)) ≫
        HomologicalComplex.ιMapBifunctor (H ⊗ K) L
          (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
            (i + j) (k + n) (p + n) (by
              change (i + j) + (k + n) = p + n
              change (i + j) + k = p at hp₁₂
              omega) =
      (α_ (H.X i) (K.X j) (L.X (k + n))).hom ≫
        CategoryStruct.id _ ≫
          ((curriedTensor (ModuleCat R)).obj (H.X i)).map
            (HomologicalComplex.ιMapBifunctor K L
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
                j (k + n) (j + k + n) (by
                  change j + (k + n) = j + k + n
                  omega)) ≫
            HomologicalComplex.ιMapBifunctor H (K ⊗ L)
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
                i (j + k + n) (p + n) (by
                  change i + (j + k + n) = p + n
                  change i + (j + k) = p at hp₂₃
                  omega) ≫
              (α_ H K L).inv.f (p + n)
    simp only [Category.id_comp]
    have hkN :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (j, k + n) = j + k + n := by
      change j + (k + n) = j + k + n
      omega
    have hpN₂₃ :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (i, j + k + n) = p + n := by
      change i + (j + k + n) = p + n
      change i + (j + k) = p at hp₂₃
      omega
    have hpNTriple :
        (ComplexShape.up ℤ).r (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (i, j, k + n) = p + n := by
      change (i + j) + (k + n) = p + n
      change (i + j) + k = p at hp₁₂
      omega
    have hpN₁₂ :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (i + j, k + n) = p + n := by
      change (i + j) + (k + n) = p + n
      change (i + j) + k = p at hp₁₂
      omega
    slice_rhs 2 3 =>
      change
        ((curriedTensor (ModuleCat R)).obj (H.X i)).map
            (HomologicalComplex.ιMapBifunctor K L
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
                j (k + n) (j + k + n) hkN) ≫
          HomologicalComplex.ιMapBifunctor H
            (HomologicalComplex.mapBifunctor K L
              (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ))
            (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
              i (j + k + n) (p + n) hpN₂₃
      rw [← HomologicalComplex.mapBifunctor₂₃.ι_eq
        (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R)) H K L
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            i j (k + n) (j + k + n) (p + n) hkN hpN₂₃]
    slice_rhs 1 2 =>
      erw [← HomologicalComplex.ι_mapBifunctorAssociatorX_hom
        (curriedAssociatorNatIso (ModuleCat R)) H K L
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            i j (k + n) (p + n) hpNTriple]
    simp only [Category.assoc]
    have hAssocHom :
        (HomologicalComplex.mapBifunctorAssociatorX
          (curriedAssociatorNatIso (ModuleCat R)) H K L
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (p + n)).hom = (α_ H K L).hom.f (p + n) := rfl
    rw [hAssocHom]
    have hIsoComp :
        (α_ H K L).hom.f (p + n) ≫ (α_ H K L).inv.f (p + n) =
          (CategoryStruct.id ((H ⊗ K) ⊗ L)).f (p + n) := by
      rw [← HomologicalComplex.comp_f, Iso.hom_inv_id]
    rw [hIsoComp]
    simp only [HomologicalComplex.id_f]
    rw [HomologicalComplex.mapBifunctor₁₂.ι_eq
      (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R)) H K L
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          i j (k + n) (i + j) (p + n) rfl hpN₁₂]
    let f :=
      ((curriedTensor (ModuleCat R)).map
          (HomologicalComplex.ιMapBifunctor H K (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) i j (i + j) rfl)).app (L.X (k + n)) ≫
        HomologicalComplex.ιMapBifunctor
          (HomologicalComplex.mapBifunctor H K
            (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)) L
          (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
            (i + j) (k + n) (p + n) hpN₁₂
    change f = f ≫ CategoryStruct.id _
    exact (Category.comp_id f).symm

/-- The canonical objectwise comparison from tensoring by the shifted unit to an ordinary
shift.  Its first factor is the signed `mapBifunctorShift₂Iso`. -/
noncomputable def tensorShiftUnitIso (K : V) (n : ℤ) :
    K ⊗ (𝟙_ V)⟦n⟧ ≅ K⟦n⟧ :=
  CochainComplex.mapBifunctorShift₂Iso K (𝟙_ V)
      (curriedTensor (ModuleCat R)) n ≪≫
    (shiftFunctor V n).mapIso (ρ_ K)

@[simp]
lemma tensorShiftUnitIso_hom (K : V) (n : ℤ) :
    (tensorShiftUnitIso (R := R) K n).hom =
      (CochainComplex.mapBifunctorShift₂Iso K (𝟙_ V)
          (curriedTensor (ModuleCat R)) n).hom ≫
        (CategoryTheory.shiftFunctor V n).map (ρ_ K).hom := rfl

@[simp]
lemma tensorShiftUnitIso_inv (K : V) (n : ℤ) :
    (tensorShiftUnitIso (R := R) K n).inv =
      (CategoryTheory.shiftFunctor V n).map (ρ_ K).inv ≫
        (CochainComplex.mapBifunctorShift₂Iso K (𝟙_ V)
          (curriedTensor (ModuleCat R)) n).inv := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The comparison from tensoring by the shifted unit is compatible with the associator. -/
lemma tensorShiftUnitIso_associator (H K : V) (n : ℤ) :
    H ◁ (tensorShiftUnitIso (R := R) K n).inv ≫
        (α_ H K ((𝟙_ V)⟦n⟧)).inv ≫
          (tensorShiftUnitIso (R := R) (H ⊗ K) n).hom =
      (CochainComplex.mapBifunctorShift₂Iso H K
        (curriedTensor (ModuleCat R)) n).hom := by
  rw [tensorShiftUnitIso_inv, tensorShiftUnitIso_hom]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  slice_lhs 3 4 => rw [mapBifunctorShift₂Iso_associator]
  slice_lhs 2 3 =>
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id]
  simp only [Category.id_comp, Category.assoc]
  slice_lhs 1 2 =>
    change HomologicalComplex.mapBifunctorMap (𝟙 H)
        ((CategoryTheory.shiftFunctor V n).map (ρ_ K).inv)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) ≫
      (CochainComplex.mapBifunctorShift₂Iso H (K ⊗ (𝟙_ V))
        (curriedTensor (ModuleCat R)) n).hom
    rw [CochainComplex.mapBifunctorShift₂Iso_hom_naturality₂]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  have hwhisker :
      HomologicalComplex.mapBifunctorMap (𝟙 H) (ρ_ K).inv
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) = H ◁ (ρ_ K).inv := rfl
  rw [hwhisker, MonoidalCategory.whiskerLeft_rightUnitor_inv]
  simp

/-- Naturality of the shifted-unit comparison. -/
lemma tensorShiftUnitIso_hom_naturality {K L : V} (f : K ⟶ L) (n : ℤ) :
    f ▷ ((𝟙_ V)⟦n⟧) ≫ (tensorShiftUnitIso (R := R) L n).hom =
      (tensorShiftUnitIso (R := R) K n).hom ≫ f⟦n⟧' := by
  rw [tensorShiftUnitIso_hom, tensorShiftUnitIso_hom]
  simp only [Category.assoc]
  rw [mapBifunctorShift₂Iso_hom_naturality₁_assoc]
  rw [← Functor.map_comp]
  simp

/-- The objectwise shift of a right DG module. -/
noncomputable def shift (M : RightModule (R := R) A) (n : ℤ) :
    RightModule (R := R) A :=
  ofObjIso A (tensorRight A M ((𝟙_ V)⟦n⟧))
    (fun X ↦ (M.obj X)⟦n⟧) (fun X ↦ tensorShiftUnitIso (R := R) (M.obj X) n)

/-- The presentation of the objectwise module shift by tensoring with the shifted unit. -/
noncomputable def shiftPresentationIso (M : RightModule (R := R) A) (n : ℤ) :
    tensorRight A M ((𝟙_ V)⟦n⟧) ≅ shift A M n :=
  ofObjIsoIso A (tensorRight A M ((𝟙_ V)⟦n⟧))
    (fun X ↦ (M.obj X)⟦n⟧) (fun X ↦ tensorShiftUnitIso (R := R) (M.obj X) n)

set_option maxHeartbeats 800000 in
-- Expanding the transported action requires additional elaboration time.
/-- The transported action on the shifted module is the standard signed shift action. -/
@[simp]
lemma shift_action (M : RightModule (R := R) A) (n : ℤ) (X Y : A) :
    (shift A M n).action X Y = shiftAction A M n X Y := by
  change
    (X ⟶[V] Y) ◁ (tensorShiftUnitIso (R := R) (M.obj Y) n).inv ≫
        (α_ (X ⟶[V] Y) (M.obj Y) ((𝟙_ V)⟦n⟧)).inv ≫
          (M.action X Y ▷ ((𝟙_ V)⟦n⟧)) ≫
            (tensorShiftUnitIso (R := R) (M.obj X) n).hom =
      (CochainComplex.mapBifunctorShift₂Iso (X ⟶[V] Y) (M.obj Y)
          (curriedTensor (ModuleCat R)) n).hom ≫
        (M.action X Y)⟦n⟧'
  slice_lhs 3 4 =>
    rw [tensorShiftUnitIso_hom_naturality]
  slice_lhs 1 3 =>
    rw [tensorShiftUnitIso_associator]

/-- The shifted morphism of right DG modules. -/
noncomputable def shiftMap {M N : RightModule (R := R) A} (f : M ⟶ N) (n : ℤ) :
    shift A M n ⟶ shift A N n :=
  ofObjIsoMap A (tensorRightMap A f ((𝟙_ V)⟦n⟧))
    (fun X ↦ tensorShiftUnitIso (R := R) (M.obj X) n)
    (fun X ↦ tensorShiftUnitIso (R := R) (N.obj X) n)

/-- The transported shifted morphism is pointwise the ordinary shifted cochain map. -/
@[simp]
lemma shiftMap_app {M N : RightModule (R := R) A} (f : M ⟶ N) (n : ℤ) (X : A) :
    (shiftMap A f n).app X = (f.app X)⟦n⟧' := by
  change (tensorShiftUnitIso (R := R) (M.obj X) n).inv ≫
    (f.app X ▷ ((𝟙_ V)⟦n⟧)) ≫
      (tensorShiftUnitIso (R := R) (N.obj X) n).hom = (f.app X)⟦n⟧'
  change ((shiftFunctor V n).map (ρ_ (M.obj X)).inv ≫
      (CochainComplex.mapBifunctorShift₂Iso (M.obj X) (𝟙_ V)
        (curriedTensor (ModuleCat R)) n).inv) ≫
    (f.app X ▷ ((𝟙_ V)⟦n⟧)) ≫
      (CochainComplex.mapBifunctorShift₂Iso (N.obj X) (𝟙_ V)
        (curriedTensor (ModuleCat R)) n).hom ≫
        (shiftFunctor V n).map (ρ_ (N.obj X)).hom = (f.app X)⟦n⟧'
  simp only [Category.assoc]
  rw [mapBifunctorShift₂Iso_hom_naturality₁_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp]
  simp

/-- Shifting right DG modules by a fixed integer. -/
noncomputable def shiftFunctor (n : ℤ) :
    CategoryTheory.Functor (RightModule (R := R) A) (RightModule (R := R) A) where
  obj M := shift A M n
  map f := shiftMap A f n
  map_id M := by
    apply Hom.ext
    funext X
    rw [shiftMap_app]
    change (CategoryTheory.shiftFunctor V n).map (𝟙 (M.obj X)) =
      𝟙 ((CategoryTheory.shiftFunctor V n).obj (M.obj X))
    exact (CategoryTheory.shiftFunctor V n).map_id (M.obj X)
  map_comp f g := by
    apply Hom.ext
    funext X
    simp only [comp_app, shiftMap_app]
    exact (CategoryTheory.shiftFunctor V n).map_comp (f.app X) (g.app X)

@[simp]
lemma shiftFunctor_map_app {M N : RightModule (R := R) A} (f : M ⟶ N)
    (n : ℤ) (X : A) :
    ((shiftFunctor A n).map f).app X = (f.app X)⟦n⟧' :=
  shiftMap_app A f n X

/-- The zero-shift comparison for right DG modules. -/
noncomputable def shiftZeroIso (M : RightModule (R := R) A) : shift A M 0 ≅ M :=
  (shiftPresentationIso A M 0).symm ≪≫
    tensorRightIso₂ A M ((CategoryTheory.shiftFunctorZero V ℤ).app (𝟙_ V)) ≪≫
      tensorRightUnitIso A M

/-- The tensor presentation of module shifts, naturally in the module. -/
noncomputable def shiftPresentationNatIso (n : ℤ) :
    tensorRightFunctor A ((𝟙_ V)⟦n⟧) ≅ shiftFunctor A n :=
  NatIso.ofComponents (fun M ↦ shiftPresentationIso A M n) (by
    intro M N f
    apply Hom.ext
    funext X
    change (f.app X ▷ ((𝟙_ V)⟦n⟧)) ≫
        (tensorShiftUnitIso (R := R) (N.obj X) n).hom =
      (tensorShiftUnitIso (R := R) (M.obj X) n).hom ≫
        (tensorShiftUnitIso (R := R) (M.obj X) n).inv ≫
          (f.app X ▷ ((𝟙_ V)⟦n⟧)) ≫
            (tensorShiftUnitIso (R := R) (N.obj X) n).hom
    simp)

/-- Tensor maps in the two variables commute. -/
lemma tensorRightMap_map₂ {M N : RightModule (R := R) A} (f : M ⟶ N)
    {K L : V} (g : K ⟶ L) :
    tensorRightMap A f K ≫ tensorRightMap₂ A N g =
      tensorRightMap₂ A M g ≫ tensorRightMap A f L := by
  apply Hom.ext
  funext X
  change (f.app X ▷ K) ≫ (N.obj X ◁ g) =
    (M.obj X ◁ g) ≫ (f.app X ▷ L)
  exact (MonoidalCategory.whisker_exchange (f.app X) g).symm

/-- Changing the second tensor factor by an isomorphism is natural in the module. -/
noncomputable def tensorRightNatIso₂ {K L : V} (e : K ≅ L) :
    tensorRightFunctor A K ≅ tensorRightFunctor A L :=
  NatIso.ofComponents (fun M ↦ tensorRightIso₂ A M e)
    (fun f ↦ tensorRightMap_map₂ A f e.hom)

/-- The right-unitor comparison is natural in the module. -/
noncomputable def tensorRightUnitNatIso :
    tensorRightFunctor A (𝟙_ V) ≅ 𝟭 (RightModule (R := R) A) :=
  NatIso.ofComponents (tensorRightUnitIso A) (by
    intro M N f
    apply Hom.ext
    funext X
    change (f.app X ▷ (𝟙_ V)) ≫ (ρ_ (N.obj X)).hom =
      (ρ_ (M.obj X)).hom ≫ f.app X
    exact MonoidalCategory.rightUnitor_naturality (f.app X))

/-- The zero-shift comparison, naturally in right DG modules. -/
noncomputable def shiftZeroNatIso : shiftFunctor A 0 ≅ 𝟭 (RightModule (R := R) A) :=
  (shiftPresentationNatIso A 0).symm ≪≫
    tensorRightNatIso₂ A ((CategoryTheory.shiftFunctorZero V ℤ).app (𝟙_ V)) ≪≫
      tensorRightUnitNatIso A

/-! ### Objectwise mapping cones -/

open CochainComplex.HomComplex

/-- Tensoring a cocycle on the right gives a cocycle, with the Koszul sign supplied by
`TensorCochain.right`. -/
noncomputable def tensorCocycleRight (H : V) {K L : V} {n : ℤ}
    (z : Cocycle K L n) : Cocycle (H ⊗ K) (H ⊗ L) n :=
  Cocycle.mk (TensorCochain.right H z.1) (n + 1) rfl (by
    rw [TensorCochain.δ_right H n (n + 1) rfl z.1]
    simp)

/-- The degree-one part of the action on an objectwise mapping cone. -/
noncomputable def mappingConeActionFst {M N : RightModule (R := R) A} (f : M ⟶ N)
    (X Y : A) :
    Cocycle ((X ⟶[V] Y) ⊗ CochainComplex.mappingCone (f.app Y)) (M.obj X) 1 :=
  (tensorCocycleRight (X ⟶[V] Y) (CochainComplex.mappingCone.fst (f.app Y))).postcomp
    (M.action X Y)

/-- The degree-zero part of the action on an objectwise mapping cone. -/
noncomputable def mappingConeActionSnd {M N : RightModule (R := R) A} (f : M ⟶ N)
    (X Y : A) :
    Cochain ((X ⟶[V] Y) ⊗ CochainComplex.mappingCone (f.app Y)) (N.obj X) 0 :=
  (TensorCochain.right (X ⟶[V] Y) (CochainComplex.mappingCone.snd (f.app Y))).comp
    (Cochain.ofHom (N.action X Y)) (add_zero 0)

lemma mappingConeAction_condition {M N : RightModule (R := R) A} (f : M ⟶ N)
    (X Y : A) :
    δ 0 1 (mappingConeActionSnd A f X Y) +
        (mappingConeActionFst A f X Y).1.comp
          (Cochain.ofHom (f.app X)) (add_zero 1) = 0 := by
  change
    δ 0 1
          ((TensorCochain.right (X ⟶[V] Y)
              (CochainComplex.mappingCone.snd (f.app Y))).comp
            (Cochain.ofHom (N.action X Y)) (add_zero 0)) +
        ((TensorCochain.right (X ⟶[V] Y)
              (CochainComplex.mappingCone.fst (f.app Y)).1).comp
            (Cochain.ofHom (M.action X Y)) (add_zero 1)).comp
          (Cochain.ofHom (f.app X)) (add_zero 1) = 0
  rw [δ_comp_ofHom]
  · rw [TensorCochain.δ_right (X ⟶[V] Y) 0 1 rfl]
    rw [CochainComplex.mappingCone.δ_snd]
    rw [TensorCochain.right_neg]
    rw [Cochain.neg_comp]
    rw [Cochain.comp_assoc_of_second_is_zero_cochain]
    rw [← Cochain.ofHom_comp, f.naturality]
    rw [Cochain.ofHom_comp]
    rw [← Cochain.comp_assoc_of_second_is_zero_cochain]
    rw [← TensorCochain.right_comp_ofHom]
    simp

/-- The action on the objectwise mapping cone, assembled from the tensor of the two
canonical projections of the cone. -/
noncomputable def mappingConeAction {M N : RightModule (R := R) A} (f : M ⟶ N)
    (X Y : A) :
    (X ⟶[V] Y) ⊗ CochainComplex.mappingCone (f.app Y) ⟶
      CochainComplex.mappingCone (f.app X) :=
  CochainComplex.mappingCone.lift (f.app X)
    (mappingConeActionFst A f X Y) (mappingConeActionSnd A f X Y)
    (mappingConeAction_condition A f X Y)

lemma mappingConeAction_fst {M N : RightModule (R := R) A} (f : M ⟶ N)
    (X Y : A) :
    (Cochain.ofHom (mappingConeAction A f X Y)).comp
        (CochainComplex.mappingCone.fst (f.app X)).1 (zero_add 1) =
      (TensorCochain.right (X ⟶[V] Y)
          (CochainComplex.mappingCone.fst (f.app Y)).1).comp
        (Cochain.ofHom (M.action X Y)) (add_zero 1) := by
  rw [mappingConeAction, CochainComplex.mappingCone.lift_fst]
  rfl

lemma mappingConeAction_snd {M N : RightModule (R := R) A} (f : M ⟶ N)
    (X Y : A) :
    (Cochain.ofHom (mappingConeAction A f X Y)).comp
        (CochainComplex.mappingCone.snd (f.app X)) (zero_add 0) =
      (TensorCochain.right (X ⟶[V] Y)
          (CochainComplex.mappingCone.snd (f.app Y))).comp
        (Cochain.ofHom (N.action X Y)) (add_zero 0) := by
  rw [mappingConeAction, CochainComplex.mappingCone.lift_snd]
  rfl

lemma tensor_mappingConeAction_fst {M N : RightModule (R := R) A} (f : M ⟶ N)
    (X Y Z : A) :
    (Cochain.ofHom ((X ⟶[V] Y) ◁ mappingConeAction A f Y Z)).comp
        (TensorCochain.right (X ⟶[V] Y)
          (CochainComplex.mappingCone.fst (f.app Y)).1) (zero_add 1) =
      (TensorCochain.right (X ⟶[V] Y)
          (TensorCochain.right (Y ⟶[V] Z)
            (CochainComplex.mappingCone.fst (f.app Z)).1)).comp
        (Cochain.ofHom ((X ⟶[V] Y) ◁ M.action Y Z)) (add_zero 1) := by
  rw [← TensorCochain.right_ofHom]
  rw [← TensorCochain.right_comp]
  rw [mappingConeAction_fst]
  rw [TensorCochain.right_comp]
  rw [TensorCochain.right_ofHom]

lemma tensor_mappingConeAction_snd {M N : RightModule (R := R) A} (f : M ⟶ N)
    (X Y Z : A) :
    (Cochain.ofHom ((X ⟶[V] Y) ◁ mappingConeAction A f Y Z)).comp
        (TensorCochain.right (X ⟶[V] Y)
          (CochainComplex.mappingCone.snd (f.app Y))) (zero_add 0) =
      (TensorCochain.right (X ⟶[V] Y)
          (TensorCochain.right (Y ⟶[V] Z)
            (CochainComplex.mappingCone.snd (f.app Z)))).comp
        (Cochain.ofHom ((X ⟶[V] Y) ◁ N.action Y Z)) (add_zero 0) := by
  rw [← TensorCochain.right_ofHom]
  rw [← TensorCochain.right_comp]
  rw [mappingConeAction_snd]
  rw [TensorCochain.right_comp]
  rw [TensorCochain.right_ofHom]

lemma action_id_tensorCochain_right_v (Q : RightModule (R := R) A) (X : A)
    {K : V} {n : ℤ} (γ : Cochain K (Q.obj X) n) (p q : ℤ) (hpq : p + n = q) :
    (λ_ K).inv.f p ≫ (eId V X ▷ K).f p ≫
        (TensorCochain.right (X ⟶[V] X) γ).v p q hpq ≫ (Q.action X X).f q =
      γ.v p q hpq := by
  have hnat := Cochain.congr_v
    (TensorCochain.right_naturality_left (eId V X) γ) p q hpq
  simp only [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q), Cochain.ofHom_v] at hnat
  have hunit := TensorCochain.leftUnitor_inv_right_v γ p q hpq
  have haction := congrArg (fun k ↦ k.f q) (Q.action_id X)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at haction
  slice_lhs 2 3 => rw [hnat]
  slice_lhs 1 2 => rw [hunit]
  slice_lhs 2 4 => rw [haction]
  simp

/-- Compatibility of a module action with composition, after applying a homogeneous
cochain in the module variable.  This is the componentwise identity used by the two
projections of an objectwise mapping cone. -/
lemma action_comp_tensorCochain_right_v (Q : RightModule (R := R) A) (X Y Z : A)
    {K : V} {n : ℤ} (γ : Cochain K (Q.obj Z) n)
    (p q : ℤ) (hpq : p + n = q) :
    (eComp V X Y Z ▷ K).f p ≫
        (TensorCochain.right (X ⟶[V] Z) γ).v p q hpq ≫
          (Q.action X Z).f q =
      (α_ (X ⟶[V] Y) (Y ⟶[V] Z) K).hom.f p ≫
        (TensorCochain.right (X ⟶[V] Y)
          (TensorCochain.right (Y ⟶[V] Z) γ)).v p q hpq ≫
            ((X ⟶[V] Y) ◁ Q.action Y Z).f q ≫
              (Q.action X Y).f q := by
  have hnat := Cochain.congr_v
    (TensorCochain.right_naturality_left (eComp V X Y Z) γ) p q hpq
  simp only [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q), Cochain.ofHom_v] at hnat
  have hassoc := Cochain.congr_v
    (TensorCochain.associator_hom_right (X ⟶[V] Y) (Y ⟶[V] Z) γ) p q hpq
  simp only [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q), Cochain.ofHom_v] at hassoc
  have haction := congrArg (fun k ↦ k.f q) (Q.action_comp X Y Z)
  simp only [HomologicalComplex.comp_f] at haction
  slice_lhs 1 2 => rw [hnat]
  simp only [Category.assoc]
  slice_lhs 2 4 => rw [haction]
  slice_lhs 1 2 => rw [← hassoc]
  simp only [Category.assoc]

lemma tensor_mappingCone_inr_fst (H : V) {K L : V} (g : K ⟶ L) :
    (Cochain.ofHom (H ◁ CochainComplex.mappingCone.inr g)).comp
        (TensorCochain.right H (CochainComplex.mappingCone.fst g).1) (zero_add 1) = 0 := by
  rw [← TensorCochain.right_ofHom]
  rw [← TensorCochain.right_comp]
  simp

lemma tensor_mappingCone_inr_snd (H : V) {K L : V} (g : K ⟶ L) :
    (Cochain.ofHom (H ◁ CochainComplex.mappingCone.inr g)).comp
        (TensorCochain.right H (CochainComplex.mappingCone.snd g)) (zero_add 0) =
      Cochain.ofHom (𝟙 (H ⊗ L)) := by
  rw [← TensorCochain.right_ofHom]
  rw [← TensorCochain.right_comp]
  simp [TensorCochain.right_ofHom]

/-- The mapping cone of a morphism of right DG modules, formed objectwise. -/
noncomputable def mappingCone {M N : RightModule (R := R) A} (f : M ⟶ N) :
    RightModule (R := R) A where
  obj X := CochainComplex.mappingCone (f.app X)
  action X Y := mappingConeAction A f X Y
  action_id X := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply CochainComplex.mappingCone.ext_to (f.app X) p (p + 1) rfl
    · simp only [HomologicalComplex.comp_f, mappingConeAction,
        HomologicalComplex.id_f, Category.id_comp, Category.assoc]
      slice_lhs 3 4 => rw [CochainComplex.mappingCone.lift_f_fst_v]
      simp only [mappingConeActionFst, Cocycle.postcomp_coe, tensorCocycleRight]
      exact action_id_tensorCochain_right_v A M X
        (CochainComplex.mappingCone.fst (f.app X)).1 p (p + 1) rfl
    · simp only [HomologicalComplex.comp_f, mappingConeAction,
        HomologicalComplex.id_f, Category.id_comp, Category.assoc]
      slice_lhs 3 4 => rw [CochainComplex.mappingCone.lift_f_snd_v]
      simp only [mappingConeActionSnd, Cochain.comp_zero_cochain_v,
        Cochain.ofHom_v]
      exact action_id_tensorCochain_right_v A N X
        (CochainComplex.mappingCone.snd (f.app X)) p p (add_zero p)
  action_comp X Y Z := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply CochainComplex.mappingCone.ext_to (f.app X) p (p + 1) rfl
    · simp only [HomologicalComplex.comp_f, Category.assoc]
      have hXZ := Cochain.congr_v (mappingConeAction_fst A f X Z) p (p + 1) rfl
      have hXY := Cochain.congr_v (mappingConeAction_fst A f X Y) p (p + 1) rfl
      have hcone := Cochain.congr_v
        (tensor_mappingConeAction_fst A f X Y Z) p (p + 1) rfl
      simp only [Cochain.comp_v _ _ (zero_add 1) p p (p + 1) (add_zero p) rfl,
        Cochain.comp_v _ _ (add_zero 1) p (p + 1) (p + 1) rfl (add_zero (p + 1)),
        Cochain.ofHom_v] at hXZ hXY hcone
      slice_lhs 2 3 => rw [hXZ]
      slice_rhs 3 4 => rw [hXY]
      slice_rhs 2 3 => rw [hcone]
      exact action_comp_tensorCochain_right_v A M X Y Z
        (CochainComplex.mappingCone.fst (f.app Z)).1 p (p + 1) rfl
    · simp only [HomologicalComplex.comp_f, Category.assoc]
      have hXZ := Cochain.congr_v (mappingConeAction_snd A f X Z) p p (add_zero p)
      have hXY := Cochain.congr_v (mappingConeAction_snd A f X Y) p p (add_zero p)
      have hcone := Cochain.congr_v
        (tensor_mappingConeAction_snd A f X Y Z) p p (add_zero p)
      simp only [Cochain.comp_v _ _ (zero_add 0) p p p (add_zero p) (add_zero p),
        Cochain.ofHom_v] at hXZ hXY hcone
      slice_lhs 2 3 => rw [hXZ]
      slice_rhs 3 4 => rw [hXY]
      slice_rhs 2 3 => rw [hcone]
      exact action_comp_tensorCochain_right_v A N X Y Z
        (CochainComplex.mappingCone.snd (f.app Z)) p p (add_zero p)

/-- The canonical inclusion into the objectwise mapping cone. -/
noncomputable def mappingConeInr {M N : RightModule (R := R) A} (f : M ⟶ N) :
    N ⟶ mappingCone A f where
  app X := CochainComplex.mappingCone.inr (f.app X)
  naturality X Y := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply CochainComplex.mappingCone.ext_to (f.app X) p (p + 1) rfl
    · simp only [HomologicalComplex.comp_f, mappingCone, Category.assoc]
      slice_lhs 2 3 => rw [CochainComplex.mappingCone.inr_f_fst_v]
      have hact := Cochain.congr_v (mappingConeAction_fst A f X Y) p (p + 1) rfl
      simp only [Cochain.comp_v _ _ (zero_add 1) p p (p + 1) (add_zero p) rfl,
        Cochain.comp_v _ _ (add_zero 1) p (p + 1) (p + 1) rfl (add_zero (p + 1)),
        Cochain.ofHom_v] at hact
      slice_rhs 2 3 => rw [hact]
      have h := Cochain.congr_v
        (tensor_mappingCone_inr_fst (X ⟶[V] Y) (f.app Y)) p (p + 1) rfl
      simp only [Cochain.comp_v _ _ (zero_add 1) p p (p + 1) (add_zero p) rfl,
        Cochain.ofHom_v, Cochain.zero_v] at h
      slice_rhs 1 2 => rw [h]
      simp
    · simp only [HomologicalComplex.comp_f, mappingCone, Category.assoc]
      slice_lhs 2 3 => rw [CochainComplex.mappingCone.inr_f_snd_v]
      simp only [Category.comp_id]
      have hact := Cochain.congr_v (mappingConeAction_snd A f X Y) p p (add_zero p)
      simp only [Cochain.comp_v _ _ (zero_add 0) p p p (add_zero p) (add_zero p),
        Cochain.ofHom_v] at hact
      slice_rhs 2 3 => rw [hact]
      have h := Cochain.congr_v
        (tensor_mappingCone_inr_snd (X ⟶[V] Y) (f.app Y)) p p (add_zero p)
      simp only [Cochain.comp_v _ _ (zero_add 0) p p p (add_zero p) (add_zero p),
        Cochain.ofHom_v, HomologicalComplex.id_f] at h
      slice_rhs 1 2 => rw [h]
      simp

end RightModule

end DGCategory
namespace DGCategory.RightModule

variable {R : Type w} [CommRing R]
variable (A : Type u) [DGCategory R A]

/-- A homotopy equivalence between right DG modules. -/
structure HomotopyEquiv (M N : RightModule (R := R) A) where
  /-- The forward module morphism. -/
  hom : M ⟶ N
  /-- The inverse module morphism up to homotopy. -/
  inv : N ⟶ M
  /-- The forward map followed by the inverse is homotopic to the identity. -/
  homotopyHomInvId : Homotopy A (hom ≫ inv) (𝟙 M)
  /-- The inverse followed by the forward map is homotopic to the identity. -/
  homotopyInvHomId : Homotopy A (inv ≫ hom) (𝟙 N)

end DGCategory.RightModule

namespace DGCategory.RightModule.HomotopyCategory

open ZeroObject

variable {R : Type w} [CommRing R]
variable (A : Type u) [DGCategory R A]

instance : (quotient (R := R) A).Full :=
  inferInstanceAs
    ((CategoryTheory.Quotient.functor (homotopic (R := R) A)).Full)

instance : (quotient (R := R) A).EssSurj :=
  inferInstanceAs
    ((CategoryTheory.Quotient.functor (homotopic (R := R) A)).EssSurj)

variable {A}

@[simp]
lemma quotient_map_out {M N : HomotopyCategory (R := R) A} (f : M ⟶ N) :
    (quotient (R := R) A).map f.out = f :=
  Quot.out_eq _

/-- An action-compatible module homotopy gives equality in the homotopy category. -/
lemma eq_of_homotopy {M N : RightModule (R := R) A} (f g : M ⟶ N)
    (h : Homotopy A f g) :
    (quotient (R := R) A).map f = (quotient (R := R) A).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- Equality of images in the quotient determines an action-compatible module homotopy. -/
noncomputable def homotopyOfEq {M N : RightModule (R := R) A} (f g : M ⟶ N)
    (h : (quotient (R := R) A).map f = (quotient (R := R) A).map g) :
    Homotopy A f g :=
  ((quotient_map_eq_iff (R := R) A f g).mp h).some

/-- Homotopy equivalent right DG modules become isomorphic in the homotopy category. -/
noncomputable def isoOfHomotopyEquiv {M N : RightModule (R := R) A}
    (e : RightModule.HomotopyEquiv A M N) :
    (quotient (R := R) A).obj M ≅ (quotient (R := R) A).obj N where
  hom := (quotient (R := R) A).map e.hom
  inv := (quotient (R := R) A).map e.inv
  hom_inv_id := by
    rw [← (quotient (R := R) A).map_comp, ← (quotient (R := R) A).map_id]
    exact eq_of_homotopy _ _ e.homotopyHomInvId
  inv_hom_id := by
    rw [← (quotient (R := R) A).map_comp, ← (quotient (R := R) A).map_id]
    exact eq_of_homotopy _ _ e.homotopyInvHomId

/-- A quotient object represented by a contractible right DG module is zero. -/
lemma isZero_quotient_obj_iff (M : RightModule (R := R) A) :
    IsZero ((quotient (R := R) A).obj M) ↔ Nonempty (Homotopy A (𝟙 M) 0) := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    exact ⟨homotopyOfEq _ _ (by simpa using h)⟩
  · rintro ⟨h⟩
    simpa using eq_of_homotopy _ _ h

instance [HasZeroObject (RightModule (R := R) A)] :
    HasZeroObject (HomotopyCategory (R := R) A) :=
  ⟨(quotient (R := R) A).obj 0, by
    rw [IsZero.iff_id_eq_zero, ← (quotient (R := R) A).map_id, id_zero,
      Functor.map_zero]⟩

end DGCategory.RightModule.HomotopyCategory

open MonoidalCategory
open CochainComplex.HomComplex

namespace CochainComplex.HomComplex.Cochain

variable {R : Type w} [CommRing R]
local notation "V" => CochainComplex (ModuleCat R) ℤ

/-- Simultaneously shifting source and target commutes with composition of homogeneous
cochains. -/
lemma shift_comp {K L M : V} {a b c : ℤ} (γ : Cochain K L a)
    (η : Cochain L M b) (hab : a + b = c) (n : ℤ) :
    (γ.comp η hab).shift n = (γ.shift n).comp (η.shift n) hab := by
  apply Cochain.ext
  intro p q hpq
  rw [Cochain.shift_v' (γ.comp η hab) n p q hpq]
  rw [Cochain.comp_v γ η hab (p + n) (p + a + n) (q + n)
    (by omega) (by omega)]
  rw [Cochain.comp_v (γ.shift n) (η.shift n) hab p (p + a) q rfl (by omega)]
  rw [Cochain.shift_v' γ n p (p + a) rfl]
  rw [Cochain.shift_v' η n (p + a) q (by omega)]
  rfl

/-- The degree-zero cochain of a shifted cochain map is its simultaneously shifted cochain. -/
lemma ofHom_shift {K L : V} (f : K ⟶ L) (n : ℤ) :
    Cochain.ofHom (f⟦n⟧') = (Cochain.ofHom f).shift n := by
  apply Cochain.ext
  intro p q hpq
  rw [Cochain.shift_v' (Cochain.ofHom f) n p q hpq]
  subst q
  rfl

end CochainComplex.HomComplex.Cochain

namespace DGCategory.RightModule

variable {R : Type w} [CommRing R]
variable (A : Type u) [DGCategory R A]
local notation "V" => CochainComplex (ModuleCat R) ℤ

/-- The degree-zero cochain of the direct shifted action, expressed through the signed
tensor-shift comparison. -/
lemma cochain_ofHom_shiftAction (M : RightModule (R := R) A) (n : ℤ) (X Y : A) :
    Cochain.ofHom (shiftAction A M n X Y) =
      (Cochain.ofHom (CochainComplex.mapBifunctorShift₂Iso (X ⟶[V] Y) (M.obj Y)
        (curriedTensor (ModuleCat R)) n).hom).comp
          ((Cochain.ofHom (M.action X Y)).shift n) (zero_add 0) := by
  rw [← Cochain.ofHom_shift]
  rw [← Cochain.ofHom_comp]
  rfl

/-- A module homotopy is a degree-minus-one graded module-natural transformation. -/
def gradedHomOfHomotopy {M N : RightModule (R := R) A} {f g : M ⟶ N}
    (h : Homotopy A f g) : GradedHom A M N (-1) where
  app X := Cochain.ofHomotopy (h.app X)
  naturality X Y := by
    rw [← cochain_ofHomotopy_compLeft]
    rw [tensorCochain_right_ofHomotopy]
    rw [← cochain_ofHomotopy_compRight]
    apply Cochain.ext
    intro p q hpq
    simpa only [Cochain.ofHomotopy, Cochain.mk_v] using h.naturality X Y p q

/-- Simultaneous shift of a graded module-natural transformation.  The hypotheses identify
the transported module actions with their direct signed formulas. -/
def GradedHom.shift {M N : RightModule (R := R) A} {d : ℤ}
    (η : GradedHom A M N d) (n : ℤ)
    (hM : ∀ X Y, (shift A M n).action X Y = shiftAction A M n X Y)
    (hN : ∀ X Y, (shift A N n).action X Y = shiftAction A N n X Y) :
    GradedHom A (shift A M n) (shift A N n) d where
  app X := (η.app X).shift n
  naturality X Y := by
    rw [hM X Y, hN X Y]
    change
      ((Cochain.ofHom (shiftAction A M n X Y) :
          Cochain ((X ⟶[V] Y) ⊗ (CategoryTheory.shiftFunctor V n).obj (M.obj Y))
            ((CategoryTheory.shiftFunctor V n).obj (M.obj X)) 0).comp
        ((η.app X).shift n) (zero_add d)) =
      ((TensorCochain.right (X ⟶[V] Y) ((η.app Y).shift n)).comp
        (Cochain.ofHom (shiftAction A N n X Y) :
          Cochain ((X ⟶[V] Y) ⊗ (CategoryTheory.shiftFunctor V n).obj (N.obj Y))
            ((CategoryTheory.shiftFunctor V n).obj (N.obj X)) 0)
        (add_zero d))
    rw [cochain_ofHom_shiftAction, cochain_ofHom_shiftAction]
    rw [Cochain.comp_assoc_of_first_is_zero_cochain]
    rw [← Cochain.shift_comp (Cochain.ofHom (M.action X Y))
      (η.app X) (zero_add d) n]
    rw [η.naturality X Y]
    rw [Cochain.shift_comp (TensorCochain.right (X ⟶[V] Y) (η.app Y))
      (Cochain.ofHom (N.action X Y)) (add_zero d) n]
    rw [← Cochain.comp_assoc_of_third_is_zero_cochain]
    rw [DGCategory.TensorCochain.right_shift_comm]
    rw [Cochain.comp_assoc_of_second_is_zero_cochain]

/-- The signed shifted cochain associated to a homotopy has the boundary of the shifted
endpoints. -/
lemma shiftHomotopyCochain_condition {K L : V} {f g : K ⟶ L}
    (h : _root_.Homotopy f g) (n : ℤ) :
    Cochain.ofHom (f⟦n⟧') =
      δ (-1) 0 (n.negOnePow • (Cochain.ofHomotopy h).shift n) +
        Cochain.ofHom (g⟦n⟧') := by
  rw [δ_units_smul, Cochain.δ_shift, δ_ofHomotopy]
  simp only [smul_smul, Int.units_mul_self, one_smul, sub_eq_add_neg,
    Cochain.shift_add, Cochain.shift_neg, ← Cochain.ofHom_shift]
  abel

/-- The signed degree-minus-one graded transformation obtained by shifting a module homotopy. -/
def shiftedGradedHom {M N : RightModule (R := R) A} {f g : M ⟶ N}
    (h : Homotopy A f g) (n : ℤ)
    (hM : ∀ X Y, (shift A M n).action X Y = shiftAction A M n X Y)
    (hN : ∀ X Y, (shift A N n).action X Y = shiftAction A N n X Y) :
    GradedHom A (shift A M n) (shift A N n) (-1) :=
  n.negOnePow • GradedHom.shift A (gradedHomOfHomotopy A h) n hM hN

set_option backward.isDefEq.respectTransparency false in
/-- The component homotopy determined by the shifted graded transformation. -/
noncomputable def shiftHomotopyApp {M N : RightModule (R := R) A} {f g : M ⟶ N}
    (h : Homotopy A f g) (n : ℤ)
    (hM : ∀ X Y, (shift A M n).action X Y = shiftAction A M n X Y)
    (hN : ∀ X Y, (shift A N n).action X Y = shiftAction A N n X Y) (X : A) :
    _root_.Homotopy ((shiftMap A f n).app X) ((shiftMap A g n).app X) := by
  have happ :
      (shiftedGradedHom A h n hM hN).app X =
        n.negOnePow • (Cochain.ofHomotopy (h.app X)).shift n := rfl
  exact (Cochain.equivHomotopy
    ((shiftMap A f n).app X) ((shiftMap A g n).app X)).symm
      ⟨(shiftedGradedHom A h n hM hN).app X, by
        rw [happ]
        simpa only [shiftMap_app] using
          shiftHomotopyCochain_condition (h.app X) n⟩

set_option backward.isDefEq.respectTransparency false in
lemma cochain_ofHomotopy_shiftHomotopyApp
    {M N : RightModule (R := R) A} {f g : M ⟶ N}
    (h : Homotopy A f g) (n : ℤ)
    (hM : ∀ X Y, (shift A M n).action X Y = shiftAction A M n X Y)
    (hN : ∀ X Y, (shift A N n).action X Y = shiftAction A N n X Y) (X : A) :
    Cochain.ofHomotopy (shiftHomotopyApp A h n hM hN X) =
      (shiftedGradedHom A h n hM hN).app X := by
  have happ :
      (shiftedGradedHom A h n hM hN).app X =
        n.negOnePow • (Cochain.ofHomotopy (h.app X)).shift n := rfl
  exact congrArg Subtype.val (Equiv.apply_symm_apply
    (Cochain.equivHomotopy ((shiftMap A f n).app X) ((shiftMap A g n).app X))
      ⟨(shiftedGradedHom A h n hM hN).app X, by
        rw [happ]
        simpa only [shiftMap_app] using
          shiftHomotopyCochain_condition (h.app X) n⟩)

/-- Objectwise shifting preserves action-compatible homotopies, provided the transported
module action has been identified with its direct signed formula. -/
noncomputable def Homotopy.shift {M N : RightModule (R := R) A} {f g : M ⟶ N}
    (h : Homotopy A f g) (n : ℤ)
    (hM : ∀ X Y, (shift A M n).action X Y = shiftAction A M n X Y)
    (hN : ∀ X Y, (shift A N n).action X Y = shiftAction A N n X Y) :
    Homotopy A (shiftMap A f n) (shiftMap A g n) where
  app X := shiftHomotopyApp A h n hM hN X
  naturality X Y p q := by
    let η := shiftedGradedHom A h n hM hN
    by_cases hpq : p + (-1) = q
    · have hη := η.naturality X Y
      rw [← cochain_ofHomotopy_shiftHomotopyApp A h n hM hN X] at hη
      rw [← cochain_ofHomotopy_shiftHomotopyApp A h n hM hN Y] at hη
      rw [← cochain_ofHomotopy_compLeft] at hη
      rw [tensorCochain_right_ofHomotopy] at hη
      rw [← cochain_ofHomotopy_compRight] at hη
      have hv := Cochain.congr_v hη p q hpq
      simpa only [Cochain.ofHomotopy, Cochain.mk_v] using hv
    · have hrel : ¬(ComplexShape.up ℤ).Rel q p := by
        intro hrel
        apply hpq
        simp only [ComplexShape.up_Rel] at hrel ⊢
        omega
      rw [((shiftHomotopyApp A h n hM hN X).compLeft
          ((RightModule.shift A M n).action X Y)).zero p q hrel]
      rw [((HomologicalComplex.mapBifunctorMapHomotopy₂
        (𝟙 (X ⟶[V] Y)) (shiftHomotopyApp A h n hM hN Y)
          (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).compRight
            ((RightModule.shift A N n).action X Y)).zero p q hrel]

end DGCategory.RightModule

-- The module, enrichment, operations, and quotient machinery are kept together deliberately:
-- they form one support layer for the pretriangulated hull.
set_option linter.style.longFile 3500
