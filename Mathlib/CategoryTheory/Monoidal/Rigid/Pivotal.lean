/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Pivotal monoidal categories

A pivotal category is a rigid monoidal category equipped with a monoidal natural isomorphism
from the double right dual functor (`X ↦ Xᘁᘁ`) to the identity functor.

## Main definitions

* `pivotalExactPairing X`: an exact pairing between `Xᘁ` and `X` in a pivotal category.
* `leftDualIsoRightDual X`: an isomorphism `ᘁX ≅ Xᘁ` in a pivotal category.
* `leftDualFunctorIsoRightDualFunctor`: a natural isomorphism between the left and
  right dual functors in a pivotal category.

## Tags

rigid category, monoidal category, pivotal category

-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

section

namespace CategoryTheory

open Functor.LaxMonoidal

/-- A pivotal category is a rigid monoidal category equipped with a monoidal natural
isomorphism from the double right dual functor to the identity functor. -/
class PivotalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    extends RigidCategory C where
  /-- A natural isomorphism from the double right dual to the identity. -/
  pivotalIso : doubleRightDualFunctor C ≅ 𝟭 C
  pivotalIso_isMonoidal : NatTrans.IsMonoidal pivotalIso.hom

attribute [instance] PivotalCategory.pivotalIso_isMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [PivotalCategory C]

/-- The chosen natural isomorphism from the double right dual to the identity. -/
abbrev pivotalIso : doubleRightDualFunctor C ≅ 𝟭 C :=
  PivotalCategory.pivotalIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma rightAdjointMate_rightAdjointMate {X Y : C} (f : X ⟶ Y) :
    (fᘁ)ᘁ = (pivotalIso.app X).hom ≫ f ≫ (pivotalIso.app Y).inv := by
  rw [← cancel_mono (pivotalIso.app Y).hom]
  erw [pivotalIso.hom.naturality]
  simp

/-
lemma pivotalIso_unit :
    ε (doubleRightDualFunctor C) ≫ (pivotalIso.app (𝟙_ C)).hom = 𝟙 (𝟙_ C) :=
  NatTrans.IsMonoidal.unit

@[reassoc]
lemma pivotalIso_tensor (X Y : C) :
    μ (doubleRightDualFunctor C) X Y ≫ (pivotalIso.app (X ⊗ Y)).hom =
      (pivotalIso.app X).hom ⊗ₘ (pivotalIso.app Y).hom := by
  have h := NatTrans.IsMonoidal.tensor X Y (τ := pivotalIso.hom)
  rwa [Functor.LaxMonoidal.id_μ, Category.comp_id] at h

@[simp]
lemma pivotalIso_inv_unit :
    (pivotalIso.app (𝟙_ C)).inv = ε (doubleRightDualFunctor C) := by
  have h := NatTrans.IsMonoidal.unit (τ := (pivotalIso (C := C)).inv)
  rwa [Functor.LaxMonoidal.id_ε, Category.id_comp] at h

@[reassoc]
lemma pivotalIso_inv_tensor (X Y : C) :
    (pivotalIso.app (X ⊗ Y)).inv =
      ((pivotalIso.app X).inv ⊗ₘ (pivotalIso.app Y).inv) ≫ μ (doubleRightDualFunctor C) X Y := by
  have h := NatTrans.IsMonoidal.tensor X Y (τ := pivotalIso.inv)
  rwa [Functor.LaxMonoidal.id_μ, Category.id_comp] at h
-/

/-- In a pivotal category, `X` is a left dual of its right dual `Xᘁ`. -/
@[implicit_reducible]
def pivotalExactPairing (X : C) : ExactPairing Xᘁ X :=
  let : ExactPairing Xᘁ ((doubleRightDualFunctor C).obj X) := HasRightDual.exact
  exactPairingCongrRight (pivotalIso.symm.app X)

@[simp]
lemma pivotalExactPairing_coevaluation (X : C) :
    letI := pivotalExactPairing X
    η_ Xᘁ X = η_ Xᘁ Xᘁᘁ ≫ Xᘁ ◁ (pivotalIso.app X).hom := rfl

@[simp]
lemma pivotalExactPairing_evaluation (X : C) :
    letI := pivotalExactPairing X
    ε_ Xᘁ X = (pivotalIso.app X).inv ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ := rfl

/-- In a pivotal category, left and right duals are canonically isomorphic. -/
def leftDualIsoRightDual (X : C) : (ᘁX) ≅ Xᘁ :=
  leftDualIso HasLeftDual.exact (pivotalExactPairing X)

private lemma leftAdjointMate_rightAdjointMate {X Y : C} (f : X ⟶ Y) :
    leftAdjointMate (rightAdjointMate f) = f := by
  rw [← cancel_mono (ρ_ Y).inv]
  have h : _ ≫ ε_ Y Yᘁ = _ :=
    (leftAdjointMate_comp_evaluation (fᘁ)).trans (rightAdjointMate_comp_evaluation f)
  simpa only [tensorLeftHomEquiv_whiskerLeft_comp_evaluation_of_exactPairing] using
    congrArg (tensorLeftHomEquiv X Y (Yᘁ) (𝟙_ C)) h

private lemma pivotalLeftAdjointMate {X Y : C} (f : X ⟶ Y) :
    letI : HasLeftDual X := { leftDual := Xᘁ, exact := pivotalExactPairing X }
    letI : HasLeftDual Y := { leftDual := Yᘁ, exact := pivotalExactPairing Y }
  leftAdjointMate f = fᘁ := by
  rw [← leftAdjointMate_rightAdjointMate (fᘁ), rightAdjointMate_rightAdjointMate]
  dsimp only [leftAdjointMate]
  rw [pivotalExactPairing_coevaluation, pivotalExactPairing_evaluation]
  monoidal

@[reassoc]
lemma leftDualIsoRightDual_hom_naturality {X Y : C} (f : X ⟶ Y) :
    (ᘁf) ≫ (leftDualIsoRightDual X).hom = (leftDualIsoRightDual Y).hom ≫ fᘁ := by
  letI : HasLeftDual X := { leftDual := Xᘁ, exact := pivotalExactPairing X }
  letI : HasLeftDual Y := { leftDual := Yᘁ, exact := pivotalExactPairing Y }
  dsimp only [leftDualIsoRightDual, leftDualIso]
  rw [← @comp_leftAdjointMate C _ _ X X Y _
    (LeftRigidCategory.leftDual X) (LeftRigidCategory.leftDual Y) (𝟙 X) f]
  rw [← pivotalLeftAdjointMate f,
    ← @comp_leftAdjointMate C _ _ X Y Y _ _ (LeftRigidCategory.leftDual Y) f (𝟙 Y)]
  simp

@[reassoc]
lemma leftDualIsoRightDual_inv_naturality {X Y : C} (f : X ⟶ Y) :
    (leftDualIsoRightDual Y).inv ≫ (ᘁf) =
      fᘁ ≫ (leftDualIsoRightDual X).inv := by
  simp [← cancel_mono (leftDualIsoRightDual X).hom, leftDualIsoRightDual_hom_naturality]

/-- The left and right dual functors are isomorphic. -/
@[simps! hom_app inv_app]
def dualFunctorIso :
    leftDualFunctor C ≅ rightDualFunctor C :=
  NatIso.ofComponents
    (fun X ↦ (leftDualIsoRightDual X).symm.op.mop)
    (fun f ↦ by
      apply MonoidalOpposite.hom_ext
      apply Quiver.Hom.unop_inj
      exact leftDualIsoRightDual_inv_naturality f)

end CategoryTheory
