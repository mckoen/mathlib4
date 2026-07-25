/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# Dual Functors for Rigid Categories

This file defines the left and right dual functors from a rigid monoidal category
to `(Cᵒᵖ)ᴹᵒᵖ` (the monoidal opposite of the opposite category).

## Main definitions

* `leftDualFunctor C`: For a left rigid category, the functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` sending
  `X` to `ᘁX` and `f` to `ᘁf`.
* `rightDualFunctor C`: For a right rigid category, the functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` sending
  `X` to `Xᘁ` and `f` to `fᘁ`.
* `doubleRightDualFunctor C`: The double-right-dual endofunctor on a right rigid category.

## Future work

* Show that in a `RigidCategory`, these functors are monoidal equivalences.
-/

namespace CategoryTheory

open Category MonoidalCategory MonoidalOpposite Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

section LeftRigid

variable [LeftRigidCategory C]

/-- The left dual functor from `C` to `(Cᵒᵖ)ᴹᵒᵖ`. -/
@[simps obj map, expose]
public def leftDualFunctor : C ⥤ (Cᵒᵖ)ᴹᵒᵖ where
  obj X := mop (op (ᘁX))
  map f := (ᘁf).op.mop
  map_id X := by simp [leftAdjointMate_id]
  map_comp f g := by simp [comp_leftAdjointMate]

end LeftRigid

section RightRigid

variable [RightRigidCategory C]

/-- The right dual functor from `C` to `(Cᵒᵖ)ᴹᵒᵖ`. -/
@[simps obj map, expose]
public def rightDualFunctor : C ⥤ (Cᵒᵖ)ᴹᵒᵖ where
  obj X := mop (op (Xᘁ))
  map f := (fᘁ).op.mop
  map_id X := by simp [rightAdjointMate_id]
  map_comp f g := by simp [comp_rightAdjointMate]

omit [RightRigidCategory C] in
private theorem rightAdjointMate_associator (X Y Z : C)
    [HasRightDual X] [HasRightDual Y] [HasRightDual Z] :
    @rightAdjointMate C _ _ ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))
      (@hasRightDualTensor C _ _ (X ⊗ Y) Z
        (@hasRightDualTensor C _ _ X Y _ _) _)
      (@hasRightDualTensor C _ _ X (Y ⊗ Z) _
        (@hasRightDualTensor C _ _ Y Z _ _))
      (α_ X Y Z).hom =
        (α_ (Zᘁ : C) (Yᘁ : C) (Xᘁ : C)).hom := by
  let hXY : HasRightDual (X ⊗ Y) := hasRightDualTensor
  let hYZ : HasRightDual (Y ⊗ Z) := hasRightDualTensor
  let hL : HasRightDual ((X ⊗ Y) ⊗ Z) := {
    rightDual := Zᘁ ⊗ (Yᘁ ⊗ Xᘁ)
    exact := ExactPairing.tensor}
  let hR : HasRightDual (X ⊗ (Y ⊗ Z)) := {
    rightDual := (Zᘁ ⊗ Yᘁ) ⊗ Xᘁ
    exact := ExactPairing.tensor}
  symm
  apply (@eq_rightAdjointMate_iff C _ _ _ _ hL hR _ _).2
  dsimp only [hL, hR, hXY, hYZ, HasRightDual.rightDual, HasRightDual.exact]
  have evalL := @ExactPairing.tensor_evaluation C _ _ (X ⊗ Y) Z
    (Yᘁ ⊗ Xᘁ) (Zᘁ) hXY.exact HasRightDual.exact
  have evalR := @ExactPairing.tensor_evaluation C _ _ X (Y ⊗ Z)
    (Xᘁ) (Zᘁ ⊗ Yᘁ) HasRightDual.exact hYZ.exact
  rw [evalL, evalR]
  rw [@ExactPairing.tensor_evaluation C _ _ X Y (Xᘁ) (Yᘁ) _ _,
    @ExactPairing.tensor_evaluation C _ _ Y Z (Yᘁ) (Zᘁ) _ _]
  monoidal

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightAdjointMate_leftUnitor (X : C) [HasRightDual X] :
    @rightAdjointMate C _ _ (𝟙_ C ⊗ X) X
      (@hasRightDualTensor C _ _ (𝟙_ C) X _ _) _
      (λ_ X).hom = (ρ_ Xᘁ).inv := by
  let hI : HasRightDual (𝟙_ C) := {
    rightDual := 𝟙_ C
    exact := exactPairingUnit }
  let hIX : HasRightDual (𝟙_ C ⊗ X) := {
    rightDual := Xᘁ ⊗ 𝟙_ C
    exact := @ExactPairing.tensor C _ _ (𝟙_ C) X (𝟙_ C) (Xᘁ) hI.exact _ }
  change @rightAdjointMate C _ _ (𝟙_ C ⊗ X) X hIX _ (λ_ X).hom =
    (ρ_ Xᘁ).inv
  symm
  refine (@eq_rightAdjointMate_iff C _ _ (𝟙_ C ⊗ X) X hIX _
    (λ_ X).hom (ρ_ Xᘁ).inv).2 ?_
  dsimp only [hIX, hI, HasRightDual.rightDual, HasRightDual.exact]
  have evalIX := @ExactPairing.tensor_evaluation C _ _ (𝟙_ C) X
    (𝟙_ C) (Xᘁ) hI.exact HasRightDual.exact
  have evalI :
      @ExactPairing.evaluation C _ _ (𝟙_ C) (𝟙_ C) exactPairingUnit =
        (ρ_ (𝟙_ C)).hom := rfl
  rw [evalIX, evalI]
  monoidal

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightAdjointMate_rightUnitor (X : C) [HasRightDual X] :
    @rightAdjointMate C _ _ (X ⊗ 𝟙_ C) X
      (@hasRightDualTensor C _ _ X (𝟙_ C) _ _) _
      (ρ_ X).hom = (λ_ Xᘁ).inv := by
  let hI : HasRightDual (𝟙_ C) := {
    rightDual := 𝟙_ C
    exact := exactPairingUnit }
  let hXI : HasRightDual (X ⊗ 𝟙_ C) := {
    rightDual := 𝟙_ C ⊗ Xᘁ
    exact := @ExactPairing.tensor C _ _ X (𝟙_ C) (Xᘁ) (𝟙_ C) _ hI.exact }
  change @rightAdjointMate C _ _ (X ⊗ 𝟙_ C) X hXI _ (ρ_ X).hom =
    (λ_ Xᘁ).inv
  symm
  refine (@eq_rightAdjointMate_iff C _ _ (X ⊗ 𝟙_ C) X hXI _
    (ρ_ X).hom (λ_ Xᘁ).inv).2 ?_
  dsimp only [hXI, hI, HasRightDual.rightDual, HasRightDual.exact]
  have evalXI := @ExactPairing.tensor_evaluation C _ _ X (𝟙_ C)
    (Xᘁ) (𝟙_ C) HasRightDual.exact hI.exact
  have evalI :
      @ExactPairing.evaluation C _ _ (𝟙_ C) (𝟙_ C) exactPairingUnit =
        (ρ_ (𝟙_ C)).hom := rfl
  rw [evalXI, evalI]
  monoidal

omit [RightRigidCategory C] in
private theorem rightDualIso_hom_trans {X Y₁ Y₂ Y₃ : C}
    (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) (p₃ : ExactPairing X Y₃) :
    (rightDualIso p₁ p₂).hom ≫ (rightDualIso p₂ p₃).hom =
      (rightDualIso p₁ p₃).hom := by
  change
    @rightAdjointMate C _ _ X X
        ({ rightDual := Y₂, exact := p₂ } : HasRightDual X)
        ({ rightDual := Y₁, exact := p₁ } : HasRightDual X) (𝟙 X) ≫
      @rightAdjointMate C _ _ X X
        ({ rightDual := Y₃, exact := p₃ } : HasRightDual X)
        ({ rightDual := Y₂, exact := p₂ } : HasRightDual X) (𝟙 X) =
      @rightAdjointMate C _ _ X X
        ({ rightDual := Y₃, exact := p₃ } : HasRightDual X)
        ({ rightDual := Y₁, exact := p₁ } : HasRightDual X) (𝟙 X)
  rw [← @comp_rightAdjointMate C _ _ X X X
    ({ rightDual := Y₃, exact := p₃ } : HasRightDual X)
    ({ rightDual := Y₂, exact := p₂ } : HasRightDual X)
    ({ rightDual := Y₁, exact := p₁ } : HasRightDual X)]
  simp

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightDualIso_tensor {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    (p₁ : ExactPairing X₁ Y₁) (p₂ : ExactPairing X₂ Y₂)
    (q₁ : ExactPairing X₁ Z₁) (q₂ : ExactPairing X₂ Z₂) :
    (rightDualIso
      (@ExactPairing.tensor C _ _ X₁ X₂ Y₁ Y₂ p₁ p₂)
      (@ExactPairing.tensor C _ _ X₁ X₂ Z₁ Z₂ q₁ q₂)).hom =
        (rightDualIso p₂ q₂).hom ⊗ₘ (rightDualIso p₁ q₁).hom := by
  change
    @rightAdjointMate C _ _ (X₁ ⊗ X₂) (X₁ ⊗ X₂)
      (@hasRightDualTensor C _ _ X₁ X₂
        ({ rightDual := Z₁, exact := q₁ } : HasRightDual X₁)
        ({ rightDual := Z₂, exact := q₂ } : HasRightDual X₂))
      (@hasRightDualTensor C _ _ X₁ X₂
        ({ rightDual := Y₁, exact := p₁ } : HasRightDual X₁)
        ({ rightDual := Y₂, exact := p₂ } : HasRightDual X₂))
      (𝟙 (X₁ ⊗ X₂)) =
        (@rightAdjointMate C _ _ X₂ X₂
          ({ rightDual := Z₂, exact := q₂ } : HasRightDual X₂)
          ({ rightDual := Y₂, exact := p₂ } : HasRightDual X₂) (𝟙 X₂)) ⊗ₘ
        (@rightAdjointMate C _ _ X₁ X₁
          ({ rightDual := Z₁, exact := q₁ } : HasRightDual X₁)
          ({ rightDual := Y₁, exact := p₁ } : HasRightDual X₁) (𝟙 X₁))
  simpa using
    (@rightAdjointMate_tensor C _ _ X₁ X₂ X₁ X₂
      ({ rightDual := Z₁, exact := q₁ } : HasRightDual X₁)
      ({ rightDual := Z₂, exact := q₂ } : HasRightDual X₂)
      ({ rightDual := Y₁, exact := p₁ } : HasRightDual X₁)
      ({ rightDual := Y₂, exact := p₂ } : HasRightDual X₂)
      (𝟙 X₁) (𝟙 X₂))

omit [RightRigidCategory C] in
private theorem rightAdjointMate_naturality {X Y A₁ A₂ B₁ B₂ : C}
    (pX₁ : ExactPairing X A₁) (pX₂ : ExactPairing X A₂)
    (pY₁ : ExactPairing Y B₁) (pY₂ : ExactPairing Y B₂)
    (f : X ⟶ Y) :
    @rightAdjointMate C _ _ X Y
        ({ rightDual := A₁, exact := pX₁ } : HasRightDual X)
        ({ rightDual := B₁, exact := pY₁ } : HasRightDual Y) f ≫
      (rightDualIso pX₁ pX₂).hom =
    (rightDualIso pY₁ pY₂).hom ≫
      @rightAdjointMate C _ _ X Y
        ({ rightDual := A₂, exact := pX₂ } : HasRightDual X)
        ({ rightDual := B₂, exact := pY₂ } : HasRightDual Y) f := by
  dsimp only [rightDualIso]
  calc
    _ = @rightAdjointMate C _ _ X Y
        ({ rightDual := A₂, exact := pX₂ } : HasRightDual X)
        ({ rightDual := B₁, exact := pY₁ } : HasRightDual Y)
        (𝟙 X ≫ f) :=
      (@comp_rightAdjointMate C _ _ X X Y
        ({ rightDual := A₂, exact := pX₂ } : HasRightDual X)
        ({ rightDual := A₁, exact := pX₁ } : HasRightDual X)
        ({ rightDual := B₁, exact := pY₁ } : HasRightDual Y)).symm
    _ = @rightAdjointMate C _ _ X Y
        ({ rightDual := A₂, exact := pX₂ } : HasRightDual X)
        ({ rightDual := B₁, exact := pY₁ } : HasRightDual Y)
        (f ≫ 𝟙 Y) := by simp
    _ = _ :=
      @comp_rightAdjointMate C _ _ X Y Y
        ({ rightDual := A₂, exact := pX₂ } : HasRightDual X)
        ({ rightDual := B₂, exact := pY₂ } : HasRightDual Y)
        ({ rightDual := B₁, exact := pY₁ } : HasRightDual Y)
        f (𝟙 Y)

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightDualTensorIso_associativity (X Y Z : C)
    [HasRightDual X] [HasRightDual Y] [HasRightDual Z]
    [HasRightDual (X ⊗ Y)] [HasRightDual (Y ⊗ Z)]
    [HasRightDual ((X ⊗ Y) ⊗ Z)] [HasRightDual (X ⊗ (Y ⊗ Z))] :
    (α_ X Y Z).homᘁ ≫ (rightDualTensorIso (X ⊗ Y) Z).hom ≫
        (Zᘁ : C) ◁ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso X (Y ⊗ Z)).hom ≫
        (rightDualTensorIso Y Z).hom ▷ Xᘁ ≫
          (α_ (Zᘁ : C) (Yᘁ : C) (Xᘁ : C)).hom := by
  let pX : ExactPairing X (Xᘁ) := HasRightDual.exact
  let pY : ExactPairing Y (Yᘁ) := HasRightDual.exact
  let pZ : ExactPairing Z (Zᘁ) := HasRightDual.exact
  let pXY : ExactPairing (X ⊗ Y) ((X ⊗ Y)ᘁ) := HasRightDual.exact
  let pYZ : ExactPairing (Y ⊗ Z) ((Y ⊗ Z)ᘁ) := HasRightDual.exact
  let pA : ExactPairing ((X ⊗ Y) ⊗ Z) (((X ⊗ Y) ⊗ Z)ᘁ) := HasRightDual.exact
  let pB : ExactPairing (X ⊗ (Y ⊗ Z)) ((X ⊗ (Y ⊗ Z))ᘁ) := HasRightDual.exact
  let pXYT : ExactPairing (X ⊗ Y) (Yᘁ ⊗ Xᘁ) :=
    @ExactPairing.tensor C _ _ X Y (Xᘁ) (Yᘁ) pX pY
  let pYZT : ExactPairing (Y ⊗ Z) (Zᘁ ⊗ Yᘁ) :=
    @ExactPairing.tensor C _ _ Y Z (Yᘁ) (Zᘁ) pY pZ
  let pAL₁ : ExactPairing ((X ⊗ Y) ⊗ Z) (Zᘁ ⊗ (X ⊗ Y)ᘁ) :=
    @ExactPairing.tensor C _ _ (X ⊗ Y) Z ((X ⊗ Y)ᘁ) (Zᘁ) pXY pZ
  let pAL₂ : ExactPairing ((X ⊗ Y) ⊗ Z) (Zᘁ ⊗ (Yᘁ ⊗ Xᘁ)) :=
    @ExactPairing.tensor C _ _ (X ⊗ Y) Z (Yᘁ ⊗ Xᘁ) (Zᘁ) pXYT pZ
  let pBR₁ : ExactPairing (X ⊗ (Y ⊗ Z)) ((Y ⊗ Z)ᘁ ⊗ Xᘁ) :=
    @ExactPairing.tensor C _ _ X (Y ⊗ Z) (Xᘁ) ((Y ⊗ Z)ᘁ) pX pYZ
  let pBR₂ : ExactPairing (X ⊗ (Y ⊗ Z)) ((Zᘁ ⊗ Yᘁ) ⊗ Xᘁ) :=
    @ExactPairing.tensor C _ _ X (Y ⊗ Z) (Xᘁ) (Zᘁ ⊗ Yᘁ) pX pYZT
  change
    @rightAdjointMate C _ _ ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))
        ({ rightDual := ((X ⊗ Y) ⊗ Z)ᘁ, exact := pA } :
          HasRightDual ((X ⊗ Y) ⊗ Z))
        ({ rightDual := (X ⊗ (Y ⊗ Z))ᘁ, exact := pB } :
          HasRightDual (X ⊗ (Y ⊗ Z))) (α_ X Y Z).hom ≫
      (rightDualIso pA pAL₁).hom ≫
        (Zᘁ : C) ◁ (rightDualIso pXY pXYT).hom =
    (rightDualIso pB pBR₁).hom ≫
      (rightDualIso pYZ pYZT).hom ▷ Xᘁ ≫
        (α_ (Zᘁ : C) (Yᘁ : C) (Xᘁ : C)).hom
  have hL :
      (rightDualIso pAL₁ pAL₂).hom =
        (Zᘁ : C) ◁ (rightDualIso pXY pXYT).hom := by
    rw [rightDualIso_tensor (C := C), rightDualIso_id]
    simp
  have hR :
      (rightDualIso pBR₁ pBR₂).hom =
        (rightDualIso pYZ pYZT).hom ▷ Xᘁ := by
    rw [rightDualIso_tensor (C := C), rightDualIso_id]
    simp
  have hα := rightAdjointMate_associator (C := C) X Y Z
  change
    @rightAdjointMate C _ _ ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))
        ({ rightDual := Zᘁ ⊗ (Yᘁ ⊗ Xᘁ), exact := pAL₂ } :
          HasRightDual ((X ⊗ Y) ⊗ Z))
        ({ rightDual := (Zᘁ ⊗ Yᘁ) ⊗ Xᘁ, exact := pBR₂ } :
          HasRightDual (X ⊗ (Y ⊗ Z))) (α_ X Y Z).hom =
      (α_ (Zᘁ : C) (Yᘁ : C) (Xᘁ : C)).hom at hα
  rw [← hL, rightDualIso_hom_trans (C := C), ← hR]
  rw [← Category.assoc, rightDualIso_hom_trans (C := C)]
  rw [← hα]
  exact rightAdjointMate_naturality (C := C) pA pAL₂ pB pBR₂ (α_ X Y Z).hom

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightDualTensorIso_left_unitality (X : C)
    [hX : HasRightDual X] [hI : HasRightDual (𝟙_ C)]
    [hIX : HasRightDual (𝟙_ C ⊗ X)] :
    (ρ_ Xᘁ).inv =
      (λ_ X).homᘁ ≫ (rightDualTensorIso (𝟙_ C) X).hom ≫
        (Xᘁ : C) ◁ (rightDualUnitIso).hom := by
  let pX : ExactPairing X (Xᘁ) := hX.exact
  let pI : ExactPairing (𝟙_ C) ((𝟙_ C)ᘁ) := hI.exact
  let pIX : ExactPairing (𝟙_ C ⊗ X) ((𝟙_ C ⊗ X)ᘁ) := hIX.exact
  let pT : ExactPairing (𝟙_ C ⊗ X) (Xᘁ ⊗ (𝟙_ C)ᘁ) :=
    @ExactPairing.tensor C _ _ (𝟙_ C) X ((𝟙_ C)ᘁ) (Xᘁ) pI pX
  let pF : ExactPairing (𝟙_ C ⊗ X) (Xᘁ ⊗ 𝟙_ C) :=
    @ExactPairing.tensor C _ _ (𝟙_ C) X (𝟙_ C) (Xᘁ) exactPairingUnit pX
  change (ρ_ Xᘁ).inv =
    @rightAdjointMate C _ _ (𝟙_ C ⊗ X) X
        ({ rightDual := (𝟙_ C ⊗ X)ᘁ, exact := pIX } : HasRightDual (𝟙_ C ⊗ X))
        ({ rightDual := Xᘁ, exact := pX } : HasRightDual X) (λ_ X).hom ≫
      (rightDualIso pIX pT).hom ≫
        (Xᘁ : C) ◁ (rightDualIso pI exactPairingUnit).hom
  have ht :
      (rightDualIso pT pF).hom =
        (Xᘁ : C) ◁ (rightDualIso pI exactPairingUnit).hom := by
    rw [rightDualIso_tensor (C := C), rightDualIso_id]
    simp
  rw [← ht, rightDualIso_hom_trans (C := C)]
  rw [rightAdjointMate_naturality (C := C) pIX pF pX pX]
  rw [rightDualIso_id, Iso.refl_hom, Category.id_comp]
  symm
  have h := rightAdjointMate_leftUnitor (C := C) X
  change @rightAdjointMate C _ _ (𝟙_ C ⊗ X) X
      ({ rightDual := Xᘁ ⊗ 𝟙_ C, exact := pF } : HasRightDual (𝟙_ C ⊗ X))
      ({ rightDual := Xᘁ, exact := pX } : HasRightDual X) (λ_ X).hom =
    (ρ_ Xᘁ).inv at h
  exact h

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightDualTensorIso_right_unitality (X : C)
    [hX : HasRightDual X] [hI : HasRightDual (𝟙_ C)]
    [hXI : HasRightDual (X ⊗ 𝟙_ C)] :
    (λ_ Xᘁ).inv =
      (ρ_ X).homᘁ ≫ (rightDualTensorIso X (𝟙_ C)).hom ≫
        (rightDualUnitIso).hom ▷ Xᘁ := by
  let pX : ExactPairing X (Xᘁ) := hX.exact
  let pI : ExactPairing (𝟙_ C) ((𝟙_ C)ᘁ) := hI.exact
  let pXI : ExactPairing (X ⊗ 𝟙_ C) ((X ⊗ 𝟙_ C)ᘁ) := hXI.exact
  let pT : ExactPairing (X ⊗ 𝟙_ C) ((𝟙_ C)ᘁ ⊗ Xᘁ) :=
    @ExactPairing.tensor C _ _ X (𝟙_ C) (Xᘁ) ((𝟙_ C)ᘁ) pX pI
  let pF : ExactPairing (X ⊗ 𝟙_ C) (𝟙_ C ⊗ Xᘁ) :=
    @ExactPairing.tensor C _ _ X (𝟙_ C) (Xᘁ) (𝟙_ C) pX exactPairingUnit
  change (λ_ Xᘁ).inv =
    @rightAdjointMate C _ _ (X ⊗ 𝟙_ C) X
        ({ rightDual := (X ⊗ 𝟙_ C)ᘁ, exact := pXI } : HasRightDual (X ⊗ 𝟙_ C))
        ({ rightDual := Xᘁ, exact := pX } : HasRightDual X) (ρ_ X).hom ≫
      (rightDualIso pXI pT).hom ≫
        (rightDualIso pI exactPairingUnit).hom ▷ Xᘁ
  have ht :
      (rightDualIso pT pF).hom =
        (rightDualIso pI exactPairingUnit).hom ▷ Xᘁ := by
    rw [rightDualIso_tensor (C := C), rightDualIso_id]
    simp
  rw [← ht, rightDualIso_hom_trans (C := C)]
  rw [rightAdjointMate_naturality (C := C) pXI pF pX pX]
  rw [rightDualIso_id, Iso.refl_hom, Category.id_comp]
  symm
  have h := rightAdjointMate_rightUnitor (C := C) X
  change @rightAdjointMate C _ _ (X ⊗ 𝟙_ C) X
      ({ rightDual := 𝟙_ C ⊗ Xᘁ, exact := pF } : HasRightDual (X ⊗ 𝟙_ C))
      ({ rightDual := Xᘁ, exact := pX } : HasRightDual X) (ρ_ X).hom =
    (λ_ Xᘁ).inv at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical core monoidal structure on the right dual functor. -/
public def rightDualFunctorCoreMonoidal : (rightDualFunctor C).CoreMonoidal where
  εIso :=
    (@rightDualUnitIso C _ _ (RightRigidCategory.rightDual (C := C) (𝟙_ C))).op.mop
  μIso X Y := (rightDualTensorIso X Y).op.mop
  μIso_hom_natural_left := by
    intro X Y f Z
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using
      (rightDualTensorIso_hom_naturality f (𝟙 Z)).symm
  μIso_hom_natural_right := by
    intro X Y Z f
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using
      (rightDualTensorIso_hom_naturality (𝟙 Z) f).symm
  associativity := by
    intro X Y Z
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using
      (rightDualTensorIso_associativity (C := C) X Y Z)
  left_unitality := by
    intro X
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using
      (@rightDualTensorIso_left_unitality C _ _ X
        (RightRigidCategory.rightDual (C := C) X)
        (RightRigidCategory.rightDual (C := C) (𝟙_ C))
        (RightRigidCategory.rightDual (C := C) (𝟙_ C ⊗ X)))
  right_unitality := by
    intro X
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using
      (@rightDualTensorIso_right_unitality C _ _ X
        (RightRigidCategory.rightDual (C := C) X)
        (RightRigidCategory.rightDual (C := C) (𝟙_ C))
        (RightRigidCategory.rightDual (C := C) (X ⊗ 𝟙_ C)))

/-- The canonical monoidal structure on the right dual functor. -/
@[instance_reducible]
public def rightDualFunctorMonoidal : (rightDualFunctor C).Monoidal :=
  (rightDualFunctorCoreMonoidal C).toMonoidal

attribute [instance] rightDualFunctorMonoidal

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem rightDualFunctor_ε :
    ε (rightDualFunctor C) =
      (@rightDualUnitIso C _ _
        (RightRigidCategory.rightDual (C := C) (𝟙_ C))).hom.op.mop :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem rightDualFunctor_η :
    η (rightDualFunctor C) =
      (@rightDualUnitIso C _ _
        (RightRigidCategory.rightDual (C := C) (𝟙_ C))).inv.op.mop :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem rightDualFunctor_μ (X Y : C) :
    μ (rightDualFunctor C) X Y = (rightDualTensorIso X Y).hom.op.mop :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem rightDualFunctor_δ (X Y : C) :
    δ (rightDualFunctor C) X Y = (rightDualTensorIso X Y).inv.op.mop :=
  rfl

/-- The conjugate of the right dual functor, used internally to construct the
monoidal structure on the double-right-dual functor. -/
private def rightDualFunctorConjugate : (Cᵒᵖ)ᴹᵒᵖ ⥤ C :=
  let d : C ⥤ Cᵒᵖ := rightDualFunctor C ⋙ unmopFunctor Cᵒᵖ
  unmopFunctor Cᵒᵖ ⋙ d.leftOp

set_option backward.isDefEq.respectTransparency.types false in
@[instance_reducible]
private def rightDualFunctorConjugateMonoidal :
    (rightDualFunctorConjugate C).Monoidal where
  ε := (η (rightDualFunctor C)).unmop.unop
  μ X Y := (δ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X))).unmop.unop
  η := (ε (rightDualFunctor C)).unmop.unop
  δ X Y := (μ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X))).unmop.unop
  μ_natural_left := by
    intro X Y f X'
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.OplaxMonoidal.δ_natural_right (rightDualFunctor C)
        (unop (unmop X')) f.unmop.unop)
    change
      f.unmop.unopᘁ ▷ (unop (unmop X'))ᘁ ≫
          (δ (rightDualFunctor C) (unop (unmop X')) (unop (unmop Y))).unmop.unop =
        (δ (rightDualFunctor C) (unop (unmop X')) (unop (unmop X))).unmop.unop ≫
          ((unop (unmop X')) ◁ f.unmop.unop)ᘁ
    simpa [rightDualFunctor] using h
  μ_natural_right := by
    intro X Y X' f
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.OplaxMonoidal.δ_natural_left (rightDualFunctor C)
        f.unmop.unop (unop (unmop X')))
    change
      (unop (unmop X'))ᘁ ◁ f.unmop.unopᘁ ≫
          (δ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X'))).unmop.unop =
        (δ (rightDualFunctor C) (unop (unmop X)) (unop (unmop X'))).unmop.unop ≫
          (f.unmop.unop ▷ (unop (unmop X')))ᘁ
    simpa [rightDualFunctor] using h
  associativity := by
    intro X Y Z
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.OplaxMonoidal.associativity (rightDualFunctor C)
        (unop (unmop Z)) (unop (unmop Y)) (unop (unmop X)))
    change
      (δ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X))).unmop.unop ▷
            (unop (unmop Z))ᘁ ≫
          (δ (rightDualFunctor C) (unop (unmop Z))
            (unop (unmop Y) ⊗ unop (unmop X))).unmop.unop ≫
          (α_ (unop (unmop Z)) (unop (unmop Y)) (unop (unmop X))).homᘁ =
        (α_ ((unop (unmop X))ᘁ : C) ((unop (unmop Y))ᘁ : C)
          ((unop (unmop Z))ᘁ : C)).hom ≫
          (unop (unmop X))ᘁ ◁
            (δ (rightDualFunctor C) (unop (unmop Z)) (unop (unmop Y))).unmop.unop ≫
          (δ (rightDualFunctor C)
            (unop (unmop Z) ⊗ unop (unmop Y)) (unop (unmop X))).unmop.unop
    simpa [rightDualFunctor] using h.symm
  left_unitality := by
    intro X
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.OplaxMonoidal.right_unitality (rightDualFunctor C) (unop (unmop X)))
    change
      (λ_ ((unop (unmop X))ᘁ : C)).hom =
        (η (rightDualFunctor C)).unmop.unop ▷ (unop (unmop X))ᘁ ≫
          (δ (rightDualFunctor C) (unop (unmop X)) (𝟙_ C)).unmop.unop ≫
          (ρ_ (unop (unmop X))).invᘁ
    simpa [rightDualFunctor] using h
  right_unitality := by
    intro X
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.OplaxMonoidal.left_unitality (rightDualFunctor C) (unop (unmop X)))
    change
      (ρ_ ((unop (unmop X))ᘁ : C)).hom =
        (unop (unmop X))ᘁ ◁ (η (rightDualFunctor C)).unmop.unop ≫
          (δ (rightDualFunctor C) (𝟙_ C) (unop (unmop X))).unmop.unop ≫
          (λ_ (unop (unmop X))).invᘁ
    simpa [rightDualFunctor] using h
  δ_natural_left := by
    intro X Y f X'
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.LaxMonoidal.μ_natural_right (rightDualFunctor C)
        (unop (unmop X')) f.unmop.unop)
    change
      (μ (rightDualFunctor C) (unop (unmop X')) (unop (unmop X))).unmop.unop ≫
          f.unmop.unopᘁ ▷ (unop (unmop X'))ᘁ =
        ((unop (unmop X')) ◁ f.unmop.unop)ᘁ ≫
          (μ (rightDualFunctor C) (unop (unmop X')) (unop (unmop Y))).unmop.unop
    simpa [rightDualFunctor] using h
  δ_natural_right := by
    intro X Y X' f
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.LaxMonoidal.μ_natural_left (rightDualFunctor C)
        f.unmop.unop (unop (unmop X')))
    change
      (μ (rightDualFunctor C) (unop (unmop X)) (unop (unmop X'))).unmop.unop ≫
          (unop (unmop X'))ᘁ ◁ f.unmop.unopᘁ =
        (f.unmop.unop ▷ (unop (unmop X')))ᘁ ≫
          (μ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X'))).unmop.unop
    simpa [rightDualFunctor] using h
  oplax_associativity := by
    intro X Y Z
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.LaxMonoidal.associativity (rightDualFunctor C)
        (unop (unmop Z)) (unop (unmop Y)) (unop (unmop X)))
    change
      (μ (rightDualFunctor C) (unop (unmop Z))
            (unop (unmop Y) ⊗ unop (unmop X))).unmop.unop ≫
          (μ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X))).unmop.unop ▷
            (unop (unmop Z))ᘁ ≫
          (α_ ((unop (unmop X))ᘁ : C) ((unop (unmop Y))ᘁ : C)
            ((unop (unmop Z))ᘁ : C)).hom =
        (α_ (unop (unmop Z)) (unop (unmop Y)) (unop (unmop X))).homᘁ ≫
          (μ (rightDualFunctor C)
            (unop (unmop Z) ⊗ unop (unmop Y)) (unop (unmop X))).unmop.unop ≫
          (unop (unmop X))ᘁ ◁
            (μ (rightDualFunctor C) (unop (unmop Z)) (unop (unmop Y))).unmop.unop
    simpa [rightDualFunctor] using h.symm
  oplax_left_unitality := by
    intro X
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.LaxMonoidal.right_unitality (rightDualFunctor C) (unop (unmop X)))
    change
      (λ_ ((unop (unmop X))ᘁ : C)).inv =
        (ρ_ (unop (unmop X))).homᘁ ≫
          (μ (rightDualFunctor C) (unop (unmop X)) (𝟙_ C)).unmop.unop ≫
          (ε (rightDualFunctor C)).unmop.unop ▷ (unop (unmop X))ᘁ
    simpa [rightDualFunctor] using h
  oplax_right_unitality := by
    intro X
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.LaxMonoidal.left_unitality (rightDualFunctor C) (unop (unmop X)))
    change
      (ρ_ ((unop (unmop X))ᘁ : C)).inv =
        (λ_ (unop (unmop X))).homᘁ ≫
          (μ (rightDualFunctor C) (𝟙_ C) (unop (unmop X))).unmop.unop ≫
          (unop (unmop X))ᘁ ◁ (ε (rightDualFunctor C)).unmop.unop
    simpa [rightDualFunctor] using h
  ε_η := by
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.Monoidal.ε_η (rightDualFunctor C))
    change
      (η (rightDualFunctor C)).unmop.unop ≫
        (ε (rightDualFunctor C)).unmop.unop = 𝟙 _
    simpa [rightDualFunctor] using h
  η_ε := by
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.Monoidal.η_ε (rightDualFunctor C))
    change
      (ε (rightDualFunctor C)).unmop.unop ≫
        (η (rightDualFunctor C)).unmop.unop = 𝟙 _
    simpa [rightDualFunctor] using h
  μ_δ := by
    intro X Y
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.Monoidal.μ_δ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X)))
    change
      (δ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X))).unmop.unop ≫
        (μ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X))).unmop.unop = 𝟙 _
    simpa [rightDualFunctor] using h
  δ_μ := by
    intro X Y
    have h := congrArg (fun k => k.unmop.unop)
      (Functor.Monoidal.δ_μ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X)))
    change
      (μ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X))).unmop.unop ≫
        (δ (rightDualFunctor C) (unop (unmop Y)) (unop (unmop X))).unmop.unop = 𝟙 _
    simpa [rightDualFunctor] using h

attribute [local instance] rightDualFunctorConjugateMonoidal

/-- The functor `X ↦ Xᘁᘁ`. -/
@[simps! obj map, expose]
public def doubleRightDualFunctor : C ⥤ C :=
  rightDualFunctor C ⋙ unmopFunctor Cᵒᵖ ⋙ (rightDualFunctor C ⋙ unmopFunctor Cᵒᵖ).leftOp

@[instance_reducible]
private def doubleRightDualFunctorComposedMonoidal :
    (doubleRightDualFunctor C).Monoidal :=
  inferInstanceAs <| (rightDualFunctor C ⋙ rightDualFunctorConjugate C).Monoidal

/-- The canonical comparison between the monoidal unit and its double right dual. -/
public def doubleRightDualUnitIso : 𝟙_ C ≅ (doubleRightDualFunctor C).obj (𝟙_ C) := by
  let u := @rightDualUnitIso C _ _
    (RightRigidCategory.rightDual (C := C) (𝟙_ C))
  exact u.symm ≪≫ @rightAdjointMateIso C _ _ _ _
    (RightRigidCategory.rightDual (C := C) _)
    (RightRigidCategory.rightDual (C := C) _) u

/-- The canonical tensorator for the double-right-dual functor. -/
public def doubleRightDualTensorIso (X Y : C) :
    (doubleRightDualFunctor C).obj X ⊗ (doubleRightDualFunctor C).obj Y ≅
      (doubleRightDualFunctor C).obj (X ⊗ Y) :=
  (rightDualTensorIso (Yᘁ : C) (Xᘁ : C)).symm ≪≫
    rightAdjointMateIso (rightDualTensorIso X Y)

/-- The canonical core monoidal structure on the double-right-dual functor. -/
public def doubleRightDualFunctorCoreMonoidal :
    (doubleRightDualFunctor C).CoreMonoidal := by
  letI := doubleRightDualFunctorComposedMonoidal C
  exact
    { εIso := doubleRightDualUnitIso C
      μIso := fun X Y => doubleRightDualTensorIso (C := C) X Y
      μIso_hom_natural_left := by
        intros
        apply Functor.LaxMonoidal.μ_natural_left
      μIso_hom_natural_right := by
        intros
        apply Functor.LaxMonoidal.μ_natural_right
      associativity := by
        intro X Y Z
        change
          μ (doubleRightDualFunctor C) X Y ▷ (doubleRightDualFunctor C).obj Z ≫
              μ (doubleRightDualFunctor C) (X ⊗ Y) Z ≫
              (doubleRightDualFunctor C).map (α_ X Y Z).hom =
            (α_ ((doubleRightDualFunctor C).obj X) ((doubleRightDualFunctor C).obj Y)
              ((doubleRightDualFunctor C).obj Z)).hom ≫
              (doubleRightDualFunctor C).obj X ◁ μ (doubleRightDualFunctor C) Y Z ≫
              μ (doubleRightDualFunctor C) X (Y ⊗ Z)
        apply Functor.LaxMonoidal.associativity
      left_unitality := by
        intros
        apply Functor.LaxMonoidal.left_unitality
      right_unitality := by
        intros
        apply Functor.LaxMonoidal.right_unitality }

/-- The canonical monoidal structure on the double-right-dual functor. -/
@[instance_reducible]
public def doubleRightDualFunctorMonoidal :
    (doubleRightDualFunctor C).Monoidal :=
  (doubleRightDualFunctorCoreMonoidal C).toMonoidal

attribute [instance] doubleRightDualFunctorMonoidal

@[simp]
theorem doubleRightDualFunctor_ε :
    ε (doubleRightDualFunctor C) = (doubleRightDualUnitIso C).hom :=
  rfl

@[simp]
theorem doubleRightDualFunctor_η :
    η (doubleRightDualFunctor C) = (doubleRightDualUnitIso C).inv :=
  rfl

@[simp]
theorem doubleRightDualFunctor_μ (X Y : C) :
    μ (doubleRightDualFunctor C) X Y =
      (doubleRightDualTensorIso (C := C) X Y).hom :=
  rfl

@[simp]
theorem doubleRightDualFunctor_δ (X Y : C) :
    δ (doubleRightDualFunctor C) X Y =
      (doubleRightDualTensorIso (C := C) X Y).inv :=
  rfl

end RightRigid

end CategoryTheory
