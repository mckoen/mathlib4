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
* `doubleRightDualFunctor C`: The functor `C ⥤ C` on a right rigid category sending
  `X` to `Xᘁᘁ` and `f` to `fᘁᘁ`.

## Future work

* Show that in a `RigidCategory`, these functors are monoidal equivalences.
-/

namespace CategoryTheory

open Category MonoidalCategory MonoidalOpposite Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

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
set_option backward.isDefEq.respectTransparency.types false

/-- The right dual functor from `C` to `(Cᵒᵖ)ᴹᵒᵖ`. -/
@[simps obj map, expose]
public def rightDualFunctor : C ⥤ (Cᵒᵖ)ᴹᵒᵖ where
  obj X := mop (op (Xᘁ))
  map f := (fᘁ).op.mop
  map_id X := by simp [rightAdjointMate_id]
  map_comp f g := by simp [comp_rightAdjointMate]

attribute [local instance] hasRightDualTensor in
omit [RightRigidCategory C] in
private theorem rightAdjointMate_associator (X Y Z : C)
    [HasRightDual X] [HasRightDual Y] [HasRightDual Z] :
    rightAdjointMate (α_ X Y Z).hom = (α_ Zᘁ Yᘁ Xᘁ).hom := by
  let hL : HasRightDual ((X ⊗ Y) ⊗ Z) := {
    rightDual := Zᘁ ⊗ (Yᘁ ⊗ Xᘁ)
    exact := ExactPairing.tensor}
  let hR : HasRightDual (X ⊗ (Y ⊗ Z)) := {
    rightDual := (Zᘁ ⊗ Yᘁ) ⊗ Xᘁ
    exact := ExactPairing.tensor}
  symm
  apply (@eq_rightAdjointMate_iff C _ _ _ _ hL hR _ _).2
  dsimp only [hL, hR, HasRightDual.rightDual, HasRightDual.exact]
  have evalL := @ExactPairing.tensor_evaluation C _ _ (X ⊗ Y) Z
    (Yᘁ ⊗ Xᘁ) (Zᘁ) hasRightDualTensor.exact HasRightDual.exact
  have evalR := @ExactPairing.tensor_evaluation C _ _ X (Y ⊗ Z)
    (Xᘁ) (Zᘁ ⊗ Yᘁ) HasRightDual.exact hasRightDualTensor.exact
  rw [evalL, evalR, ExactPairing.tensor_evaluation, ExactPairing.tensor_evaluation]
  monoidal

attribute [local instance] hasRightDualTensor in
omit [RightRigidCategory C] in
private theorem rightAdjointMate_leftUnitor (X : C) [HasRightDual X] :
    rightAdjointMate (λ_ X).hom = (ρ_ Xᘁ).inv := by
  let hIX : HasRightDual (𝟙_ C ⊗ X) := {
    rightDual := Xᘁ ⊗ 𝟙_ C
    exact := ExactPairing.tensor }
  symm
  rw [eq_rightAdjointMate_iff (λ_ X).hom (ρ_ Xᘁ).inv]
  dsimp only [hIX, HasRightDual.rightDual, HasRightDual.exact]
  have evalIX := @ExactPairing.tensor_evaluation C _ _ (𝟙_ C) X
    (𝟙_ C) (Xᘁ) hasRightDualUnit.exact HasRightDual.exact
  have evalI :
      @ExactPairing.evaluation C _ _ (𝟙_ C) (𝟙_ C) exactPairingUnit =
        (ρ_ (𝟙_ C)).hom := rfl
  rw [evalIX, evalI]
  monoidal

attribute [local instance] hasRightDualTensor in
omit [RightRigidCategory C] in
private theorem rightAdjointMate_rightUnitor (X : C) [HasRightDual X] :
    rightAdjointMate (ρ_ X).hom = (λ_ Xᘁ).inv := by
  let hXI : HasRightDual (X ⊗ 𝟙_ C) := {
    rightDual := 𝟙_ C ⊗ Xᘁ
    exact := ExactPairing.tensor }
  symm
  refine (@eq_rightAdjointMate_iff C _ _ (X ⊗ 𝟙_ C) X hXI _
    (ρ_ X).hom (λ_ Xᘁ).inv).2 ?_
  dsimp only [hXI, HasRightDual.rightDual, HasRightDual.exact]
  have evalXI := @ExactPairing.tensor_evaluation C _ _ X (𝟙_ C)
    (Xᘁ) (𝟙_ C) HasRightDual.exact hasRightDualUnit.exact
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

/-- The canonical core monoidal structure on the right dual functor. -/
public def rightDualFunctorCoreMonoidal : (rightDualFunctor C).CoreMonoidal where
  εIso := (@rightDualUnitIso C _ _ (RightRigidCategory.rightDual (𝟙_ C))).op.mop
  μIso X Y := (rightDualTensorIso X Y).op.mop
  μIso_hom_natural_left {X Y} f Z := by
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using (rightDualTensorIso_hom_naturality f (𝟙 Z)).symm
  μIso_hom_natural_right {X Y} Z f := by
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using (rightDualTensorIso_hom_naturality (𝟙 Z) f).symm
  associativity X Y Z := by
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using (rightDualTensorIso_associativity C X Y Z)
  left_unitality X := by
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using
      (@rightDualTensorIso_left_unitality C _ _ X
        (RightRigidCategory.rightDual (C := C) X)
        (RightRigidCategory.rightDual (C := C) (𝟙_ C))
        (RightRigidCategory.rightDual (C := C) (𝟙_ C ⊗ X)))
  right_unitality X := by
    apply MonoidalOpposite.hom_ext
    apply Quiver.Hom.unop_inj
    simpa [rightDualFunctor] using
      (@rightDualTensorIso_right_unitality C _ _ X
        (RightRigidCategory.rightDual (C := C) X)
        (RightRigidCategory.rightDual (C := C) (𝟙_ C))
        (RightRigidCategory.rightDual (C := C) (X ⊗ 𝟙_ C)))

/-- The canonical monoidal structure on the right dual functor. -/
@[instance_reducible, instance]
public def rightDualFunctorMonoidal : (rightDualFunctor C).Monoidal :=
  (rightDualFunctorCoreMonoidal C).toMonoidal

@[simp] theorem rightDualFunctor_ε :
    letI := (RightRigidCategory.rightDual (𝟙_ C))
    ε (rightDualFunctor C) = rightDualUnitIso.hom.op.mop := rfl

@[simp] theorem rightDualFunctor_η :
    letI := (RightRigidCategory.rightDual (𝟙_ C))
    η (rightDualFunctor C) = rightDualUnitIso.inv.op.mop := rfl

@[simp] theorem rightDualFunctor_μ (X Y : C) :
    μ (rightDualFunctor C) X Y = (rightDualTensorIso X Y).hom.op.mop := rfl

@[simp] theorem rightDualFunctor_δ (X Y : C) :
    δ (rightDualFunctor C) X Y = (rightDualTensorIso X Y).inv.op.mop := rfl

/-- The functor `X ↦ Xᘁᘁ`. -/
@[simps!, expose]
public def doubleRightDualFunctor : C ⥤ C :=
  rightDualFunctor C ⋙ unmopFunctor Cᵒᵖ ⋙ (rightDualFunctor C ⋙ unmopFunctor Cᵒᵖ).leftOp

variable {C}

local instance : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)

/-- The canonical comparison between the monoidal unit and its double right dual. -/
public def doubleRightDualUnitIso : 𝟙_ C ≅ (doubleRightDualFunctor C).obj (𝟙_ C) :=
  rightDualUnitIso.symm ≪≫ rightAdjointMateIso rightDualUnitIso

/-- The canonical tensorator for the double-right-dual functor. -/
public def doubleRightDualTensorIso (X Y : C) :
    (doubleRightDualFunctor C).obj X ⊗ (doubleRightDualFunctor C).obj Y ≅
      (doubleRightDualFunctor C).obj (X ⊗ Y) :=
  (rightDualTensorIso Yᘁ Xᘁ).symm ≪≫ rightAdjointMateIso (rightDualTensorIso X Y)

set_option backward.isDefEq.respectTransparency false
private theorem doubleRightDualTensorIso_hom_naturality {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (fᘁᘁ ⊗ₘ gᘁᘁ) ≫ (doubleRightDualTensorIso X' Y').hom =
      (doubleRightDualTensorIso X Y).hom ≫ (f ⊗ₘ g)ᘁᘁ := by
  simpa [doubleRightDualTensorIso, ← rightDualTensorIso_inv_naturality_assoc (gᘁ) (fᘁ),
    cancel_epi, comp_rightAdjointMate] using
    congrArg rightAdjointMate (rightDualTensorIso_hom_naturality f g).symm

/-- The canonical core monoidal structure on the double-right-dual functor. -/
public def doubleRightDualFunctorCoreMonoidal : (doubleRightDualFunctor C).CoreMonoidal where
  εIso := doubleRightDualUnitIso
  μIso := doubleRightDualTensorIso
  μIso_hom_natural_left f Z := by
    change fᘁᘁ ▷ (Zᘁ)ᘁ ≫ _ = _
    simpa using doubleRightDualTensorIso_hom_naturality f (𝟙 Z)
  μIso_hom_natural_right Z f := by
    change (Zᘁ)ᘁ ◁ fᘁᘁ ≫ _ = _
    simpa using doubleRightDualTensorIso_hom_naturality (𝟙 Z) f
  associativity X Y Z := by
    dsimp [doubleRightDualFunctor, rightDualFunctor, unmopFunctor, Functor.comp, Functor.leftOp]
    simp only [doubleRightDualTensorIso, Iso.trans_hom, Iso.symm_hom,
      rightAdjointMateIso_hom, comp_whiskerRight, assoc, whiskerLeft_comp]
    have hnat₁ := (rightDualTensorIso_inv_naturality (𝟙 (Zᘁ)) (rightDualTensorIso X Y).hom).symm
    have hinner := congrArg (rightAdjointMate (C := C)) (rightDualTensorIso_associativity C X Y Z)
    have houter := congrArg (fun k => k.unmop.unop)
      (Functor.OplaxMonoidal.associativity (rightDualFunctor C) Zᘁ Yᘁ Xᘁ)
    have hnat₂ := rightDualTensorIso_inv_naturality (rightDualTensorIso Y Z).hom (𝟙 (Xᘁ))
    simp only [comp_rightAdjointMate, Category.assoc, rightDualFunctor_δ] at hinner houter
    simp only [rightAdjointMate_id, tensorHom_id, id_tensorHom, rightDualFunctor, unmop_tensorObj,
      unop_tensorObj, op_tensorObj, unmop_comp, Quiver.Hom.unmop_mop, unmop_whiskerRight,
      unmop_hom_associator, unop_comp, unop_inv_associator, unop_whiskerLeft,
      Quiver.Hom.unop_op, assoc, unmop_whiskerLeft, unop_whiskerRight] at hnat₁ houter hnat₂
    rw [reassoc_of% hnat₁, hinner, ← reassoc_of% houter, reassoc_of% hnat₂]
  left_unitality X := by
    change (λ_ ((Xᘁ)ᘁ : C)).hom = _ ▷ (Xᘁ)ᘁ ≫ _ ≫ (λ_ X).homᘁᘁ
    simp only [doubleRightDualUnitIso, Iso.trans_hom, Iso.symm_hom,
      rightAdjointMateIso_hom, comp_whiskerRight, doubleRightDualTensorIso, assoc]
    have hnat := (rightDualTensorIso_inv_naturality (𝟙 (Xᘁ : C)) rightDualUnitIso.hom).symm
    have hinner := congrArg (rightAdjointMate (C := C)) (rightDualTensorIso_left_unitality C X)
    simp only [rightAdjointMate_id, tensorHom_id, id_tensorHom, comp_rightAdjointMate,
      assoc] at hnat hinner
    rw [reassoc_of% hnat, ← hinner, ← cancel_mono (λ_ ((Xᘁ)ᘁ : C)).inv, Iso.hom_inv_id,
      rightDualTensorIso_right_unitality C]
    simp [← comp_rightAdjointMate_assoc]
  right_unitality X := by
    change (ρ_ ((Xᘁ)ᘁ : C)).hom = (Xᘁ)ᘁ ◁ _ ≫ _ ≫ (ρ_ X).homᘁᘁ
    simp only [doubleRightDualUnitIso, Iso.trans_hom, Iso.symm_hom,
      rightAdjointMateIso_hom, whiskerLeft_comp, doubleRightDualTensorIso, assoc]
    have hnat := (rightDualTensorIso_inv_naturality rightDualUnitIso.hom (𝟙 (Xᘁ : C))).symm
    have hinner := congrArg (rightAdjointMate (C := C)) (rightDualTensorIso_right_unitality C X)
    simp only [rightAdjointMate_id, id_tensorHom, tensorHom_id, comp_rightAdjointMate,
      assoc] at hnat hinner
    rw [reassoc_of% hnat, ← hinner, ← cancel_mono (ρ_ ((Xᘁ)ᘁ : C)).inv, Iso.hom_inv_id,
      rightDualTensorIso_left_unitality C]
    simp [← comp_rightAdjointMate_assoc]

/-- The canonical monoidal structure on the double-right-dual functor. -/
@[instance_reducible, instance]
public def doubleRightDualFunctorMonoidal : (doubleRightDualFunctor C).Monoidal :=
  doubleRightDualFunctorCoreMonoidal.toMonoidal

@[simp] theorem doubleRightDualFunctor_ε :
    ε (doubleRightDualFunctor C) = doubleRightDualUnitIso.hom := rfl

@[simp] theorem doubleRightDualFunctor_η :
    η (doubleRightDualFunctor C) = doubleRightDualUnitIso.inv := rfl

@[simp] theorem doubleRightDualFunctor_μ (X Y : C) :
    μ (doubleRightDualFunctor C) X Y = (doubleRightDualTensorIso X Y).hom := rfl

@[simp] theorem doubleRightDualFunctor_δ (X Y : C) :
    δ (doubleRightDualFunctor C) X Y = (doubleRightDualTensorIso X Y).inv := rfl

end RightRigid

end CategoryTheory
