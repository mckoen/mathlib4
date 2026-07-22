/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Triangulated.Triangulated

@[expose] public section

universe u u₁ u₂ v w

open CategoryTheory

variable {R : Type w} [CommRing R]

instance : (MonoidalCategory.curriedTensor (ModuleCat.{w} R)).Additive :=
  MonoidalPreadditive.instAdditiveFunctorCurriedTensor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' (fun (i : ℤ) => (-1 : ℤˣ) ^ i) (zpow_add (-1 : ℤˣ))
  rel_add p q r (hpq : q + 1 = p) := by dsimp; lia
  add_rel p q r (hpq : q + 1 = p) := by dsimp; lia
  ε'_succ := by
    rintro _ q rfl
    dsimp
    erw [zpow_add]
    rw [zpow_one, mul_neg, mul_one, neg_neg]
    rfl

/-- A category enriched over cochain complexes of `R`-modules. -/
abbrev DGCategory (R : Type w) [CommRing R] :=
  EnrichedCategory (ChainComplex (ModuleCat.{w} R) ℤ)

noncomputable section

namespace DGCategory

local notation "V" => ChainComplex (ModuleCat R) ℤ

/-- The category with the same objects as a DG category and closed degree-zero morphisms. -/
abbrev Z0 (C : Type u) [DGCategory R C] :=
  ForgetEnrichment V C

variable {C : Type u} [DGCategory R C]

/-- Two closed degree-zero morphisms are homotopic when the corresponding morphisms from the
tensor unit to the enriched hom complex are homotopic. -/
def homotopic : HomRel (Z0 (R := R) C) := fun _ _ f g =>
  Nonempty (Homotopy (ForgetEnrichment.homTo V f) (ForgetEnrichment.homTo V g))

/-- Homotopy of closed degree-zero morphisms is compatible with composition. -/
noncomputable instance homotopy_congruence :
    Congruence (homotopic (R := R) (C := C)) where
  equivalence :=
    { refl := fun _ => ⟨Homotopy.refl _⟩
      symm := fun ⟨h⟩ => ⟨h.symm⟩
      trans := fun ⟨h₁⟩ ⟨h₂⟩ => ⟨h₁.trans h₂⟩ }
  comp_left := fun f _ _ ⟨h⟩ => ⟨by
    simp only [ForgetEnrichment.homTo_comp]
    exact ((HomologicalComplex.mapBifunctorMapHomotopy₂
      (ForgetEnrichment.homTo V f) h (MonoidalCategory.curriedTensor (ModuleCat R))
      (ComplexShape.down ℤ)).compLeft
        (MonoidalCategoryStruct.leftUnitor (MonoidalCategoryStruct.tensorUnit V)).inv).compRight
          (eComp V _ _ _)⟩
  comp_right := fun g ⟨h⟩ => ⟨by
    simp only [ForgetEnrichment.homTo_comp]
    exact ((HomologicalComplex.mapBifunctorMapHomotopy₁ h
      (ForgetEnrichment.homTo V g) (MonoidalCategory.curriedTensor (ModuleCat R))
      (ComplexShape.down ℤ)).compLeft
        (MonoidalCategoryStruct.leftUnitor (MonoidalCategoryStruct.tensorUnit V)).inv).compRight
          (eComp V _ _ _)⟩

/-- The homotopy category `H⁰(C)` of a DG category `C`. -/
def HomotopyCategory (C : Type u) [DGCategory R C] := Quotient (homotopic (R := R) (C := C))

instance : Category (HomotopyCategory (R := R) C) := inferInstanceAs (Category (Quotient homotopic))

namespace HomotopyCategory

/-- The quotient functor from closed degree-zero morphisms to the homotopy category. -/
def quotient : Z0 (R := R) C ⥤ HomotopyCategory (R := R) C := Quotient.functor _

instance : (quotient (R := R) (C := C)).Full := Quotient.full_functor _

instance : (quotient (R := R) (C := C)).EssSurj := Quotient.essSurj_functor _

/-- Equality in the homotopy category is exactly homotopy of representatives. -/
theorem quotient_map_eq_iff {X Y : Z0 C} (f g : X ⟶ Y) :
    quotient.map f = quotient.map g ↔
      Nonempty (Homotopy (ForgetEnrichment.homTo V f) (ForgetEnrichment.homTo V g)) :=
  Quotient.functor_map_eq_iff _ _ _

end HomotopyCategory

/-- The currently formalized data of an `R`-linear DG enhancement of a triangulated category
`T`: a DG category `B` and an equivalence `H⁰(B) ≌ T`.

The requirements that `B` be pretriangulated and that the equivalence preserve the triangulated
structures are intentionally not included yet. -/
structure Enhancement (R : Type w) [CommRing R]
    (T : Type u₂) [Category.{v} T] [Limits.HasZeroObject T] [Preadditive T]
    [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
    [Pretriangulated T] [IsTriangulated T] where
  /-- The DG category furnishing the enhancement. -/
  B : Type u₁
  /-- The `R`-linear DG enrichment on `B`. -/
  [dgCategory : DGCategory R B]
  /-- The equivalence from the homotopy category of `B` to `T`. -/
  ε : HomotopyCategory (R := R) B ≌ T

attribute [instance] Enhancement.dgCategory

end DGCategory
