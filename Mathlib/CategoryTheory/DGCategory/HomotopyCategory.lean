/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/

module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.CategoryTheory.DGCategory.Basic
public import Mathlib.CategoryTheory.Quotient

/-!
# Homotopy categories of DG-categories

For a category `C` enriched over cochain complexes, `DGCategory.Z0 C` is its category of
closed degree-zero morphisms. The homotopy category `DGCategory.HomotopyCategory C` is the
quotient of this category by homotopy of maps from the tensor unit into the enriched hom
complexes.
-/

@[expose] public section

universe u₁ u₂ w

noncomputable section

open CategoryTheory

variable {R : Type w} [CommRing R]

namespace DGCategory

local notation "V" => CochainComplex (ModuleCat R) ℤ

/-- The category with the same objects as a DG-category and closed degree-zero morphisms. -/
abbrev Z0 (C : Type u₁) [DGCategory R C] := ForgetEnrichment V C

variable {C : Type u₁} [DGCategory R C]

/-- Two closed degree-zero morphisms in a DG-category are homotopic when the corresponding
maps from the tensor unit into the enriched hom complex are homotopic cochain maps. -/
def homotopic : HomRel (Z0 (R := R) C) := fun _ _ f g =>
  Nonempty (Homotopy (ForgetEnrichment.homTo V f) (ForgetEnrichment.homTo V g))

/-- Homotopy of closed degree-zero morphisms is compatible with composition. -/
noncomputable instance homotopy_congruence : Congruence (homotopic (R := R) (C := C)) where
  equivalence :=
    { refl := fun f => ⟨Homotopy.refl _⟩
      symm := fun ⟨h⟩ => ⟨h.symm⟩
      trans := fun ⟨h₁⟩ ⟨h₂⟩ => ⟨h₁.trans h₂⟩ }
  comp_left := fun f g g' ⟨h⟩ => ⟨by
    simp only [ForgetEnrichment.homTo_comp]
    exact ((HomologicalComplex.mapBifunctorMapHomotopy₂
      (ForgetEnrichment.homTo V f) h (MonoidalCategory.curriedTensor (ModuleCat R))
      (ComplexShape.up ℤ)).compLeft
        (MonoidalCategoryStruct.leftUnitor (MonoidalCategoryStruct.tensorUnit V)).inv).compRight
          (eComp V _ _ _)⟩
  comp_right := fun g ⟨h⟩ => ⟨by
    simp only [ForgetEnrichment.homTo_comp]
    exact ((HomologicalComplex.mapBifunctorMapHomotopy₁ h
      (ForgetEnrichment.homTo V g) (MonoidalCategory.curriedTensor (ModuleCat R))
      (ComplexShape.up ℤ)).compLeft
        (MonoidalCategoryStruct.leftUnitor (MonoidalCategoryStruct.tensorUnit V)).inv).compRight
          (eComp V _ _ _)⟩

/-- The homotopy category of a DG-category. Its morphisms are closed degree-zero morphisms
modulo homotopy. -/
def HomotopyCategory (C : Type u₁) [DGCategory R C] :=
  CategoryTheory.Quotient (homotopic (R := R) (C := C))

instance : Category (HomotopyCategory (R := R) C) :=
  inferInstanceAs (Category (CategoryTheory.Quotient (homotopic (R := R) (C := C))))

namespace HomotopyCategory

/-- The quotient functor from closed degree-zero morphisms to the homotopy category. -/
def quotient : Z0 (R := R) C ⥤ HomotopyCategory (R := R) C :=
  CategoryTheory.Quotient.functor _

instance : (quotient (R := R) (C := C)).Full :=
  CategoryTheory.Quotient.full_functor _

instance : (quotient (R := R) (C := C)).EssSurj :=
  CategoryTheory.Quotient.essSurj_functor _

lemma quotient_obj_surjective (X : HomotopyCategory (R := R) C) :
    ∃ K : Z0 (R := R) C, (quotient (R := R) (C := C)).obj K = X :=
  ⟨_, rfl⟩

-- Not `@[simp]` because it hinders the automatic application of `quotient_map_out`.
theorem quotient_obj_as (X : Z0 (R := R) C) :
    ((quotient (R := R) (C := C)).obj X).as = X :=
  rfl

@[simp]
theorem quotient_map_out {X Y : HomotopyCategory (R := R) C} (f : X ⟶ Y) :
    (quotient (R := R) (C := C)).map f.out = f :=
  Quot.out_eq _

theorem quot_mk_eq_quotient_map {X Y : Z0 (R := R) C} (f : X ⟶ Y) :
    Quot.mk _ f = (quotient (R := R) (C := C)).map f :=
  rfl

/-- Homotopic closed degree-zero morphisms have the same image in the homotopy category. -/
theorem eq_of_homotopy {X Y : Z0 (R := R) C} (f g : X ⟶ Y)
    (h : Homotopy (ForgetEnrichment.homTo V f) (ForgetEnrichment.homTo V g)) :
    (quotient (R := R) (C := C)).map f = (quotient (R := R) (C := C)).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two closed degree-zero morphisms become equal in the homotopy category, then they are
homotopic. -/
def homotopyOfEq {X Y : Z0 (R := R) C} (f g : X ⟶ Y)
    (h : (quotient (R := R) (C := C)).map f =
      (quotient (R := R) (C := C)).map g) :
    Homotopy (ForgetEnrichment.homTo V f) (ForgetEnrichment.homTo V g) :=
  ((CategoryTheory.Quotient.functor_map_eq_iff _ _ _).mp h).some

/-- Equality in the homotopy category is exactly homotopy of representatives. -/
theorem quotient_map_eq_iff {X Y : Z0 (R := R) C} (f g : X ⟶ Y) :
    (quotient (R := R) (C := C)).map f = (quotient (R := R) (C := C)).map g ↔
      Nonempty (Homotopy (ForgetEnrichment.homTo V f) (ForgetEnrichment.homTo V g)) :=
  CategoryTheory.Quotient.functor_map_eq_iff _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem quotient_map_out_comp_out {X Y Z : HomotopyCategory (R := R) C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (quotient (R := R) (C := C)).map (Quot.out f ≫ Quot.out g) = f ≫ g := by
  simp

end HomotopyCategory

end DGCategory

namespace CategoryTheory.EnrichedFunctor

local notation "V" => CochainComplex (ModuleCat R) ℤ

variable {C : Type u₁} {D : Type u₂} [DGCategory R C] [DGCategory R D]

/-- A DG-functor induces a functor between homotopy categories. -/
noncomputable def mapHomotopyCategory (F : EnrichedFunctor V C D) :
    DGCategory.HomotopyCategory (R := R) C ⥤ DGCategory.HomotopyCategory (R := R) D :=
  CategoryTheory.Quotient.lift _
    (F.forget ⋙ DGCategory.HomotopyCategory.quotient (R := R) (C := D)) (by
      rintro X Y f g ⟨h⟩
      apply CategoryTheory.Quotient.sound
      exact ⟨by
        simpa [EnrichedFunctor.forget_map] using
          h.compRight (F.map (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y))⟩)

/-- The functor induced by a DG-functor maps a representative to the class of its image. -/
@[simp]
theorem mapHomotopyCategory_map (F : EnrichedFunctor V C D)
    {X Y : DGCategory.Z0 (R := R) C} (f : X ⟶ Y) :
    F.mapHomotopyCategory.map
        ((DGCategory.HomotopyCategory.quotient (R := R) (C := C)).map f) =
      (DGCategory.HomotopyCategory.quotient (R := R) (C := D)).map (F.forget.map f) :=
  rfl

/-- The functor induced on homotopy categories factors the underlying functor on closed
degree-zero morphisms through the quotient functors. -/
noncomputable def mapHomotopyCategoryFactors (F : EnrichedFunctor V C D) :
    DGCategory.HomotopyCategory.quotient (R := R) (C := C) ⋙ F.mapHomotopyCategory ≅
      F.forget ⋙ DGCategory.HomotopyCategory.quotient (R := R) (C := D) :=
  CategoryTheory.Quotient.lift.isLift _ _ _

end CategoryTheory.EnrichedFunctor
