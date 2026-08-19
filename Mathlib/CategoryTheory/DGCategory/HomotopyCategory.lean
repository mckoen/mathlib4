/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/

module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.CategoryTheory.DGCategory.Basic
public import Mathlib.CategoryTheory.Quotient.Linear
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# Homotopy categories of DG categories

This file defines the homotopy category `H⁰(C)` of a DG category `C` by quotienting its
closed degree-zero morphisms by homotopy. It also constructs the functor `H⁰(F)` induced by
a DG functor.
-/

@[expose] public section

universe u u₂ w

open CategoryTheory MonoidalCategory

variable {R : Type w} [CommRing R]

noncomputable section

namespace DGCategory

local notation "V" => CochainComplex (ModuleCat R) ℤ

variable {C : Type u} [DGCategory R C]

/-- Two closed degree-zero morphisms are homotopic when the corresponding morphisms from the
tensor unit to the enriched hom complex are homotopic. -/
def homotopic : HomRel (Z0 (R := R) C) := fun _ _ f g =>
  Nonempty (Homotopy (ForgetEnrichment.homTo V f) (ForgetEnrichment.homTo V g))

instance : Congruence (homotopic (R := R) (C := C)) where
  equivalence :=
    { refl := fun _ => ⟨Homotopy.refl _⟩
      symm := fun ⟨h⟩ => ⟨h.symm⟩
      trans := fun ⟨h₁⟩ ⟨h₂⟩ => ⟨h₁.trans h₂⟩ }
  comp_left := fun f _ _ ⟨h⟩ => ⟨((HomologicalComplex.mapBifunctorMapHomotopy₂
    (ForgetEnrichment.homTo V f) h _ (ComplexShape.up ℤ)).compLeft (λ_ (𝟙_ V)).inv).compRight
      (eComp V _ _ _)⟩
  comp_right := fun g ⟨h⟩ => ⟨((HomologicalComplex.mapBifunctorMapHomotopy₁ h
    (ForgetEnrichment.homTo V g) _ (ComplexShape.up ℤ)).compLeft (λ_ (𝟙_ V)).inv).compRight
      (eComp V _ _ _)⟩

/-- The homotopy category `H⁰(C)` of a DG category `C`. -/
def HomotopyCategory (C : Type u) [DGCategory R C] := Quotient (homotopic (R := R) (C := C))
deriving Category

namespace HomotopyCategory

instance preadditiveQuotient :
    Preadditive (Quotient (homotopic (R := R) (C := C))) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨Homotopy.add h h'⟩)

instance : Preadditive (HomotopyCategory (R := R) C) :=
  inferInstanceAs (Preadditive (Quotient homotopic))

/-- The quotient functor from closed degree-zero morphisms to the homotopy category. -/
def quotient : Z0 (R := R) C ⥤ HomotopyCategory (R := R) C := Quotient.functor _

instance additiveQuotient : (Quotient.functor (homotopic (R := R) (C := C))).Additive where

instance : (quotient (R := R) (C := C)).Additive :=
  inferInstanceAs ((Quotient.functor homotopic).Additive)

instance : Linear R (HomotopyCategory (R := R) C) := Quotient.linear R homotopic
  (fun _ _ _ _ _ h ↦ ⟨h.some.smul _⟩)

instance : (quotient (R := R) (C := C)).Full := Quotient.full_functor _

instance : (quotient (R := R) (C := C)).EssSurj := Quotient.essSurj_functor _

theorem quotient_map_eq_iff {X Y : Z0 C} (f g : X ⟶ Y) :
    quotient.map f = quotient.map g ↔
      Nonempty (Homotopy (ForgetEnrichment.homTo V f) (ForgetEnrichment.homTo V g)) :=
  Quotient.functor_map_eq_iff _ _ _

end HomotopyCategory

variable {D : Type u₂} [DGCategory R D]

instance (F : EnrichedFunctor V C D) : F.forget.Additive where
  map_add {_ _ _ _}:= by
    apply_fun ForgetEnrichment.homTo V
    · exact Preadditive.add_comp ..
    · intro a b h
      simpa

lemma map_homotopic (F : EnrichedFunctor V C D)
    {X Y : Z0 C} {f g : X ⟶ Y} (h : homotopic f g) :
    homotopic (F.forget.map f) (F.forget.map g) :=
  ⟨h.some.compRight (F.map (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y))⟩

/-- The functor `H⁰(F) : H⁰(C) ⥤ H⁰(D)` induced by a DG functor. -/
def homotopyCategoryFunctor (F : EnrichedFunctor V C D) :
    HomotopyCategory (R := R) C ⥤ HomotopyCategory (R := R) D :=
  CategoryTheory.Quotient.lift homotopic
    (F.forget ⋙ HomotopyCategory.quotient)
    (fun _ _ _ _ h ↦ (HomotopyCategory.quotient_map_eq_iff _ _).2 (map_homotopic F h))

instance (F : EnrichedFunctor V C D) : (homotopyCategoryFunctor F).Additive :=
  letI : (HomotopyCategory.quotient ⋙ homotopyCategoryFunctor F).Additive :=
    inferInstanceAs (F.forget ⋙ HomotopyCategory.quotient (R := R) (C := D)).Additive
  Functor.additive_of_full_essSurj_comp HomotopyCategory.quotient (homotopyCategoryFunctor F)

end DGCategory
