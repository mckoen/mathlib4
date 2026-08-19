/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# DG categories

A DG category over a commutative ring is a category enriched in cochain complexes of
modules. This file also constructs its ordinary category `Z0` of closed degree-zero
morphisms and equips that category with its natural preadditive and linear structures.
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory ForgetEnrichment

variable {R : Type w} [CommRing R]

/-- A category enriched over cochain complexes of `R`-modules. -/
abbrev DGCategory (R : Type w) [CommRing R] :=
  EnrichedCategory (CochainComplex (ModuleCat.{w} R) ℤ)

noncomputable section

namespace DGCategory

local notation "V" => CochainComplex (ModuleCat R) ℤ

open HomologicalComplex

lemma tensor_add_left {A B C D : V} (f g : A ⟶ B) (h : C ⟶ D) :
    (f + g) ⊗ₘ h = f ⊗ₘ h + g ⊗ₘ h := by
  change mapBifunctorMap (f + g) h .. = mapBifunctorMap f h .. + mapBifunctorMap g h ..
  ext1 n
  apply mapBifunctor.hom_ext
  simp

lemma tensor_add_right {A B C D : V} (f : A ⟶ B) (g h : C ⟶ D) :
    f ⊗ₘ (g + h) = f ⊗ₘ g + f ⊗ₘ h := by
  change mapBifunctorMap f (g + h) .. = mapBifunctorMap f g .. + mapBifunctorMap f h ..
  ext1 n
  apply mapBifunctor.hom_ext
  simp

lemma tensor_smul_left {A B C D : V} (r : R) (f : A ⟶ B) (h : C ⟶ D) :
    (r • f) ⊗ₘ h = r • (f ⊗ₘ h) := by
  change mapBifunctorMap (r • f) h .. = r • mapBifunctorMap f h ..
  ext1 n
  apply mapBifunctor.hom_ext
  simp

lemma tensor_smul_right {A B C D : V} (r : R) (f : A ⟶ B) (h : C ⟶ D) :
    f ⊗ₘ (r • h) = r • (f ⊗ₘ h) := by
  change mapBifunctorMap f (r • h) .. = r • mapBifunctorMap f h ..
  ext1 n
  apply mapBifunctor.hom_ext
  simp

/-- The category with the same objects as a DG category and closed degree-zero morphisms. -/
abbrev Z0 (C : Type u) [DGCategory R C] := ForgetEnrichment V C

variable {C : Type u} [DGCategory R C]

instance (X Y : Z0 (R := R) C) : AddCommGroup (X ⟶ Y) := inferInstanceAs
  (AddCommGroup (𝟙_ V ⟶ ((ForgetEnrichment.to V X) ⟶[V] (ForgetEnrichment.to V Y))))

instance (X Y : Z0 (R := R) C) : Module R (X ⟶ Y) := inferInstanceAs
  (Module R (𝟙_ V ⟶ ((ForgetEnrichment.to V X) ⟶[V] (ForgetEnrichment.to V Y))))

set_option backward.isDefEq.respectTransparency false in
instance z0Preadditive : Preadditive (Z0 (R := R) C) where
  homGroup X Y := inferInstance
  add_comp := by
    intro X Y Z f g h
    change (λ_ (𝟙_ V)).inv ≫ ((f + g) ⊗ₘ h) ≫ _ = _
    rw [tensor_add_left]
    simp only [Preadditive.comp_add, Preadditive.add_comp]
    rfl
  comp_add := by
    intro X Y Z f g h
    change (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ (g + h)) ≫ _ = _
    rw [tensor_add_right]
    simp only [Preadditive.comp_add, Preadditive.add_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
instance z0Linear : Linear R (Z0 (R := R) C) where
  homModule X Y := inferInstance
  smul_comp := by
    intro X Y Z r f g
    change (λ_ (𝟙_ V)).inv ≫ ((r • f) ⊗ₘ g) ≫ _ = _
    rw [tensor_smul_left]
    simp only [Linear.comp_smul, Linear.smul_comp]
    rfl
  comp_smul := by
    intro X Y Z f r g
    change (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ (r • g)) ≫ _ = _
    rw [tensor_smul_right]
    simp only [Linear.comp_smul, Linear.smul_comp]
    rfl

end DGCategory
