/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Trace
public import Mathlib.CategoryTheory.Quotient

/-!
# Spherical monoidal categories

A pivotal category is spherical when its left and right traces agree.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- A pivotal category is spherical when its left and right traces agree. -/
class SphericalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [PivotalCategory C] : Prop where
  leftTrace_eq_rightTrace {X : C} (f : X ⟶ X) : leftTrace f = rightTrace f

/-- The trace in a spherical category. -/
def SphericalCategory.trace [PivotalCategory C] [SphericalCategory C]
    {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  leftTrace f

variable [PivotalCategory C] [SphericalCategory C]

lemma SphericalCategory.trace_eq_leftTrace {X : C} (f : X ⟶ X) : trace f = leftTrace f := rfl

lemma SphericalCategory.trace_eq_rightTrace {X : C} (f : X ⟶ X) : trace f = rightTrace f :=
  leftTrace_eq_rightTrace f

section Negligible

open SphericalCategory

variable [Preadditive C]

class Negligible {X Y : C} (f : X ⟶ Y) : Prop where
  trace_zero : ∀ h : Y ⟶ X, trace (f ≫ h) = 0

lemma sub_negligible_iff [MonoidalPreadditive C] {X Y : C} [HasRightDual X] {f g : X ⟶ Y} :
    Negligible (f - g) ↔
      ∀ h : Y ⟶ X, trace (f ≫ h) = trace (g ≫ h) := by
  constructor
  · intro r h
    simp only [trace_eq_leftTrace]
    rw [← sub_eq_zero, ← leftTrace_sub, ← Preadditive.sub_comp]
    exact r.trace_zero h
  · intro r
    constructor
    intro h
    simp only [trace_eq_leftTrace, Preadditive.sub_comp, leftTrace_sub, sub_eq_zero]
    exact r h

instance comp_negligible_of_left {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [hn : Negligible f] :
    Negligible (f ≫ g) where
  trace_zero h := by simpa only [Category.assoc] using hn.trace_zero (g ≫ h)

instance comp_negligible_of_right {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [hn : Negligible g] :
    Negligible (f ≫ g) where
  trace_zero h := by
    simp only [trace_eq_leftTrace]
    rw [Category.assoc, leftTrace_cyclic, Category.assoc]
    exact hn.trace_zero (h ≫ f)

instance zero_negligible [MonoidalPreadditive C] {X Y : C} :
    Negligible (0 : X ⟶ Y) where
  trace_zero h := by simp [trace_eq_leftTrace]

instance sub_negligible_comm [MonoidalPreadditive C] {X Y : C} {f g : X ⟶ Y}
    [Negligible (f - g)] :
  Negligible (g - f) := by rw [sub_negligible_iff] at *; grind

instance sub_add_negligible [MonoidalPreadditive C] {X Y : C} (f₁ f₂ g₁ g₂ : X ⟶ Y)
    [hf : Negligible (f₁ - f₂)] [hg : Negligible (g₁ - g₂)] :
    Negligible ((f₁ + g₁) - (f₂ + g₂)) where
  trace_zero h := by
    calc
      _ = (trace (((f₁ - f₂) + (g₁ - g₂)) ≫ h)) := by congr; grind
      _ = _ := by
        rw [Preadditive.add_comp, trace_eq_leftTrace, leftTrace_add]
        simp only [← trace_eq_leftTrace]
        grind [hf.trace_zero h, hg.trace_zero h]

instance whiskerLeft_negligible {X Y : C} {f : X ⟶ Y} {W : C} [hf : Negligible f] :
    Negligible (W ◁ f) where
  trace_zero h := by
    sorry

instance whiskerRight_negligible {X Y : C} {f : X ⟶ Y} {W : C} [hf : Negligible f] :
    Negligible (f ▷ W) where
  trace_zero h := by
    sorry

instance smul_negligible {R : Type*} [CommRing R] [Linear R C] [MonoidalPreadditive C]
    [MonoidalLinear R C] {X Y : C} {f : X ⟶ Y} (a : R) [hf : Negligible f] :
    Negligible (a • f) where
  trace_zero h := by
    rw [Linear.smul_comp, trace_eq_leftTrace, leftTrace_smul]
    exact smul_eq_zero_of_right a (hf.trace_zero h)

instance [MonoidalPreadditive C] :
    Congruence (C := C) (fun _ _ f g ↦ Negligible (f - g)) where
  comp_left _ _ _ _ := by rw [← Preadditive.comp_sub]; infer_instance
  comp_right _ _ := by rw [← Preadditive.sub_comp]; infer_instance
  equivalence {X Y} := {
    refl _ := by rw [sub_self]; infer_instance
    symm _ := inferInstance
    trans r₁ r₂ := by
      rw [sub_negligible_iff] at r₁ r₂ ⊢
      grind }

end Negligible

end CategoryTheory
