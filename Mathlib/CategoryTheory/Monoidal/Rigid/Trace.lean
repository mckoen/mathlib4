/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.Pivotal

/-!
# Traces in pivotal categories

The left and right traces of an endomorphism in a pivotal category.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RigidCategory C] [PivotalCategory C]

/-- The left trace of an endomorphism in a pivotal category. -/
def leftTrace {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  letI := pivotalExactPairing X
  η_ Xᘁ X ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ

/-- The right trace of an endomorphism in a pivotal category. -/
def rightTrace {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  letI := pivotalExactPairing X
  η_ X Xᘁ ≫ f ▷ Xᘁ ≫ ε_ Xᘁ X

lemma leftTrace_cyclic {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    leftTrace (f ≫ g) = leftTrace (g ≫ f) := by
  letI : HasLeftDual X := { leftDual := Xᘁ, exact := pivotalExactPairing X }
  letI : HasLeftDual Y := { leftDual := Yᘁ, exact := pivotalExactPairing Y }
  simp only [leftTrace, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  erw [← coevaluation_comp_leftAdjointMate_assoc f]
  rw [pivotal_adjointMate]
  erw [← whisker_exchange_assoc]
  rw [rightAdjointMate_comp_evaluation]
  rfl

lemma rightTrace_cyclic {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    rightTrace (f ≫ g) = rightTrace (g ≫ f) := by
  letI : HasLeftDual X := { leftDual := Xᘁ, exact := pivotalExactPairing X }
  letI : HasLeftDual Y := { leftDual := Yᘁ, exact := pivotalExactPairing Y }
  rw [rightTrace, rightTrace, comp_whiskerRight_assoc]
  erw [← leftAdjointMate_comp_evaluation g]
  rw [pivotal_adjointMate, ← whisker_exchange_assoc,
    coevaluation_comp_rightAdjointMate_assoc g]
  erw [← comp_whiskerRight_assoc]
  rfl

section

variable {X : C} {f g : X ⟶ X}

variable [Preadditive C] [MonoidalPreadditive C]

@[simp]
lemma leftTrace_zero : leftTrace (0 : X ⟶ X) = 0 := by simp [leftTrace]

@[simp]
lemma rightTrace_zero : rightTrace (0 : X ⟶ X) = 0 := by simp [rightTrace]

@[simp]
lemma leftTrace_add : leftTrace (f + g) = leftTrace f + leftTrace g := by simp [leftTrace]

@[simp]
lemma rightTrace_add : rightTrace (f + g) = rightTrace f + rightTrace g := by simp [rightTrace]

@[simp]
lemma leftTrace_neg : leftTrace (-f) = - leftTrace f := by
  simp [eq_neg_iff_add_eq_zero, ← leftTrace_add]

@[simp]
lemma rightTrace_neg : rightTrace (-f) = - rightTrace f := by
  simp [eq_neg_iff_add_eq_zero, ← rightTrace_add]

@[simp]
lemma leftTrace_sub : leftTrace (f - g) = (leftTrace f) - (leftTrace g) := by
  simp [sub_eq_add_neg]

@[simp]
lemma rightTrace_sub : rightTrace (f - g) = (rightTrace f) - (rightTrace g) := by
  simp [sub_eq_add_neg]

variable {R : Type*} [CommRing R]

@[simp]
lemma leftTrace_smul [Linear R C] [MonoidalLinear R C] (a : R) :
    leftTrace (a • f) = a • (leftTrace f) := by
  simp [leftTrace]

@[simp]
lemma rightTrace_smul [Linear R C] [MonoidalLinear R C] (a : R) :
    rightTrace (a • f) = a • (rightTrace f) := by
  simp [rightTrace]

end

end CategoryTheory
