/-
Copyright (c) 2025 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal structure on the arrow category

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite Limits MonoidalCategory

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

section Defs

variable [HasPushouts C₃] {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂)

/-- The pushout-product of `f` and `g`. -/
@[simp]
noncomputable
abbrev Functor.pushoutProduct := (Functor.PushoutObjObj.ofHasPushout F f₁ f₂).ι

notation3 f₁ " [" F "] " f₂:10 => Functor.pushoutProduct F f₁ f₂

end Defs

section Functor

@[simp]
noncomputable
def leftFunctor_map_left (f₁ : Arrow C₁) {f₂ f₂' : Arrow C₂} (sq : f₂ ⟶ f₂')
    (sq₁₂ : F.PushoutObjObj f₁.hom f₂.hom)
    (sq₁₂' : F.PushoutObjObj f₁.hom f₂'.hom) :
    sq₁₂.pt ⟶ sq₁₂'.pt := by
  refine sq₁₂.isPushout.desc ?_ ?_ ?_
  · exact ((F.obj f₁.right).map sq.left) ≫ sq₁₂'.inl
  · exact ((F.obj f₁.left).map sq.right) ≫ sq₁₂'.inr
  · simp
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp]
    erw [← sq.w, ← (F.map f₁.hom).naturality sq.left]
    have := sq₁₂'.isPushout.w
    dsimp at this ⊢
    simp only [this, Functor.map_comp, Category.assoc]

@[simp]
noncomputable
def leftFunctor_map (f₁ : Arrow C₁) {f₂ f₂' : Arrow C₂} (sq : f₂ ⟶ f₂')
    (sq₁₂ : F.PushoutObjObj f₁.hom f₂.hom)
    (sq₁₂' : F.PushoutObjObj f₁.hom f₂'.hom) :
    Arrow.mk sq₁₂.ι ⟶ Arrow.mk sq₁₂'.ι where
  left := leftFunctor_map_left F f₁ sq sq₁₂ sq₁₂'
  right := (F.obj f₁.right).map sq.right
  w := by
    dsimp
    apply sq₁₂.isPushout.hom_ext
    · simp only [Functor.id_obj, IsPushout.inl_desc_assoc, Category.assoc,
        Functor.PushoutObjObj.inl_ι, ← Functor.map_comp, Arrow.w_mk_right, Arrow.mk_right,
        Functor.PushoutObjObj.inl_ι_assoc]
    · simp only [Functor.id_obj, IsPushout.inr_desc_assoc, Category.assoc,
        Functor.PushoutObjObj.inr_ι, NatTrans.naturality, Functor.PushoutObjObj.inr_ι_assoc]

@[simp]
noncomputable
def leftFunctor [HasPushouts C₃] (f₁ : Arrow C₁) : Arrow C₂ ⥤ Arrow C₃ where
  obj f₂ := f₁.hom [F] f₂.hom
  map sq := leftFunctor_map F f₁ sq (Functor.PushoutObjObj.ofHasPushout _ _ _)
    (Functor.PushoutObjObj.ofHasPushout _ _ _)

@[simp]
noncomputable
def leftBifunctor_map_left {f₁ f₁' : Arrow C₁} (f₂ : Arrow C₂) (sq : f₁ ⟶ f₁')
    (sq₁₂ : F.PushoutObjObj f₁.hom f₂.hom)
    (sq₁₂' : F.PushoutObjObj f₁'.hom f₂.hom) :
    sq₁₂.pt ⟶ sq₁₂'.pt := by
  refine sq₁₂.isPushout.desc ?_ ?_ ?_
  · exact (F.map sq.right).app f₂.left ≫ sq₁₂'.inl
  · exact (F.map sq.left).app f₂.right ≫ sq₁₂'.inr
  · simp
    rw [← Category.assoc, ← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp]
    erw [← sq.w]
    dsimp only [Functor.id_obj, Functor.id_map]
    rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, Category.assoc]
    have := sq₁₂'.isPushout.w
    dsimp at this ⊢
    rw [← this]

@[simp]
noncomputable
def leftBifunctor_map [HasPushouts C₃] {f₁ f₁' : Arrow C₁} (sq : f₁ ⟶ f₁') :
    leftFunctor F f₁ ⟶ leftFunctor F f₁' where
  app f₂ := {
    left := leftBifunctor_map_left F f₂ sq (Functor.PushoutObjObj.ofHasPushout _ _ _)
      (Functor.PushoutObjObj.ofHasPushout _ _ _)
    right := (F.map sq.right).app f₂.right
    w := by
      apply pushout.hom_ext
      · simp [Functor.PushoutObjObj.ι]
      · simp [Functor.PushoutObjObj.ι, ← NatTrans.comp_app, ← Functor.map_comp] }
  naturality f' g' sq' := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      all_goals simp
    · simp [Functor.PushoutObjObj.ι]

@[simps!]
noncomputable
def leftBifunctor [HasPushouts C₃] : Arrow C₁ ⥤ Arrow C₂ ⥤ Arrow C₃ where
  obj := leftFunctor F
  map := leftBifunctor_map F

end Functor

end CategoryTheory
