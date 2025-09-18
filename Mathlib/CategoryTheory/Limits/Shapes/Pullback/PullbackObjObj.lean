/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
#

Let `F : C₁ ⥤ C₂ ⥤ C₃`. Given morphisms `f₁ : X₁ ⟶ Y₁` in `C₁`
and `f₂ : X₂ ⟶ Y₂` in `C₂`, we introduce a structure
`F.PushoutObjObj f₁ f₂` which contains the data of a
pushout of `(F.obj Y₁).obj X₂` and `(F.obj X₁).obj Y₂`
along `(F.obj X₁).obj X₂`. If `sq₁₂ : F.PushoutObjObj f₁ f₂`,
we have a canonical "inclusion" `sq₁₂.ι : sq₁₂.pt ⟶ (F.obj Y₁).obj Y₂`.

Similarly, if we have a bifunctor `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`, and
morphisms `f₁ : X₁ ⟶ Y₁` in `C₁` and `f₃ : X₃ ⟶ Y₃` in `C₃`,
we introduce a structure `F.PullbackObjObj f₁ f₃` which
contains the data of a pullback of `(G.obj (op X₁)).obj X₃`
and `(G.obj (op Y₁)).obj Y₃` over `(G.obj (op X₁)).obj Y₃`.
If `sq₁₃ : F.PullbackObjObj f₁ f₃`, we have a canonical
projection `sq₁₃.π : (G.obj Y₁).obj X₃ ⟶ sq₁₃.pt`.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

namespace Functor

section

variable {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂)

/-- Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C₃`, and morphisms `f₁ : X₁ ⟶ Y₁` in `C₁`
and `f₂ : X₂ ⟶ Y₂` in `C₂`, this structure contains the data of
a pushout of `(F.obj Y₁).obj X₂` and `(F.obj X₁).obj Y₂`
along `(F.obj X₁).obj X₂`. -/
structure PushoutObjObj where
  /-- the pushout -/
  pt : C₃
  /-- the first inclusion -/
  inl : (F.obj Y₁).obj X₂ ⟶ pt
  /-- the second inclusion -/
  inr : (F.obj X₁).obj Y₂ ⟶ pt
  isPushout : IsPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂) inl inr

namespace PushoutObjObj

/-- The `PushoutObjObj` structure given by the pushout of the colimits API. -/
@[simps]
noncomputable def ofHasPushout
    [HasPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂)] :
    F.PushoutObjObj f₁ f₂ :=
  { isPushout := IsPushout.of_hasPushout _ _, .. }

variable {F f₁ f₂} (sq : F.PushoutObjObj f₁ f₂)

/-- The "inclusion" `sq.pt ⟶ (F.obj Y₁).obj Y₂` when
`sq : F.PushoutObjObj f₁ f₂`. -/
noncomputable def ι : sq.pt ⟶ (F.obj Y₁).obj Y₂ :=
  sq.isPushout.desc ((F.obj Y₁).map f₂) ((F.map f₁).app Y₂) (by simp)

@[reassoc (attr := simp)]
lemma inl_ι : sq.inl ≫ sq.ι = (F.obj Y₁).map f₂ := by simp [ι]

@[reassoc (attr := simp)]
lemma inr_ι : sq.inr ≫ sq.ι = (F.map f₁).app Y₂ := by simp [ι]

/-- Given `sq : F.PushoutObjObj f₁ f₂`, flipping the pushout square gives
`sq.flip : F.flip.PushoutObjObj f₂ f₁`. -/
@[simps]
def flip : F.flip.PushoutObjObj f₂ f₁ where
  pt := sq.pt
  inl := sq.inr
  inr := sq.inl
  isPushout := sq.isPushout.flip

@[simp]
lemma ι_flip : sq.flip.ι = sq.ι := by
  apply sq.flip.isPushout.hom_ext
  · rw [inl_ι, flip_inl, inr_ι, flip_obj_map]
  · rw [inr_ι, flip_inr, inl_ι, flip_map_app]

end PushoutObjObj

end

section

variable {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₃ Y₃ : C₃} (f₃ : X₃ ⟶ Y₃)

/-- Given a bifunctor `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`, and morphisms `f₁ : X₁ ⟶ Y₁` in `C₁`
and `f₃ : X₃ ⟶ Y₃` in `C₃`, this structure contains the data of
a pullback of `(G.obj (op X₁)).obj X₃`
and `(G.obj (op Y₁)).obj Y₃` over `(G.obj (op X₁)).obj Y₃`. -/
structure PullbackObjObj where
  /-- the pullback -/
  pt : C₂
  /-- the first projection -/
  fst : pt ⟶ (G.obj (op X₁)).obj X₃
  /-- the second projection -/
  snd : pt ⟶ (G.obj (op Y₁)).obj Y₃
  isPullback : IsPullback fst snd ((G.obj (op X₁)).map f₃)
    ((G.map f₁.op).app Y₃)

namespace PullbackObjObj

/-- The `PullbackObjObj` structure given by the pullback of the limits API. -/
@[simps]
noncomputable def ofHasPullback
    [HasPullback ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)] :
    G.PullbackObjObj f₁ f₃ :=
  { isPullback := IsPullback.of_hasPullback _ _, ..}

variable {G f₁ f₃} (sq : G.PullbackObjObj f₁ f₃)

/-- The projection `(G.obj (op Y₁)).obj X₃ ⟶ sq.pt` when
`sq : G.PullbackObjObj f₁ f₃`. -/
noncomputable def π : (G.obj (op Y₁)).obj X₃ ⟶ sq.pt :=
  sq.isPullback.lift ((G.map f₁.op).app X₃) ((G.obj (op Y₁)).map f₃) (by simp)

@[reassoc (attr := simp)]
lemma π_fst : sq.π ≫ sq.fst = (G.map f₁.op).app X₃ := by simp [π]

@[reassoc (attr := simp)]
lemma π_snd : sq.π ≫ sq.snd = (G.obj (op Y₁)).map f₃ := by simp [π]

end PullbackObjObj

end

end Functor

end CategoryTheory
