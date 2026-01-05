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

universe v u

namespace CategoryTheory.Arrow

open Opposite Limits MonoidalCategory Functor PushoutProduct

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (F : C ⥤ C ⥤ C) (G : Cᵒᵖ ⥤ C ⥤ C)



noncomputable
instance [HasPushouts C] [HasInitial C] : MonoidalCategory (Arrow C) where
  tensorObj X Y := ((leftBifunctor F).obj X).obj Y
  whiskerLeft X _ _ f := ((leftBifunctor F).obj X).map f
  whiskerRight f X := ((leftBifunctor F).map f).app X
  tensorUnit := Arrow.mk (initial.to (𝟙_ C))
  associator X Y Z := by

    sorry
  leftUnitor X := sorry
  rightUnitor X := sorry

end CategoryTheory.Arrow
