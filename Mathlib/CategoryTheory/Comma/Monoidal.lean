/-
Copyright (c) 2025 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Monoidal structure on the arrow category

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

end CategoryTheory
