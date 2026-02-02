/-
Copyright (c) 2026 Jack McKoen~. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Subobject.Basic

/-!

# Subojects in adhesive categories

## Main Results
- Subobjects in adhesive categories have binary coproducts

-/

@[expose] public section

namespace CategoryTheory

open Limits Subobject

universe v u

variable {C : Type u} [Category.{v} C]

instance [Adhesive C] {X : C} (a b : Subobject X) : HasColimit (pair a b) where
  exists_colimit := ⟨{
    cocone := {
      pt := mk (pushout.desc a.arrow b.arrow pullback.condition)
      ι := {
        app := by
          rintro ⟨_ | _⟩
          · exact (le_mk_of_comm (pushout.inl _ _) (pushout.inl_desc _ _ _)).hom
          · exact (le_mk_of_comm (pushout.inr _ _) (pushout.inr_desc _ _ _)).hom }}
    isColimit := {
      desc s := (mk_le_of_comm
        (pushout.desc (underlying.map (s.ι.app ⟨WalkingPair.left⟩))
        (underlying.map (s.ι.app ⟨WalkingPair.right⟩))
        (by ext; simp [pullback.condition])) (by cat_disch)).hom }}⟩

instance [Adhesive C] {X : C} : HasBinaryCoproducts (Subobject X) := by
  apply hasBinaryCoproducts_of_hasColimit_pair

end CategoryTheory
