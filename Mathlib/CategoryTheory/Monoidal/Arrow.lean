/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Monoidal structure on the arrow category

-/

universe v v₁ u u₁

namespace CategoryTheory

open Opposite Limits MonoidalCategory Functor PushoutObjObj

variable {C : Type u} [Category.{v} C]

attribute [local simp] PushoutObjObj.ι ofHasPushout_pt ofHasPushout_inl ofHasPushout_inr

section IsPushout

namespace IsPushout

variable [MonoidalCategory C] {Z X Y P W : C} {f : Z ⟶ X} {g : Z ⟶ Y}
    {inl : X ⟶ P} {inr : Y ⟶ P} (hP : IsPushout f g inl inr)
    {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k)

@[reassoc (attr := simp)]
lemma whiskerLeft_inl_desc {Q : C} :
    Q ◁ inl ≫ Q ◁ hP.desc h k w = Q ◁ h := by
  rw [← MonoidalCategory.whiskerLeft_comp, inl_desc]

@[reassoc (attr := simp)]
lemma whiskerLeft_inr_desc {Q : C} :
    Q ◁ inr ≫ Q ◁ hP.desc h k w = Q ◁ k := by
  rw [← MonoidalCategory.whiskerLeft_comp, inr_desc]

@[reassoc (attr := simp)]
lemma inl_desc_whiskerRight {Q : C} :
    inl ▷ Q ≫ hP.desc h k w ▷ Q = h ▷ Q := by
  rw [← comp_whiskerRight, inl_desc]

@[reassoc (attr := simp)]
lemma inr_desc_whiskerRight {Q : C} :
    inr ▷ Q ≫ hP.desc h k w ▷ Q = k ▷ Q := by
  rw [← comp_whiskerRight, inr_desc]

@[reassoc]
lemma whiskerLeft_w (hP : IsPushout f g inl inr) {Q : C} :
    Q ◁ f ≫ Q ◁ inl = Q ◁ g ≫ Q ◁ inr := by
  simp [← MonoidalCategory.whiskerLeft_comp, hP.w]

@[reassoc]
lemma w_whiskerRight (hP : IsPushout f g inl inr) {Q : C} :
    f ▷ Q ≫ inl ▷ Q = g ▷ Q ≫ inr ▷ Q := by
  simp [← MonoidalCategory.comp_whiskerRight, hP.w]

end IsPushout

end IsPushout

section Pushout

variable [HasPushouts C] [MonoidalCategory C]
  {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) {Q : C}

@[reassoc]
lemma Limits.pushout.whiskerLeft_condition :
    Q ◁ f ≫ Q ◁ inl f g = Q ◁ g ≫ Q ◁ inr f g := by
  simp [← MonoidalCategory.whiskerLeft_comp, pushout.condition]

@[reassoc]
lemma Limits.pushout.condition_whiskerRight :
    f ▷ Q ≫ inl f g ▷ Q = g ▷ Q ≫ inr f g ▷ Q := by
  simp [← comp_whiskerRight, pushout.condition]

variable {A B X Y Z W : C} {f : A ⟶ B} {g : X ⟶ Y}

@[reassoc]
lemma Limits.pushout.associator_naturality_left_condition {h : Z ⊗ W ⟶ X} :
    f ▷ Z ▷ W ≫ (α_ B Z W).hom ≫ B ◁ h ≫ inl (f ▷ X) (A ◁ g) =
      (α_ A Z W).hom ≫ A ◁ (h ≫ g) ≫ inr (f ▷ X) (A ◁ g) := by
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, pushout.condition,
    ← MonoidalCategory.whiskerLeft_comp_assoc]

@[reassoc]
lemma Limits.pushout.associator_inv_naturality_right_condition {h : Z ⊗ W ⟶ A} :
    Z ◁ W ◁ g ≫ (α_ Z W Y).inv ≫ h ▷ Y ≫ inr (f ▷ X) (A ◁ g) =
      (α_ Z W X).inv ≫ (h ≫ f) ▷ X ≫ inl (f ▷ X) (A ◁ g) := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← pushout.condition,
    ← comp_whiskerRight_assoc]

end Pushout

@[simp]
noncomputable
abbrev pushoutProduct [HasPushouts C] [MonoidalCategory C] := (curriedTensor C).leibnizPushout

/-- Notation for the pushout-product of morphisms. -/
notation3 f " □ " g:10 => (pushoutProduct.obj f).obj g

namespace Arrow

section Monoidal

variable [HasPushouts C] [MonoidalCategory C] (X₁ X₂ X₃ : Arrow C) {W : C}

@[simps!]
noncomputable
def PushoutProduct.whiskerRight_iso
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight W)] :
    Arrow.mk ((X₁ □ X₂).hom ▷ W) ≅ (X₁ □ (X₂.hom ▷ W)) := by
  dsimp
  exact
  Arrow.isoMk (((tensorRight W).map_isPushout (IsPushout.of_hasPushout _ _)).isoPushout ≪≫
    HasColimit.isoOfNatIso (spanExt (α_ _ _ W) (α_ _ _ W) (α_ _ _ W)
      (associator_naturality_left _ _ W).symm (associator_naturality_middle _ _ W).symm)) (α_ _ _ W)
    (((tensorRight W).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext (by simp) (by simp))

@[simps!]
noncomputable
def PushoutProduct.whiskerLeft_iso
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorLeft W)] :
    Arrow.mk (W ◁ (X₁ □ X₂).hom) ≅ ((W ◁ X₁.hom) □ X₂) := by
  dsimp
  exact
  Arrow.isoMk (((tensorLeft W).map_isPushout (IsPushout.of_hasPushout _ _)).isoPushout ≪≫
    HasColimit.isoOfNatIso (spanExt (α_ W _ _).symm (α_ W _ _).symm (α_ W _ _).symm
      (associator_inv_naturality_middle W _ _).symm (associator_inv_naturality_right W _ _).symm))
    (α_ W _ _).symm
    (((tensorLeft W).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext (by simp) (by simp))

@[simps]
noncomputable
def PushoutProduct.associator_iso_left
    [PreservesColimit (span (X₂.hom ▷ X₃.left) (X₂.left ◁ X₃.hom)) (tensorLeft X₁.left)]
    [PreservesColimit (span (X₂.hom ▷ X₃.left) (X₂.left ◁ X₃.hom)) (tensorLeft X₁.right)]
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight X₃.left)]
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight X₃.right)] :
    (ofHasPushout (curriedTensor C) (X₁ □ X₂).hom X₃.hom).pt ≅
      (ofHasPushout (curriedTensor C) X₁.hom (X₂ □ X₃).hom).pt where
  hom := by
    dsimp
    exact
      pushout.desc ((α_ _ _ _).hom ≫ _ ◁ pushout.inl _ _ ≫ pushout.inl _ _)
        ((whiskerRight_iso _ _).hom.left ≫
          pushout.desc (_ ◁ pushout.inr _ _ ≫ pushout.inl _ _) (pushout.inr _ _)
          (by simp [pushout.associator_naturality_left_condition]))
        (((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        (by simp [pushout.whiskerLeft_condition_assoc, ← whisker_exchange_assoc])
        (by simp [← whisker_exchange_assoc, pushout.associator_naturality_left_condition]))
  inv := by
    dsimp
    exact
      pushout.desc ((whiskerLeft_iso _ _).hom.left ≫
        pushout.desc (pushout.inl _ _) ((pushout.inl _ _ ▷ _) ≫ pushout.inr _ _)
          (by simp [pushout.associator_inv_naturality_right_condition]))
        ((α_ _ _ _).inv ≫ (pushout.inr _ _) ▷ _ ≫ pushout.inr _ _)
        (((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        (by simp [whisker_exchange_assoc, pushout.associator_inv_naturality_right_condition])
        (by simp [whisker_exchange_assoc, pushout.condition_whiskerRight_assoc]))
  hom_inv_id := by
    ext
    · simp
    · dsimp; apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
  inv_hom_id := by
    ext
    · dsimp; apply ((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
    · simp

@[simps!]
noncomputable
def PushoutProduct.associator
    [PreservesColimit (span (X₂.hom ▷ X₃.left) (X₂.left ◁ X₃.hom)) (tensorLeft X₁.left)]
    [PreservesColimit (span (X₂.hom ▷ X₃.left) (X₂.left ◁ X₃.hom)) (tensorLeft X₁.right)]
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight X₃.left)]
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight X₃.right)] :
    ((X₁ □ X₂) □ X₃) ≅ X₁ □ X₂ □ X₃ := by
  dsimp
  refine Arrow.isoMk (associator_iso_left X₁ X₂ X₃) (α_ X₁.right X₂.right X₃.right) ?_
  · apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp]
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight_assoc]
      · simp [← MonoidalCategory.comp_whiskerRight_assoc]

@[simps!]
noncomputable
def PushoutProduct.braiding [BraidedCategory C] (X Y : Arrow C) : (X □ Y) ≅ (Y □ X) :=
  Arrow.isoMk (pushoutSymmetry .. ≪≫
    (HasColimit.isoOfNatIso (spanExt (β_ _ _) (β_ _ _) (β_ _ _)
    (BraidedCategory.braiding_naturality_right ..).symm
    (BraidedCategory.braiding_naturality_left ..).symm))) (β_ _ _) (by cat_disch)

section Pentagon

omit [HasPushouts C]

variable {Z X Y P W : C} {f : Z ⟶ X} {g : Z ⟶ Y}
    {inl : X ⟶ P} {inr : Y ⟶ P} (hP : IsPushout f g inl inr)
    {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k)

--not needed
@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.IsPushout.whiskerLeft_inl_isoPushout_inv [HasPushout f g] {Q : C} :
    Q ◁ pushout.inl _ _ ≫ Q ◁ hP.isoPushout.inv = Q ◁ inl := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.IsPushout.whiskerLeft_inr_isoPushout_inv [HasPushout f g] {Q : C} :
    Q ◁ pushout.inr _ _ ≫ Q ◁ hP.isoPushout.inv = Q ◁ inr := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.IsPushout.whiskerLeft_inl_isoPushout_hom [HasPushout f g] {Q : C} :
    Q ◁ inl ≫ Q ◁ hP.isoPushout.hom = Q ◁ pushout.inl _ _ := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.IsPushout.whiskerLeft_inr_isoPushout_hom [HasPushout f g] {Q : C} :
    Q ◁ inr ≫ Q ◁ hP.isoPushout.hom = Q ◁ pushout.inr _ _ := by
  simp [← MonoidalCategory.whiskerLeft_comp]

--not needed
@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.IsPushout.inl_isoPushout_inv_whiskerRight [HasPushout f g] {Q : C} :
    pushout.inl _ _ ▷ Q ≫ hP.isoPushout.inv ▷ Q = inl ▷ Q := by
  simp [← comp_whiskerRight]

--not needed
@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.IsPushout.inr_isoPushout_inv_whiskerRight [HasPushout f g] {Q : C} :
    pushout.inr _ _ ▷ Q ≫ hP.isoPushout.inv ▷ Q = inr ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.IsPushout.inl_isoPushout_hom_whiskerRight [HasPushout f g] {Q : C} :
    inl ▷ Q ≫ hP.isoPushout.hom ▷ Q = pushout.inl _ _ ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.IsPushout.inr_isoPushout_hom_whiskerRight [HasPushout f g] {Q : C} :
    inr ▷ Q ≫ hP.isoPushout.hom ▷ Q = pushout.inr _ _ ▷ Q := by
  simp [← comp_whiskerRight]

end Pentagon

omit [HasPushouts C] in
@[reassoc]
lemma temp₂ (X₁ X₂ X₃ Y₁ Y₃ : Arrow C) (f₁ : X₁ ⟶ Y₁) (f₃ : X₃ ⟶ Y₃) :
    X₁.right ◁ X₂.left ◁ f₃.right ≫
    (α_ X₁.right X₂.left Y₃.right).inv ≫
    f₁.right ▷ X₂.left ▷ Y₃.right ≫
    (α_ Y₁.right X₂.left Y₃.right).hom =
    (α_ X₁.right X₂.left X₃.right).inv ≫
    f₁.right ▷ X₂.left ▷ X₃.right ≫
    (α_ Y₁.right X₂.left X₃.right).hom ≫
    Y₁.right ◁ X₂.left ◁ f₃.right := by
  simp only [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    ← associator_inv_naturality_left_assoc, associator_naturality_right]

omit [HasPushouts C] in
@[reassoc]
lemma _root_.CategoryTheory.MonoidalCategory.temp₁ (X₁ X₂ X₃ Y₁ Y₂ Y₃ : Arrow C)
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    (α_ X₁.left X₂.right X₃.right).hom ≫
    X₁.left ◁ X₂.right ◁ f₃.right ≫
    (α_ X₁.left X₂.right Y₃.right).inv ≫
    f₁.left ▷ X₂.right ▷ Y₃.right ≫
    (α_ Y₁.left X₂.right Y₃.right).hom ≫
    Y₁.left ◁ f₂.right ▷ Y₃.right =
    f₁.left ▷ X₂.right ▷ X₃.right ≫
    (α_ Y₁.left X₂.right X₃.right).hom ≫
    Y₁.left ◁ f₂.right ▷ X₃.right ≫
    Y₁.left ◁ Y₂.right ◁ f₃.right := by
  simp only [Iso.inv_hom_id_assoc, associator_naturality_left_assoc, whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp, whisker_exchange]

@[reassoc]
lemma _root_.CategoryTheory.MonoidalCategory.temp₃ (X₁ X₂ X₃ Y₁ Y₂ Y₃ : Arrow C)
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    X₁.right ◁ X₂.left ◁ f₃.right ≫
    (α_ X₁.right X₂.left Y₃.right).inv ≫
    f₁.right ▷ X₂.left ▷ Y₃.right ≫
    (α_ Y₁.right X₂.left Y₃.right).hom ≫
    Y₁.right ◁ f₂.left ▷ Y₃.right ≫
    Y₁.right ◁ pushout.inr (Y₂.hom ▷ Y₃.left) (Y₂.left ◁ Y₃.hom) =
    X₁.right ◁ f₂.left ▷ X₃.right ≫
    X₁.right ◁ Y₂.left ◁ f₃.right ≫
    X₁.right ◁ pushout.inr (Y₂.hom ▷ Y₃.left) (Y₂.left ◁ Y₃.hom) ≫
    f₁.right ▷ pushout (Y₂.hom ▷ Y₃.left) (Y₂.left ◁ Y₃.hom) := by
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange, whisker_exchange_assoc,
    ← whisker_exchange, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    ← associator_inv_naturality_left_assoc, associator_naturality_right_assoc, Iso.inv_hom_id_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc]

lemma PushoutProduct.associator_naturality {C : Type u} [Category.{v} C] [HasPushouts C]
    [CartesianMonoidalCategory C]
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Arrow C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((pushoutProduct.map ((pushoutProduct.map f₁).app X₂ ≫
    (pushoutProduct.obj Y₁).map f₂)).app X₃ ≫
    (pushoutProduct.obj (Y₁ □ Y₂)).map f₃) ≫
    (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫
    (pushoutProduct.map f₁).app (X₂ □ X₃) ≫
    (pushoutProduct.obj Y₁).map ((pushoutProduct.map f₂).app X₃ ≫
    (pushoutProduct.obj Y₂).map f₃) := by
  ext
  · apply pushout.hom_ext
    · simp [whisker_exchange_assoc]
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp [← whisker_exchange_assoc, temp₃_assoc]
      · simp [← whisker_exchange_assoc, temp₁_assoc]
  · simp

omit [HasPushouts C] in
@[reassoc (attr := simp)]
lemma Limits.colimit.whiskerLeft_ι_desc {J : Type u₁} [Category.{v₁, u₁} J]
    {F : J ⥤ C} [HasColimit F] (c : Cocone F) (j : J) {Q : C} :
    Q ◁ colimit.ι F j ≫ Q ◁ colimit.desc F c = Q ◁ c.ι.app j := by
  simp [← MonoidalCategory.whiskerLeft_comp]

omit [HasPushouts C] in
@[reassoc (attr := simp)]
lemma Limits.colimit.ι_desc_whiskerRight {J : Type u₁} [Category.{v₁, u₁} J]
    {F : J ⥤ C} [HasColimit F] (c : Cocone F) (j : J) {Q : C} :
    colimit.ι F j ▷ Q ≫ colimit.desc F c ▷ Q = c.ι.app j ▷ Q := by
  simp [← comp_whiskerRight]

/-
lemma PushoutProduct.pentagon
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)]
    (W X Y Z : Arrow C) :
    (pushoutProduct.map (associator W X Y).hom).app Z ≫
      (associator W (X □ Y) Z).hom ≫
        (pushoutProduct.obj W).map (associator X Y Z).hom =
    (associator (W □ X) Y Z).hom ≫
      (associator W X (Y □ Z)).hom := by
  ext
  · apply pushout.hom_ext
    · simp
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp
      · apply ((tensorRight _ ⋙ tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        <;> simp [associator_naturality_left_assoc]
  · exact MonoidalCategory.pentagon W.right X.right Y.right Z.right
-/

end Monoidal

section CartesianMonoidal

variable [HasInitial C] [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C]
  {A B X Y Z W : C} (f : A ⟶ B) (g : X ⟶ Y) (h : Z ⟶ W)

@[simps!]
noncomputable
def PushoutProduct.leftUnitor [BraidedCategory C]
    (X : Arrow C) : (initial.to (𝟙_ C) □ X.hom) ≅ X := by
  refine Arrow.isoMk ?_ (λ_ X.right) ?_
  · refine Iso.mk ?_ ((λ_ X.left).inv ≫ pushout.inl _ _) ?_ ?_
    · refine pushout.desc (λ_ X.left).hom ?_ ?_
      · exact (initialIsInitial.ofIso (mulZero initialIsInitial).symm).to _
      · apply (initialIsInitial.ofIso (mulZero initialIsInitial).symm).hom_ext
    · apply pushout.hom_ext
      · simp
      · apply (initialIsInitial.ofIso (mulZero initialIsInitial).symm).hom_ext
    · simp
  · apply pushout.hom_ext
    · simp
    · apply (initialIsInitial.ofIso (mulZero initialIsInitial).symm).hom_ext

@[simps!]
noncomputable
def PushoutProduct.rightUnitor (X : Arrow C) :
    (X □ initial.to (𝟙_ C)) ≅ X := by
  refine Arrow.isoMk ?_ (ρ_ X.right) ?_
  · refine Iso.mk ?_ ((ρ_ X.left).inv ≫ pushout.inr _ _) ?_ ?_
    · refine pushout.desc ?_ (ρ_ X.left).hom ?_
      · exact (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).to _
      · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
    · apply pushout.hom_ext
      · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
      · simp
    · simp
  · apply pushout.hom_ext
    · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
    · simp

end CartesianMonoidal

instance [MonoidalCategory C] [MonoidalClosed C] :
    ∀ S : C, PreservesColimitsOfSize (tensorLeft S) := fun S ↦
  (ihom.adjunction S).leftAdjoint_preservesColimits

instance [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] :
    ∀ S : C, PreservesColimitsOfSize (tensorRight S) := fun S ↦
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight S)

@[simps]
noncomputable
instance [HasInitial C] [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C] : MonoidalCategory (Arrow C) where
  tensorObj X Y := (pushoutProduct.obj X).obj Y
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    ext
    · apply pushout.hom_ext <;> simp [whisker_exchange_assoc]
    · simp [whisker_exchange_assoc]
  whiskerLeft X _ _ f := (pushoutProduct.obj X).map f
  whiskerRight f X := (pushoutProduct.map f).app X
  tensorUnit := initial.to (𝟙_ C)
  associator _ _ _ := PushoutProduct.associator ..
  associator_naturality _ _ _ := by
    ext
    · apply pushout.hom_ext
      · simp [whisker_exchange_assoc]
      · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        · simp [← whisker_exchange_assoc, temp₃_assoc]
        · simp [← whisker_exchange_assoc, temp₁_assoc]
    · simp
  pentagon _ _ _ _ := by
    ext
    · apply pushout.hom_ext
      · simp
      · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        · simp
        · apply ((tensorRight _ ⋙ tensorRight _).map_isPushout
            (IsPushout.of_hasPushout _ _)).hom_ext <;> simp [associator_naturality_left_assoc]
    · exact MonoidalCategory.pentagon ..
  leftUnitor := PushoutProduct.leftUnitor
  leftUnitor_naturality f := by
    ext
    · apply pushout.hom_ext
      · simp
      · apply (initialIsInitial.ofIso (mulZero initialIsInitial).symm).hom_ext
    · exact leftUnitor_naturality f.right
  rightUnitor := PushoutProduct.rightUnitor
  rightUnitor_naturality f := by
    ext
    · apply pushout.hom_ext
      · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
      · simp
    · exact rightUnitor_naturality f.right
  triangle X Y := by
    ext
    · apply pushout.hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp_assoc]
      · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        · apply (initialIsInitial.ofIso ((initialIsoIsInitial ?_) ≪≫ (mulZero ?_).symm)).hom_ext
          <;> exact initialIsInitial.ofIso (zeroMul initialIsInitial).symm
        · simp [← comp_whiskerRight_assoc]
    · exact MonoidalCategory.triangle X.right Y.right

noncomputable
instance [HasInitial C] [HasPushouts C] [HasPullbacks C]
  [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] :
    MonoidalClosed (Arrow C) where
  closed X := {
    rightAdj := MonoidalClosed.internalHom.leibnizPullback.obj (op X)
    adj := LeibnizAdjunction.adj _ _ (MonoidalClosed.internalHomAdjunction₂) X }

section Hexagon

variable [HasPushouts C] [MonoidalCategory C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) {Q : C}

@[reassoc (attr := simp)]
lemma Limits.whiskerLeft_inl_comp_pushoutSymmetry_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    Q ◁ pushout.inl f g ≫ Q ◁ (pushoutSymmetry f g).hom = Q ◁ pushout.inr g f := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma Limits.whiskerLeft_inr_comp_pushoutSymmetry_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    Q ◁ pushout.inr f g ≫ Q ◁ (pushoutSymmetry f g).hom = Q ◁ pushout.inl g f := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma Limits.inl_comp_pushoutSymmetry_hom_whiskerRight (f : X ⟶ Y) (g : X ⟶ Z) :
    pushout.inl f g ▷ Q ≫ (pushoutSymmetry f g).hom ▷ Q = pushout.inr g f ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
lemma Limits.inr_comp_pushoutSymmetry_hom_whiskerRight (f : X ⟶ Y) (g : X ⟶ Z) :
    pushout.inr f g ▷ Q ≫ (pushoutSymmetry f g).hom ▷ Q = pushout.inl g f ▷ Q := by
  simp [← comp_whiskerRight]

omit [HasPushouts C]

@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.Limits.HasColimit.whiskerLeft_isoOfNatIso_ι_hom
    {J : Type u₁} [Category.{v₁, u₁} J]
    {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G) (j : J) {Q : C} :
    Q ◁ colimit.ι F j ≫ Q ◁ (HasColimit.isoOfNatIso w).hom =
      Q ◁ w.hom.app j ≫ Q ◁ colimit.ι G j := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom_whiskerRight
    {J : Type u₁} [Category.{v₁, u₁} J]
    {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G) (j : J) {Q : C} :
    colimit.ι F j ▷ Q ≫ (HasColimit.isoOfNatIso w).hom ▷ Q =
      w.hom.app j ▷ Q ≫ colimit.ι G j ▷ Q := by
  simp [← MonoidalCategory.comp_whiskerRight]

end Hexagon

@[simps]
noncomputable
instance [HasInitial C] [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C] : BraidedCategory (Arrow C) where
  braiding := PushoutProduct.braiding
  hexagon_forward _ _ _ := by
    ext
    · apply pushout.hom_ext
      · simp
      · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
    · exact BraidedCategory.hexagon_forward ..
  hexagon_reverse _ _ _ := by
    ext
    · apply pushout.hom_ext
      · dsimp
        apply ((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
      · simp
    · exact BraidedCategory.hexagon_reverse ..

@[simps!]
noncomputable
instance [HasInitial C] [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C] : SymmetricCategory (Arrow C) where

end CategoryTheory.Arrow
