/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.DGCategory.HomotopyCategory

/-!
# Quasi-equivalences of DG categories

A DG functor is quasi-fully faithful when it induces quasi-isomorphisms on all Hom
complexes, and is a quasi-equivalence when it is additionally essentially surjective on `H⁰`.
-/

@[expose] public section

universe w u u'

noncomputable section

open CategoryTheory DGCategory MonoidalCategory CochainComplex
open CochainComplex.HomComplex HomologicalComplex

namespace CategoryTheory.EnrichedFunctor

variable {R : Type w} [CommRing R]

local notation "V" => CochainComplex (ModuleCat R) ℤ
private abbrev Q := HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
private abbrev Q₀ {E : Type*} [DGCategory R E] :=
  DGCategory.HomotopyCategory.quotient (R := R) (C := E)

variable {C : Type u} [DGCategory R C] {D : Type u'} [DGCategory R D]

/-- A DG functor is quasi-fully-faithful if its maps on Hom complexes are quasi-isomorphisms. -/
class QuasiFullyFaithful (F : EnrichedFunctor V C D) : Prop where
  quasiIso_map (X Y : C) : QuasiIso (F.map X Y)

/-- A quasi-equivalence is a quasi-fully-faithful DG functor which is essentially
surjective on the homotopy category. -/
class QuasiEquivalence (F : EnrichedFunctor V C D) : Prop extends QuasiFullyFaithful F where
  essSurj : (homotopyCategoryFunctor F).EssSurj

attribute [instance] QuasiFullyFaithful.quasiIso_map QuasiEquivalence.essSurj

instance (F : EnrichedFunctor V C D) [∀ X Y : C, IsIso (F.map X Y)] : F.QuasiFullyFaithful :=
  ⟨fun _ _ ↦ inferInstance⟩

namespace QuasiFullyFaithful

private def unitHomAddEquiv (M : ModuleCat R) :
    (ModuleCat.of R R ⟶ M) ≃+ M :=
  (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R M)).toAddEquiv

set_option backward.isDefEq.respectTransparency false in
private def unitHomComplexIso (K : V) :
    HomComplex (𝟙_ V) K ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (HomologicalComplex.Hom.isoOfComponents (fun n ↦ (((unitHomAddEquiv (K.X n)).symm.trans
    (Cochain.fromSingleEquiv (by simp)).symm).toAddCommGrpIso)) (by
    rintro n _ rfl
    ext x
    change δ n (n + 1)
        (Cochain.fromSingleMk
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X n) x)) (by simp)) =
        Cochain.fromSingleMk
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X (n + 1)) ((K.d n (n + 1)) x))) (by simp)
    rw [Cochain.δ_fromSingleMk
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X n) x)) (by simp)
        (n + 1) (n + 1) (by simp)]
    apply (Cochain.fromSingleEquiv
      (show (0 : ℤ) + (n + 1) = n + 1 by simp)).injective
    ext
    simp [LinearMap.toSpanSingleton_apply])).symm

set_option backward.isDefEq.respectTransparency false in
private def postcompHomComplex {K L : V} (f : K ⟶ L) :
    HomComplex (𝟙_ V) K ⟶ HomComplex (𝟙_ V) L where
  f n := AddCommGrpCat.ofHom <| AddMonoidHom.mk'
    (fun z ↦ z.comp (Cochain.ofHom f) (add_zero n)) (by simp)
  comm' n m _ := by
    ext z
    exact δ_comp_ofHom z f m

set_option backward.isDefEq.respectTransparency false in
private instance {K L : V} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (postcompHomComplex f) := by
  let G := forget₂ (ModuleCat R) AddCommGrpCat
  letI := quasiIso_map_of_preservesHomology f G
  haveI : QuasiIso (postcompHomComplex f ≫ (unitHomComplexIso L).hom) := by
    rw [show postcompHomComplex f ≫ (unitHomComplexIso L).hom =
        (unitHomComplexIso K).hom ≫
          (G.mapHomologicalComplex (ComplexShape.up ℤ)).map f by
      ext n z
      obtain ⟨g, rfl⟩ := Cochain.fromSingleMk_surjective z n (by simp)
      have h (M : V) (z : Cochain (𝟙_ V) M n) :
          (unitHomComplexIso M).hom.f n z = unitHomAddEquiv (M.X n)
            (Cochain.fromSingleEquiv (by simp) z) := rfl
      rw [comp_f, comp_f]
      rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, h, h]
      dsimp [unitHomAddEquiv, postcompHomComplex]
      rw [Cochain.fromSingleEquiv_fromSingleMk]
      change ((Cochain.fromSingleEquiv (by simp))
          ((Cochain.fromSingleMk g (by simp)).comp
            (Cochain.ofHom f) (add_zero n))) 1 = f.f n (g 1)
      rw [← Cochain.fromSingleMk_postcomp]
      simp]
    infer_instance
  exact quasiIso_of_comp_right (postcompHomComplex f) (unitHomComplexIso L).hom

private def cocyclePostcompAddHom {K L : V} (f : K ⟶ L) (n : ℤ) :
    Cocycle (𝟙_ V) K n →+
      Cocycle (𝟙_ V) L n :=
  AddMonoidHom.mk' (.postcomp · f) (by intros; ext1; simp)

private def cohomologyClassPostcompAddHom {K L : V} (f : K ⟶ L) (n : ℤ) :
    CohomologyClass (𝟙_ V) K n →+
      CohomologyClass (𝟙_ V) L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom
      (𝟙_ V) L n).comp (cocyclePostcompAddHom f n)) <| by
    rintro z ⟨m, hm, β, hβ⟩
    rw [AddMonoidHom.mem_ker]
    change CohomologyClass.mk ((cocyclePostcompAddHom f n) z) = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    refine ⟨m, hm, β.comp (Cochain.ofHom f) (add_zero m), ?_⟩
    rw [δ_comp_ofHom, hβ]
    rfl

open ForgetEnrichment

private def homotopyHomToComplexHomAddEquiv (X Y : C) :
    (Q₀.obj (of V X) ⟶ Q₀.obj (of V Y)) ≃+
      (Q.obj (𝟙_ V) ⟶ Q.obj (X ⟶[V] Y)) where
  toEquiv := Quot.congr ({toFun := homTo V, invFun := homOf V})
    (fun _ _ ↦ by simp only [CategoryTheory.HomRel.compClosure_iff_self]; rfl)
  map_add' := by rintro ⟨f⟩ ⟨g⟩; rfl

private def cohomologyClassHomotopyHomAddEquiv (K : V) :
    CohomologyClass
        (𝟙_ V) K 0 ≃+
      (Q.obj (𝟙_ V) ⟶ Q.obj K) :=
  CohomologyClass.homAddEquiv.trans
    (Linear.homCongr ℤ (Iso.refl _)
      (Q.mapIso ((shiftFunctorZero V ℤ).app K))).toAddEquiv

private def homotopyHomToClassAddEquiv (X Y : C) :
    (Q₀.obj (of V X) ⟶ Q₀.obj (of V Y)) ≃+
      CohomologyClass
        (𝟙_ V) (X ⟶[V] Y) 0 :=
  (homotopyHomToComplexHomAddEquiv X Y).trans
    (cohomologyClassHomotopyHomAddEquiv
      (X ⟶[V] Y)).symm

private lemma homotopyHomToClassAddEquiv_apply_quotient (X Y : C)
    (f : of V X ⟶ of V Y) :
    homotopyHomToClassAddEquiv X Y
        (Q₀.map f) =
      CohomologyClass.mk
        (Cocycle.ofHom
          (homTo V f)) := by
  apply (cohomologyClassHomotopyHomAddEquiv
    (X ⟶[V] Y)).injective
  simp only [cohomologyClassHomotopyHomAddEquiv, Functor.id_obj, homotopyHomToClassAddEquiv,
    AddEquiv.trans_apply, AddEquiv.symm_trans_apply, AddEquiv.symm_mk, AddHom.toFun_eq_coe,
    LinearMap.coe_toAddHom, LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm, Equiv.symm_mk,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    to_of, CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk, Linear.homCongr_apply,
    Iso.refl_inv, Category.id_comp, Functor.mapIso_hom, Iso.app_hom]
  change Q.map (homTo V f) = _
  rw [← Functor.map_comp]
  congr 1
  apply from_single_hom_ext
  simp only [Cocycle.equivHomShift_symm_apply,
    comp_f, Cocycle.homOf_f,
    Cocycle.rightShift_coe]
  rw [Cochain.rightShift_v _ 0 0 (by simp)
    0 0 (by simp) 0 (by simp)]
  let K := X ⟶[V] Y
  let e := K.shiftFunctorObjXIso 0 0 0 (by simp)
  change (homTo V f).f 0 =
    ((homTo V f).f 0 ≫ e.inv) ≫
      ((shiftFunctorZero V ℤ).hom.app K).f 0
  rw [shiftFunctorZero_hom_app_f]
  change (homTo V f).f 0 =
    ((homTo V f).f 0 ≫ e.inv) ≫ e.hom
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma homotopyCategoryFunctor_map_bijective
    (F : EnrichedFunctor V C D) [F.QuasiFullyFaithful] (X Y : C) :
    Function.Bijective ((homotopyCategoryFunctor F).map
      (X := Q₀.obj (of V X)) (Y := Q₀.obj (of V Y))) := by
  let K := X ⟶[V] Y
  let L := F.obj X ⟶[V] F.obj Y
  let φ : K ⟶ L := F.map X Y
  let h := homologyMap (postcompHomComplex φ) 0
  let eC := homologyAddEquiv (𝟙_ V) K 0
  let eD := homologyAddEquiv (𝟙_ V) L 0
  have hp : Function.Bijective (cohomologyClassPostcompAddHom φ 0) := by
    let γ : ShortComplex.LeftHomologyMapData
        ((shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) 0).map
          (postcompHomComplex φ))
        (leftHomologyData (𝟙_ V) K 0) (leftHomologyData (𝟙_ V) L 0) :=
      { φK := AddCommGrpCat.ofHom (cocyclePostcompAddHom φ 0)
        φH := AddCommGrpCat.ofHom (cohomologyClassPostcompAddHom φ 0)
        commi := by ext; rfl
        commf' := by
          rw [← cancel_mono (leftHomologyData (𝟙_ V) L 0).i]
          exact ((shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) 0).map
            (postcompHomComplex φ)).comm₁₂.symm
        commπ := by ext; rfl }
    convert eD.bijective.comp
      ((ConcreteCategory.bijective_of_isIso h).comp eC.symm.bijective) using 1
    funext z
    obtain ⟨x, rfl⟩ := eC.surjective z
    simp only [Function.comp_apply, AddEquiv.symm_apply_apply]
    dsimp only [eC, eD, h, homologyAddEquiv]
    exact (ConcreteCategory.congr_hom γ.homologyMap_comm x).symm
  apply Function.Bijective.of_comp_left
    (f := homotopyHomToClassAddEquiv (F.obj X) (F.obj Y))
    (hf := (homotopyHomToClassAddEquiv (F.obj X) (F.obj Y)).injective)
  convert hp.comp (homotopyHomToClassAddEquiv X Y).bijective using 1
  funext f
  induction f using Quot.inductionOn with
  | _ f =>
    let f' : of V X ⟶ of V Y := f
    change homotopyHomToClassAddEquiv (F.obj X) (F.obj Y)
        (Q₀.map (homOf V (homTo V f' ≫ φ))) =
      cohomologyClassPostcompAddHom φ 0
        (homotopyHomToClassAddEquiv X Y (Q₀.map f'))
    rw [homotopyHomToClassAddEquiv_apply_quotient,
      homotopyHomToClassAddEquiv_apply_quotient]
    congr 1
    apply Cocycle.ext
    exact Cochain.ofHom_comp (homTo V f') φ

instance (F : EnrichedFunctor V C D) [F.QuasiFullyFaithful] :
    (homotopyCategoryFunctor F).Full :=
  ⟨(homotopyCategoryFunctor_map_bijective F _ _).surjective⟩

instance (F : EnrichedFunctor V C D) [F.QuasiFullyFaithful] :
    (homotopyCategoryFunctor F).Faithful :=
  ⟨fun {_ _} ↦ (homotopyCategoryFunctor_map_bijective F _ _).injective⟩

instance (F : EnrichedFunctor V C D) [F.QuasiEquivalence] :
    (homotopyCategoryFunctor F).IsEquivalence where

end QuasiFullyFaithful

end CategoryTheory.EnrichedFunctor
