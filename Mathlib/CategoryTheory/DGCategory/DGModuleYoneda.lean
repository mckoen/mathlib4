/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/

module

public import Mathlib.CategoryTheory.DGCategory.DGModule
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Enriched Yoneda Hom complexes for right DG modules

This file compares the literal homotopy category of right DG modules with its quotient
presentation by action-compatible module homotopies. It constructs the enriched Yoneda
Hom-complex isomorphism and proves its compatibility with identities and composition, as used
by the inclusion into the pretriangulated hull.
-/

universe w

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory

namespace DGCategory.RightModule

variable {R : Type w} [CommRing R]

local notation "V" => CochainComplex (ModuleCat R) ℤ

variable (A : Type w) [DGCategory R A]

open CochainComplex.HomComplex

/-! ## Closed maps in the genuine module enrichment -/

/-- The element `1` in degree zero of the tensor-unit cochain complex. -/
def unitElement : ((𝟙_ V).X 0) :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat R))).inv.hom' (1 : R)

/-- The linear morphism from the tensor unit which selects a homogeneous graded
module transformation. -/
def elementMorphism {M N : RightModule (R := R) A} (n : ℤ)
    (f : GradedHom A M N n) :
    𝟙_ (ModuleCat R) ⟶ (homComplex A M N).X n :=
  ModuleCat.ofHom
    { toFun := fun r ↦ r • f
      map_add' := fun r s ↦ by rw [add_smul]
      map_smul' := fun r s ↦ by simp [smul_smul] }

@[simp]
lemma elementMorphism_one {M N : RightModule (R := R) A} (n : ℤ)
    (f : GradedHom A M N n) :
    (elementMorphism A n f).hom' 1 = f := by
  change (1 : R) • f = f
  exact one_smul R f

@[simp]
lemma elementMorphism_zero {M N : RightModule (R := R) A} (n : ℤ) :
    elementMorphism A n (0 : GradedHom A M N n) = 0 := by
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro r
  change r • (0 : GradedHom A M N n) = 0
  exact smul_zero r

@[simp]
lemma elementMorphism_sub {M N : RightModule (R := R) A} (n : ℤ)
    (f g : GradedHom A M N n) :
    elementMorphism A n (f - g) = elementMorphism A n f - elementMorphism A n g := by
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro r
  exact smul_sub r f g

/-- The differential of an element morphism is represented by the pointwise
differential of the corresponding graded transformation. -/
lemma elementMorphism_comp_d {M N : RightModule (R := R) A} (n m : ℤ)
    (f : GradedHom A M N n) :
    elementMorphism A n f ≫ (homComplex A M N).d n m =
      elementMorphism A m (differential A n m f) := by
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro r
  change differential A n m (r • f) = r • differential A n m f
  exact (differentialLinear A n m).map_smul r f

/-- The degree-zero graded transformation underlying a morphism in the closed
degree-zero category of the genuine DG category of right modules. -/
def gradedHomOfZ0
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} (f : M ⟶ N) :
    GradedHom A (ForgetEnrichment.to V M) (ForgetEnrichment.to V N) 0 :=
  ((ForgetEnrichment.homTo V f).f 0).hom' (unitElement (R := R))

/-- The graded transformation extracted from a closed morphism is a cocycle. -/
lemma differential_gradedHomOfZ0_eq_zero
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} (f : M ⟶ N) :
    differential A 0 1 (gradedHomOfZ0 A f) = 0 := by
  have h := congrArg (fun k ↦ k.hom' (unitElement (R := R)))
    ((ForgetEnrichment.homTo V f).comm 0 1)
  change differential A 0 1 (gradedHomOfZ0 A f) =
    (((𝟙_ V).d 0 1 ≫ (ForgetEnrichment.homTo V f).f 1).hom'
      (unitElement (R := R))) at h
  rw [show (𝟙_ V).d 0 1 = 0 by rfl] at h
  rw [CategoryTheory.Limits.zero_comp] at h
  have hz : (0 : ((𝟙_ V).X 0 ⟶
      (homComplex A (ForgetEnrichment.to V M) (ForgetEnrichment.to V N)).X 1)).hom'
        (unitElement (R := R)) =
      (0 : GradedHom A (ForgetEnrichment.to V M) (ForgetEnrichment.to V N) 1) := rfl
  rw [hz] at h
  exact h

/-- A closed degree-zero graded transformation gives an ordinary closed module map. -/
def homOfClosedGraded {M N : RightModule (R := R) A}
    (f : GradedHom A M N 0) (hf : differential A 0 1 f = 0) : M ⟶ N where
  app X := CochainComplex.HomComplex.Cocycle.homOf
    (CochainComplex.HomComplex.Cocycle.mk (f.app X) 1 (zero_add 1)
      (by
        have h := congrArg (fun g ↦ g.app X) hf
        change δ 0 1 (f.app X) = 0 at h
        exact h))
  naturality X Y := by
    have hX : Cochain.ofHom
        (CochainComplex.HomComplex.Cocycle.homOf
          (CochainComplex.HomComplex.Cocycle.mk (f.app X) 1 (zero_add 1)
            (by
              have h := congrArg (fun g ↦ g.app X) hf
              change δ 0 1 (f.app X) = 0 at h
              exact h))) = f.app X := by
      apply Cochain.ext₀
      intro p
      rfl
    have hY : Cochain.ofHom
        (CochainComplex.HomComplex.Cocycle.homOf
          (CochainComplex.HomComplex.Cocycle.mk (f.app Y) 1 (zero_add 1)
            (by
              have h := congrArg (fun g ↦ g.app Y) hf
              change δ 0 1 (f.app Y) = 0 at h
              exact h))) = f.app Y := by
      apply Cochain.ext₀
      intro p
      rfl
    apply Cochain.ofHom_injective
    rw [Cochain.ofHom_comp, Cochain.ofHom_comp]
    rw [← TensorCochain.right_ofHom]
    rw [hX, hY]
    exact f.naturality X Y

@[simp]
lemma ofHom_homOfClosedGraded {M N : RightModule (R := R) A}
    (f : GradedHom A M N 0) (hf : differential A 0 1 f = 0) :
    ofHom A (homOfClosedGraded A f hf) = f := by
  apply GradedHom.ext
  funext X
  change Cochain.ofHom ((homOfClosedGraded A f hf).app X) = f.app X
  apply Cochain.ext₀
  intro p
  rfl

/-- Forget a literal closed morphism of the enriched module category to the
corresponding ordinary module morphism. -/
def moduleHomOfZ0
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} (f : M ⟶ N) :
    ForgetEnrichment.to V M ⟶ ForgetEnrichment.to V N :=
  homOfClosedGraded A (gradedHomOfZ0 A f) (differential_gradedHomOfZ0_eq_zero A f)

/-! ## Ordinary module maps as literal closed maps -/

/-- A closed module map, represented as an actual closed degree-zero morphism into
the genuine module Hom complex. -/
def enrichedHomOfModule {M N : RightModule (R := R) A} (f : M ⟶ N) :
    𝟙_ V ⟶ homComplex A M N :=
  CochainComplex.HomComplex.Cocycle.homOf
    (CochainComplex.HomComplex.Cocycle.fromSingleMk
      (elementMorphism A 0 (ofHom A f)) (zero_add 0) 1 (zero_add 1) (by
        rw [elementMorphism_comp_d, differential_ofHom, elementMorphism_zero]))

/-- An ordinary module map as a morphism in the literal closed degree-zero
category of the enriched module category. -/
def z0HomOfModule {M N : RightModule (R := R) A} (f : M ⟶ N) :
    ForgetEnrichment.of V M ⟶ ForgetEnrichment.of V N :=
  ForgetEnrichment.homOf V (enrichedHomOfModule A f)

/-- The literal closed map constructed from an ordinary module map extracts back
to its degree-zero graded transformation. -/
lemma gradedHomOfZ0_z0HomOfModule {M N : RightModule (R := R) A} (f : M ⟶ N) :
    gradedHomOfZ0 A (z0HomOfModule A f) = ofHom A f := by
  unfold gradedHomOfZ0 z0HomOfModule
  rw [ForgetEnrichment.homTo_homOf]
  unfold enrichedHomOfModule
  change (elementMorphism A 0 (ofHom A f)).hom'
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom.hom'
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (ModuleCat R))).inv.hom' (1 : R))) = ofHom A f
  rw [show (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat R))).hom.hom'
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv.hom' (1 : R)) = 1 by
    exact congrArg (fun e ↦ e.hom' (1 : R))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv_hom_id]
  exact elementMorphism_one A 0 (ofHom A f)

/-- The embedding of ordinary closed module maps into degree-zero graded
transformations is injective. -/
lemma ofHom_injective {M N : RightModule (R := R) A} {f g : M ⟶ N}
    (h : ofHom A f = ofHom A g) : f = g := by
  apply Hom.ext
  funext X
  apply Cochain.ofHom_injective
  exact congrArg (fun k ↦ k.app X) h

@[simp]
lemma moduleHomOfZ0_z0HomOfModule {M N : RightModule (R := R) A} (f : M ⟶ N) :
    moduleHomOfZ0 A (z0HomOfModule A f) = f := by
  apply ofHom_injective A
  unfold moduleHomOfZ0
  rw [ofHom_homOfClosedGraded, gradedHomOfZ0_z0HomOfModule]

/-- Extraction sends the literal enriched identity to the ordinary identity
transformation. -/
lemma gradedHomOfZ0_id
    (M : DGCategory.Z0 (R := R) (RightModule (R := R) A)) :
    gradedHomOfZ0 A (𝟙 M) = ofHom A (𝟙 (ForgetEnrichment.to V M)) := by
  unfold gradedHomOfZ0
  rw [ForgetEnrichment.homTo_id]
  change ((enrichedId A (ForgetEnrichment.to V M)).f 0).hom'
      (unitElement (R := R)) = ofHom A (𝟙 (ForgetEnrichment.to V M))
  unfold enrichedId
  rw [HomologicalComplex.mkHomFromSingle_f]
  change (idComponent A (ForgetEnrichment.to V M)).hom'
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom.hom'
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (ModuleCat R))).inv.hom' (1 : R))) = _
  rw [show (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat R))).hom.hom'
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv.hom' (1 : R)) = 1 by
    exact congrArg (fun e ↦ e.hom' (1 : R))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv_hom_id]
  exact idComponent_one A (ForgetEnrichment.to V M)

set_option backward.isDefEq.respectTransparency false in
/-- Extraction turns literal closed composition into degree-zero enriched
composition. -/
lemma gradedHomOfZ0_comp
    {M N P : DGCategory.Z0 (R := R) (RightModule (R := R) A)}
    (f : M ⟶ N) (g : N ⟶ P) :
    gradedHomOfZ0 A (f ≫ g) =
      signedComp A 0 0 0 (zero_add 0) (gradedHomOfZ0 A f) (gradedHomOfZ0 A g) := by
  unfold gradedHomOfZ0
  change ((ForgetEnrichment.homTo V (f ≫ g)).f 0).hom'
      (unitElement (R := R)) =
    (compComponent A 0 0 0 (zero_add 0)).hom'
      (((ForgetEnrichment.homTo V f).f 0).hom' (unitElement (R := R)) ⊗ₜ[R]
        ((ForgetEnrichment.homTo V g).f 0).hom' (unitElement (R := R)))
  rw [ForgetEnrichment.homTo_comp]
  simp only [HomologicalComplex.comp_f]
  change ((((HomologicalComplex.leftUnitor' (𝟙_ V)).inv 0 ≫
      (HomologicalComplex.mapBifunctorMap
        (ForgetEnrichment.homTo V f) (ForgetEnrichment.homTo V g)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f 0) ≫
          (comp A).f 0).hom' (unitElement (R := R))) = _
  rw [HomologicalComplex.leftUnitor'_inv]
  simp only [Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  unfold comp
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  rw [show ((curriedTensor (ModuleCat R)).map
      ((ForgetEnrichment.homTo V f).f 0)).app ((𝟙_ V).X 0) =
    (ForgetEnrichment.homTo V f).f 0 ▷ (𝟙_ V).X 0 by rfl]
  rw [show ((curriedTensor (ModuleCat R)).obj
      ((ForgetEnrichment.to V M ⟶[V] ForgetEnrichment.to V N).X 0)).map
        ((ForgetEnrichment.homTo V g).f 0) =
    (ForgetEnrichment.to V M ⟶[V] ForgetEnrichment.to V N).X 0 ◁
      (ForgetEnrichment.homTo V g).f 0 by rfl]
  change (compComponent A 0 0 0 (zero_add 0)).hom'
      (((ForgetEnrichment.to V M ⟶[V] ForgetEnrichment.to V N).X 0 ◁
          (ForgetEnrichment.homTo V g).f 0).hom'
        (((ForgetEnrichment.homTo V f).f 0 ▷ (𝟙_ V).X 0).hom'
          (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (𝟙_ (ModuleCat R))).inv ▷ (𝟙_ V).X 0).hom'
            ((λ_ ((𝟙_ V).X 0)).inv.hom' (unitElement (R := R)))))) = _
  rw [show ( λ_ ((𝟙_ V).X 0)).inv.hom' (unitElement (R := R)) =
      1 ⊗ₜ[R] unitElement (R := R) by
    exact ModuleCat.MonoidalCategory.leftUnitor_inv_apply
      (M := (𝟙_ V).X 0) (unitElement (R := R))]
  rw [show ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat R))).inv ▷ (𝟙_ V).X 0).hom'
        (1 ⊗ₜ[R] unitElement (R := R)) =
      unitElement (R := R) ⊗ₜ[R] unitElement (R := R) by
    exact ModuleCat.MonoidalCategory.whiskerRight_apply
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ((𝟙_ V).X 0) 1 (unitElement (R := R))]
  rw [show ((ForgetEnrichment.homTo V f).f 0 ▷ (𝟙_ V).X 0).hom'
        (unitElement (R := R) ⊗ₜ[R] unitElement (R := R)) =
      ((ForgetEnrichment.homTo V f).f 0).hom' (unitElement (R := R)) ⊗ₜ[R]
        unitElement (R := R) by
    exact ModuleCat.MonoidalCategory.whiskerRight_apply
      ((ForgetEnrichment.homTo V f).f 0) ((𝟙_ V).X 0)
        (unitElement (R := R)) (unitElement (R := R))]
  rw [show ((ForgetEnrichment.to V M ⟶[V] ForgetEnrichment.to V N).X 0 ◁
      (ForgetEnrichment.homTo V g).f 0).hom'
        (((ForgetEnrichment.homTo V f).f 0).hom' (unitElement (R := R)) ⊗ₜ[R]
          unitElement (R := R)) =
      ((ForgetEnrichment.homTo V f).f 0).hom' (unitElement (R := R)) ⊗ₜ[R]
        ((ForgetEnrichment.homTo V g).f 0).hom' (unitElement (R := R)) by
    exact ModuleCat.MonoidalCategory.whiskerLeft_apply
      ((ForgetEnrichment.to V M ⟶[V] ForgetEnrichment.to V N).X 0)
      ((ForgetEnrichment.homTo V g).f 0)
      (((ForgetEnrichment.homTo V f).f 0).hom' (unitElement (R := R)))
      (unitElement (R := R))]

/-- In degree zero, signed enriched composition is ordinary composition of
closed module maps. -/
lemma signedComp_ofHom_zero {M N P : RightModule (R := R) A}
    (f : M ⟶ N) (g : N ⟶ P) :
    signedComp A 0 0 0 (zero_add 0) (ofHom A f) (ofHom A g) =
      ofHom A (f ≫ g) := by
  apply GradedHom.ext
  funext X
  change (0 : ℤ).negOnePow •
      ((Cochain.ofHom (f.app X)).comp (Cochain.ofHom (g.app X)) (zero_add 0)) =
    Cochain.ofHom ((f ≫ g).app X)
  rw [Int.negOnePow_zero, one_smul]
  exact (Cochain.ofHom_comp (f.app X) (g.app X)).symm

@[simp]
lemma moduleHomOfZ0_id
    (M : DGCategory.Z0 (R := R) (RightModule (R := R) A)) :
    moduleHomOfZ0 A (𝟙 M) = 𝟙 (ForgetEnrichment.to V M) := by
  apply ofHom_injective A
  unfold moduleHomOfZ0
  rw [ofHom_homOfClosedGraded, gradedHomOfZ0_id]

@[simp]
lemma moduleHomOfZ0_comp
    {M N P : DGCategory.Z0 (R := R) (RightModule (R := R) A)}
    (f : M ⟶ N) (g : N ⟶ P) :
    moduleHomOfZ0 A (f ≫ g) = moduleHomOfZ0 A f ≫ moduleHomOfZ0 A g := by
  apply ofHom_injective A
  unfold moduleHomOfZ0
  rw [ofHom_homOfClosedGraded, gradedHomOfZ0_comp,
    ← signedComp_ofHom_zero A]
  rw [ofHom_homOfClosedGraded, ofHom_homOfClosedGraded]

/-- Forgetting the literal closed degree-zero presentation of the genuine DG
module enrichment recovers the ordinary category of right DG modules. -/
def z0ToModule :
    DGCategory.Z0 (R := R) (RightModule (R := R) A) ⥤ RightModule (R := R) A where
  obj M := ForgetEnrichment.to V M
  map f := moduleHomOfZ0 A f
  map_id := moduleHomOfZ0_id A
  map_comp := moduleHomOfZ0_comp A

private lemma gradedHomOfZ0_add
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)}
    (f g : M ⟶ N) :
    gradedHomOfZ0 A (f + g) = gradedHomOfZ0 A f + gradedHomOfZ0 A g := by
  rfl

private lemma moduleHomOfZ0_add
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)}
    (f g : M ⟶ N) :
    moduleHomOfZ0 A (f + g) = moduleHomOfZ0 A f + moduleHomOfZ0 A g := by
  apply ofHom_injective A
  unfold moduleHomOfZ0
  rw [ofHom_homOfClosedGraded, gradedHomOfZ0_add]
  rw [ofHom_add, ofHom_homOfClosedGraded, ofHom_homOfClosedGraded]

instance z0ToModule_additive : (z0ToModule (R := R) A).Additive where
  map_add := by
    intro X Y f g
    change moduleHomOfZ0 A (f + g) =
      moduleHomOfZ0 A f + moduleHomOfZ0 A g
    exact moduleHomOfZ0_add A f g

/-! ## Literal homotopies and action-compatible module homotopies -/

/-- Evaluate a cochain from the tensor unit into a module Hom complex at the
canonical generator of the tensor unit. -/
noncomputable def unitCochainElement {M N : RightModule (R := R) A} {n : ℤ}
    (z : Cochain (𝟙_ V) (homComplex A M N) n) : GradedHom A M N n :=
  ((Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
    (K := homComplex A M N) (p := 0) (q := n) (n := n) (zero_add n)) z).hom' 1

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma unitCochainElement_sub {M N : RightModule (R := R) A} {n : ℤ}
    (z z' : Cochain (𝟙_ V) (homComplex A M N) n) :
    unitCochainElement A (z - z') =
      unitCochainElement A z - unitCochainElement A z' := by
  unfold unitCochainElement
  rw [map_sub]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma unitCochainElement_ofHom_homTo
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} (f : M ⟶ N) :
    unitCochainElement A
        (Cochain.ofHom (ForgetEnrichment.homTo V f)) = gradedHomOfZ0 A f := by
  rfl

/-- The linear map represented by a cochain from the tensor unit is the
element morphism of its value at `1`. -/
lemma elementMorphism_unitCochainElement {M N : RightModule (R := R) A} {n : ℤ}
    (z : Cochain (𝟙_ V) (homComplex A M N) n) :
    elementMorphism A n (unitCochainElement A z) =
      (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
        (K := homComplex A M N) (p := 0) (q := n) (n := n) (zero_add n)) z := by
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro r
  change r •
      ((Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
        (K := homComplex A M N) (zero_add n)) z).hom' 1 =
    ((Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
      (K := homComplex A M N) (zero_add n)) z).hom' r
  rw [show r = r • (1 : R) by simp, map_smul]
  simp

/-- Reconstruct a cochain from the tensor unit from its value at the unit
generator. -/
lemma fromSingleMk_unitCochainElement {M N : RightModule (R := R) A} {n : ℤ}
    (z : Cochain (𝟙_ V) (homComplex A M N) n) :
    Cochain.fromSingleMk (elementMorphism A n (unitCochainElement A z))
        (zero_add n) = z := by
  apply (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
    (K := homComplex A M N) (p := 0) (q := n) (n := n) (zero_add n)).injective
  rw [Cochain.fromSingleEquiv_fromSingleMk,
    elementMorphism_unitCochainElement]

@[simp]
lemma unitCochainElement_fromSingleMk {M N : RightModule (R := R) A} (n : ℤ)
    (f : GradedHom A M N n) :
    unitCochainElement A
        (Cochain.fromSingleMk (elementMorphism A n f) (zero_add n)) = f := by
  unfold unitCochainElement
  rw [Cochain.fromSingleEquiv_fromSingleMk, elementMorphism_one]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation at the tensor-unit generator intertwines the genuine Hom-complex
differential with the pointwise differential on graded module maps. -/
lemma unitCochainElement_delta {M N : RightModule (R := R) A} (n m : ℤ)
    (z : Cochain (𝟙_ V) (homComplex A M N) n) :
    unitCochainElement A (δ n m z) =
      differential A n m (unitCochainElement A z) := by
  rw [← fromSingleMk_unitCochainElement A z]
  rw [unitCochainElement_fromSingleMk (R := R) A n]
  rw [Cochain.δ_fromSingleMk
    (elementMorphism A n (unitCochainElement A z)) (zero_add n)
      m m (zero_add m)]
  rw [elementMorphism_comp_d]
  exact unitCochainElement_fromSingleMk (R := R) A (M := M) (N := N) m
    (differential A n m (unitCochainElement A z))

/-- The degree `-1` graded module-natural transformation carried by an
action-compatible module homotopy. -/
noncomputable def gradedHomOfModuleHomotopy {M N : RightModule (R := R) A}
    {f g : M ⟶ N} (h : RightModule.Homotopy A f g) : GradedHom A M N (-1) where
  app X := Cochain.ofHomotopy (h.app X)
  naturality X Y := by
    rw [← cochain_ofHomotopy_compLeft]
    rw [tensorCochain_right_ofHomotopy]
    rw [← cochain_ofHomotopy_compRight]
    apply Cochain.ext
    intro p q hpq
    change ((h.app X).compLeft (M.action X Y)).hom p q =
      ((HomologicalComplex.mapBifunctorMapHomotopy₂
        (𝟙 (X ⟶[V] Y)) (h.app Y) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ)).compRight (N.action X Y)).hom p q
    exact h.naturality X Y p q

/-- The differential of the degree `-1` transformation associated to a module
homotopy is the difference of its endpoints. -/
lemma differential_gradedHomOfModuleHomotopy {M N : RightModule (R := R) A}
    {f g : M ⟶ N} (h : RightModule.Homotopy A f g) :
    differential A (-1) 0 (gradedHomOfModuleHomotopy A h) =
      ofHom A f - ofHom A g := by
  apply GradedHom.ext
  funext X
  exact δ_ofHomotopy (h.app X)

/-- A degree `-1` graded module-natural transformation whose differential is
the difference of two closed module maps determines a component homotopy. -/
noncomputable def componentHomotopyOfGraded {M N : RightModule (R := R) A}
    (f g : M ⟶ N) (z : GradedHom A M N (-1))
    (hz : differential A (-1) 0 z = ofHom A f - ofHom A g) (X : A) :
    _root_.Homotopy (f.app X) (g.app X) :=
  (Cochain.equivHomotopy (f.app X) (g.app X)).symm
    ⟨z.app X, by
      have hX := congrArg (fun k ↦ k.app X) hz
      change δ (-1) 0 (z.app X) =
        Cochain.ofHom (f.app X) - Cochain.ofHom (g.app X) at hX
      rw [hX, sub_add_cancel]⟩

@[simp]
lemma cochain_ofHomotopy_componentHomotopyOfGraded
    {M N : RightModule (R := R) A} (f g : M ⟶ N)
    (z : GradedHom A M N (-1))
    (hz : differential A (-1) 0 z = ofHom A f - ofHom A g) (X : A) :
    Cochain.ofHomotopy (componentHomotopyOfGraded A f g z hz X) = z.app X := by
  exact congrArg Subtype.val
    ((Cochain.equivHomotopy (f.app X) (g.app X)).apply_symm_apply
      ⟨z.app X, by
        have hX := congrArg (fun k ↦ k.app X) hz
        change δ (-1) 0 (z.app X) =
          Cochain.ofHom (f.app X) - Cochain.ofHom (g.app X) at hX
        rw [hX, sub_add_cancel]⟩)

/-- A degree `-1` graded module-natural transformation with prescribed
differential gives an action-compatible module homotopy. -/
noncomputable def moduleHomotopyOfGraded {M N : RightModule (R := R) A}
    (f g : M ⟶ N) (z : GradedHom A M N (-1))
    (hz : differential A (-1) 0 z = ofHom A f - ofHom A g) :
    RightModule.Homotopy A f g where
  app X := componentHomotopyOfGraded A f g z hz X
  naturality X Y p q := by
    let hX := componentHomotopyOfGraded A f g z hz X
    let hY := componentHomotopyOfGraded A f g z hz Y
    change (hX.compLeft (M.action X Y)).hom p q =
      ((HomologicalComplex.mapBifunctorMapHomotopy₂
        (𝟙 (X ⟶[V] Y)) hY (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ)).compRight (N.action X Y)).hom p q
    have hcoX : Cochain.ofHomotopy hX = z.app X := by
      exact cochain_ofHomotopy_componentHomotopyOfGraded A f g z hz X
    have hcoY : Cochain.ofHomotopy hY = z.app Y := by
      exact cochain_ofHomotopy_componentHomotopyOfGraded A f g z hz Y
    have hnat := z.naturality X Y
    rw [← hcoX, ← hcoY] at hnat
    rw [← cochain_ofHomotopy_compLeft,
      tensorCochain_right_ofHomotopy,
      ← cochain_ofHomotopy_compRight] at hnat
    by_cases hpq : p + (-1) = q
    · have h := Cochain.congr_v hnat p q hpq
      simpa only [Cochain.ofHomotopy, Cochain.mk_v] using h
    · have hzero : q + 1 ≠ p := by omega
      rw [(hX.compLeft (M.action X Y)).zero p q hzero,
        ((HomologicalComplex.mapBifunctorMapHomotopy₂
          (𝟙 (X ⟶[V] Y)) hY (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ)).compRight (N.action X Y)).zero p q hzero]

/-- The degree `-1` graded module map obtained from a literal chain homotopy
between enriched closed maps. -/
noncomputable def gradedHomOfLiteralHomotopy
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} {f g : M ⟶ N}
    (h : _root_.Homotopy (ForgetEnrichment.homTo V f)
      (ForgetEnrichment.homTo V g)) :
    GradedHom A (ForgetEnrichment.to V M) (ForgetEnrichment.to V N) (-1) :=
  unitCochainElement A (Cochain.ofHomotopy h)

/-- The extracted degree `-1` map has differential equal to the difference of
the extracted endpoint maps. -/
lemma differential_gradedHomOfLiteralHomotopy
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} {f g : M ⟶ N}
    (h : _root_.Homotopy (ForgetEnrichment.homTo V f)
      (ForgetEnrichment.homTo V g)) :
    differential A (-1) 0 (gradedHomOfLiteralHomotopy A h) =
      gradedHomOfZ0 A f - gradedHomOfZ0 A g := by
  unfold gradedHomOfLiteralHomotopy
  rw [← unitCochainElement_delta]
  rw [δ_ofHomotopy, unitCochainElement_sub,
    unitCochainElement_ofHom_homTo, unitCochainElement_ofHom_homTo]

/-- A literal chain homotopy induces an action-compatible homotopy between the
underlying ordinary right-module maps. -/
noncomputable def moduleHomotopyOfLiteral
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} {f g : M ⟶ N}
    (h : _root_.Homotopy (ForgetEnrichment.homTo V f)
      (ForgetEnrichment.homTo V g)) :
    RightModule.Homotopy A (moduleHomOfZ0 A f) (moduleHomOfZ0 A g) :=
  moduleHomotopyOfGraded A (moduleHomOfZ0 A f) (moduleHomOfZ0 A g)
    (gradedHomOfLiteralHomotopy A h) (by
      rw [differential_gradedHomOfLiteralHomotopy]
      unfold moduleHomOfZ0
      rw [ofHom_homOfClosedGraded, ofHom_homOfClosedGraded])

set_option backward.isDefEq.respectTransparency false in
/-- A degree `-1` graded transformation with the prescribed endpoint
differential gives a literal chain homotopy from the tensor unit. -/
noncomputable def literalHomotopyOfGraded
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} (f g : M ⟶ N)
    (z : GradedHom A (ForgetEnrichment.to V M) (ForgetEnrichment.to V N) (-1))
    (hz : differential A (-1) 0 z = gradedHomOfZ0 A f - gradedHomOfZ0 A g) :
    _root_.Homotopy (ForgetEnrichment.homTo V f)
      (ForgetEnrichment.homTo V g) :=
  (Cochain.equivHomotopy (ForgetEnrichment.homTo V f)
    (ForgetEnrichment.homTo V g)).symm
      ⟨Cochain.fromSingleMk (elementMorphism A (-1) z) (zero_add (-1)), by
        apply (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
          (K := homComplex A (ForgetEnrichment.to V M) (ForgetEnrichment.to V N))
          (p := 0) (q := 0) (n := 0) (zero_add 0)).injective
        rw [map_add]
        rw [← elementMorphism_unitCochainElement A
          (Cochain.ofHom (ForgetEnrichment.homTo V f))]
        rw [← elementMorphism_unitCochainElement A
          (δ (-1) 0 (Cochain.fromSingleMk
            (elementMorphism A (-1) z) (zero_add (-1))))]
        rw [← elementMorphism_unitCochainElement A
          (Cochain.ofHom (ForgetEnrichment.homTo V g))]
        rw [unitCochainElement_ofHom_homTo,
          unitCochainElement_delta,
          unitCochainElement_fromSingleMk,
          unitCochainElement_ofHom_homTo, hz,
          elementMorphism_sub]
        simp⟩

/-- An action-compatible homotopy of the extracted module maps induces a
literal chain homotopy of the original enriched closed maps. -/
noncomputable def literalHomotopyOfModule
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} (f g : M ⟶ N)
    (h : RightModule.Homotopy A (moduleHomOfZ0 A f) (moduleHomOfZ0 A g)) :
    _root_.Homotopy (ForgetEnrichment.homTo V f)
      (ForgetEnrichment.homTo V g) :=
  literalHomotopyOfGraded A f g (gradedHomOfModuleHomotopy A h) (by
    rw [differential_gradedHomOfModuleHomotopy]
    unfold moduleHomOfZ0
    rw [ofHom_homOfClosedGraded, ofHom_homOfClosedGraded])

/-- Literal DG homotopy in the genuine enriched right-module category is
equivalent, in both directions, to action-compatible module homotopy. -/
theorem literalHomotopy_iff_moduleHomotopy
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} (f g : M ⟶ N) :
    Nonempty (_root_.Homotopy (ForgetEnrichment.homTo V f)
      (ForgetEnrichment.homTo V g)) ↔
      Nonempty (RightModule.Homotopy A
        (moduleHomOfZ0 A f) (moduleHomOfZ0 A g)) :=
  ⟨fun ⟨h⟩ ↦ ⟨moduleHomotopyOfLiteral A h⟩,
    fun ⟨h⟩ ↦ ⟨literalHomotopyOfModule A f g h⟩⟩

/-- Reformulation directly in terms of the two congruence relations used to
form the literal and manual quotient categories. -/
theorem literal_homotopic_iff_module_homotopic
    {M N : DGCategory.Z0 (R := R) (RightModule (R := R) A)} (f g : M ⟶ N) :
    DGCategory.homotopic (R := R) (C := RightModule (R := R) A) f g ↔
      RightModule.homotopic (R := R) A
        (moduleHomOfZ0 A f) (moduleHomOfZ0 A g) :=
  literalHomotopy_iff_moduleHomotopy A f g

/-- Comparison from the literal DG homotopy category to the quotient by
action-compatible module homotopies. -/
noncomputable def kToHomotopyCategory :
    DGCategory.HomotopyCategory (R := R) (RightModule (R := R) A) ⥤
      RightModule.HomotopyCategory (R := R) A :=
  CategoryTheory.Quotient.lift
    (DGCategory.homotopic (R := R) (C := RightModule (R := R) A))
    (z0ToModule (R := R) A ⋙
      RightModule.HomotopyCategory.quotient (R := R) A)
    (fun _ _ f g h ↦
      (RightModule.HomotopyCategory.quotient_map_eq_iff
        (R := R) A (moduleHomOfZ0 A f) (moduleHomOfZ0 A g)).2
          ((literal_homotopic_iff_module_homotopic A f g).1 h))

instance : (kToHomotopyCategory (R := R) A).Full where
  map_surjective := by
    intro X Y f
    refine ⟨(DGCategory.HomotopyCategory.quotient
      (R := R) (C := RightModule (R := R) A)).map
        (z0HomOfModule A f.out), ?_⟩
    change (RightModule.HomotopyCategory.quotient (R := R) A).map
      (moduleHomOfZ0 A (z0HomOfModule A f.out)) = f
    rw [moduleHomOfZ0_z0HomOfModule,
      RightModule.HomotopyCategory.quotient_map_out]

instance : (kToHomotopyCategory (R := R) A).Faithful where
  map_injective := by
    intro X Y f g h
    rw [← Quot.out_eq f, ← Quot.out_eq g] at h ⊢
    apply (DGCategory.HomotopyCategory.quotient_map_eq_iff
      (R := R) (C := RightModule (R := R) A) f.out g.out).2
    apply (literal_homotopic_iff_module_homotopic A f.out g.out).2
    apply (RightModule.HomotopyCategory.quotient_map_eq_iff
      (R := R) A (moduleHomOfZ0 A f.out) (moduleHomOfZ0 A g.out)).1
    exact h

instance kToHomotopyCategory_additive :
    (kToHomotopyCategory (R := R) A).Additive := by
  let Q := DGCategory.HomotopyCategory.quotient
    (R := R) (C := RightModule (R := R) A)
  letI : (Q ⋙ kToHomotopyCategory (R := R) A).Additive := by
    change (z0ToModule (R := R) A ⋙
      RightModule.HomotopyCategory.quotient (R := R) A).Additive
    infer_instance
  exact Functor.additive_of_full_essSurj_comp Q
    (kToHomotopyCategory (R := R) A)

/-! ## The enriched DG Yoneda functor -/

/-- The linear map from the tensor unit selecting an element of an `R`-module. -/
def moduleElementMorphism {H : ModuleCat R} (x : H) : 𝟙_ (ModuleCat R) ⟶ H :=
  ModuleCat.ofHom
    { toFun := fun r ↦ r • x
      map_add' := fun r s ↦ by rw [add_smul]
      map_smul' := fun r s ↦ by simp [smul_smul] }

@[simp]
lemma moduleElementMorphism_one {H : ModuleCat R} (x : H) :
    (moduleElementMorphism x).hom' 1 = x := by
  exact one_smul R x

@[simp]
lemma moduleElementMorphism_zero (H : ModuleCat R) :
    moduleElementMorphism (0 : H) = 0 := by
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro r
  exact smul_zero r

@[simp]
lemma moduleElementMorphism_add {H : ModuleCat R} (x y : H) :
    moduleElementMorphism (x + y) =
      moduleElementMorphism x + moduleElementMorphism y := by
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro r
  exact smul_add r x y

@[simp]
lemma moduleElementMorphism_smul {H : ModuleCat R} (r : R) (x : H) :
    moduleElementMorphism (r • x) = r • moduleElementMorphism x := by
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro s
  change s • (r • x) = r • (s • x)
  rw [smul_smul, smul_smul, mul_comm]

lemma moduleElementMorphism_comp {H K : ModuleCat R} (x : H) (f : H ⟶ K) :
    moduleElementMorphism x ≫ f = moduleElementMorphism (f.hom' x) := by
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro r
  change f.hom' (r • x) = r • f.hom' x
  exact map_smul f.hom' r x

/-- A homogeneous element of a cochain complex as a cochain from the tensor
unit concentrated in degree zero. -/
noncomputable def elementCochain (K : V) (n : ℤ) (x : K.X n) :
    Cochain (𝟙_ V) K n :=
  Cochain.fromSingleMk (moduleElementMorphism x) (zero_add n)

@[simp]
lemma elementCochain_zero (K : V) (n : ℤ) :
    elementCochain K n 0 = 0 := by
  unfold elementCochain
  rw [moduleElementMorphism_zero]
  rw [Cochain.fromSingleMk_zero]
  rfl

@[simp]
lemma elementCochain_add (K : V) (n : ℤ) (x y : K.X n) :
    elementCochain K n (x + y) = elementCochain K n x + elementCochain K n y := by
  unfold elementCochain
  rw [moduleElementMorphism_add, Cochain.fromSingleMk_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma elementCochain_smul (K : V) (n : ℤ) (r : R) (x : K.X n) :
    elementCochain K n (r • x) = r • elementCochain K n x := by
  unfold elementCochain
  rw [moduleElementMorphism_smul]
  apply (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
    (K := K) (p := 0) (q := n) (n := n) (zero_add n)).injective
  rw [Cochain.fromSingleEquiv_fromSingleMk]
  simp [Cochain.fromSingleEquiv]

set_option backward.isDefEq.respectTransparency false in
lemma delta_elementCochain (K : V) (n m : ℤ) (x : K.X n) :
    δ n m (elementCochain K n x) = elementCochain K m (K.d n m x) := by
  unfold elementCochain
  rw [Cochain.δ_fromSingleMk
    (moduleElementMorphism x) (zero_add n) m m (zero_add m)]
  rw [moduleElementMorphism_comp]
  change elementCochain K m ((K.d n m).hom' x) =
    elementCochain K m ((K.d n m).hom' x)
  rfl

/-- Evaluate a cochain from the tensor unit at its canonical generator. -/
noncomputable def cochainElement (K : V) {n : ℤ} (z : Cochain (𝟙_ V) K n) :
    K.X n :=
  ((Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
    (K := K) (p := 0) (q := n) (n := n) (zero_add n)) z).hom' 1

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma cochainElement_add (K : V) {n : ℤ} (z z' : Cochain (𝟙_ V) K n) :
    cochainElement K (z + z') = cochainElement K z + cochainElement K z' := by
  unfold cochainElement
  rw [map_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma cochainElement_smul (K : V) {n : ℤ} (r : R) (z : Cochain (𝟙_ V) K n) :
    cochainElement K (r • z) = r • cochainElement K z := by
  unfold cochainElement Cochain.fromSingleEquiv
  simp only [AddEquiv.coe_mk, Equiv.coe_fn_mk, Cochain.smul_v, Linear.comp_smul]
  change r •
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ≫ z.v 0 n (zero_add n)).hom' 1) = _
  rfl

@[simp]
lemma cochainElement_elementCochain (K : V) (n : ℤ) (x : K.X n) :
    cochainElement K (elementCochain K n x) = x := by
  unfold cochainElement elementCochain
  rw [Cochain.fromSingleEquiv_fromSingleMk, moduleElementMorphism_one]

lemma moduleElementMorphism_cochainElement (K : V) {n : ℤ}
    (z : Cochain (𝟙_ V) K n) :
    moduleElementMorphism (cochainElement K z) =
      (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
        (K := K) (p := 0) (q := n) (n := n) (zero_add n)) z := by
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro r
  change r •
      ((Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
        (K := K) (zero_add n)) z).hom' 1 =
    ((Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
      (K := K) (zero_add n)) z).hom' r
  rw [show r = r • (1 : R) by simp, map_smul]
  simp

lemma elementCochain_cochainElement (K : V) {n : ℤ}
    (z : Cochain (𝟙_ V) K n) :
    elementCochain K n (cochainElement K z) = z := by
  apply (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat R))
    (K := K) (p := 0) (q := n) (n := n) (zero_add n)).injective
  unfold elementCochain
  rw [Cochain.fromSingleEquiv_fromSingleMk,
    moduleElementMorphism_cochainElement]

set_option backward.isDefEq.respectTransparency false in
lemma cochainElement_delta (K : V) (n m : ℤ) (z : Cochain (𝟙_ V) K n) :
    cochainElement K (δ n m z) = (K.d n m).hom' (cochainElement K z) := by
  rw [← elementCochain_cochainElement K z]
  rw [delta_elementCochain]
  rw [cochainElement_elementCochain, cochainElement_elementCochain]
  rfl

/-- The homogeneous cochain obtained by postcomposing with a fixed homogeneous
morphism, including the Koszul sign forced by right tensoring. -/
noncomputable def yonedaComponentCochain {X Y : A} (n : ℤ)
    (f : (X ⟶[V] Y).X n) (P : A) :
    Cochain (P ⟶[V] X) (P ⟶[V] Y) n :=
  ((Cochain.ofHom (ρ_ (P ⟶[V] X)).inv).comp
    (TensorCochain.right (P ⟶[V] X)
      (elementCochain (X ⟶[V] Y) n f)) (zero_add n)).comp
        (Cochain.ofHom (eComp V P X Y)) (add_zero n)

set_option backward.isDefEq.respectTransparency false in
/-- A homogeneous morphism of the DG category acts by signed
postcomposition on representable right modules. -/
noncomputable def yonedaGradedHom {X Y : A} (n : ℤ)
    (f : (X ⟶[V] Y).X n) :
    GradedHom A (representable (R := R) A X) (representable (R := R) A Y) n where
  app P := yonedaComponentCochain A n f P
  naturality P Q := by
    unfold yonedaComponentCochain
    change (Cochain.ofHom (eComp V P Q X)).comp _ _ =
      Cochain.comp _ (Cochain.ofHom (eComp V P Q Y)) _
    rw [← Cochain.comp_assoc_of_third_is_zero_cochain]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
    rw [← Cochain.ofHom_comp]
    rw [show eComp V P Q X ≫ (ρ_ (P ⟶[V] X)).inv =
        (ρ_ ((P ⟶[V] Q) ⊗ (Q ⟶[V] X))).inv ≫
          eComp V P Q X ▷ (𝟙_ V) by
      exact rightUnitor_inv_naturality (eComp V P Q X)]
    rw [Cochain.ofHom_comp]
    rw [Cochain.comp_assoc_of_first_is_zero_cochain]
    have hnat := TensorCochain.right_naturality_left
      (eComp V P Q X) (elementCochain (X ⟶[V] Y) n f)
    have hnat' := congrArg (fun z ↦ z.comp
      (Cochain.ofHom (eComp V P X Y)) (add_zero n)) hnat
    rw [Cochain.comp_assoc_of_third_is_zero_cochain,
      Cochain.comp_assoc_of_third_is_zero_cochain] at hnat'
    rw [Cochain.comp_assoc_of_first_is_zero_cochain]
    rw [hnat']
    rw [← Cochain.ofHom_comp]
    rw [← e_assoc' V P Q X Y]
    rw [Cochain.ofHom_comp, Cochain.ofHom_comp]
    have hassoc := TensorCochain.associator_hom_right
      (P ⟶[V] Q) (Q ⟶[V] X) (elementCochain (X ⟶[V] Y) n f)
    have hassoc' := congrArg (fun z ↦ z.comp
      ((Cochain.ofHom ((P ⟶[V] Q) ◁ eComp V Q X Y)).comp
        (Cochain.ofHom (eComp V P Q Y)) (zero_add 0)) (add_zero n)) hassoc
    rw [Cochain.comp_assoc_of_third_is_zero_cochain,
      Cochain.comp_assoc_of_third_is_zero_cochain] at hassoc'
    rw [← hassoc']
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
    rw [← Cochain.ofHom_comp]
    rw [show (ρ_ ((P ⟶[V] Q) ⊗ (Q ⟶[V] X))).inv ≫
        (α_ (P ⟶[V] Q) (Q ⟶[V] X) (𝟙_ V)).hom =
      (P ⟶[V] Q) ◁ (ρ_ (Q ⟶[V] X)).inv by
        exact (MonoidalCategory.whiskerLeft_rightUnitor_inv
          (P ⟶[V] Q) (Q ⟶[V] X)).symm]
    rw [TensorCochain.right_comp, TensorCochain.right_comp,
      TensorCochain.right_ofHom, TensorCochain.right_ofHom]
    simp only [Cochain.comp_assoc_of_first_is_zero_cochain,
      Cochain.comp_assoc_of_second_is_zero_cochain]

/-- The degree-`n` component of the enriched Yoneda map, as an `R`-linear
map. -/
noncomputable def yonedaGradedMap {X Y : A} (n : ℤ) :
    (X ⟶[V] Y).X n →ₗ[R]
      GradedHom A (representable (R := R) A X) (representable (R := R) A Y) n where
  toFun := yonedaGradedHom A n
  map_add' f g := by
    apply GradedHom.ext
    funext P
    change yonedaComponentCochain A n (f + g) P =
      yonedaComponentCochain A n f P + yonedaComponentCochain A n g P
    unfold yonedaComponentCochain
    rw [elementCochain_add, TensorCochain.right_add]
    simp
  map_smul' r f := by
    apply GradedHom.ext
    funext P
    change yonedaComponentCochain A n (r • f) P =
      r • yonedaComponentCochain A n f P
    unfold yonedaComponentCochain
    rw [elementCochain_smul, TensorCochain.right_smul]
    simp

/-- The enriched Yoneda map commutes with the differentials on homogeneous
components. -/
lemma differential_yonedaGradedHom {X Y : A} (n m : ℤ)
    (f : (X ⟶[V] Y).X n) :
    differential A n m (yonedaGradedHom A n f) =
      yonedaGradedHom A m ((X ⟶[V] Y).d n m f) := by
  apply GradedHom.ext
  funext P
  change δ n m (yonedaComponentCochain A n f P) =
    yonedaComponentCochain A m ((X ⟶[V] Y).d n m f) P
  unfold yonedaComponentCochain
  simp only [δ_comp_ofHom, δ_ofHom_comp]
  by_cases hnm : n + 1 = m
  · rw [TensorCochain.δ_right _ n m hnm, delta_elementCochain]
  · rw [δ_shape n m hnm]
    have hd : (X ⟶[V] Y).d n m = 0 :=
      HomologicalComplex.shape _ n m (by simpa using hnm)
    rw [hd]
    simp

/-- The morphism of Hom complexes underlying the enriched DG Yoneda functor. -/
noncomputable def enrichedYonedaMap (X Y : A) :
    (X ⟶[V] Y) ⟶
      homComplex A (representable (R := R) A X) (representable (R := R) A Y) where
  f n := ModuleCat.ofHom (yonedaGradedMap A n)
  comm' n m _ := by
    apply ModuleCat.Hom.ext
    apply LinearMap.ext
    intro f
    change differential A n m (yonedaGradedHom A n f) =
      yonedaGradedHom A m ((X ⟶[V] Y).d n m f)
    exact differential_yonedaGradedHom A n m f

/-- The cochain obtained by evaluating a homogeneous graded transformation of
representables at the enriched identity. -/
noncomputable def yonedaEvaluationCochain {X Y : A} (n : ℤ)
    (f : GradedHom A (representable (R := R) A X)
      (representable (R := R) A Y) n) :
    Cochain (𝟙_ V) (X ⟶[V] Y) n :=
  (Cochain.ofHom (eId V X)).comp (f.app X) (zero_add n)

/-- Evaluation at the enriched identity on homogeneous transformations. -/
noncomputable def yonedaEvaluationGraded {X Y : A} (n : ℤ)
    (f : GradedHom A (representable (R := R) A X)
      (representable (R := R) A Y) n) :
    (X ⟶[V] Y).X n :=
  cochainElement (X ⟶[V] Y) (yonedaEvaluationCochain A n f)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation at the enriched identity is linear in each degree. -/
noncomputable def yonedaEvaluationGradedMap {X Y : A} (n : ℤ) :
    GradedHom A (representable (R := R) A X)
      (representable (R := R) A Y) n →ₗ[R] (X ⟶[V] Y).X n where
  toFun := yonedaEvaluationGraded A n
  map_add' f g := by
    unfold yonedaEvaluationGraded yonedaEvaluationCochain
    change cochainElement (X ⟶[V] Y)
      ((Cochain.ofHom (eId V X)).comp (f.app X + g.app X) (zero_add n)) = _
    rw [Cochain.comp_add, cochainElement_add]
  map_smul' r f := by
    unfold yonedaEvaluationGraded yonedaEvaluationCochain
    change cochainElement (X ⟶[V] Y)
      ((Cochain.ofHom (eId V X)).comp (r • f.app X) (zero_add n)) = _
    rw [Cochain.comp_smul, cochainElement_smul]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation at the enriched identity commutes with differentials. -/
lemma yonedaEvaluationGraded_differential {X Y : A} (n m : ℤ)
    (f : GradedHom A (representable (R := R) A X)
      (representable (R := R) A Y) n) :
    (X ⟶[V] Y).d n m (yonedaEvaluationGraded A n f) =
      yonedaEvaluationGraded A m (differential A n m f) := by
  unfold yonedaEvaluationGraded yonedaEvaluationCochain
  change ((X ⟶[V] Y).d n m).hom'
      (cochainElement (X ⟶[V] Y)
        ((Cochain.ofHom (eId V X)).comp (f.app X) (zero_add n))) =
    cochainElement (X ⟶[V] Y)
      ((Cochain.ofHom (eId V X)).comp (δ n m (f.app X)) (zero_add m))
  rw [← cochainElement_delta]
  rw [δ_ofHom_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation at the enriched identity as a morphism of cochain complexes. -/
noncomputable def enrichedYonedaEvaluation (X Y : A) :
    homComplex A (representable (R := R) A X) (representable (R := R) A Y) ⟶
      (X ⟶[V] Y) where
  f n := ModuleCat.ofHom (yonedaEvaluationGradedMap A n)
  comm' n m _ := by
    apply ModuleCat.Hom.ext
    apply LinearMap.ext
    intro f
    change (X ⟶[V] Y).d n m (yonedaEvaluationGraded A n f) =
      yonedaEvaluationGraded A m (differential A n m f)
    exact yonedaEvaluationGraded_differential A n m f

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating a homogeneous Yoneda transformation at the identity recovers
the original homogeneous morphism. -/
lemma yonedaEvaluationCochain_yonedaGradedHom {X Y : A} (n : ℤ)
    (f : (X ⟶[V] Y).X n) :
    yonedaEvaluationCochain A n (yonedaGradedHom A n f) =
      elementCochain (X ⟶[V] Y) n f := by
  unfold yonedaEvaluationCochain yonedaGradedHom yonedaComponentCochain
  rw [← Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.ofHom_comp]
  rw [show eId V X ≫ (ρ_ (X ⟶[V] X)).inv =
      (ρ_ (𝟙_ V)).inv ≫ eId V X ▷ (𝟙_ V) by
    exact rightUnitor_inv_naturality (eId V X)]
  rw [Cochain.ofHom_comp]
  rw [Cochain.comp_assoc_of_first_is_zero_cochain]
  have hnat := TensorCochain.right_naturality_left
    (eId V X) (elementCochain (X ⟶[V] Y) n f)
  have hnat' := congrArg (fun z ↦ z.comp
    (Cochain.ofHom (eComp V X X Y)) (add_zero n)) hnat
  rw [Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain] at hnat'
  rw [Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [hnat']
  rw [← unitors_inv_equal]
  have hunit := TensorCochain.leftUnitor_inv_right
    (elementCochain (X ⟶[V] Y) n f)
  have hunit' := congrArg (fun z ↦ z.comp
    ((Cochain.ofHom (eId V X ▷ (X ⟶[V] Y))).comp
      (Cochain.ofHom (eComp V X X Y)) (zero_add 0)) (add_zero n)) hunit
  rw [Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain] at hunit'
  rw [hunit']
  rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  rw [e_id_comp]
  rw [Cochain.comp_id]

@[simp]
lemma yonedaEvaluationGraded_yonedaGradedHom {X Y : A} (n : ℤ)
    (f : (X ⟶[V] Y).X n) :
    yonedaEvaluationGraded A n (yonedaGradedHom A n f) = f := by
  unfold yonedaEvaluationGraded
  rw [yonedaEvaluationCochain_yonedaGradedHom,
    cochainElement_elementCochain]

set_option backward.isDefEq.respectTransparency false in
/-- A homogeneous transformation of representables is recovered from its
value at the enriched identity. -/
lemma yonedaGradedHom_yonedaEvaluationGraded {X Y : A} (n : ℤ)
    (f : GradedHom A (representable (R := R) A X)
      (representable (R := R) A Y) n) :
    yonedaGradedHom A n (yonedaEvaluationGraded A n f) = f := by
  apply GradedHom.ext
  funext P
  change yonedaComponentCochain A n (yonedaEvaluationGraded A n f) P = f.app P
  unfold yonedaComponentCochain yonedaEvaluationGraded yonedaEvaluationCochain
  rw [elementCochain_cochainElement]
  rw [TensorCochain.right_comp, TensorCochain.right_ofHom]
  simp only [Cochain.comp_assoc_of_first_is_zero_cochain]
  have hf := f.naturality P X
  change (Cochain.ofHom (eComp V P X X)).comp (f.app P) (zero_add n) =
    (TensorCochain.right (P ⟶[V] X) (f.app X)).comp
      (Cochain.ofHom (eComp V P X Y)) (add_zero n) at hf
  rw [← hf]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  rw [show (((ρ_ (P ⟶[V] X)).inv ≫ (P ⟶[V] X) ◁ eId V X) ≫
      eComp V P X X) = 𝟙 (P ⟶[V] X) by
    simpa only [Category.assoc] using e_comp_id V P X]
  rw [Cochain.id_comp]

/-- The enriched Yoneda comparison on every Hom complex is an actual
isomorphism of cochain complexes. -/
noncomputable def enrichedYonedaHomIso (X Y : A) :
    (X ⟶[V] Y) ≅
      homComplex A (representable (R := R) A X) (representable (R := R) A Y) where
  hom := enrichedYonedaMap A X Y
  inv := enrichedYonedaEvaluation A X Y
  hom_inv_id := by
    ext n : 1
    apply ModuleCat.Hom.ext
    apply LinearMap.ext
    intro f
    change yonedaEvaluationGraded A n (yonedaGradedHom A n f) = f
    exact yonedaEvaluationGraded_yonedaGradedHom A n f
  inv_hom_id := by
    ext n : 1
    apply ModuleCat.Hom.ext
    apply LinearMap.ext
    intro f
    change yonedaGradedHom A n (yonedaEvaluationGraded A n f) = f
    exact yonedaGradedHom_yonedaEvaluationGraded A n f

def dgIdentityElement (X : A) : (X ⟶[V] X).X 0 :=
  cochainElement (X ⟶[V] X) (Cochain.ofHom (eId V X))

lemma elementCochain_dgIdentityElement (X : A) :
    elementCochain (X ⟶[V] X) 0 (dgIdentityElement A X) =
      Cochain.ofHom (eId V X) := by
  exact elementCochain_cochainElement _ _

@[simp]
lemma elementCochain_v (K : V) (n : ℤ) (x : K.X n) :
    (elementCochain K n x).v 0 n (zero_add n) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ≫ moduleElementMorphism x := by
  unfold elementCochain
  exact Cochain.fromSingleMk_v _ _

lemma elementCochain_v_of_eq (K : V) (n q : ℤ) (x : K.X n)
    (h₀ : 0 + n = q) (h : n = q) :
    (elementCochain K n x).v 0 q h₀ =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ≫ moduleElementMorphism x ≫
          eqToHom (congrArg K.X h) := by
  cases h
  simpa only [eqToHom_refl, Category.comp_id] using elementCochain_v K n x

@[reassoc]
lemma whiskerLeft_eqToHom_ιMapBifunctor (H K : V)
    (i j j' p : ℤ) (hjj' : j = j') (hij' : i + j' = p) :
    (H.X i ◁ eqToHom (congrArg K.X hjj')) ≫
        HomologicalComplex.ιMapBifunctor H K (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) i j' p hij' =
      HomologicalComplex.ιMapBifunctor H K (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i j p (by rw [hjj']; exact hij') := by
  subst j'
  simp

lemma dgIdentityElement_eq (X : A) :
    dgIdentityElement A X =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ≫ (eId V X).f 0).hom' 1 := by
  rfl

lemma cochainElement_injective (K : V) (n : ℤ) :
    Function.Injective (cochainElement K : Cochain (𝟙_ V) K n → K.X n) := by
  intro z z' h
  rw [← elementCochain_cochainElement K z,
    ← elementCochain_cochainElement K z', h]

@[simp]
lemma cochainElement_units_smul (K : V) {n : ℤ} (u : ℤˣ)
    (z : Cochain (𝟙_ V) K n) :
    cochainElement K (u • z) = u • cochainElement K z := by
  rcases Int.units_eq_one_or u with (rfl | rfl)
  · simp
  · simpa only [Units.neg_smul, one_smul, neg_one_smul] using
      cochainElement_smul K (-1 : R) z

set_option backward.isDefEq.respectTransparency false in
lemma yonedaGradedHom_dgIdentityElement (X : A) :
    yonedaGradedHom A 0 (dgIdentityElement A X) =
      gradedId A (representable (R := R) A X) := by
  apply GradedHom.ext
  funext P
  change yonedaComponentCochain A 0 (dgIdentityElement A X) P =
    Cochain.ofHom (𝟙 (P ⟶[V] X))
  unfold yonedaComponentCochain
  rw [elementCochain_dgIdentityElement]
  rw [TensorCochain.right_ofHom]
  rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  rw [Category.assoc]
  rw [e_comp_id]

set_option backward.isDefEq.respectTransparency false in
lemma enrichedYoneda_map_id (X : A) :
    eId V X ≫ enrichedYonedaMap A X X =
      eId V (representable (R := R) A X) := by
  apply HomologicalComplex.from_single_hom_ext
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat R))
  apply (cancel_epi e.inv).1
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro r
  rw [show r = r • (1 : R) by simp]
  simp only [HomologicalComplex.comp_f, map_smul]
  have hsrc :
      ((e.inv ≫ (eId V X).f 0 ≫ (enrichedYonedaMap A X X).f 0).hom' 1) =
        yonedaGradedHom A 0 (dgIdentityElement A X) := by
    change yonedaGradedHom A 0
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ≫ (eId V X).f 0).hom' 1) = _
    rw [← dgIdentityElement_eq]
  have htgt :
      ((e.inv ≫ (eId V (representable (R := R) A X)).f 0).hom' 1) =
        gradedId A (representable (R := R) A X) := by
    change ((e.inv ≫ (enrichedId A (representable (R := R) A X)).f 0).hom' 1) = _
    unfold enrichedId
    rw [HomologicalComplex.mkHomFromSingle_f]
    change (idComponent A (representable (R := R) A X)).hom'
      ((e.hom).hom' ((e.inv).hom' 1)) = _
    rw [show (e.hom).hom' ((e.inv).hom' 1) = 1 by
      exact congrArg (fun k ↦ k.hom' 1) e.inv_hom_id]
    exact idComponent_one A _
  rw [hsrc]
  erw [htgt]
  rw [yonedaGradedHom_dgIdentityElement]

/-- The value of enriched composition on a pure homogeneous tensor. -/
def dgCompElement {X Y Z : A} (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂)
    (f : (X ⟶[V] Y).X n₁) (g : (Y ⟶[V] Z).X n₂) :
    (X ⟶[V] Z).X n₁₂ :=
  ((HomologicalComplex.ιMapBifunctor (X ⟶[V] Y) (Y ⟶[V] Z)
      (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
      n₁ n₂ n₁₂ h ≫ (eComp V X Y Z).f n₁₂).hom' (f ⊗ₜ[R] g))

lemma elementCochain_comp_yonedaComponent {X Y Z : A}
    (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂)
    (f : (X ⟶[V] Y).X n₁) (g : (Y ⟶[V] Z).X n₂) :
    (n₁ * n₂).negOnePow •
        ((elementCochain (X ⟶[V] Y) n₁ f).comp
          (yonedaComponentCochain A n₂ g X) h) =
      elementCochain (X ⟶[V] Z) n₁₂
        (dgCompElement A n₁ n₂ n₁₂ h f g) := by
  apply cochainElement_injective
  rw [cochainElement_units_smul, cochainElement_elementCochain]
  unfold cochainElement
  change (n₁ * n₂).negOnePow •
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv ≫
        ((elementCochain (X ⟶[V] Y) n₁ f).comp
          (yonedaComponentCochain A n₂ g X) h).v 0 n₁₂ (zero_add n₁₂)).hom' 1 =
    dgCompElement A n₁ n₂ n₁₂ h f g
  rw [Cochain.comp_v _ _ h 0 n₁ n₁₂ (zero_add n₁) h]
  rw [elementCochain_v]
  unfold yonedaComponentCochain
  rw [Cochain.comp_v _ _ (add_zero n₂) n₁ n₁₂ n₁₂ h (add_zero n₁₂)]
  rw [Cochain.comp_v _ _ (zero_add n₂) n₁ n₁ n₁₂ (add_zero n₁) h]
  simp only [Cochain.ofHom_v, Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  have hright : (ρ_ (X ⟶[V] Y)).inv.f n₁ =
      (HomologicalComplex.rightUnitor' (X ⟶[V] Y)).inv n₁ := rfl
  rw [hright, HomologicalComplex.rightUnitor'_inv]
  simp only [Category.assoc]
  have hι := TensorCochain.ι_right_v_assoc (X ⟶[V] Y)
    (elementCochain (Y ⟶[V] Z) n₂ g)
      n₁ 0 n₁ n₁₂ (add_zero n₁) h ((eComp V X Y Z).f n₁₂)
  change HomologicalComplex.ιTensorObj (X ⟶[V] Y)
      (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
        n₁ 0 n₁ (add_zero n₁) ≫
      (TensorCochain.right (X ⟶[V] Y)
        (elementCochain (Y ⟶[V] Z) n₂ g)).v n₁ n₁₂ h ≫
          (eComp V X Y Z).f n₁₂ = _ at hι
  rw [hι]
  simp only [Linear.units_smul_comp]
  let q : 𝟙_ (ModuleCat R) ⟶ (X ⟶[V] Z).X n₁₂ :=
    moduleElementMorphism f ≫
      (ρ_ ((X ⟶[V] Y).X n₁)).inv ≫
      (X ⟶[V] Y).X n₁ ◁
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv ≫
      ((X ⟶[V] Y).X n₁ ◁
          (elementCochain (Y ⟶[V] Z) n₂ g).v 0 (0 + n₂) rfl ≫
        HomologicalComplex.ιMapBifunctor (X ⟶[V] Y) (Y ⟶[V] Z)
          (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
            n₁ (0 + n₂) n₁₂ (by dsimp; omega)) ≫
      (eComp V X Y Z).f n₁₂
  change (n₁ * n₂).negOnePow •
      (((n₁ * n₂).negOnePow • q).hom' 1) = _
  rw [show (((n₁ * n₂).negOnePow • q).hom' 1) =
      (n₁ * n₂).negOnePow • q.hom' 1 by
        rcases Int.units_eq_one_or (n₁ * n₂).negOnePow with (hu | hu)
        · rw [hu]
          simp
        · rw [hu]
          simp only [Units.neg_smul, one_smul]
          rfl]
  rw [smul_smul]
  rw [show (n₁ * n₂).negOnePow * (n₁ * n₂).negOnePow = 1 by simp]
  simp only [one_smul]
  dsimp only [q]
  rw [elementCochain_v_of_eq (K := Y ⟶[V] Z) (n := n₂)
    (q := 0 + n₂) g rfl (zero_add n₂).symm]
  rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [Iso.inv_hom_id]
  rw [MonoidalCategory.whiskerLeft_id]
  simp only [Category.id_comp]
  erw [whiskerLeft_eqToHom_ιMapBifunctor_assoc
    (H := X ⟶[V] Y) (K := Y ⟶[V] Z) (i := n₁) (j := n₂)
      (j' := 0 + n₂) (p := n₁₂) (hjj' := (zero_add n₂).symm)
        (hij' := by omega) ((eComp V X Y Z).f n₁₂)]
  unfold dgCompElement
  change ((eComp V X Y Z).f n₁₂).hom'
      ((HomologicalComplex.ιMapBifunctor (X ⟶[V] Y) (Y ⟶[V] Z)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
        n₁ n₂ n₁₂ (by omega)).hom'
          (((X ⟶[V] Y).X n₁ ◁ moduleElementMorphism g).hom'
            ((ρ_ ((X ⟶[V] Y).X n₁)).inv.hom'
              ((moduleElementMorphism f).hom' 1)))) =
    ((eComp V X Y Z).f n₁₂).hom'
      ((HomologicalComplex.ιMapBifunctor (X ⟶[V] Y) (Y ⟶[V] Z)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
        n₁ n₂ n₁₂ h).hom' (f ⊗ₜ[R] g))
  rw [moduleElementMorphism_one]
  rw [show (ρ_ ((X ⟶[V] Y).X n₁)).inv.hom' f =
      f ⊗ₜ[R] (1 : R) by
    exact ModuleCat.MonoidalCategory.rightUnitor_inv_apply f]
  rw [show (((X ⟶[V] Y).X n₁ ◁ moduleElementMorphism g).hom'
      (f ⊗ₜ[R] (1 : R))) = f ⊗ₜ[R] g by
    rw [show (((X ⟶[V] Y).X n₁ ◁ moduleElementMorphism g).hom'
        (f ⊗ₜ[R] (1 : R))) =
        f ⊗ₜ[R] (moduleElementMorphism g).hom' 1 by
      exact ModuleCat.MonoidalCategory.whiskerLeft_apply
        ((X ⟶[V] Y).X n₁) (moduleElementMorphism g) f 1,
      moduleElementMorphism_one]]

set_option backward.isDefEq.respectTransparency false in
lemma yonedaGradedHom_comp {X Y Z : A}
    (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂)
    (f : (X ⟶[V] Y).X n₁) (g : (Y ⟶[V] Z).X n₂) :
    yonedaGradedHom A n₁₂ (dgCompElement A n₁ n₂ n₁₂ h f g) =
      signedComp A n₁ n₂ n₁₂ h
        (yonedaGradedHom A n₁ f) (yonedaGradedHom A n₂ g) := by
  apply (Function.LeftInverse.injective
    (fun k ↦ yonedaGradedHom_yonedaEvaluationGraded A n₁₂ k))
  rw [yonedaEvaluationGraded_yonedaGradedHom]
  unfold yonedaEvaluationGraded yonedaEvaluationCochain
  rw [← cochainElement_elementCochain (X ⟶[V] Z) n₁₂
    (dgCompElement A n₁ n₂ n₁₂ h f g)]
  apply congrArg (cochainElement (X ⟶[V] Z))
  change elementCochain (X ⟶[V] Z) n₁₂
      (dgCompElement A n₁ n₂ n₁₂ h f g) =
    (Cochain.ofHom (eId V X)).comp
      ((n₁ * n₂).negOnePow •
        ((yonedaComponentCochain A n₁ f X).comp
          (yonedaComponentCochain A n₂ g X) h)) (zero_add n₁₂)
  rw [Cochain.comp_units_smul]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [show (Cochain.ofHom (eId V X)).comp
      (yonedaComponentCochain A n₁ f X) (zero_add n₁) =
      elementCochain (X ⟶[V] Y) n₁ f by
    change yonedaEvaluationCochain A n₁ (yonedaGradedHom A n₁ f) = _
    exact yonedaEvaluationCochain_yonedaGradedHom A n₁ f]
  rw [elementCochain_comp_yonedaComponent A n₁ n₂ n₁₂ h f g]

set_option backward.isDefEq.respectTransparency false in
lemma enrichedYoneda_map_comp (X Y Z : A) :
    eComp V X Y Z ≫ enrichedYonedaMap A X Z =
      (enrichedYonedaMap A X Y ⊗ₘ enrichedYonedaMap A Y Z) ≫
        eComp V (representable (R := R) A X)
          (representable (R := R) A Y) (representable (R := R) A Z) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro n₁ n₂ h
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro f g
  change yonedaGradedHom A n
      (dgCompElement A n₁ n₂ n h f g) = _
  change yonedaGradedHom A n
      (dgCompElement A n₁ n₂ n h f g) =
    (HomologicalComplex.ιMapBifunctor (X ⟶[V] Y) (Y ⟶[V] Z)
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) n₁ n₂ n h ≫
      (HomologicalComplex.mapBifunctorMap (enrichedYonedaMap A X Y)
        (enrichedYonedaMap A Y Z) (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ)).f n ≫
      (comp A).f n).hom' (f ⊗ₜ[R] g)
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  unfold comp
  dsimp only
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  rw [show ((curriedTensor (ModuleCat R)).map
      ((enrichedYonedaMap A X Y).f n₁)).app ((Y ⟶[V] Z).X n₂) =
      (enrichedYonedaMap A X Y).f n₁ ▷ (Y ⟶[V] Z).X n₂ by rfl]
  rw [show ((curriedTensor (ModuleCat R)).obj
      ((homComplex A (representable (R := R) A X)
        (representable (R := R) A Y)).X n₁)).map
          ((enrichedYonedaMap A Y Z).f n₂) =
      (homComplex A (representable (R := R) A X)
        (representable (R := R) A Y)).X n₁ ◁
          (enrichedYonedaMap A Y Z).f n₂ by rfl]
  change yonedaGradedHom A n
      (dgCompElement A n₁ n₂ n h f g) =
    (compComponent A n₁ n₂ n h).hom'
      (((homComplex A (representable (R := R) A X)
          (representable (R := R) A Y)).X n₁ ◁
            (enrichedYonedaMap A Y Z).f n₂).hom'
        (((enrichedYonedaMap A X Y).f n₁ ▷ (Y ⟶[V] Z).X n₂).hom'
          (f ⊗ₜ[R] g)))
  rw [show (((enrichedYonedaMap A X Y).f n₁ ▷
      (Y ⟶[V] Z).X n₂).hom' (f ⊗ₜ[R] g)) =
      yonedaGradedHom A n₁ f ⊗ₜ[R] g by
    exact ModuleCat.MonoidalCategory.whiskerRight_apply
      ((enrichedYonedaMap A X Y).f n₁) ((Y ⟶[V] Z).X n₂) f g]
  rw [show (((homComplex A (representable (R := R) A X)
      (representable (R := R) A Y)).X n₁ ◁
        (enrichedYonedaMap A Y Z).f n₂).hom'
          (yonedaGradedHom A n₁ f ⊗ₜ[R] g)) =
      yonedaGradedHom A n₁ f ⊗ₜ[R] yonedaGradedHom A n₂ g by
    exact ModuleCat.MonoidalCategory.whiskerLeft_apply
      ((homComplex A (representable (R := R) A X)
        (representable (R := R) A Y)).X n₁)
      ((enrichedYonedaMap A Y Z).f n₂) (yonedaGradedHom A n₁ f) g]
  unfold compComponent
  change yonedaGradedHom A n
      (dgCompElement A n₁ n₂ n h f g) =
    signedComp A n₁ n₂ n h
      (yonedaGradedHom A n₁ f) (yonedaGradedHom A n₂ g)
  exact yonedaGradedHom_comp A n₁ n₂ n h f g

end DGCategory.RightModule
