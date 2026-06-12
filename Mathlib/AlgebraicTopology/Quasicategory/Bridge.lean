module

public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.CategoryTheory.Monoidal.Subcategory

@[expose] public section

universe u

namespace SSet

open CategoryTheory MonoidalClosed MonoidalCategory Simplicial SimplicialObject.Truncated Truncated

open Quasicategory SemiCartesianMonoidalCategory in
instance : ObjectProperty.IsMonoidal Quasicategory where
  prop_unit := {
    hornFilling' := fun _ _ _ _ _ ↦ ⟨toUnit _, by cat_disch⟩ }
  prop_tensor _ _ _ _ := {
    hornFilling' _ _ σ₀ h0 hn := by
      obtain ⟨σ_X, _⟩ := hornFilling h0 hn (σ₀ ≫ fst ..)
      obtain ⟨σ_Y, _⟩ := hornFilling h0 hn (σ₀ ≫ snd ..)
      use CartesianMonoidalCategory.lift σ_X σ_Y
      cat_disch }

instance : ObjectProperty.IsMonoidalClosed Quasicategory where
  prop_ihom _ _ _ _ := inferInstance

variable (C D : QCat)

def QCat.functorQCat : QCat := (ihom C).obj D

open stdSimplex Functor SemiCartesianMonoidalCategory in
@[simps!]
def QCat.functorVertexEquivAux : (functorQCat C D).obj _⦋0⦌ ≃ (C.obj ⟶ D.obj) :=
  (yonedaEquiv.symm.trans ((functorHomEquiv ..).trans (homObjEquiv ..))).trans
    (C.obj ◁ᵢ (isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit) ≪≫ ρ_ C.obj).homFromEquiv

abbrev QCat.functorVertex {C D} (F : C ⟶ D) : (functorQCat C D).obj _⦋0⦌ :=
  (functorVertexEquivAux _ _).symm F.hom

abbrev QCat.functorOfVertex {C D} (x : (functorQCat C D).obj _⦋0⦌) : C ⟶ D :=
  ObjectProperty.homMk ((functorVertexEquivAux _ _) x)

open stdSimplex Functor SemiCartesianMonoidalCategory in
@[simps!]
def QCat.functorVertexEquiv : (functorQCat C D).obj _⦋0⦌ ≃ (C ⟶ D) where
  toFun := functorOfVertex
  invFun := functorVertex
  left_inv _ := by simp [functorVertex]

instance : Category (C ⟶ D) := QCat.bicategory.homCategory C D
instance : Quasicategory D.obj := D.property

variable {C D} {F G H : C ⟶ D}

def QCat.edgeToTwoCell (e : SSet.Edge (functorVertex F) (functorVertex G)) : F ⟶ G where
  base' := HomotopyCategory.homMk e

@[simp]
def QCat.edgeToTwoCell.comp_eq (e₀ : Edge (functorVertex F) (functorVertex G))
      (e₁ : Edge (functorVertex G) (functorVertex H))
      (e₂ : Edge (functorVertex F) (functorVertex H)) (h : Edge.CompStruct e₀ e₁ e₂) :
    edgeToTwoCell e₀ ≫ edgeToTwoCell e₁ = edgeToTwoCell e₂ :=
  CatEnrichedOrdinary.Hom.ext _ _ (Truncated.HomotopyCategory.homMk_comp_homMk h)

@[simp]
def QCat.edgeToTwoCell.id_eq : edgeToTwoCell (Edge.id (functorVertex F)) = 𝟙 _ :=
  CatEnrichedOrdinary.Hom.ext _ _ (Truncated.HomotopyCategory.homMk_id _)

-- Done elsewhere
instance (X : SSet) [X.Quasicategory] : ((truncation 2).obj X).Quasicategory₂ := sorry

noncomputable
def quotientReflPrefunctor₂ {A : Truncated.{u} 2} [Quasicategory₂ A] :
    (OneTruncation₂.{u} A) ⥤rq (HomotopyCategory₂.{u} A) where
  obj X := ⟨X⟩
  map f := Quotient.mk' { edge := f.edge, src_eq := f.src_eq, tgt_eq := f.tgt_eq }

noncomputable
def quotientFunctor₂ {A : Truncated.{u} 2} [Quasicategory₂ A] :
    Cat.FreeRefl (OneTruncation₂ A) ⥤ HomotopyCategory₂ A :=
  ((ReflQuiv.adj.homEquiv
    (V := (ReflQuiv.of (OneTruncation₂ A)))
    (C := (Cat.of (HomotopyCategory₂ A)))).invFun quotientReflPrefunctor₂)

set_option backward.isDefEq.respectTransparency false in
lemma qFunctor_map_toPath {A : Truncated.{u} 2} [Quasicategory₂ A]
    (x y : Cat.FreeRefl.{u} (OneTruncation₂ A)) (f : Truncated.Edge x.as y.as) :
    quotientFunctor₂.map.{u} (Quot.mk _ (Quiver.Hom.toPath f)) = quotientReflPrefunctor₂.map f := by
  dsimp [quotientFunctor₂, Adjunction.homEquiv, Cat.FreeRefl.lift]
  dsimp [quotientReflPrefunctor₂, Cat.FreeRefl.homMk,
    Cat.FreeRefl.quotientFunctor, Quotient.functor, ReflQuiv.adj, ReflQuiv.adj.homEquiv,
    Cat.FreeRefl.lift, Paths.lift, CategoryTheory.Quotient.lift, Cat.Hom.equivFunctor]
  rw [Quot.liftOn_mk]
  change 𝟙 _ ≫ _ = _
  simp

theorem qFunctor_respects_horel₂ {A : Truncated.{u} 2} [Quasicategory₂ A]
    (x y : Cat.FreeRefl.{u} (OneTruncation₂.{u} A)) (f g : x ⟶ y)
    (r : OneTruncation₂.HoRel₂ _ f g) :
    quotientFunctor₂.map.{u} f = quotientFunctor₂.map.{u} g := by
  rcases r with @⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, hcs⟩
  change
    quotientFunctor₂.map (Quot.mk _ (Quiver.Hom.toPath e₀₁) ≫ Quot.mk _ (Quiver.Hom.toPath e₁₂))
      = quotientFunctor₂.map (Quot.mk _ (Quiver.Hom.toPath e₀₂))
  rw [Functor.map_comp, qFunctor_map_toPath, qFunctor_map_toPath, qFunctor_map_toPath]
  exact hcs.homotopyCategory₂_fac

def edgeToHom {A : Truncated.{u} 2} {x₀ x₁ : A _⦋0⦌₂} (f : Truncated.Edge x₀ x₁) :
    @Quiver.Hom (OneTruncation₂.{u} A) _ x₀ x₁ where
  edge := f.edge
  src_eq := f.src_eq
  tgt_eq := f.tgt_eq

def edgeToFreeHom {A : Truncated.{u} 2} {x₀ x₁ : A _⦋0⦌₂}
    (f : Truncated.Edge x₀ x₁) :
    @Quiver.Hom (Cat.FreeRefl.{u} (OneTruncation₂.{u} A)) _ ⟨x₀⟩ ⟨x₁⟩ :=
  Quot.mk _ (edgeToHom f).toPath

lemma compose_id_path {A : Truncated.{u} 2} {x₀ x₁ : A _⦋0⦌₂} (f : Truncated.Edge x₀ x₁) :
    edgeToFreeHom f = Quot.mk _
      ((edgeToHom f).toPath.comp (edgeToHom (Truncated.Edge.id x₁)).toPath) := by
  rw [show edgeToFreeHom f = Cat.FreeRefl.homMk (edgeToHom f) from rfl]
  rw [← Category.comp_id (Cat.FreeRefl.homMk (edgeToHom f)),
      ← Cat.FreeRefl.homMk_id (V := OneTruncation₂ A) x₁]
  rw [Quiver.Path.comp_toPath_eq_cons]
  rfl

lemma homotopic_edges_are_equiv {A : Truncated.{u} 2} [Quasicategory₂ A] {x₀ x₁ : A _⦋0⦌₂}
    (f g : Truncated.Edge.{u} x₀ x₁) (htpy : HomotopicL f g) :
    OneTruncation₂.HoRel₂ _ (edgeToFreeHom f) (edgeToFreeHom g) := by
  rw [compose_id_path f]
  rcases htpy with ⟨htpy⟩
  exact OneTruncation₂.HoRel₂.of_compStruct htpy

noncomputable
def liftRq₂ {A : Truncated.{u} 2} [Quasicategory₂ A] {C : Type*} [ReflQuiver C]
    (F : Cat.FreeRefl.{u} (OneTruncation₂.{u} A) ⥤rq C)
    (h : ∀ (x y : Cat.FreeRefl.{u} (OneTruncation₂.{u} A))
      (f g : x ⟶ y),
      (r : OneTruncation₂.HoRel₂ _ f g) → F.map f = F.map g) :
    HomotopyCategory₂.{u} A ⥤rq C where
  obj x := F.obj ⟨x.1⟩
  map f := Quotient.liftOn f
    (fun e ↦ F.map (edgeToFreeHom e))
    (fun f g ↦ by
      intro htpy
      apply h
      exact homotopic_edges_are_equiv f g htpy)
  map_id := by
    intro x
    dsimp [CategoryStruct.id]
    have e : edgeToFreeHom (Truncated.Edge.id x.pt) =
        𝟙 (⟨x.1⟩ : Cat.FreeRefl.{u} (OneTruncation₂.{u} A)) :=
      Cat.FreeRefl.homMk_id (V := OneTruncation₂ A) x.pt
    change F.map (edgeToFreeHom (Truncated.Edge.id x.pt)) = 𝟙rq (F.obj ⟨x.1⟩)
    rw [e]
    exact F.map_id _

noncomputable
def lift₂ {A : Truncated.{u} 2} [Quasicategory₂ A] {C : Type*} [Category* C]
    (F : Cat.FreeRefl.{u} (OneTruncation₂.{u} A) ⥤ C)
    (h : ∀ (x y : Cat.FreeRefl.{u} (OneTruncation₂.{u} A))
      (f g : x ⟶ y),
      (r : OneTruncation₂.HoRel₂ _ f g) → F.map f = F.map g) :
    HomotopyCategory₂ A ⥤ C := by
  let G := liftRq₂ F.toReflPrefunctor h
  exact {
    obj := G.obj
    map := G.map
    map_id := G.map_id
    map_comp := by
      intro x₀ x₁ x₂
      apply Quotient.ind₂
      intro f g
      dsimp only [G, liftRq₂, Quotient.lift_mk, Functor.toReflPrefunctor]
      rw [← Functor.map_comp]
      let p := (Quasicategory₂.fill21 f g).some
      -- `⟦f⟧ ≫ ⟦g⟧` is defeq `⟦p.fst⟧`.
      change F.map (edgeToFreeHom p.fst) = F.map (edgeToFreeHom f ≫ edgeToFreeHom g)
      -- `.symm`: `of_compStruct` orients the relation as `composite`–`single`.
      exact (h _ _ _ _ (OneTruncation₂.HoRel₂.of_compStruct p.snd)).symm
  }

-- Done elsewhere
noncomputable
def isoHomotopyCategories (A : Truncated 2) [A.Quasicategory₂] :
    (Cat.of (HomotopyCategory.{u} A)) ≅ (Cat.of (HomotopyCategory₂.{u} A)) where
  hom := (CategoryTheory.Quotient.lift _ quotientFunctor₂ qFunctor_respects_horel₂).toCatHom
  inv := lift₂ (HomotopyCategory.quotientFunctor.{u} A) (fun _ _ _ _ h =>
    CategoryTheory.Quotient.sound _ h) |>.toCatHom
  hom_inv_id := sorry
  inv_hom_id := sorry

lemma HomotopyCategory.homMk_surjective {A : Truncated 2} [Quasicategory₂ A] {x y : A _⦋0⦌₂} :
    Function.Surjective (HomotopyCategory.homMk : Truncated.Edge x y → _) := by
  intro f
  have h := HomotopyCategory₂.homMk_surjective ((isoHomotopyCategories A).hom.toFunctor.map f)
  have H := congr_arg ((isoHomotopyCategories A).inv.toFunctor.map) h.choose_spec
  have : (isoHomotopyCategories A).inv.toFunctor.map
      ((isoHomotopyCategories A).hom.toFunctor.map f) = f := by
    rw [← @Cat.Hom.comp_map]
    rw [Functor.congr_hom (congr_arg Cat.Hom.toFunctor (isoHomotopyCategories A).hom_inv_id) f]
    exact Eq.symm (eq_conj_eqToHom f)
  erw [this] at H
  exact ⟨h.choose, H⟩

noncomputable
def QCat.twoCellRepresentative (α : F ⟶ G) :
    SSet.Edge (functorVertex F) (functorVertex G) :=
  (HomotopyCategory.homMk_surjective (A := (truncation 2).obj (C.functorQCat D).obj) α.base).choose

@[simp]
lemma QCat.edgeToTwoCell_twoCellRepresentative (α : F ⟶ G) :
    edgeToTwoCell (twoCellRepresentative α) = α := by
  apply CatEnrichedOrdinary.Hom.ext
  exact (HomotopyCategory.homMk_surjective
    (A := (truncation 2).obj (C.functorQCat D).obj) α.base).choose_spec

@[ext]
structure Edge.InvStruct {X : SSet} {x₀ x₁ : X _⦋0⦌} (hom : Edge x₀ x₁) where
  /-- The backwards edge -/
  inv : Edge x₁ x₀
  /-- The simplex witnessing that `hom` and `inv` compose to the identity -/
  homInvId  : CompStruct hom inv (id x₀)
  /-- The simplex witnessing that `inv` and `hom` compose to the identity -/
  invHomId  : CompStruct inv hom (id x₁)

lemma QCat.edgeToTwoCell.isIso_of_equivalenceEdge
    (e : Edge (functorVertex F) (functorVertex G)) (he : Edge.InvStruct e) :
    IsIso (edgeToTwoCell e) where
  out := by
    use (edgeToTwoCell) he.inv
    simp [comp_eq _ _ _ he.homInvId, id_eq, comp_eq _ _ _ he.invHomId]

open HomotopyCategory in
lemma QCat.CompStruct.nonempty_iff {A : Truncated 2} [Quasicategory₂ A]
    {x y z : A _⦋0⦌₂} {f : Truncated.Edge x y} {g : Truncated.Edge y z} {h : Truncated.Edge x z} :
    Nonempty (Truncated.Edge.CompStruct f g h) ↔ homMk f ≫ homMk g = homMk h :=
  sorry

-- Doable
noncomputable
def QCat.invStruct_twoCellRepresentative_of_isIso
    (α : F ⟶ G) [IsIso α] : Edge.InvStruct (QCat.twoCellRepresentative α) where
  inv := twoCellRepresentative (inv α)
  homInvId := by
    refine (CompStruct.nonempty_iff.2 ?_).some
    have := Edge.compStruct (twoCellRepresentative α) (twoCellRepresentative (inv α))
    erw [HomotopyCategory.homMk_comp_homMk this]
    simp
    sorry
  invHomId := sorry

end SSet
