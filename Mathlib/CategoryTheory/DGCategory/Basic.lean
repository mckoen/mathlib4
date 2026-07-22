import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

universe w

open CategoryTheory

variable {R : Type w} [CommRing R]

instance : (MonoidalCategory.curriedTensor (ModuleCat.{w} R)).Additive :=
  MonoidalPreadditive.instAdditiveFunctorCurriedTensor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' (fun (i : ℤ) => (-1 : ℤˣ) ^ i) (zpow_add (-1 : ℤˣ))
  rel_add p q r (hpq : q + 1 = p) := by dsimp; lia
  add_rel p q r (hpq : q + 1 = p) := by dsimp; lia
  ε'_succ := by
    rintro _ q rfl
    dsimp
    erw [zpow_add]
    rw [zpow_one, mul_neg, mul_one, neg_neg]
    rfl

abbrev DGCategory (R : Type w) [CommRing R] := EnrichedCategory (ChainComplex (ModuleCat.{w} R) ℤ)
