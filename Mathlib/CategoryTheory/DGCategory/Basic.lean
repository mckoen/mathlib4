/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

@[expose] public section

universe u w

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

/-- A category enriched over cochain complexes of `R`-modules. -/
abbrev DGCategory (R : Type w) [CommRing R] :=
  EnrichedCategory (ChainComplex (ModuleCat.{w} R) ℤ)
