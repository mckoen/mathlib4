/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/

module

public import Mathlib.CategoryTheory.DGCategory.PretriangulatedHull

/-!
# Linear triangulated categories without DG enhancements

This file gives the statement-level formulation of DG enhanceability using mathlib's ordinary
typeclass-based category interface.  No category, field, or equivalence is repackaged into a
project-specific bundle.

For a pretriangulated DG category `A`, the source of an enhancement is the literal homotopy
category `H⁰(A)`. Its zero object, shifts, and pretriangulation are transported from the
pretriangulated hull along the quasi-equivalence induced by enriched Yoneda.

The final proposition is relative to one fixed ambient universe.  It is parameterized by an
arbitrary characteristic-zero field `k`, in accordance with the quantification in the paper.
The paper-specific construction and obstruction proof remain outside this statement interface.
-/

@[expose] public section

universe w

noncomputable section

open CategoryTheory

namespace DGCategory

/-- The proposition that an `R`-linear triangulated category admits a DG enhancement.

The witnesses are an `R`-linear DG category `A`, the property that enriched Yoneda identifies
`A` with its pretriangulated hull up to quasi-equivalence, and an ordinary equivalence from
literal `H⁰(A)` to `T` whose forward functor is linear, commutes coherently with shifts, and
is triangulated. -/
def Enhanceable {R : Type w} [CommRing R]
    (T : Type w) [Category.{w} T] [Preadditive T] [Linear R T]
    [Limits.HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive]
    [∀ n : ℤ, (shiftFunctor T n).Linear R]
    [Pretriangulated T] [IsTriangulated T] : Prop :=
  ∃ (A : Type w)
    (_ : DGCategory R A)
    (_ : IsPretriangulatedDG (R := R) A)
    (e : HomotopyCategory (R := R) A ≌ T)
    (_ : e.functor.Linear R)
    (_ : e.functor.CommShift ℤ),
    e.functor.IsTriangulated

/-- For an arbitrary characteristic-zero field `k`, there is a `k`-linear triangulated category
with no DG enhancement, relative to the fixed ambient universe `w`.

This is the formal proposition advertised by the paper.  It is a statement, not a formal proof
of the paper's example or obstruction argument. -/
def CharacteristicZeroNonenhanceabilityStatement
    (k : Type w) [Field k] [CharZero k] : Prop :=
  ∃ (T : Type w)
    (_ : Category.{w} T)
    (_ : Preadditive T)
    (_ : Linear k T)
    (_ : Limits.HasZeroObject T)
    (_ : HasShift T ℤ)
    (_ : ∀ n : ℤ, (shiftFunctor T n).Additive)
    (_ : ∀ n : ℤ, (shiftFunctor T n).Linear k)
    (_ : Pretriangulated T)
    (_ : IsTriangulated T),
    ¬ Enhanceable (R := k) T

end DGCategory
