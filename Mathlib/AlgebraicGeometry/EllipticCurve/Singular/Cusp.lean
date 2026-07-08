/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Singular cubic with cusps

We introduce the standard cusp curve `Y² = X³`, on which lies the rational point `(1,1)`, with
the nice property that `ψₙ(1,1) = n`, from which we can show that the universal division polynomial
`ψₙ ≠ 0` when `n ≠ 0` by specializing, or equivalently `(X,Y)` is a point of infinite
order on the universal pointed elliptic curve.
-/

namespace WeierstrassCurve

variable (R) [CommRing R] (W : WeierstrassCurve R)

/-- The standard cusp curve `Y² = X³` over a commutative ring. -/
@[expose] public def standardCusp : WeierstrassCurve R :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

lemma standardCusp_equation_one_one : Affine.Equation (standardCusp R) 1 1 := by
  simp [Affine.Equation, Affine.polynomial, standardCusp, Polynomial.evalEval]

end WeierstrassCurve
