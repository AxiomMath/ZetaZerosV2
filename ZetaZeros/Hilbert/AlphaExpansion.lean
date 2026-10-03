/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Hilbert.AlphaExpansion.Coefficients
public import ZetaZeros.Hilbert.AlphaExpansion.CoefficientSums
public import ZetaZeros.Hilbert.AlphaExpansion.AdaptedBasis
public import ZetaZeros.Hilbert.AlphaExpansion.RescaledZeros
public import ZetaZeros.Hilbert.AlphaExpansion.KernelBessel
public import ZetaZeros.Hilbert.AlphaExpansion.SecondMoment

/-!
# The Bessel expansion of the kernel second moment

This module collects the six modules under `ZetaZeros.Hilbert.AlphaExpansion`: the Bessel
coefficients of the two-variable kernel against a symmetric adapted orthonormal basis, the
estimates on their sums over the three ranges of the basis, and the resulting lower bounds.

## Main results

* `alphaCoeff_eq`: the Bessel coefficient in terms of one-variable integrals.
* `alphaCoeff_im_eq_zero`: the Bessel coefficients are real.
* `alphaOf_re_nonpos`: past `dim V` the Bessel coefficient is non-positive.
* `finrank_subspaceU_le`: `dim U ≤ |R₂| + |S| / 2`.
* `sum_alphaOf_re_le_card_simpleRealPart`: the coefficients with `dim U ≤ j < dim V` sum to at
  most `|R₁|`.
* `sum_alphaOf_re_eq_sum_mult`: over the whole basis the coefficients sum to the total
  multiplicity.
* `exists_isAdaptedBasis_symmetric`: a symmetric adapted orthonormal basis exists.
* `sum_alphaOf_re_sq_le_integral_norm_bigF_sq`: Bessel's inequality for the two-variable kernel.
* `isConjInvariant_rescaledZerosFinset`: the rescaled zeros form a conjugation-invariant multiset.
* `sum_alphaOf_re_first_lower`: the coefficients with `j < dim U` sum to at least `2|R₂| + |S|`.
* `card_simpleRealPart_lower`: the lower bound for the number of simple real elements.
* `card_lower`: the lower bound for the number of distinct elements.
-/
