/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import Zeta23.FromPNTPlus.MediumPNT

/-!
# A quantitative prime number theorem for pair correlation

This file gives the pair-correlation development a stable, namespaced interface to the
medium-strength prime number theorem vendored from the permitted `zeta23` reference.
-/

namespace ZetaZeros.Unconditional

open Filter
open scoped Chebyshev

/-- A quantitative PNT input for the prime sums in the BGST pair-correlation argument. -/
theorem pairCorrelation_mediumPNT :
    ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) :=
  MediumPNT

end ZetaZeros.Unconditional
