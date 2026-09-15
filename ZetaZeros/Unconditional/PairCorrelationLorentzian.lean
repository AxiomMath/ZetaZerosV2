/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationBasic

/-!
# Elementary Lorentzian estimates for pair correlation

This file starts the Lorentzian dependency chain in the unconditional blueprint with its purely
algebraic denominator estimate.
-/

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex

/-- Blueprint `lem_lorentz_lower`: a uniform lower bound for a Lorentzian denominator in the
critical strip. -/
theorem shiftedLorentzian_norm_lower (u δ : ℝ) (hδ : |δ| ≤ (1 / 2 : ℝ)) :
    (3 / 4 : ℝ) * (1 + u ^ 2) ≤
      ‖(1 : ℂ) + ((u : ℂ) + Complex.I * (δ : ℂ)) ^ 2‖ := by
  rw [abs_le] at hδ
  calc
    (3 / 4 : ℝ) * (1 + u ^ 2) ≤ 1 - δ ^ 2 + u ^ 2 := by
      nlinarith [sq_nonneg (δ - 1 / 2), sq_nonneg (δ + 1 / 2)]
    _ = ((1 : ℂ) + ((u : ℂ) + Complex.I * (δ : ℂ)) ^ 2).re := by
      simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.one_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    _ ≤ ‖(1 : ℂ) + ((u : ℂ) + Complex.I * (δ : ℂ)) ^ 2‖ :=
      Complex.re_le_norm _

end ZetaZeros.Unconditional.PairCorrelationProof
