/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationIntegratedAssembly
import ZetaZeros.Unconditional.PairCorrelationAssembly

/-!
# Integrating the closed-endpoint full-window comparison

The pointwise Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh comparison has exactly the
size needed by the integrated pair-correlation assembly.  A pointwise norm bound alone does
not imply measurability of the moment difference.  Rather than adding an artificial
regularity hypothesis, this file obtains the required interval integrability from the
integrated full-zero moment contract already needed by the final assembly: the finite-pair
and model terms are continuous in the exponent, while the remaining full-zero error is
integrable by that contract.

Thus the only analytic endpoint input below is `BGSTFullWindowMomentComparison`.  Its proof
is precisely the still-missing Vinogradov--Korobov-strength truncation theorem recorded in
`PairCorrelationVKEndpoint`.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set

/-- Montgomery's finite pair function is continuous in the logarithmic exponent. -/
theorem continuous_finitePairFunction_rpow (T : ℝ) (hT : 0 < T) :
    Continuous (fun a : ℝ => finitePairFunction (T ^ a) T) := by
  rw [show (fun a : ℝ => finitePairFunction (T ^ a) T) =
      fun a : ℝ =>
        ∑ rho ∈ (Zeta23.zerosIn_finite 0 T).toFinset,
          ∑ rho' ∈ (Zeta23.zerosIn_finite 0 T).toFinset,
            ((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ) *
              pairPower (T ^ a) (rho - rho') * finitePairKernel (rho - rho') by
    funext a
    exact finitePairFunction_eq_finset_sum (T ^ a) T]
  apply continuous_finsetSum
  intro rho hrho
  apply continuous_finsetSum
  intro rho' hrho'
  exact ((continuous_const.mul
    (continuous_pairPower_rpow T (rho - rho') hT)).mul continuous_const)

/-- The explicit model is continuous in the logarithmic exponent for positive height. -/
theorem continuous_finitePairModel (T : ℝ) (hT : 0 < T) :
    Continuous (finitePairModel T) := by
  unfold finitePairModel
  rw [show (fun a : ℝ => T ^ (-2 * a) * Real.log T + a) =
      fun a : ℝ => Real.exp (Real.log T * (-2 * a)) * Real.log T + a by
    funext a
    rw [Real.rpow_def_of_pos hT]]
  fun_prop

/-- The finite-window moment minus the explicit model is interval integrable against every
integrable test function. -/
theorem intervalIntegrable_test_mul_finiteWindowSecondMoment_sub_model
    (f : ℝ → ℝ) (hf : Integrable f) (T : ℝ) (hT : 0 < T) :
    IntervalIntegrable
      (fun a : ℝ => (f a : ℂ) *
        (finiteWindowSecondMoment (T ^ a) T -
          ((2 * Real.pi : ℝ) : ℂ) * pairNormalization T *
            (finitePairModel T a : ℂ))) volume 0 1 := by
  have hfC : IntervalIntegrable (fun a : ℝ => (f a : ℂ)) volume 0 1 :=
    hf.ofReal.intervalIntegrable
  have hfinite : Continuous (fun a : ℝ =>
      finiteWindowSecondMoment (T ^ a) T) := by
    rw [show (fun a : ℝ => finiteWindowSecondMoment (T ^ a) T) =
        (fun _ : ℝ => (2 : ℂ) * (Real.pi : ℂ)) *
          (fun a : ℝ => finitePairFunction (T ^ a) T) by
      funext a
      rw [finiteWindowSecondMoment_eq]
      simp only [Pi.mul_apply]]
    exact continuous_const.mul (continuous_finitePairFunction_rpow T hT)
  have hmodel : Continuous (fun a : ℝ =>
      ((2 * Real.pi : ℝ) : ℂ) * pairNormalization T *
        (finitePairModel T a : ℂ)) := by
    exact (continuous_const.mul continuous_const).mul
      (Complex.continuous_ofReal.comp (continuous_finitePairModel T hT))
  exact hfC.mul_continuousOn (hfinite.sub hmodel).continuousOn

end ZetaZeros.Unconditional.PairCorrelationProof
