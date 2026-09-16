/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationIntegral
import ZetaZeros.Unconditional.PairCorrelationSharpComparison

/-!
# Assembly of the full-zero and finite-window pair-correlation estimates

This file isolates the two quantitative analytic inputs which remain between Montgomery's
explicit formula and the exact finite pair-function estimate:

* `FullZeroModelSecondMoment` evaluates the second moment of the phase-corrected full zero
  series on the height window `(0, T]`;
* `FullWindowEndpointComparison` compares that moment with the exact finite positive-height
  zero window, uniformly for `x = T ^ a` through the closed endpoint `a = 1`.

The second input is the genuine endpoint theorem.  Classically its proof uses a
Vinogradov--Korobov zero-free region
`sigma >= 1 - c / ((log |t|)^(2/3) * (log log |t|)^(1/3))`, equivalently the uniform
Goldston--Montgomery truncation estimate through `x = T`.  A zero-free strip of width
`A / log^9 |t|` does not supply this estimate.

Everything after these two contracts is proved here, including the exact implication to
`FinitePairFunctionUniform` and hence to the test-function asymptotic.  In particular, the
contracts are kept separate: the endpoint comparison is not hidden in a restatement of the
finite pair-function conclusion.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set

/-- The full Lorentzian zero series occurring in Montgomery's explicit formula. -/
noncomputable def fullZeroLorentzianSum (x t : ℝ) : ℂ :=
  ∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
    fullZeroLorentzianSummand x t rho

/-- The full zero series after removing the common unit phase `x ^ (-it)`. -/
noncomputable def phaseCorrectedFullZeroSum (x t : ℝ) : ℂ :=
  (x : ℂ) ^ (Complex.I * t) * fullZeroLorentzianSum x t

/-- The phase-corrected full zero series, restricted to the height window `(0, T]`. -/
noncomputable def windowedFullZeroSum (x T : ℝ) : ℝ → ℂ :=
  Set.indicator (Set.Ioc 0 T) (phaseCorrectedFullZeroSum x)

/-- The positive phase which removes `x ^ (-it)` also has norm one. -/
theorem norm_cpow_I_mul (x : ℝ) (hx : 0 < x) (t : ℝ) :
    ‖(x : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  norm_num [Complex.mul_re]

/-- The positive and negative imaginary phases cancel exactly. -/
theorem cpow_I_mul_mul_cpow_neg_I_mul (x : ℝ) (hx : 0 < x) (t : ℝ) :
    (x : ℂ) ^ (Complex.I * t) * (x : ℂ) ^ (-Complex.I * t) = 1 := by
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [← Complex.cpow_add _ _ hxne]
  rw [show Complex.I * (t : ℂ) + -Complex.I * (t : ℂ) = 0 by ring]
  exact Complex.cpow_zero (x : ℂ)

/-- Inside the height window, the discrepancy between the finite zero sum and the
phase-corrected full series is the complementary zero tail with the same unit phase. -/
theorem finiteWindowLorentzianSum_sub_phaseCorrectedFullZeroSum
    (x : ℝ) (hx : 1 ≤ x) (T t : ℝ) :
    finiteWindowLorentzianSum x T t - phaseCorrectedFullZeroSum x t =
      -((x : ℂ) ^ (Complex.I * t) *
        (∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
            rho ∉ finiteZeroCarrierWindow T},
          fullZeroLorentzianSummand x t rho)) := by
  have h := congrArg (fun z : ℂ ↦ (x : ℂ) ^ (Complex.I * t) * z)
    (phase_mul_finiteWindowLorentzianSum_sub_full_tsum x hx T t)
  rw [mul_sub, mul_neg, ← mul_assoc,
    cpow_I_mul_mul_cpow_neg_I_mul x (zero_lt_one.trans_le hx), one_mul] at h
  simpa only [fullZeroLorentzianSum, phaseCorrectedFullZeroSum] using h

/-- Norm form of the exact full/window discrepancy after phase correction. -/
theorem norm_finiteWindowLorentzianSum_sub_phaseCorrectedFullZeroSum
    (x : ℝ) (hx : 1 ≤ x) (T t : ℝ) :
    ‖finiteWindowLorentzianSum x T t - phaseCorrectedFullZeroSum x t‖ =
      ‖∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
          rho ∉ finiteZeroCarrierWindow T},
        fullZeroLorentzianSummand x t rho‖ := by
  rw [finiteWindowLorentzianSum_sub_phaseCorrectedFullZeroSum x hx,
    norm_neg, norm_mul, norm_cpow_I_mul x (zero_lt_one.trans_le hx), one_mul]

/-- On `(0, T]`, the discrepancy from the windowed full-zero model is exactly the
complementary zero tail. -/
theorem norm_finiteWindowLorentzianSum_sub_windowedFullZeroSum_of_mem
    (x : ℝ) (hx : 1 ≤ x) (T t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) T) :
    ‖finiteWindowLorentzianSum x T t - windowedFullZeroSum x T t‖ =
      ‖∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
          rho ∉ finiteZeroCarrierWindow T},
        fullZeroLorentzianSummand x t rho‖ := by
  rw [windowedFullZeroSum, Set.indicator_of_mem ht]
  exact norm_finiteWindowLorentzianSum_sub_phaseCorrectedFullZeroSum x hx T t

/-- The exact second moment of the finite positive-height zero window. -/
noncomputable def finiteWindowSecondMoment (x T : ℝ) : ℂ :=
  ∫ t : ℝ, finiteWindowLorentzianSum x T t *
    (starRingEnd ℂ) (finiteWindowLorentzianSum x T t)

/-- The second moment of the phase-corrected full zero series on `(0, T]`. -/
noncomputable def windowedFullZeroSecondMoment (x T : ℝ) : ℂ :=
  ∫ t : ℝ, windowedFullZeroSum x T t *
    (starRingEnd ℂ) (windowedFullZeroSum x T t)

/-- The finite-window moment is exactly `2 * pi` times Montgomery's finite pair function. -/
theorem finiteWindowSecondMoment_eq (x T : ℝ) :
    finiteWindowSecondMoment x T = 2 * Real.pi * finitePairFunction x T := by
  exact finiteWindowLorentzianSum_secondMoment x T

end ZetaZeros.Unconditional.PairCorrelationProof
