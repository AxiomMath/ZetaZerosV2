/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationIntegratedAssembly
import ZetaZeros.Unconditional.PairCorrelationVKEndpoint

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

/-- The pointwise `O(T + x)` BGST comparison, together with the full-zero integrated
contract already required downstream, gives the exact integrated closed-endpoint contract.
No separate measurability assumption on the full-zero moment is needed. -/
theorem integratedFullWindowEndpointComparison_of_bgstFullWindowMomentComparison
    (hfull : IntegratedFullZeroModelSecondMoment)
    (hBGST : BGSTFullWindowMomentComparison) :
    IntegratedFullWindowEndpointComparison := by
  rcases hfull with ⟨Kfull, hKfull, Tfull, hfull⟩
  rcases hBGST with ⟨C, hC, TBGST, hBGST⟩
  refine ⟨2 * C, mul_pos (by norm_num) hC,
    max (max Tfull TBGST) (Real.exp 1), ?_⟩
  intro f L hf hL hLip T hT
  have hTfull : Tfull ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTBGST : TBGST ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hexpT : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTone : 1 ≤ T :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hexpT
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hlogone : 1 ≤ Real.log T :=
    (Real.le_log_iff_exp_le hTpos).2 hexpT
  have hlognonneg : 0 ≤ Real.log T := zero_le_one.trans hlogone
  have hsqrtpos : 0 < Real.sqrt (Real.log T) :=
    Real.sqrt_pos.2 (zero_lt_one.trans_le hlogone)
  have hsqrtone : 1 ≤ Real.sqrt (Real.log T) := by
    nlinarith [Real.sq_sqrt hlognonneg, Real.sqrt_nonneg (Real.log T)]
  have hmainIntegrable := (hfull f L hf hL hLip T hTfull).1
  have hfiniteIntegrable :=
    intervalIntegrable_test_mul_finiteWindowSecondMoment_sub_model f hf T hTpos
  have hcomparisonIntegrable : IntervalIntegrable
      (fun a : ℝ => (f a : ℂ) *
        (finiteWindowSecondMoment (T ^ a) T -
          windowedFullZeroSecondMoment (T ^ a) T)) volume 0 1 := by
    convert hfiniteIntegrable.sub hmainIntegrable using 1
    funext a
    ring
  refine ⟨hcomparisonIntegrable, ?_⟩
  have hmajorIntegrable : IntervalIntegrable
      (fun a : ℝ => (2 * C * T) * |f a|) volume 0 1 := by
    have habs : IntervalIntegrable (fun a : ℝ => |f a|) volume 0 1 := by
      simpa only [Real.norm_eq_abs] using hf.norm.intervalIntegrable
    exact habs.const_mul (2 * C * T)
  have hpoint : ∀ a : ℝ, a ∈ Set.uIoc (0 : ℝ) 1 →
      ‖(f a : ℂ) *
          (finiteWindowSecondMoment (T ^ a) T -
            windowedFullZeroSecondMoment (T ^ a) T)‖ ≤
        (2 * C * T) * |f a| := by
    intro a ha
    rw [Set.uIoc_of_le zero_le_one] at ha
    have ha0 : 0 ≤ a := le_trans (by simpa using ha.1.le) le_rfl
    have ha1 : a ≤ 1 := ha.2
    have hxa : 1 ≤ T ^ a := Real.one_le_rpow hTone ha0
    have hxaT : T ^ a ≤ T := by
      simpa using Real.rpow_le_rpow_of_exponent_le hTone ha1
    have hraw := hBGST T hTBGST (T ^ a) hxa hxaT
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |f a| * ‖finiteWindowSecondMoment (T ^ a) T -
          windowedFullZeroSecondMoment (T ^ a) T‖ ≤
          |f a| * (C * (T + T ^ a)) :=
        mul_le_mul_of_nonneg_left hraw (abs_nonneg _)
      _ ≤ |f a| * (C * (2 * T)) := by
        gcongr
        linarith
      _ = (2 * C * T) * |f a| := by ring
  have hnormBound :
      ‖∫ a : ℝ in 0..1, (f a : ℂ) *
          (finiteWindowSecondMoment (T ^ a) T -
            windowedFullZeroSecondMoment (T ^ a) T)‖ ≤
        ∫ a : ℝ in 0..1, (2 * C * T) * |f a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · filter_upwards [] with a ha
      exact hpoint a (by simpa [Set.uIoc_of_le zero_le_one] using ha)
    · exact hmajorIntegrable
  have hI : 0 ≤ ∫ a : ℝ in 0..1, |f a| := by
    exact intervalIntegral.integral_nonneg zero_le_one fun a _ => abs_nonneg _
  have hISize :
      (∫ a : ℝ in 0..1, |f a|) ≤ integratedTestSize f L := by
    unfold integratedTestSize
    linarith [abs_nonneg (f 0)]
  have hsize : 0 ≤ integratedTestSize f L := le_trans hI hISize
  have hnorm : 2 * Real.pi * ‖pairNormalization T‖ = T * Real.log T := by
    rw [pairNormalization, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos]
    · field_simp
    · positivity
  calc
    ‖∫ a : ℝ in 0..1, (f a : ℂ) *
        (finiteWindowSecondMoment (T ^ a) T -
          windowedFullZeroSecondMoment (T ^ a) T)‖ ≤
        ∫ a : ℝ in 0..1, (2 * C * T) * |f a| := hnormBound
    _ = (2 * C * T) * (∫ a : ℝ in 0..1, |f a|) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (2 * C * T) * integratedTestSize f L := by
      exact mul_le_mul_of_nonneg_left hISize (by positivity)
    _ ≤ (2 * C * T) *
        (Real.sqrt (Real.log T) * integratedTestSize f L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left hsize hsqrtone
    _ = T * Real.log T *
        ((2 * C) * integratedTestSize f L / Real.sqrt (Real.log T)) := by
      field_simp [ne_of_gt hsqrtpos]
      ring_nf
      rw [Real.sq_sqrt hlognonneg]
      ring
    _ = 2 * Real.pi * ‖pairNormalization T‖ *
        ((2 * C) * integratedTestSize f L / Real.sqrt (Real.log T)) := by
      rw [hnorm]

/-- The Vinogradov--Korobov form of the BGST endpoint theorem gives the same exact
integrated endpoint contract after the elementary remainder absorption. -/
theorem integratedFullWindowEndpointComparison_of_bgstVinogradovKorobovMomentComparison
    (hfull : IntegratedFullZeroModelSecondMoment)
    (hBGST : BGSTVinogradovKorobovMomentComparison) :
    IntegratedFullWindowEndpointComparison :=
  integratedFullWindowEndpointComparison_of_bgstFullWindowMomentComparison hfull
    (bgstFullWindowMomentComparison_of_vinogradovKorobov hBGST)

end ZetaZeros.Unconditional.PairCorrelationProof
