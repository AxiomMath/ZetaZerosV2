import ZetaZeros.Unconditional.PairCorrelationZeroFree
import ZetaZeros.Unconditional.PairCorrelationEndpointEnergy
import ZetaZeros.Unconditional.PairCorrelationEndpointExterior

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set

theorem pairCorrelation_boundaryEnergyBounds :
    FiniteMediumFullZeroEndpointEnergyBound ∧ FiniteWindowExteriorEnergyBound := by
  obtain ⟨margin, threshold, hthreshold, hmargin, hsaving, hstrip⟩ :=
    exists_pairCorrelation_zeroFree_boundary_margin
  constructor
  · apply finiteMediumFullZeroEndpointEnergyBound_of_strip margin threshold hmargin hsaving
    intro height hheight zero hzeroWindow hzeroHeight
    exact hstrip height hheight zero zero.property hzeroHeight
  · apply finiteWindowExteriorEnergyBound_of_strip margin threshold hmargin hsaving
    intro height hheight zero hzeroWindow
    have hwindow := mem_finiteZeroWindow.mp (mem_finiteZeroCarrierWindow.mp hzeroWindow)
    have hheightPos : 0 < height := (Real.exp_pos 2).trans_le (hthreshold.trans hheight)
    have hlogTwo : 2 ≤ Real.log height :=
      (Real.le_log_iff_exp_le hheightPos).2 (hthreshold.trans hheight)
    have hcutoffHeight : height ≤ height * (Real.log height) ^ 2 := by
      have hlogSquare : 1 ≤ (Real.log height) ^ 2 := by nlinarith
      nlinarith
    have hzeroHeight : |(zero : ℂ).im| ≤ height * (Real.log height) ^ 2 := by
      rw [abs_of_pos hwindow.2.1]
      exact hwindow.2.2.trans hcutoffHeight
    have hzeroStrip := hstrip height hheight zero zero.property hzeroHeight
    have hupper := (abs_le.mp hzeroStrip).2
    linarith

theorem integratedFullWindowEndpointComparison : IntegratedFullWindowEndpointComparison :=
  integratedFullWindowEndpointComparison_of_boundaryEnergyBounds
    pairCorrelation_boundaryEnergyBounds.1 pairCorrelation_boundaryEnergyBounds.2

theorem rawPairCorrelation_asymptotic
    (test : ℝ → ℝ) (heven : ∀ argument, test (-argument) = test argument)
    (hintegrable : Integrable test)
    (hsupported : ∀ argument : ℝ, 1 < |argument| → test argument = 0)
    (hlipschitz : ∃ constant : ℝ, ∀ argument, |test argument - test 0| ≤ constant * |argument|) :
    ∃ constant : ℝ, 0 < constant ∧ ∃ threshold : ℝ, ∀ height ≥ threshold,
      ‖rawPairCorrelation test height / pairNormalization height -
        ((test 0 + 2 * ∫ exponent in (0 : ℝ)..1, exponent * test exponent : ℝ) : ℂ)‖ ≤
        constant / Real.sqrt (Real.log height) :=
  rawPairCorrelation_asymptotic_of_integratedSecondMomentContracts
    integratedFullZeroModelSecondMoment integratedFullWindowEndpointComparison
    test heven hintegrable hsupported hlipschitz

end ZetaZeros.Unconditional.PairCorrelationProof
