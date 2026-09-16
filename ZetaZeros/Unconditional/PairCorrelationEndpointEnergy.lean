import ZetaZeros.Unconditional.PairCorrelationFullZeroFinal
import ZetaZeros.Unconditional.PairCorrelationHighTail

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set
open scoped Interval

theorem exists_windowedFullZero_energy_le_log_sq :
    ∃ constant : ℝ, 0 < constant ∧ ∀ scale height : ℝ,
      1 ≤ scale → scale ≤ height → Real.exp 1 ≤ height →
      (∫ ordinate in Set.Ioc 0 height,
        ‖windowedFullZeroSum scale height ordinate‖ ^ 2) ≤
        constant * height * (Real.log height) ^ 2 := by
  obtain ⟨constant, hconstant, hbound⟩ := exists_windowedFullZero_energy_le
  refine ⟨2 * constant, by positivity, ?_⟩
  intro scale height hscale hscaleHeight hheight
  have hheightPos : 0 < height := (Real.exp_pos 1).trans_le hheight
  have hlogOne : 1 ≤ Real.log height :=
    (Real.le_log_iff_exp_le hheightPos).2 hheight
  have hscaleSquare : 1 ≤ scale ^ 2 := by nlinarith
  have hratio : (Real.log height) ^ 2 / scale ^ 2 ≤ (Real.log height) ^ 2 :=
    div_le_self (sq_nonneg _) hscaleSquare
  calc
    (∫ ordinate in Set.Ioc 0 height,
        ‖windowedFullZeroSum scale height ordinate‖ ^ 2) ≤
        constant * height * (Real.log height + (Real.log height) ^ 2 / scale ^ 2) :=
      hbound scale height hscale hscaleHeight hheight
    _ ≤ constant * height * (2 * (Real.log height) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hconstant.le hheightPos.le)
      nlinarith [sq_nonneg (Real.log height - 1)]
    _ = (2 * constant) * height * (Real.log height) ^ 2 := by ring

theorem fullWindowMomentComparison_sqrtlog_of_boundaryEnergyBounds
    (hmedium : FiniteMediumFullZeroEndpointEnergyBound)
    (hexterior : FiniteWindowExteriorEnergyBound) :
    ∃ constant : ℝ, 0 < constant ∧ ∃ threshold : ℝ,
      ∀ height ≥ threshold, ∀ scale : ℝ, 1 ≤ scale → scale ≤ height →
        ‖finiteWindowSecondMoment scale height - windowedFullZeroSecondMoment scale height‖ ≤
          constant * height * Real.sqrt (Real.log height) := by
  obtain ⟨complementConstant, hcomplementConstant, complementThreshold, hcomplement⟩ :=
    fullWindowComplement_endpointEnergyBound_of_finiteMedium hmedium
  obtain ⟨exteriorConstant, hexteriorConstant, exteriorThreshold, hexterior⟩ := hexterior
  obtain ⟨fullConstant, hfullConstant, hfull⟩ := exists_windowedFullZero_energy_le_log_sq
  let constant : ℝ := 2 * exteriorConstant + complementConstant +
    2 * Real.sqrt (complementConstant * fullConstant)
  have hconstant : 0 < constant := by dsimp only [constant]; positivity
  refine ⟨constant, hconstant,
    max (max complementThreshold exteriorThreshold) (Real.exp 2), ?_⟩
  intro height hheight scale hscale hscaleHeight
  have hheightComplement : complementThreshold ≤ height :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hheight
  have hheightExterior : exteriorThreshold ≤ height :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hheight
  have hheightExp : Real.exp 2 ≤ height := (le_max_right _ _).trans hheight
  have hheightPos : 0 < height := (Real.exp_pos 2).trans_le hheightExp
  have hheightOne : 1 ≤ height :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hheightExp
  have hlogTwo : 2 ≤ Real.log height :=
    (Real.le_log_iff_exp_le hheightPos).2 hheightExp
  have hlogPos : 0 < Real.log height := by linarith
  have hrootOne : 1 ≤ Real.sqrt (Real.log height) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ Real.log height by linarith)
  have hcutoffThree : 3 ≤ height * (Real.log height) ^ 2 := by
    have hlogSquare : 4 ≤ (Real.log height) ^ 2 := by nlinarith
    nlinarith
  have hcutoffHeight : 2 * height ≤ height * (Real.log height) ^ 2 := by
    have hlogSquare : 2 ≤ (Real.log height) ^ 2 := by nlinarith
    nlinarith
  let complementEnergy : ℝ := ∫ ordinate in Set.Ioc 0 height,
    ‖(∑' zero : {zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
        zero ∉ finiteZeroCarrierWindow height},
      fullZeroLorentzianSummand scale ordinate zero)‖ ^ 2
  let fullEnergy : ℝ := ∫ ordinate in Set.Ioc 0 height,
    ‖windowedFullZeroSum scale height ordinate‖ ^ 2
  let exteriorEnergy : ℝ := ∫ ordinate in (Set.Ioc 0 height)ᶜ,
    ‖finiteWindowLorentzianSum scale height ordinate‖ ^ 2
  have hcomplementEnergy : complementEnergy ≤ complementConstant * height / Real.log height :=
    hcomplement height hheightComplement scale hscale hscaleHeight
  have hfullEnergy : fullEnergy ≤ fullConstant * height * (Real.log height) ^ 2 :=
    hfull scale height hscale hscaleHeight
      ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hheightExp)
  have hexteriorEnergy : exteriorEnergy ≤ exteriorConstant * (height + scale) :=
    hexterior height hheightExterior scale hscale hscaleHeight
  have hfullEnergyNonneg : 0 ≤ fullEnergy := integral_nonneg (fun _ => sq_nonneg _)
  have hproduct : complementEnergy * fullEnergy ≤
      (complementConstant * fullConstant) * height ^ 2 * Real.log height := by
    calc
      complementEnergy * fullEnergy ≤
          (complementConstant * height / Real.log height) *
            (fullConstant * height * (Real.log height) ^ 2) :=
        mul_le_mul hcomplementEnergy hfullEnergy hfullEnergyNonneg (by positivity)
      _ = (complementConstant * fullConstant) * height ^ 2 * Real.log height := by
        field_simp
  have hsqrt : Real.sqrt (complementEnergy * fullEnergy) ≤
      Real.sqrt (complementConstant * fullConstant) * height *
        Real.sqrt (Real.log height) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hcomplementConstant.le hfullConstant.le),
      Real.sq_sqrt hlogPos.le]
    exact hproduct
  have hcomplementSimple : complementEnergy ≤ complementConstant * height := by
    apply hcomplementEnergy.trans
    exact div_le_self (by positivity) (by linarith)
  have hexteriorSimple : exteriorEnergy ≤ 2 * exteriorConstant * height := by
    apply hexteriorEnergy.trans
    nlinarith
  have hcomparison :=
    norm_finiteWindowSecondMoment_sub_windowedFullZeroSecondMoment_le_energy
      scale height (height * (Real.log height) ^ 2) hscale hheightPos.le
      hcutoffThree hcutoffHeight
  change ‖finiteWindowSecondMoment scale height - windowedFullZeroSecondMoment scale height‖ ≤
    exteriorEnergy + complementEnergy + 2 * Real.sqrt (complementEnergy * fullEnergy)
    at hcomparison
  calc
    ‖finiteWindowSecondMoment scale height - windowedFullZeroSecondMoment scale height‖ ≤
        exteriorEnergy + complementEnergy + 2 * Real.sqrt (complementEnergy * fullEnergy) :=
      hcomparison
    _ ≤ 2 * exteriorConstant * height + complementConstant * height +
        2 * (Real.sqrt (complementConstant * fullConstant) * height *
          Real.sqrt (Real.log height)) := by
      gcongr
    _ ≤ 2 * exteriorConstant * height * Real.sqrt (Real.log height) +
        complementConstant * height * Real.sqrt (Real.log height) +
        2 * (Real.sqrt (complementConstant * fullConstant) * height *
          Real.sqrt (Real.log height)) := by
      apply add_le_add ?_ le_rfl
      apply add_le_add
      · exact le_mul_of_one_le_right (by positivity) hrootOne
      · exact le_mul_of_one_le_right (by positivity) hrootOne
    _ = constant * height * Real.sqrt (Real.log height) := by
      dsimp only [constant]
      ring

theorem integratedFullWindowEndpointComparison_of_sqrtlog_bound
    (hcomparison : ∃ constant : ℝ, 0 < constant ∧ ∃ threshold : ℝ,
      ∀ height ≥ threshold, ∀ scale : ℝ, 1 ≤ scale → scale ≤ height →
        ‖finiteWindowSecondMoment scale height - windowedFullZeroSecondMoment scale height‖ ≤
          constant * height * Real.sqrt (Real.log height)) :
    IntegratedFullWindowEndpointComparison := by
  obtain ⟨constant, hconstant, comparisonThreshold, hcomparison⟩ := hcomparison
  obtain ⟨fullConstant, hfullConstant, fullThreshold, hfull⟩ :=
    integratedFullZeroModelSecondMoment
  refine ⟨constant, hconstant, max (max comparisonThreshold fullThreshold) (Real.exp 1), ?_⟩
  intro test lipschitz htest hlipschitz hatZero height hheight
  have hheightComparison : comparisonThreshold ≤ height :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hheight
  have hheightFull : fullThreshold ≤ height :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hheight
  have hheightExp : Real.exp 1 ≤ height := (le_max_right _ _).trans hheight
  have hheightPos : 0 < height := (Real.exp_pos 1).trans_le hheightExp
  have hheightOne : 1 ≤ height :=
    (Real.one_le_exp zero_le_one).trans hheightExp
  have hlogOne : 1 ≤ Real.log height :=
    (Real.le_log_iff_exp_le hheightPos).2 hheightExp
  have hlogNonneg : 0 ≤ Real.log height := zero_le_one.trans hlogOne
  have hrootPos : 0 < Real.sqrt (Real.log height) :=
    Real.sqrt_pos.2 (zero_lt_one.trans_le hlogOne)
  have hfullIntegrable :=
    (hfull test lipschitz htest hlipschitz hatZero height hheightFull).1
  have hfiniteIntegrable :=
    intervalIntegrable_test_mul_finiteWindowSecondMoment_sub_model test htest height hheightPos
  have hintegrable : IntervalIntegrable
      (fun exponent => (test exponent : ℂ) *
        (finiteWindowSecondMoment (height ^ exponent) height -
          windowedFullZeroSecondMoment (height ^ exponent) height)) volume 0 1 := by
    convert hfiniteIntegrable.sub hfullIntegrable using 1
    funext exponent
    ring
  refine ⟨hintegrable, ?_⟩
  have hmajor : IntervalIntegrable
      (fun exponent => (constant * height * Real.sqrt (Real.log height)) * |test exponent|)
      volume 0 1 :=
    htest.abs.intervalIntegrable.const_mul (constant * height * Real.sqrt (Real.log height))
  have hpoint : ∀ exponent ∈ Set.Ioc (0 : ℝ) 1,
      ‖(test exponent : ℂ) *
        (finiteWindowSecondMoment (height ^ exponent) height -
          windowedFullZeroSecondMoment (height ^ exponent) height)‖ ≤
      (constant * height * Real.sqrt (Real.log height)) * |test exponent| := by
    intro exponent hexponent
    have hscale : 1 ≤ height ^ exponent := Real.one_le_rpow hheightOne hexponent.1.le
    have hscaleHeight : height ^ exponent ≤ height := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hheightOne hexponent.2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (hcomparison height hheightComparison (height ^ exponent) hscale hscaleHeight)
      (abs_nonneg _)
  have hnormBound := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (by filter_upwards [] with exponent hexponent; exact hpoint exponent hexponent) hmajor
  have hsize : (∫ exponent in (0 : ℝ)..1, |test exponent|) ≤
      integratedTestSize test lipschitz := by
    unfold integratedTestSize
    linarith [abs_nonneg (test 0)]
  have hnormalization : 2 * Real.pi * ‖pairNormalization height‖ =
      height * Real.log height := by
    rw [pairNormalization, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    · field_simp
    · positivity
  calc
    ‖∫ exponent in (0 : ℝ)..1, (test exponent : ℂ) *
        (finiteWindowSecondMoment (height ^ exponent) height -
          windowedFullZeroSecondMoment (height ^ exponent) height)‖ ≤
        ∫ exponent in (0 : ℝ)..1,
          (constant * height * Real.sqrt (Real.log height)) * |test exponent| := hnormBound
    _ = (constant * height * Real.sqrt (Real.log height)) *
        (∫ exponent in (0 : ℝ)..1, |test exponent|) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (constant * height * Real.sqrt (Real.log height)) *
        integratedTestSize test lipschitz :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = height * Real.log height *
        (constant * integratedTestSize test lipschitz / Real.sqrt (Real.log height)) := by
      field_simp [hrootPos.ne']
      ring_nf
      rw [Real.sq_sqrt hlogNonneg]
      ring
    _ = 2 * Real.pi * ‖pairNormalization height‖ *
        (constant * integratedTestSize test lipschitz / Real.sqrt (Real.log height)) := by
      rw [hnormalization]

theorem integratedFullWindowEndpointComparison_of_boundaryEnergyBounds
    (hmedium : FiniteMediumFullZeroEndpointEnergyBound)
    (hexterior : FiniteWindowExteriorEnergyBound) :
    IntegratedFullWindowEndpointComparison :=
  integratedFullWindowEndpointComparison_of_sqrtlog_bound
    (fullWindowMomentComparison_sqrtlog_of_boundaryEnergyBounds hmedium hexterior)

end ZetaZeros.Unconditional.PairCorrelationProof
