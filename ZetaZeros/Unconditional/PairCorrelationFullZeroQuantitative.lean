import ZetaZeros.Unconditional.PairCorrelationFullZeroAssembly

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set
open scoped Interval

lemma abs_norm_three_terms_sub_diagonals_le_scaled
    (prime arch remainder : ℂ) (scale small : ℝ)
    (hscale : 0 < scale) (hsmall : 0 < small) :
    |‖-prime + arch + remainder‖ ^ 2 - (‖prime‖ ^ 2 + ‖arch‖ ^ 2)| ≤
      (scale + small) * ‖prime‖ ^ 2 +
        (scale⁻¹ + small) * ‖arch‖ ^ 2 +
        (2 * small⁻¹ + 1) * ‖remainder‖ ^ 2 := by
  have hcross := abs_norm_neg_add_add_sq_sub_squares_le prime arch remainder
  have hprimeArch := two_mul_le_add_mul_sq
    (a := ‖prime‖) (b := ‖arch‖) (ε := scale) hscale
  have hprimeRemainder := two_mul_le_add_mul_sq
    (a := ‖prime‖) (b := ‖remainder‖) (ε := small) hsmall
  have harchRemainder := two_mul_le_add_mul_sq
    (a := ‖arch‖) (b := ‖remainder‖) (ε := small) hsmall
  nlinarith

theorem abs_intervalIntegral_norm_three_terms_sub_diagonals_le_scaled
    (prime arch remainder : ℝ → ℂ) (height scale small : ℝ)
    (hheight : 0 ≤ height) (hscale : 0 < scale) (hsmall : 0 < small)
    (hprime : IntervalIntegrable (fun ordinate => ‖prime ordinate‖ ^ 2)
      volume 0 height)
    (harch : IntervalIntegrable (fun ordinate => ‖arch ordinate‖ ^ 2)
      volume 0 height)
    (hremainder : IntervalIntegrable (fun ordinate => ‖remainder ordinate‖ ^ 2)
      volume 0 height)
    (htotal : IntervalIntegrable
      (fun ordinate => ‖-prime ordinate + arch ordinate + remainder ordinate‖ ^ 2)
      volume 0 height) :
    |(∫ ordinate in 0..height,
        ‖-prime ordinate + arch ordinate + remainder ordinate‖ ^ 2) -
        ((∫ ordinate in 0..height, ‖prime ordinate‖ ^ 2) +
          ∫ ordinate in 0..height, ‖arch ordinate‖ ^ 2)| ≤
      (scale + small) * (∫ ordinate in 0..height, ‖prime ordinate‖ ^ 2) +
        (scale⁻¹ + small) * (∫ ordinate in 0..height, ‖arch ordinate‖ ^ 2) +
        (2 * small⁻¹ + 1) *
          (∫ ordinate in 0..height, ‖remainder ordinate‖ ^ 2) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hheight
    (f := fun ordinate =>
      ‖-prime ordinate + arch ordinate + remainder ordinate‖ ^ 2 -
        (‖prime ordinate‖ ^ 2 + ‖arch ordinate‖ ^ 2))
    (g := fun ordinate =>
      (scale + small) * ‖prime ordinate‖ ^ 2 +
        (scale⁻¹ + small) * ‖arch ordinate‖ ^ 2 +
        (2 * small⁻¹ + 1) * ‖remainder ordinate‖ ^ 2)
    (by
      filter_upwards [] with ordinate hordinate
      rw [Real.norm_eq_abs]
      exact abs_norm_three_terms_sub_diagonals_le_scaled
        (prime ordinate) (arch ordinate) (remainder ordinate) scale small
        hscale hsmall)
    (((hprime.const_mul (scale + small)).add
      (harch.const_mul (scale⁻¹ + small))).add
        (hremainder.const_mul (2 * small⁻¹ + 1)))
  rw [Real.norm_eq_abs, intervalIntegral.integral_sub htotal (hprime.add harch),
    intervalIntegral.integral_add hprime harch,
    intervalIntegral.integral_add
      ((hprime.const_mul (scale + small)).add (harch.const_mul (scale⁻¹ + small)))
      (hremainder.const_mul (2 * small⁻¹ + 1)),
    intervalIntegral.integral_add
      (hprime.const_mul (scale + small)) (harch.const_mul (scale⁻¹ + small)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hbound
  exact hbound

def fullZeroResidualTerm (scale ordinate : ℝ) : ℂ :=
  fullZeroPoleTerm scale ordinate +
    (fullZeroArchimedeanTerm scale ordinate -
      (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ))

theorem continuous_fullZeroArchimedeanMain (scale : ℝ) :
    Continuous (fun ordinate : ℝ =>
      (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)) := by
  have hdensity : Continuous (fun ordinate : ℝ => (Zeta23.mu ordinate : ℂ)) :=
    Complex.continuous_ofReal.comp archimedeanDensity_smooth.continuous
  simpa only [Pi.mul_apply] using
    (continuous_const.mul hdensity).div_const (scale : ℂ)

theorem exists_fullZeroResidualTerm_energy_bound :
    ∃ bound : ℝ, 0 < bound ∧ ∀ scale height : ℝ,
      1 ≤ scale → 0 ≤ height →
      IntervalIntegrable (fun ordinate => ‖fullZeroResidualTerm scale ordinate‖ ^ 2)
        volume 0 height ∧
      (∫ ordinate in 0..height, ‖fullZeroResidualTerm scale ordinate‖ ^ 2) ≤
        bound * (scale + height) := by
  obtain ⟨constant, hconstant, harch⟩ := montgomeryKernel_archimedeanTerm
  let poleBound : ℝ := (256 / 9 : ℝ) * Real.pi
  let bound : ℝ := 2 * poleBound + 2 * constant ^ 2 + 1
  have hpoleBound : 0 ≤ poleBound := by dsimp [poleBound]; positivity
  have hbound : 0 < bound := by dsimp [bound]; positivity
  refine ⟨bound, hbound, ?_⟩
  intro scale height hscale hheight
  have hscaleNonneg : 0 ≤ scale := zero_le_one.trans hscale
  let major : ℝ → ℝ := fun ordinate =>
    2 * ‖fullZeroPoleTerm scale ordinate‖ ^ 2 + 2 * constant ^ 2
  have hpole : IntervalIntegrable
      (fun ordinate => ‖fullZeroPoleTerm scale ordinate‖ ^ 2) volume 0 height :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hheight).2
      (integrableOn_norm_fullZeroPoleTerm_sq_Ioc scale height)
  have hmajor : IntervalIntegrable major volume 0 height :=
    (hpole.const_mul 2).add intervalIntegrable_const
  have hresidualMeasurable : Measurable (fullZeroResidualTerm scale) :=
    (continuous_fullZeroPoleTerm scale).measurable.add
      ((measurable_fullZeroArchimedeanTerm scale).sub
        (continuous_fullZeroArchimedeanMain scale).measurable)
  have hpoint : ∀ ordinate : ℝ,
      ‖fullZeroResidualTerm scale ordinate‖ ^ 2 ≤ major ordinate := by
    intro ordinate
    have hrem :
        ‖fullZeroArchimedeanTerm scale ordinate -
          (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ≤ constant := by
      simpa only [fullZeroArchimedeanTerm] using harch scale hscale ordinate
    have htriangle : ‖fullZeroResidualTerm scale ordinate‖ ≤
        ‖fullZeroPoleTerm scale ordinate‖ + constant := by
      exact (norm_add_le _ _).trans (add_le_add le_rfl hrem)
    dsimp only [major]
    nlinarith [norm_nonneg (fullZeroResidualTerm scale ordinate),
      norm_nonneg (fullZeroPoleTerm scale ordinate),
      sq_nonneg (‖fullZeroPoleTerm scale ordinate‖ - constant)]
  have hresidual : IntervalIntegrable
      (fun ordinate => ‖fullZeroResidualTerm scale ordinate‖ ^ 2) volume 0 height := by
    apply hmajor.mono_fun'
      (hresidualMeasurable.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with ordinate
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖fullZeroResidualTerm scale ordinate‖)]
    exact hpoint ordinate
  refine ⟨hresidual, ?_⟩
  calc
    (∫ ordinate in 0..height, ‖fullZeroResidualTerm scale ordinate‖ ^ 2) ≤
        ∫ ordinate in 0..height, major ordinate :=
      intervalIntegral.integral_mono_on hheight hresidual hmajor
        (fun ordinate _ => hpoint ordinate)
    _ = 2 * (∫ ordinate in 0..height, ‖fullZeroPoleTerm scale ordinate‖ ^ 2) +
        2 * constant ^ 2 * height := by
      dsimp only [major]
      rw [intervalIntegral.integral_add (hpole.const_mul 2) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      ring
    _ ≤ 2 * (poleBound * scale) + 2 * constant ^ 2 * height := by
      gcongr
      exact intervalIntegral_fullZeroPoleTerm_sq_le scale height hscale hheight
    _ ≤ bound * (scale + height) := by
      dsimp only [bound]
      nlinarith [mul_nonneg hpoleBound hheight,
        mul_nonneg (sq_nonneg constant) hscaleNonneg]

def fullZeroMomentErrorEnvelope (height exponent : ℝ) : ℝ :=
  height * Real.sqrt (Real.log height) +
    height * Real.log height * Real.sqrt (Real.log height) * height ^ (-exponent) +
    height ^ exponent * (1 + Real.log height)

theorem continuous_fullZeroMomentErrorEnvelope (height : ℝ) (hheight : 0 < height) :
    Continuous (fullZeroMomentErrorEnvelope height) := by
  unfold fullZeroMomentErrorEnvelope
  exact (continuous_const.add
    (continuous_const.mul
      ((Real.continuous_const_rpow hheight.ne').comp continuous_neg))).add
        ((Real.continuous_const_rpow hheight.ne').mul continuous_const)

theorem intervalIntegral_fullZeroMomentErrorEnvelope_le
    (height : ℝ) (hheight : Real.exp 1 ≤ height) :
    (∫ exponent in (0 : ℝ)..1, fullZeroMomentErrorEnvelope height exponent) ≤
      4 * height * Real.sqrt (Real.log height) := by
  have hheightPos : 0 < height := (Real.exp_pos 1).trans_le hheight
  have hheightOne : 1 ≤ height :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hheight
  have hlogOne : 1 ≤ Real.log height :=
    (Real.le_log_iff_exp_le hheightPos).2 hheight
  have hlogPos : 0 < Real.log height := zero_lt_one.trans_le hlogOne
  have hsqrtOne : 1 ≤ Real.sqrt (Real.log height) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlogOne
  have hpower : IntervalIntegrable (fun exponent : ℝ => height ^ exponent)
      volume 0 1 := (Real.continuous_const_rpow hheightPos.ne').intervalIntegrable _ _
  have hnegative : IntervalIntegrable (fun exponent : ℝ => height ^ (-exponent))
      volume 0 1 :=
    ((Real.continuous_const_rpow hheightPos.ne').comp continuous_neg).intervalIntegrable _ _
  have hratio : (1 + Real.log height) / Real.log height ≤ 2 := by
    rw [div_le_iff₀ hlogPos]
    linarith
  have hpositiveIntegral :
      (1 + Real.log height) * ((height - 1) / Real.log height) ≤ 2 * height := by
    calc
      (1 + Real.log height) * ((height - 1) / Real.log height) =
          ((1 + Real.log height) / Real.log height) * (height - 1) := by ring
      _ ≤ 2 * (height - 1) :=
        mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr hheightOne)
      _ ≤ 2 * height := by linarith
  have hnegativeIntegral := intervalIntegral_const_rpow_neg_le_inv_log height hheight
  have hweightedNegative :
      (height * Real.log height * Real.sqrt (Real.log height)) *
          (∫ exponent in (0 : ℝ)..1, height ^ (-exponent)) ≤
        height * Real.sqrt (Real.log height) := by
    calc
      (height * Real.log height * Real.sqrt (Real.log height)) *
          (∫ exponent in (0 : ℝ)..1, height ^ (-exponent)) ≤
          (height * Real.log height * Real.sqrt (Real.log height)) *
            (1 / Real.log height) :=
        mul_le_mul_of_nonneg_left hnegativeIntegral (by positivity)
      _ = height * Real.sqrt (Real.log height) := by field_simp
  unfold fullZeroMomentErrorEnvelope
  rw [intervalIntegral.integral_add
      (intervalIntegrable_const.add
        (hnegative.const_mul (height * Real.log height * Real.sqrt (Real.log height))))
      (hpower.mul_const (1 + Real.log height)),
    intervalIntegral.integral_add intervalIntegrable_const
      (hnegative.const_mul (height * Real.log height * Real.sqrt (Real.log height))),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const,
    intervalIntegral_const_rpow_eq height hheightPos hlogPos.ne']
  simp only [sub_zero, one_smul]
  have hheightSqrt := mul_le_mul_of_nonneg_left hsqrtOne hheightPos.le
  nlinarith

theorem test_mul_errorEnvelope_integral_bound
    (test : ℝ → ℝ) (htest : Integrable test)
    (lipschitz : ℝ) (hlipschitz : 0 ≤ lipschitz)
    (hatZero : ∀ argument : ℝ, |argument| ≤ 1 →
      |test argument - test 0| ≤ lipschitz * |argument|)
    (error : ℝ → ℂ)
    (herrorMeasurable : AEStronglyMeasurable error (volume.restrict (Set.Icc 0 1)))
    (constant height : ℝ) (hconstant : 0 ≤ constant) (hheight : Real.exp 1 ≤ height)
    (herror : ∀ exponent ∈ Set.Icc (0 : ℝ) 1,
      ‖error exponent‖ ≤ constant * fullZeroMomentErrorEnvelope height exponent) :
    IntervalIntegrable (fun exponent => (test exponent : ℂ) * error exponent)
      volume 0 1 ∧
    ‖∫ exponent in (0 : ℝ)..1, (test exponent : ℂ) * error exponent‖ ≤
      4 * constant * (|test 0| + lipschitz) * height * Real.sqrt (Real.log height) := by
  have hheightPos : 0 < height := (Real.exp_pos 1).trans_le hheight
  have hsize : 0 ≤ |test 0| + lipschitz := add_nonneg (abs_nonneg _) hlipschitz
  let major : ℝ → ℝ := fun exponent =>
    (constant * (|test 0| + lipschitz)) * fullZeroMomentErrorEnvelope height exponent
  have hmajor : IntervalIntegrable major volume 0 1 :=
    ((continuous_fullZeroMomentErrorEnvelope height hheightPos).const_mul
      (constant * (|test 0| + lipschitz))).intervalIntegrable _ _
  have hmeasurable : AEStronglyMeasurable
      (fun exponent => (test exponent : ℂ) * error exponent)
      (volume.restrict (Set.uIoc 0 1)) := by
    rw [Set.uIoc_of_le zero_le_one]
    exact htest.ofReal.aestronglyMeasurable.restrict.mul
      (herrorMeasurable.mono_set Set.Ioc_subset_Icc_self)
  have hpoint : ∀ exponent ∈ Set.Icc (0 : ℝ) 1,
      ‖(test exponent : ℂ) * error exponent‖ ≤ major exponent := by
    intro exponent hexponent
    have htestBound := abs_le_abs_zero_add_of_lipschitzAtZero
      test lipschitz hlipschitz hatZero exponent hexponent.1 hexponent.2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |test exponent| * ‖error exponent‖ ≤
          (|test 0| + lipschitz) *
            (constant * fullZeroMomentErrorEnvelope height exponent) :=
        mul_le_mul htestBound (herror exponent hexponent) (norm_nonneg _) hsize
      _ = major exponent := by dsimp only [major]; ring
  have hintegrable : IntervalIntegrable
      (fun exponent => (test exponent : ℂ) * error exponent) volume 0 1 := by
    apply hmajor.mono_fun' hmeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with exponent hexponent
    have hclosed : exponent ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at hexponent
      exact Set.Ioc_subset_Icc_self hexponent
    exact hpoint exponent hclosed
  refine ⟨hintegrable, ?_⟩
  calc
    ‖∫ exponent in (0 : ℝ)..1, (test exponent : ℂ) * error exponent‖ ≤
        ∫ exponent in (0 : ℝ)..1, major exponent :=
      intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (by
          filter_upwards [] with exponent hexponent
          exact hpoint exponent (Set.Ioc_subset_Icc_self hexponent)) hmajor
    _ = (constant * (|test 0| + lipschitz)) *
        (∫ exponent in (0 : ℝ)..1, fullZeroMomentErrorEnvelope height exponent) := by
      exact intervalIntegral.integral_const_mul _ _
    _ ≤ (constant * (|test 0| + lipschitz)) *
        (4 * height * Real.sqrt (Real.log height)) :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral_fullZeroMomentErrorEnvelope_le height hheight)
        (mul_nonneg hconstant hsize)
    _ = 4 * constant * (|test 0| + lipschitz) * height *
        Real.sqrt (Real.log height) := by ring

lemma scaled_energy_bound
    (primeEnergy archEnergy residualEnergy constant height scale root : ℝ)
    (hconstant : 0 ≤ constant) (hheight : 0 ≤ height)
    (hscale : 1 ≤ scale) (hroot : 1 ≤ root)
    (hprime : primeEnergy ≤ constant * height * root ^ 2)
    (harch : archEnergy ≤ constant * height * root ^ 4 / scale ^ 2)
    (hresidual : residualEnergy ≤ constant * height) :
    (root / scale + root⁻¹) * primeEnergy +
        ((root / scale)⁻¹ + root⁻¹) * archEnergy +
        (2 * root + 1) * residualEnergy ≤
      4 * constant * (height * root + height * root ^ 3 / scale) := by
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hrootPos : 0 < root := zero_lt_one.trans_le hroot
  have hscaleSquare : scale ≤ scale ^ 2 := by nlinarith
  have hratio : root ^ 3 / scale ^ 2 ≤ root ^ 3 / scale :=
    div_le_div_of_nonneg_left (by positivity) hscalePos hscaleSquare
  have hratioNonneg : 0 ≤ root ^ 3 / scale := by positivity
  calc
    (root / scale + root⁻¹) * primeEnergy +
        ((root / scale)⁻¹ + root⁻¹) * archEnergy +
        (2 * root + 1) * residualEnergy ≤
        (root / scale + root⁻¹) * (constant * height * root ^ 2) +
          ((root / scale)⁻¹ + root⁻¹) *
            (constant * height * root ^ 4 / scale ^ 2) +
          (2 * root + 1) * (constant * height) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left hprime (by positivity)
        · exact mul_le_mul_of_nonneg_left harch (by positivity)
      · exact mul_le_mul_of_nonneg_left hresidual (by positivity)
    _ = constant * height *
        (3 * root + 1 + 2 * (root ^ 3 / scale) + root ^ 3 / scale ^ 2) := by
      field_simp
      ring
    _ ≤ constant * height * (4 * root + 4 * (root ^ 3 / scale)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hconstant hheight)
      linarith
    _ = 4 * constant * (height * root + height * root ^ 3 / scale) := by ring

end ZetaZeros.Unconditional.PairCorrelationProof
