import ZetaZeros.Unconditional.PairCorrelationFiniteMedium

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex Finset MeasureTheory Set
open scoped Interval Topology

theorem fullZeroLorentzianSummand_norm_le_of_re_le
    (scale : ℝ) (hscale : 1 ≤ scale) (time exponent : ℝ)
    (zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier)
    (hrealPart : (zero : ℂ).re - 1 / 2 ≤ exponent) :
    ‖fullZeroLorentzianSummand scale time zero‖ ≤
      (8 / 3 : ℝ) * scale ^ exponent * Zeta23.zeroMult zero /
        (1 + (time - (zero : ℂ).im) ^ 2) := by
  let shift : ℂ := (zero : ℂ) - 1 / 2 - Complex.I * time
  let distance : ℝ := time - (zero : ℂ).im
  let realShift : ℝ := (zero : ℂ).re - 1 / 2
  have hstrip := (Zeta23.zetaZeros Zeta23.zetaSeam).strip (zero : ℂ) zero.property
  have hrealShift : |realShift| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    dsimp [realShift]
    constructor <;> linarith [hstrip.1, hstrip.2]
  have hdenominator : (1 : ℂ) - shift ^ 2 =
      1 + ((distance : ℂ) + Complex.I * (realShift : ℂ)) ^ 2 := by
    apply Complex.ext <;>
      simp only [shift, distance, realShift, pow_two, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] <;> norm_num <;> ring
  have hdenominatorLower : (3 / 4 : ℝ) * (1 + distance ^ 2) ≤
      ‖(1 : ℂ) - shift ^ 2‖ := by
    rw [hdenominator]
    exact shiftedLorentzian_norm_lower distance realShift hrealShift
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hshiftReal : shift.re ≤ exponent := by
    simpa [shift, Complex.mul_re] using hrealPart
  have hpower : ‖(scale : ℂ) ^ shift‖ ≤ scale ^ exponent := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hscalePos]
    exact Real.rpow_le_rpow_of_exponent_le hscale hshiftReal
  have hdenominatorPos : 0 < ‖(1 : ℂ) - shift ^ 2‖ :=
    (by positivity : 0 < (3 / 4 : ℝ) * (1 + distance ^ 2)).trans_le hdenominatorLower
  have hinverse : 1 / ‖(1 : ℂ) - shift ^ 2‖ ≤
      (4 / 3 : ℝ) / (1 + distance ^ 2) := by
    rw [div_le_div_iff₀ hdenominatorPos (by positivity)]
    linarith
  change ‖(2 * Zeta23.zeroMult zero : ℂ) * (scale : ℂ) ^ shift /
      (1 - shift ^ 2)‖ ≤
    (8 / 3 : ℝ) * scale ^ exponent * Zeta23.zeroMult zero / (1 + distance ^ 2)
  calc
    ‖(2 * Zeta23.zeroMult zero : ℂ) * (scale : ℂ) ^ shift / (1 - shift ^ 2)‖ =
        (2 * (Zeta23.zeroMult zero : ℝ)) * ‖(scale : ℂ) ^ shift‖ *
          (1 / ‖(1 : ℂ) - shift ^ 2‖) := by
      rw [norm_div, norm_mul, norm_mul]
      norm_num [Complex.norm_natCast]
      ring
    _ ≤ (2 * (Zeta23.zeroMult zero : ℝ)) * scale ^ exponent *
        (1 / ‖(1 : ℂ) - shift ^ 2‖) := by gcongr
    _ ≤ (2 * (Zeta23.zeroMult zero : ℝ)) * scale ^ exponent *
        ((4 / 3 : ℝ) / (1 + distance ^ 2)) :=
      mul_le_mul_of_nonneg_left hinverse (by positivity)
    _ = _ := by ring

theorem finiteMediumFullZeroLorentzianTail_norm_bound :
    ∃ boundConst > 0, ∀ scale height cutoff exponent time : ℝ,
      1 ≤ scale → 0 ≤ height → height ≤ cutoff → 0 ≤ time → time ≤ height →
      (∀ zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        zero ∉ finiteZeroCarrierWindow height → |(zero : ℂ).im| ≤ cutoff →
        (zero : ℂ).re - 1 / 2 ≤ exponent) →
      ‖finiteMediumFullZeroLorentzianTail scale height cutoff time‖ ≤
        boundConst * scale ^ exponent * Real.log (cutoff + 4) *
          ((1 + time)⁻¹ + (1 + (height - time))⁻¹) := by
  classical
  obtain ⟨countConst, hcountConst, hlocal⟩ := Zeta23.RvM.zeta_local_zero_count
  have hcount := Zeta23.Tail.LocalCount.ofWindowCount
    (Zeta23.zetaZeros Zeta23.zetaSeam) hcountConst (fun center ↦ by
      rw [Zeta23.zetaZeros_N]
      exact hlocal center)
  refine ⟨(32 / 3 : ℝ) * countConst, by positivity, ?_⟩
  intro scale height cutoff exponent time hscale hheight hcutoff htimeLower htimeUpper hstrip
  let mediumSet : Set (Zeta23.zetaZeros Zeta23.zetaSeam).carrier :=
    {zero | zero ∉ finiteZeroCarrierWindow height ∧ |(zero : ℂ).im| ≤ cutoff}
  have hfull : Summable (fullZeroLorentzianSummand scale time) := by
    apply (zeroLorentzianSummand_summable scale hscale time).congr
    intro zero
    rfl
  have hmedium : Summable (fun zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier ↦
      if zero ∉ finiteZeroCarrierWindow height ∧ |(zero : ℂ).im| ≤ cutoff then
        fullZeroLorentzianSummand scale time zero else 0) := by
    apply (hfull.indicator mediumSet).congr
    intro zero
    simp only [Set.indicator_apply, mediumSet, Set.mem_ofPred_eq]
  have hshift : Summable (fun zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier ↦
      if zero ∉ finiteZeroCarrierWindow height ∧ |(zero : ℂ).im| ≤ cutoff then
        (Zeta23.zeroMult zero : ℝ) / (1 + (time - (zero : ℂ).im) ^ 2) else 0) := by
    apply ((shiftedZeroLorentzian_summable time).indicator mediumSet).congr
    intro zero
    simp only [Set.indicator_apply, mediumSet, Set.mem_ofPred_eq]
  have hshiftBound :
      (∑' zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        if zero ∉ finiteZeroCarrierWindow height ∧ |(zero : ℂ).im| ≤ cutoff then
          (Zeta23.zeroMult zero : ℝ) / (1 + (time - (zero : ℂ).im) ^ 2) else 0) ≤
        4 * (countConst * Real.log (cutoff + 4)) *
          ((1 + time)⁻¹ + (1 + (height - time))⁻¹) := by
    apply Real.tsum_le_of_sum_le (fun zero ↦ by split_ifs <;> positivity)
    intro zeros
    have hfinite := complementary_medium_shifted_lorentzian_sum_le_of_localCount
      hcount hheight hcutoff htimeLower htimeUpper
      (zeros.filter fun zero ↦
        zero ∉ finiteZeroCarrierWindow height ∧ |(zero : ℂ).im| ≤ cutoff)
      (by
        intro zero hzero
        have hmediumZero := (Finset.mem_filter.mp hzero).2
        by_cases hlower : (zero : ℂ).im ≤ 0
        · exact Or.inl hlower
        · right
          by_contra hupper
          apply hmediumZero.1
          rw [mem_finiteZeroCarrierWindow, mem_finiteZeroWindow]
          exact ⟨zero.property, lt_of_not_ge hlower, le_of_not_gt hupper⟩)
      (fun zero hzero ↦ (Finset.mem_filter.mp hzero).2.2)
    rw [← Finset.sum_filter]
    exact hfinite
  have hpointwise : ∀ zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
      ‖if zero ∉ finiteZeroCarrierWindow height ∧ |(zero : ℂ).im| ≤ cutoff then
        fullZeroLorentzianSummand scale time zero else 0‖ ≤
      (8 / 3 : ℝ) * scale ^ exponent *
        (if zero ∉ finiteZeroCarrierWindow height ∧ |(zero : ℂ).im| ≤ cutoff then
          (Zeta23.zeroMult zero : ℝ) / (1 + (time - (zero : ℂ).im) ^ 2) else 0) := by
    intro zero
    split_ifs with hzero
    · simpa only [mul_div_assoc] using
        fullZeroLorentzianSummand_norm_le_of_re_le scale hscale time exponent zero
          (hstrip zero hzero.1 hzero.2)
    · simp
  calc
    ‖finiteMediumFullZeroLorentzianTail scale height cutoff time‖ ≤
        ∑' zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
          ‖if zero ∉ finiteZeroCarrierWindow height ∧ |(zero : ℂ).im| ≤ cutoff then
            fullZeroLorentzianSummand scale time zero else 0‖ :=
      norm_tsum_le_tsum_norm hmedium.norm
    _ ≤ ∑' zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        (8 / 3 : ℝ) * scale ^ exponent *
          (if zero ∉ finiteZeroCarrierWindow height ∧ |(zero : ℂ).im| ≤ cutoff then
            (Zeta23.zeroMult zero : ℝ) / (1 + (time - (zero : ℂ).im) ^ 2) else 0) :=
      Summable.tsum_le_tsum hpointwise hmedium.norm
        (hshift.mul_left ((8 / 3 : ℝ) * scale ^ exponent))
    _ = (8 / 3 : ℝ) * scale ^ exponent *
        (∑' zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
          if zero ∉ finiteZeroCarrierWindow height ∧ |(zero : ℂ).im| ≤ cutoff then
            (Zeta23.zeroMult zero : ℝ) / (1 + (time - (zero : ℂ).im) ^ 2) else 0) := by
      rw [tsum_mul_left]
    _ ≤ (8 / 3 : ℝ) * scale ^ exponent *
        (4 * (countConst * Real.log (cutoff + 4)) *
          ((1 + time)⁻¹ + (1 + (height - time))⁻¹)) :=
      mul_le_mul_of_nonneg_left hshiftBound (by positivity)
    _ = ((32 / 3 : ℝ) * countConst) * scale ^ exponent * Real.log (cutoff + 4) *
        ((1 + time)⁻¹ + (1 + (height - time))⁻¹) := by ring

theorem boundaryInverseSquare_intervalIntegrable (height : ℝ) (hheight : 0 ≤ height) :
    IntervalIntegrable (fun time : ℝ ↦ ((1 + time)⁻¹) ^ 2) volume 0 height := by
  apply ContinuousOn.intervalIntegrable_of_Icc hheight
  intro time htime
  have hdenominator : 1 + time ≠ 0 := by linarith [htime.1]
  have hcontinuous : ContinuousAt (fun value : ℝ ↦ 1 + value) time :=
    continuousAt_const.add continuousAt_id
  exact ((hcontinuous.inv₀ hdenominator).pow 2).continuousWithinAt

theorem boundaryInverseSquare_integral_le (height : ℝ) (hheight : 0 ≤ height) :
    (∫ time in 0..height, ((1 + time)⁻¹) ^ 2) ≤ 1 := by
  have hderivative : ∀ time ∈ Set.uIcc (0 : ℝ) height,
      HasDerivAt (fun value : ℝ ↦ -(1 + value)⁻¹) (((1 + time)⁻¹) ^ 2) time := by
    intro time htime
    rw [Set.uIcc_of_le hheight] at htime
    have hlinear : HasDerivAt (fun value : ℝ ↦ 1 + value) 1 time :=
      (hasDerivAt_id time).const_add 1
    have hdenominator : 1 + time ≠ 0 := by linarith [htime.1]
    have hvalue : -(-1 / (1 + time) ^ 2) = ((1 + time)⁻¹) ^ 2 := by
      simp only [neg_div, one_div, neg_neg, inv_pow]
    exact hvalue ▸ (hlinear.inv hdenominator).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderivative
    (boundaryInverseSquare_intervalIntegrable height hheight)]
  simp only [add_zero, inv_one, sub_neg_eq_add]
  have hinverse : 0 ≤ (1 + height)⁻¹ := by positivity
  linarith

theorem reflectedBoundaryInverseSquare_intervalIntegrable
    (height : ℝ) (hheight : 0 ≤ height) :
    IntervalIntegrable (fun time : ℝ ↦ ((1 + (height - time))⁻¹) ^ 2)
      volume 0 height := by
  apply ContinuousOn.intervalIntegrable_of_Icc hheight
  intro time htime
  have hdenominator : 1 + (height - time) ≠ 0 := by linarith [htime.2]
  have hcontinuous : ContinuousAt (fun value : ℝ ↦ 1 + (height - value)) time :=
    continuousAt_const.add (continuousAt_const.sub continuousAt_id)
  exact ((hcontinuous.inv₀ hdenominator).pow 2).continuousWithinAt

theorem reflectedBoundaryInverseSquare_integral_le
    (height : ℝ) (hheight : 0 ≤ height) :
    (∫ time in 0..height, ((1 + (height - time))⁻¹) ^ 2) ≤ 1 := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun time : ℝ ↦ ((1 + time)⁻¹) ^ 2) height]
  simpa only [sub_self, sub_zero] using boundaryInverseSquare_integral_le height hheight

theorem finiteMediumFullZeroLorentzianTail_energy_bound_of_re_le :
    ∃ energyConst > 0, ∀ scale height cutoff exponent : ℝ,
      1 ≤ scale → 0 ≤ height → height ≤ cutoff →
      (∀ zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        zero ∉ finiteZeroCarrierWindow height → |(zero : ℂ).im| ≤ cutoff →
        (zero : ℂ).re - 1 / 2 ≤ exponent) →
      (∫ time in Set.Ioc 0 height,
        ‖finiteMediumFullZeroLorentzianTail scale height cutoff time‖ ^ 2) ≤
        energyConst * scale ^ (2 * exponent) * Real.log (cutoff + 4) ^ 2 := by
  obtain ⟨boundConst, hboundConst, hbound⟩ := finiteMediumFullZeroLorentzianTail_norm_bound
  refine ⟨4 * boundConst ^ 2, by positivity, ?_⟩
  intro scale height cutoff exponent hscale hheight hcutoff hstrip
  let amplitude : ℝ := boundConst * scale ^ exponent * Real.log (cutoff + 4)
  have hamplitude : 0 ≤ amplitude := by
    dsimp [amplitude]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hpointwise : ∀ time ∈ Set.Icc (0 : ℝ) height,
      ‖finiteMediumFullZeroLorentzianTail scale height cutoff time‖ ^ 2 ≤
        2 * amplitude ^ 2 *
          (((1 + time)⁻¹) ^ 2 + ((1 + (height - time))⁻¹) ^ 2) := by
    intro time htime
    have hnorm := hbound scale height cutoff exponent time hscale hheight hcutoff
      htime.1 htime.2 hstrip
    change ‖finiteMediumFullZeroLorentzianTail scale height cutoff time‖ ≤
      amplitude * ((1 + time)⁻¹ + (1 + (height - time))⁻¹) at hnorm
    have hsquare : ‖finiteMediumFullZeroLorentzianTail scale height cutoff time‖ ^ 2 ≤
        (amplitude * ((1 + time)⁻¹ + (1 + (height - time))⁻¹)) ^ 2 := by
      gcongr
    have hboundary : ((1 + time)⁻¹ + (1 + (height - time))⁻¹) ^ 2 ≤
        2 * (((1 + time)⁻¹) ^ 2 + ((1 + (height - time))⁻¹) ^ 2) := by
      nlinarith [sq_nonneg ((1 + time)⁻¹ - (1 + (height - time))⁻¹)]
    calc
      ‖finiteMediumFullZeroLorentzianTail scale height cutoff time‖ ^ 2 ≤
          (amplitude * ((1 + time)⁻¹ + (1 + (height - time))⁻¹)) ^ 2 := hsquare
      _ = amplitude ^ 2 * ((1 + time)⁻¹ + (1 + (height - time))⁻¹) ^ 2 := mul_pow _ _ _
      _ ≤ amplitude ^ 2 *
          (2 * (((1 + time)⁻¹) ^ 2 + ((1 + (height - time))⁻¹) ^ 2)) :=
        mul_le_mul_of_nonneg_left hboundary (sq_nonneg _)
      _ = _ := by ring
  have hlower := boundaryInverseSquare_intervalIntegrable height hheight
  have hupper := reflectedBoundaryInverseSquare_intervalIntegrable height hheight
  have hmajor := (hlower.add hupper).const_mul (2 * amplitude ^ 2)
  have hmedium : IntervalIntegrable
      (fun time ↦ ‖finiteMediumFullZeroLorentzianTail scale height cutoff time‖ ^ 2)
      volume 0 height :=
    ((continuous_finiteMediumFullZeroLorentzianTail scale hscale height cutoff).norm.pow 2)
      |>.intervalIntegrable 0 height
  have hpower : (scale ^ exponent) ^ (2 : ℕ) = scale ^ (2 * exponent) := by
    calc
      (scale ^ exponent) ^ (2 : ℕ) = (scale ^ exponent) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = scale ^ (exponent * 2) :=
        (Real.rpow_mul (zero_le_one.trans hscale) exponent 2).symm
      _ = scale ^ (2 * exponent) := by rw [mul_comm exponent 2]
  rw [← intervalIntegral.integral_of_le hheight]
  calc
    (∫ time in 0..height,
        ‖finiteMediumFullZeroLorentzianTail scale height cutoff time‖ ^ 2) ≤
        ∫ time in 0..height, 2 * amplitude ^ 2 *
          (((1 + time)⁻¹) ^ 2 + ((1 + (height - time))⁻¹) ^ 2) :=
      intervalIntegral.integral_mono_on hheight hmedium hmajor hpointwise
    _ = 2 * amplitude ^ 2 *
        ((∫ time in 0..height, ((1 + time)⁻¹) ^ 2) +
          ∫ time in 0..height, ((1 + (height - time))⁻¹) ^ 2) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hlower hupper]
    _ ≤ 2 * amplitude ^ 2 * (1 + 1) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (boundaryInverseSquare_integral_le height hheight)
          (reflectedBoundaryInverseSquare_integral_le height hheight)) (by positivity)
    _ = (4 * boundConst ^ 2) * scale ^ (2 * exponent) * Real.log (cutoff + 4) ^ 2 := by
      dsimp [amplitude]
      rw [mul_pow, mul_pow, hpower]
      ring

theorem finiteMediumFullZeroLorentzianTail_energy_bound_of_strip :
    ∃ energyConst > 0, ∀ scale height cutoff margin : ℝ,
      1 ≤ scale → 0 ≤ height → height ≤ cutoff →
      (∀ zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        zero ∉ finiteZeroCarrierWindow height → |(zero : ℂ).im| ≤ cutoff →
        |(zero : ℂ).re - 1 / 2| ≤ 1 / 2 - margin) →
      (∫ time in Set.Ioc 0 height,
        ‖finiteMediumFullZeroLorentzianTail scale height cutoff time‖ ^ 2) ≤
        energyConst * scale ^ (1 - 2 * margin) * Real.log (cutoff + 4) ^ 2 := by
  obtain ⟨energyConst, henergyConst, henergy⟩ :=
    finiteMediumFullZeroLorentzianTail_energy_bound_of_re_le
  refine ⟨energyConst, henergyConst, ?_⟩
  intro scale height cutoff margin hscale hheight hcutoff hstrip
  have hrealPart : ∀ zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
      zero ∉ finiteZeroCarrierWindow height → |(zero : ℂ).im| ≤ cutoff →
      (zero : ℂ).re - 1 / 2 ≤ 1 / 2 - margin := by
    intro zero houtside hzeroHeight
    exact (le_abs_self _).trans (hstrip zero houtside hzeroHeight)
  have hexponent : 2 * (1 / 2 - margin) = 1 - 2 * margin := by ring
  simpa only [hexponent] using
    henergy scale height cutoff (1 / 2 - margin) hscale hheight hcutoff hrealPart

theorem finiteMediumFullZeroLorentzianTail_logSquaredCutoff_energy_bound_of_strip :
    ∃ energyConst > 0, ∀ height : ℝ, Real.exp 1 ≤ height →
      ∀ scale margin : ℝ, 1 ≤ scale →
      (∀ zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        zero ∉ finiteZeroCarrierWindow height →
        |(zero : ℂ).im| ≤ height * Real.log height ^ 2 →
        |(zero : ℂ).re - 1 / 2| ≤ 1 / 2 - margin) →
      (∫ time in Set.Ioc 0 height,
        ‖finiteMediumFullZeroLorentzianTail scale height
          (height * Real.log height ^ 2) time‖ ^ 2) ≤
        energyConst * scale ^ (1 - 2 * margin) *
          Real.log (height * Real.log height ^ 2 + 4) ^ 2 := by
  obtain ⟨energyConst, henergyConst, henergy⟩ :=
    finiteMediumFullZeroLorentzianTail_energy_bound_of_strip
  refine ⟨energyConst, henergyConst, ?_⟩
  intro height hheight scale margin hscale hstrip
  have hheightPos : 0 < height := (Real.exp_pos 1).trans_le hheight
  have hlog : 1 ≤ Real.log height := (Real.le_log_iff_exp_le hheightPos).2 hheight
  have hcutoff : height ≤ height * Real.log height ^ 2 := by
    have hsquare : 1 ≤ Real.log height ^ 2 := by nlinarith
    nlinarith
  exact henergy scale height (height * Real.log height ^ 2) margin hscale hheightPos.le
    hcutoff hstrip

theorem logSquaredCutoff_add_four_log_le (height : ℝ) (hheight : Real.exp 2 ≤ height) :
    Real.log (height * Real.log height ^ 2 + 4) ≤ 4 * Real.log height := by
  have hheightPos : 0 < height := (Real.exp_pos 2).trans_le hheight
  have hheightOne : 1 ≤ height :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hheight
  have hlog : 2 ≤ Real.log height := (Real.le_log_iff_exp_le hheightPos).2 hheight
  have hlogPos : 0 < Real.log height := by linarith
  have hcutoff : 4 ≤ height * Real.log height ^ 2 := by
    have hsquare : 4 ≤ Real.log height ^ 2 := by nlinarith
    exact hsquare.trans (le_mul_of_one_le_left (sq_nonneg _) hheightOne)
  calc
    Real.log (height * Real.log height ^ 2 + 4) ≤
        Real.log (2 * (height * Real.log height ^ 2)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 2 + Real.log height + 2 * Real.log (Real.log height) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
        Real.log_mul hheightPos.ne' (pow_ne_zero 2 hlogPos.ne'), Real.log_pow]
      ring
    _ ≤ 4 * Real.log height := by
      linarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2),
        Real.log_le_self hlogPos.le]

theorem finiteMedium_strip_factor_le (height scale margin : ℝ)
    (hheight : Real.exp 2 ≤ height) (hscale : 1 ≤ scale) (hscaleHeight : scale ≤ height)
    (hmargin : margin ≤ 1 / 2)
    (hsaving : 3 * Real.log (Real.log height) ≤ 2 * margin * Real.log height) :
    scale ^ (1 - 2 * margin) * Real.log (height * Real.log height ^ 2 + 4) ^ 2 ≤
      16 * height / Real.log height := by
  have hheightPos : 0 < height := (Real.exp_pos 2).trans_le hheight
  have hlog : 2 ≤ Real.log height := (Real.le_log_iff_exp_le hheightPos).2 hheight
  have hlogPos : 0 < Real.log height := by linarith
  have hscalePower : scale ^ (1 - 2 * margin) ≤ height ^ (1 - 2 * margin) :=
    Real.rpow_le_rpow (zero_le_one.trans hscale) hscaleHeight (by linarith)
  have hlogPower : Real.log height ^ 3 = Real.exp (3 * Real.log (Real.log height)) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hlogPos] using
      (Real.exp_nat_mul (Real.log (Real.log height)) 3).symm
  have hheightPower : height ^ (1 - 2 * margin) * Real.log height ^ 3 ≤ height := by
    rw [Real.rpow_def_of_pos hheightPos, hlogPower, ← Real.exp_add]
    exact (Real.exp_le_exp.mpr (by nlinarith [hsaving])).trans_eq (Real.exp_log hheightPos)
  have hpowerBound : scale ^ (1 - 2 * margin) ≤ height / Real.log height ^ 3 :=
    hscalePower.trans ((le_div_iff₀ (by positivity)).2 hheightPower)
  have hlogCutoff : Real.log (height * Real.log height ^ 2 + 4) ≤ 4 * Real.log height :=
    logSquaredCutoff_add_four_log_le height hheight
  have hlogCutoffNonneg : 0 ≤ Real.log (height * Real.log height ^ 2 + 4) :=
    Real.log_nonneg (by nlinarith [mul_nonneg hheightPos.le (sq_nonneg (Real.log height))])
  have hlogSquare : Real.log (height * Real.log height ^ 2 + 4) ^ 2 ≤
      16 * Real.log height ^ 2 := by
    calc
      Real.log (height * Real.log height ^ 2 + 4) ^ 2 ≤ (4 * Real.log height) ^ 2 := by
        gcongr
      _ = 16 * Real.log height ^ 2 := by ring
  calc
    scale ^ (1 - 2 * margin) * Real.log (height * Real.log height ^ 2 + 4) ^ 2 ≤
        (height / Real.log height ^ 3) * (16 * Real.log height ^ 2) :=
      mul_le_mul hpowerBound hlogSquare (sq_nonneg _) (by positivity)
    _ = 16 * height / Real.log height := by
      field_simp

theorem finiteMediumFullZeroLorentzianTail_endpoint_energy_le_of_strip :
    ∃ energyConst > 0, ∀ height : ℝ, Real.exp 2 ≤ height →
      ∀ scale margin : ℝ, 1 ≤ scale → scale ≤ height → margin ≤ 1 / 2 →
      3 * Real.log (Real.log height) ≤ 2 * margin * Real.log height →
      (∀ zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        zero ∉ finiteZeroCarrierWindow height →
        |(zero : ℂ).im| ≤ height * Real.log height ^ 2 →
        |(zero : ℂ).re - 1 / 2| ≤ 1 / 2 - margin) →
      (∫ time in Set.Ioc 0 height,
        ‖finiteMediumFullZeroLorentzianTail scale height
          (height * Real.log height ^ 2) time‖ ^ 2) ≤
        energyConst * height / Real.log height := by
  obtain ⟨stripConst, hstripConst, hstripBound⟩ :=
    finiteMediumFullZeroLorentzianTail_logSquaredCutoff_energy_bound_of_strip
  refine ⟨16 * stripConst, by positivity, ?_⟩
  intro height hheight scale margin hscale hscaleHeight hmargin hsaving hstrip
  have hheightOne : Real.exp 1 ≤ height :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hheight
  calc
    (∫ time in Set.Ioc 0 height,
        ‖finiteMediumFullZeroLorentzianTail scale height
          (height * Real.log height ^ 2) time‖ ^ 2) ≤
        stripConst * scale ^ (1 - 2 * margin) *
          Real.log (height * Real.log height ^ 2 + 4) ^ 2 :=
      hstripBound height hheightOne scale margin hscale hstrip
    _ = stripConst * (scale ^ (1 - 2 * margin) *
        Real.log (height * Real.log height ^ 2 + 4) ^ 2) := by ring
    _ ≤ stripConst * (16 * height / Real.log height) :=
      mul_le_mul_of_nonneg_left
        (finiteMedium_strip_factor_le height scale margin hheight hscale hscaleHeight
          hmargin hsaving) hstripConst.le
    _ = (16 * stripConst) * height / Real.log height := by ring

theorem finiteMediumFullZeroEndpointEnergyBound_of_strip
    (margin : ℝ → ℝ) (threshold : ℝ)
    (hmargin : ∀ height ≥ threshold, margin height ≤ 1 / 2)
    (hsaving : ∀ height ≥ threshold,
      3 * Real.log (Real.log height) ≤ 2 * margin height * Real.log height)
    (hstrip : ∀ height ≥ threshold,
      ∀ zero : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        zero ∉ finiteZeroCarrierWindow height →
        |(zero : ℂ).im| ≤ height * Real.log height ^ 2 →
        |(zero : ℂ).re - 1 / 2| ≤ 1 / 2 - margin height) :
    FiniteMediumFullZeroEndpointEnergyBound := by
  obtain ⟨energyConst, henergyConst, henergy⟩ :=
    finiteMediumFullZeroLorentzianTail_endpoint_energy_le_of_strip
  refine ⟨energyConst, henergyConst, max threshold (Real.exp 2), ?_⟩
  intro height hheight scale hscale hscaleHeight
  have hthreshold : threshold ≤ height := (le_max_left _ _).trans hheight
  have hheightExp : Real.exp 2 ≤ height := (le_max_right _ _).trans hheight
  exact henergy height hheightExp scale (margin height) hscale hscaleHeight
    (hmargin height hthreshold) (hsaving height hthreshold) (hstrip height hthreshold)

end ZetaZeros.Unconditional.PairCorrelationProof
