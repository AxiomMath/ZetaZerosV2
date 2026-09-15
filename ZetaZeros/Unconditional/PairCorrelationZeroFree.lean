import ZetaZeros.Unconditional.PairCorrelationPNT
import ZetaZeros.Unconditional.PairCorrelationVKEndpoint
import ErdosProblems.Erdos421.ZetaLogPowerZeroFree

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex Filter Asymptotics

theorem logPowerZeroFreeStrip_of_eventual
    (hsource : ∃ threshold > 1, ∀ ordinate realPart : ℝ,
      threshold ≤ |ordinate| →
      1 - ((2 : ℝ) ^ 44)⁻¹ / (Real.log |ordinate|) ^ (15 / 16 : ℝ) ≤ realPart →
        riemannZeta ((realPart : ℂ) + ordinate * Complex.I) ≠ 0) :
    ∃ constant : ℝ, 0 < constant ∧ constant ≤ 1 / 2 ∧ ∃ threshold : ℝ,
      Real.exp 1 ≤ threshold ∧ ∀ cutoff ≥ threshold, ∀ zero : ℂ,
        riemannZeta zero = 0 → |zero.im| ≤ cutoff →
          zero.re ≤ 1 - constant / (Real.log cutoff) ^ (15 / 16 : ℝ) := by
  obtain ⟨sourceThreshold, hsourceThreshold, hsource⟩ := hsource
  obtain ⟨lowRealPart, hlowRealPart, hlow⟩ := ZetaNoZerosInBox sourceThreshold
  let constant : ℝ := min ((2 : ℝ) ^ 44)⁻¹ (min (1 - lowRealPart) (1 / 2))
  have hconstant : 0 < constant := by
    dsimp only [constant]
    exact lt_min (by positivity) (lt_min (by linarith) (by norm_num))
  have hconstantSource : constant ≤ ((2 : ℝ) ^ 44)⁻¹ := min_le_left _ _
  have hconstantLow : constant ≤ 1 - lowRealPart :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hconstantHalf : constant ≤ 1 / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨constant, hconstant, hconstantHalf,
    max sourceThreshold (Real.exp 1), le_max_right _ _, ?_⟩
  intro cutoff hcutoff zero hzero hzeroHeight
  have hcutoffExp : Real.exp 1 ≤ cutoff := (le_max_right _ _).trans hcutoff
  have hcutoffPos : 0 < cutoff := (Real.exp_pos 1).trans_le hcutoffExp
  have hlogOne : 1 ≤ Real.log cutoff :=
    (Real.le_log_iff_exp_le hcutoffPos).2 hcutoffExp
  have hdenominatorOne : 1 ≤ (Real.log cutoff) ^ (15 / 16 : ℝ) :=
    Real.one_le_rpow hlogOne (by norm_num)
  have hdenominatorPos : 0 < (Real.log cutoff) ^ (15 / 16 : ℝ) :=
    zero_lt_one.trans_le hdenominatorOne
  by_cases hheightLow : |zero.im| ≤ sourceThreshold
  · have hrealPartLow : zero.re < lowRealPart := by
      by_contra hrealPart
      have hnonzero := hlow zero.im hheightLow zero.re (le_of_not_gt hrealPart)
      rw [Complex.re_add_im] at hnonzero
      exact hnonzero hzero
    have hwidth : constant / (Real.log cutoff) ^ (15 / 16 : ℝ) ≤ 1 - lowRealPart :=
      (div_le_self hconstant.le hdenominatorOne).trans hconstantLow
    linarith
  · have hheightHigh : sourceThreshold ≤ |zero.im| := (lt_of_not_ge hheightLow).le
    have hzeroHeightPos : 0 < |zero.im| := zero_lt_one.trans (hsourceThreshold.trans_le hheightHigh)
    have hzeroLogPos : 0 < Real.log |zero.im| :=
      Real.log_pos (hsourceThreshold.trans_le hheightHigh)
    have hsourceUpper :
        zero.re < 1 - ((2 : ℝ) ^ 44)⁻¹ / (Real.log |zero.im|) ^ (15 / 16 : ℝ) := by
      by_contra hrealPart
      have hnonzero := hsource zero.im zero.re hheightHigh (le_of_not_gt hrealPart)
      rw [Complex.re_add_im] at hnonzero
      exact hnonzero hzero
    have hlogMonotone : Real.log |zero.im| ≤ Real.log cutoff :=
      Real.log_le_log hzeroHeightPos hzeroHeight
    have hpowerMonotone :
        (Real.log |zero.im|) ^ (15 / 16 : ℝ) ≤ (Real.log cutoff) ^ (15 / 16 : ℝ) :=
      Real.rpow_le_rpow hzeroLogPos.le hlogMonotone (by norm_num)
    have hwidth : constant / (Real.log cutoff) ^ (15 / 16 : ℝ) ≤
        ((2 : ℝ) ^ 44)⁻¹ / (Real.log |zero.im|) ^ (15 / 16 : ℝ) := by
      calc
        constant / (Real.log cutoff) ^ (15 / 16 : ℝ) ≤
            ((2 : ℝ) ^ 44)⁻¹ / (Real.log cutoff) ^ (15 / 16 : ℝ) :=
          div_le_div_of_nonneg_right hconstantSource hdenominatorPos.le
        _ ≤ ((2 : ℝ) ^ 44)⁻¹ / (Real.log |zero.im|) ^ (15 / 16 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity)
            (Real.rpow_pos_of_pos hzeroLogPos _) hpowerMonotone
    linarith

theorem log_logSquaredCutoff_bounds (height : ℝ) (hheight : Real.exp 2 ≤ height) :
    1 ≤ Real.log (height * (Real.log height) ^ 2) ∧
      Real.log (height * (Real.log height) ^ 2) ≤ 3 * Real.log height ∧
      0 ≤ Real.log (height * (Real.log height) ^ 2 + 4) ∧
      Real.log (height * (Real.log height) ^ 2 + 4) ≤ 4 * Real.log height := by
  have hheightPos : 0 < height := (Real.exp_pos 2).trans_le hheight
  have hheightThree : 3 ≤ height := by
    have hexp := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hlogTwo : 2 ≤ Real.log height :=
    (Real.le_log_iff_exp_le hheightPos).2 hheight
  have hlogPos : 0 < Real.log height := by linarith
  have hloglogNonneg : 0 ≤ Real.log (Real.log height) :=
    Real.log_nonneg (by linarith)
  have hloglogLe : Real.log (Real.log height) ≤ Real.log height :=
    (Real.log_le_sub_one_of_pos hlogPos).trans (by linarith)
  have hformula : Real.log (height * (Real.log height) ^ 2) =
      Real.log height + 2 * Real.log (Real.log height) := by
    rw [Real.log_mul hheightPos.ne' (pow_ne_zero _ hlogPos.ne'), Real.log_pow]
    norm_num
  have hcutoffFour : 4 ≤ height * (Real.log height) ^ 2 := by
    have hlogSquare : 4 ≤ (Real.log height) ^ 2 := by nlinarith
    nlinarith
  have hcutoffPos : 0 < height * (Real.log height) ^ 2 := by positivity
  have hbaseOne : 1 ≤ Real.log (height * (Real.log height) ^ 2) := by
    rw [hformula]
    linarith
  have hbaseUpper : Real.log (height * (Real.log height) ^ 2) ≤ 3 * Real.log height := by
    rw [hformula]
    linarith
  refine ⟨hbaseOne, hbaseUpper, Real.log_nonneg (by linarith), ?_⟩
  calc
    Real.log (height * (Real.log height) ^ 2 + 4) ≤
        Real.log (2 * (height * (Real.log height) ^ 2)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 2 + Real.log (height * (Real.log height) ^ 2) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hcutoffPos.ne']
    _ ≤ Real.log height + 3 * Real.log height :=
      add_le_add (Real.log_le_log (by norm_num) (by linarith)) hbaseUpper
    _ = 4 * Real.log height := by ring

theorem logPowerZeroFree_at_logSquaredCutoff
    (hstrip : ∃ constant : ℝ, 0 < constant ∧ constant ≤ 1 / 2 ∧ ∃ threshold : ℝ,
      Real.exp 1 ≤ threshold ∧ ∀ cutoff ≥ threshold, ∀ zero : ℂ,
        riemannZeta zero = 0 → |zero.im| ≤ cutoff →
          zero.re ≤ 1 - constant / (Real.log cutoff) ^ (15 / 16 : ℝ)) :
    ∃ constant : ℝ, 0 < constant ∧ constant ≤ 1 / 2 ∧ ∃ threshold : ℝ,
      Real.exp 2 ≤ threshold ∧ ∀ height ≥ threshold, ∀ zero : ℂ,
        riemannZeta zero = 0 → |zero.im| ≤ height * (Real.log height) ^ 2 →
          zero.re ≤ 1 - constant / (Real.log height) ^ (15 / 16 : ℝ) := by
  obtain ⟨sourceConstant, hsourceConstant, hsourceHalf, sourceThreshold,
    hsourceThreshold, hstrip⟩ := hstrip
  refine ⟨sourceConstant / 3, by positivity, by linarith,
    max sourceThreshold (Real.exp 2), le_max_right _ _, ?_⟩
  intro height hheight zero hzero hzeroHeight
  have hheightExp : Real.exp 2 ≤ height := (le_max_right _ _).trans hheight
  have hheightPos : 0 < height := (Real.exp_pos 2).trans_le hheightExp
  have hlogTwo : 2 ≤ Real.log height :=
    (Real.le_log_iff_exp_le hheightPos).2 hheightExp
  have hlogPos : 0 < Real.log height := by linarith
  have hcutoffHeight : height ≤ height * (Real.log height) ^ 2 := by
    have hlogSquare : 1 ≤ (Real.log height) ^ 2 := by nlinarith
    nlinarith
  have hcutoffThreshold : sourceThreshold ≤ height * (Real.log height) ^ 2 :=
    ((le_max_left _ _).trans hheight).trans hcutoffHeight
  obtain ⟨hcutoffLogOne, hcutoffLogUpper, _, _⟩ :=
    log_logSquaredCutoff_bounds height hheightExp
  have hdenominatorPos : 0 < (Real.log (height * (Real.log height) ^ 2)) ^ (15 / 16 : ℝ) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hcutoffLogOne) _
  have hthreePower : (3 : ℝ) ^ (15 / 16 : ℝ) ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by norm_num : (15 / 16 : ℝ) ≤ 1)
  have hdenominatorUpper :
      (Real.log (height * (Real.log height) ^ 2)) ^ (15 / 16 : ℝ) ≤
        3 * (Real.log height) ^ (15 / 16 : ℝ) := by
    calc
      (Real.log (height * (Real.log height) ^ 2)) ^ (15 / 16 : ℝ) ≤
          (3 * Real.log height) ^ (15 / 16 : ℝ) :=
        Real.rpow_le_rpow (zero_le_one.trans hcutoffLogOne) hcutoffLogUpper (by norm_num)
      _ = (3 : ℝ) ^ (15 / 16 : ℝ) * (Real.log height) ^ (15 / 16 : ℝ) :=
        Real.mul_rpow (by norm_num) hlogPos.le
      _ ≤ 3 * (Real.log height) ^ (15 / 16 : ℝ) := by gcongr
  have hwidth :
      (sourceConstant / 3) / (Real.log height) ^ (15 / 16 : ℝ) ≤
        sourceConstant / (Real.log (height * (Real.log height) ^ 2)) ^ (15 / 16 : ℝ) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hsourceConstant.le hdenominatorPos hdenominatorUpper
  have hrealPart := hstrip (height * (Real.log height) ^ 2) hcutoffThreshold zero hzero hzeroHeight
  linarith

theorem eventually_logPowerZeroFree_saving (constant : ℝ) (hconstant : 0 < constant) :
    ∃ threshold : ℝ, ∀ height ≥ threshold,
      3 * Real.log (Real.log height) ≤
        2 * (constant / (Real.log height) ^ (15 / 16 : ℝ)) * Real.log height := by
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp_tendsto
    Real.tendsto_log_atTop
  have hbound := hsmall.bound (by positivity : 0 < 2 * constant / 3)
  have heventually : ∀ᶠ height : ℝ in atTop,
      3 * Real.log (Real.log height) ≤
        2 * (constant / (Real.log height) ^ (15 / 16 : ℝ)) * Real.log height := by
    filter_upwards [hbound, eventually_ge_atTop (Real.exp 2)] with height hboundHeight hheight
    have hheightPos : 0 < height := (Real.exp_pos 2).trans_le hheight
    have hlogTwo : 2 ≤ Real.log height :=
      (Real.le_log_iff_exp_le hheightPos).2 hheight
    have hlogPos : 0 < Real.log height := by linarith
    have hloglogNonneg : 0 ≤ Real.log (Real.log height) :=
      Real.log_nonneg (by linarith)
    have hpowerPos : 0 < (Real.log height) ^ (15 / 16 : ℝ) :=
      Real.rpow_pos_of_pos hlogPos _
    have hproduct :
        (Real.log height) ^ (15 / 16 : ℝ) * (Real.log height) ^ (1 / 16 : ℝ) =
          Real.log height := by
      rw [← Real.rpow_add hlogPos]
      norm_num
    have hratio : Real.log height / (Real.log height) ^ (15 / 16 : ℝ) =
        (Real.log height) ^ (1 / 16 : ℝ) := by
      apply (div_eq_iff hpowerPos.ne').2
      rw [mul_comm]
      exact hproduct.symm
    simp only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg hloglogNonneg,
      abs_of_nonneg (Real.rpow_nonneg hlogPos.le (1 / 16 : ℝ))] at hboundHeight
    rw [show 2 * (constant / (Real.log height) ^ (15 / 16 : ℝ)) * Real.log height =
        2 * constant * (Real.log height / (Real.log height) ^ (15 / 16 : ℝ)) by ring,
      hratio]
    linarith
  exact eventually_atTop.1 heventually

theorem zero_re_sub_half_abs_le_of_strip
    (margin cutoff : ℝ)
    (hstrip : ∀ zero : ℂ, riemannZeta zero = 0 → |zero.im| ≤ cutoff → zero.re ≤ 1 - margin)
    (zero : ℂ) (hzero : Zeta23.IsNontrivialZero zero) (hheight : |zero.im| ≤ cutoff) :
    |zero.re - 1 / 2| ≤ 1 / 2 - margin := by
  have hupper := hstrip zero hzero.1 hheight
  have hreflected := Zeta23.zetaSeam.reflect_zero zero hzero
  have hreflectedHeight : |(Zeta23.reflect zero).im| ≤ cutoff := by
    simpa [Zeta23.reflect] using hheight
  have hreflectedUpper := hstrip (Zeta23.reflect zero) hreflected.1 hreflectedHeight
  have hreflectedReal : (Zeta23.reflect zero).re = 1 - zero.re := by
    simp [Zeta23.reflect]
  rw [hreflectedReal] at hreflectedUpper
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem exists_pairCorrelation_zeroFree_boundary_margin :
    ∃ margin : ℝ → ℝ, ∃ threshold : ℝ, Real.exp 2 ≤ threshold ∧
      (∀ height ≥ threshold, margin height ≤ 1 / 2) ∧
      (∀ height ≥ threshold,
        3 * Real.log (Real.log height) ≤ 2 * margin height * Real.log height) ∧
      (∀ height ≥ threshold, ∀ zero : ℂ, Zeta23.IsNontrivialZero zero →
        |zero.im| ≤ height * (Real.log height) ^ 2 →
          |zero.re - 1 / 2| ≤ 1 / 2 - margin height) := by
  obtain ⟨constant, hconstant, hconstantHalf, sourceThreshold, hsourceThreshold, hstrip⟩ :=
    logPowerZeroFree_at_logSquaredCutoff
      (logPowerZeroFreeStrip_of_eventual
        Erdos421.riemannZeta_eventually_ne_zero_log_power_strip)
  obtain ⟨savingThreshold, hsaving⟩ := eventually_logPowerZeroFree_saving constant hconstant
  let margin : ℝ → ℝ := fun height => constant / (Real.log height) ^ (15 / 16 : ℝ)
  refine ⟨margin, max sourceThreshold savingThreshold,
    hsourceThreshold.trans (le_max_left _ _), ?_, ?_, ?_⟩
  · intro height hheight
    have hsource : sourceThreshold ≤ height := (le_max_left _ _).trans hheight
    have hheightPos : 0 < height := (Real.exp_pos 2).trans_le (hsourceThreshold.trans hsource)
    have hlogTwo : 2 ≤ Real.log height :=
      (Real.le_log_iff_exp_le hheightPos).2 (hsourceThreshold.trans hsource)
    have hdenominatorOne : 1 ≤ (Real.log height) ^ (15 / 16 : ℝ) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    exact (div_le_self hconstant.le hdenominatorOne).trans hconstantHalf
  · intro height hheight
    exact hsaving height ((le_max_right _ _).trans hheight)
  · intro height hheight zero hzero hzeroHeight
    apply zero_re_sub_half_abs_le_of_strip (margin height)
      (height * (Real.log height) ^ 2) _ zero hzero hzeroHeight
    exact hstrip height ((le_max_left _ _).trans hheight)

end ZetaZeros.Unconditional.PairCorrelationProof
