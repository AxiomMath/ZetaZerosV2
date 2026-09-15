import ZetaZeros.Unconditional.PairCorrelationFullZeroQuantitative
import ZetaZeros.Unconditional.PairCorrelationWindowedEnergy
import ZetaZeros.Unconditional.PairCorrelationPrimeMoment

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set
open scoped Interval

theorem exists_fullZeroMoment_interaction_bound :
    ∃ constant : ℝ, 0 < constant ∧ ∀ scale height : ℝ,
      1 ≤ scale → scale ≤ height → Real.exp 1 ≤ height →
      |(∫ ordinate in 0..height,
          ‖fullZeroPoleTerm scale ordinate - fullZeroPrimeTerm scale ordinate +
            fullZeroArchimedeanTerm scale ordinate‖ ^ 2) -
          ((∫ ordinate in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2) +
            ∫ ordinate in 0..height,
              ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2)| ≤
        constant * (height * Real.sqrt (Real.log height) +
          height * Real.log height * Real.sqrt (Real.log height) / scale) := by
  obtain ⟨primeConstant, hprimeConstant, hprime⟩ :=
    exists_intervalIntegral_fullZeroPrimeTerm_sq_le
  obtain ⟨archConstant, harchConstant, harch⟩ :=
    exists_intervalIntegral_archimedeanMain_sq_le
  obtain ⟨residualConstant, hresidualConstant, hresidual⟩ :=
    exists_fullZeroResidualTerm_energy_bound
  let common : ℝ := primeConstant + archConstant + 2 * residualConstant
  have hcommon : 0 < common := by dsimp only [common]; positivity
  refine ⟨4 * common, by positivity, ?_⟩
  intro scale height hscale hscaleHeight hheight
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hheightPos : 0 < height := (Real.exp_pos 1).trans_le hheight
  have hlogOne : 1 ≤ Real.log height :=
    (Real.le_log_iff_exp_le hheightPos).2 hheight
  have hlogNonneg : 0 ≤ Real.log height := zero_le_one.trans hlogOne
  let root : ℝ := Real.sqrt (Real.log height)
  have hrootOne : 1 ≤ root := by
    simpa only [root, Real.sqrt_one] using Real.sqrt_le_sqrt hlogOne
  have hrootPos : 0 < root := zero_lt_one.trans_le hrootOne
  have hrootSquare : root ^ 2 = Real.log height := Real.sq_sqrt hlogNonneg
  have hrootFourth : root ^ 4 = (Real.log height) ^ 2 := by
    calc
      root ^ 4 = (root ^ 2) ^ 2 := by ring
      _ = (Real.log height) ^ 2 := by rw [hrootSquare]
  have hprimeIntegrable : IntervalIntegrable
      (fun ordinate => ‖fullZeroPrimeTerm scale ordinate‖ ^ 2) volume 0 height :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hheightPos.le).2
      (integrableOn_norm_fullZeroPrimeTerm_sq_Ioc scale height hscale)
  have harchIntegrable : IntervalIntegrable
      (fun ordinate => ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2)
      volume 0 height :=
    ((continuous_fullZeroArchimedeanMain scale).norm.pow 2).intervalIntegrable _ _
  obtain ⟨hresidualIntegrable, hresidualBound⟩ :=
    hresidual scale height hscale hheightPos.le
  have htotalIntegrable : IntervalIntegrable
      (fun ordinate =>
        ‖-fullZeroPrimeTerm scale ordinate +
          (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ) +
          fullZeroResidualTerm scale ordinate‖ ^ 2) volume 0 height := by
    have hexplicit := (intervalIntegrable_iff_integrableOn_Ioc_of_le hheightPos.le).2
      (integrableOn_norm_fullZeroExplicitTerm_sq_Ioc scale height hscale)
    convert hexplicit using 1
    funext ordinate
    congr 1
    unfold fullZeroResidualTerm
    ring
  have hprimeBound :
      (∫ ordinate in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2) ≤
        common * height * root ^ 2 := by
    rw [hrootSquare]
    calc
      (∫ ordinate in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2) ≤
          primeConstant * height * Real.log height :=
        hprime scale height hscale hscaleHeight hheight
      _ ≤ common * height * Real.log height := by
        gcongr
        dsimp only [common]
        linarith
  have harchBound :
      (∫ ordinate in 0..height,
          ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2) ≤
        common * height * root ^ 4 / scale ^ 2 := by
    rw [hrootFourth]
    calc
      (∫ ordinate in 0..height,
          ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2) ≤
          archConstant * height * (Real.log height) ^ 2 / scale ^ 2 :=
        harch scale height hheight
      _ ≤ common * height * (Real.log height) ^ 2 / scale ^ 2 := by
        gcongr
        dsimp only [common]
        linarith
  have hresidualBound' :
      (∫ ordinate in 0..height, ‖fullZeroResidualTerm scale ordinate‖ ^ 2) ≤
        common * height := by
    calc
      (∫ ordinate in 0..height, ‖fullZeroResidualTerm scale ordinate‖ ^ 2) ≤
          residualConstant * (scale + height) := hresidualBound
      _ ≤ (2 * residualConstant) * height := by nlinarith
      _ ≤ common * height := by
        gcongr
        dsimp only [common]
        linarith
  have hinteraction := abs_intervalIntegral_norm_three_terms_sub_diagonals_le_scaled
    (fullZeroPrimeTerm scale)
    (fun ordinate => (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ))
    (fullZeroResidualTerm scale) height (root / scale) root⁻¹
    hheightPos.le (div_pos hrootPos hscalePos) (inv_pos.mpr hrootPos)
    hprimeIntegrable harchIntegrable hresidualIntegrable htotalIntegrable
  simp only [inv_inv] at hinteraction
  have hscaled := scaled_energy_bound
    (∫ ordinate in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2)
    (∫ ordinate in 0..height,
      ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2)
    (∫ ordinate in 0..height, ‖fullZeroResidualTerm scale ordinate‖ ^ 2)
    common height scale root hcommon.le hheightPos.le hscale hrootOne
    hprimeBound harchBound hresidualBound'
  have hrootCube : root ^ 3 = Real.log height * root := by
    calc
      root ^ 3 = root ^ 2 * root := by ring
      _ = Real.log height * root := by rw [hrootSquare]
  have hequality :
      (fun ordinate =>
        ‖-fullZeroPrimeTerm scale ordinate +
          (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ) +
          fullZeroResidualTerm scale ordinate‖ ^ 2) =
      fun ordinate =>
        ‖fullZeroPoleTerm scale ordinate - fullZeroPrimeTerm scale ordinate +
          fullZeroArchimedeanTerm scale ordinate‖ ^ 2 := by
    funext ordinate
    congr 1
    unfold fullZeroResidualTerm
    ring
  rw [hequality] at hinteraction
  simpa only [hrootCube, root, mul_assoc] using hinteraction.trans hscaled

theorem exists_fullZeroMoment_pointwise_error_bound :
    ∃ constant : ℝ, 0 < constant ∧ ∀ scale height : ℝ,
      1 ≤ scale → scale ≤ height → Real.exp 1 ≤ height →
      ‖windowedFullZeroSecondMoment scale height -
        ((height * Real.log scale +
          height * (Real.log height) ^ 2 / scale ^ 2 : ℝ) : ℂ)‖ ≤
        constant * (height * Real.sqrt (Real.log height) +
          height * Real.log height * Real.sqrt (Real.log height) / scale +
          scale * (1 + Real.log height)) := by
  obtain ⟨interactionConstant, hinteractionConstant, hinteraction⟩ :=
    exists_fullZeroMoment_interaction_bound
  obtain ⟨primeConstant, hprimeConstant, meanConstant, hmeanConstant, hprime⟩ :=
    exists_fullZeroPrimeTerm_log_meanValue_bound
  obtain ⟨archConstant, harchConstant, harch⟩ := cumulative_archimedeanDensity_sq
  let constant : ℝ := interactionConstant + primeConstant + 2 * archConstant + meanConstant
  have hconstant : 0 < constant := by dsimp only [constant]; positivity
  refine ⟨constant, hconstant, ?_⟩
  intro scale height hscale hscaleHeight hheight
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hheightPos : 0 < height := (Real.exp_pos 1).trans_le hheight
  have hlogOne : 1 ≤ Real.log height :=
    (Real.le_log_iff_exp_le hheightPos).2 hheight
  have hlogNonneg : 0 ≤ Real.log height := zero_le_one.trans hlogOne
  have hrootOne : 1 ≤ Real.sqrt (Real.log height) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlogOne
  have hscaleSquare : scale ≤ scale ^ 2 := by nlinarith
  have hlogScale : Real.log scale ≤ Real.log height :=
    Real.log_le_log hscalePos hscaleHeight
  let base : ℝ := height * Real.sqrt (Real.log height)
  let decay : ℝ := height * Real.log height * Real.sqrt (Real.log height) / scale
  let growth : ℝ := scale * (1 + Real.log height)
  have hbase : 0 ≤ base := by dsimp only [base]; positivity
  have hdecay : 0 ≤ decay := by dsimp only [decay]; positivity
  have hgrowth : 0 ≤ growth := by dsimp only [growth]; positivity
  have hprimeBound :
      |(∫ ordinate in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2) -
          height * Real.log scale| ≤ primeConstant * base + meanConstant * growth := by
    calc
      |(∫ ordinate in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2) -
          height * Real.log scale| ≤
          primeConstant * height + meanConstant * scale * (1 + Real.log scale) :=
        hprime scale hscale height hheightPos.le
      _ ≤ primeConstant * base + meanConstant * growth := by
        dsimp only [base, growth]
        apply add_le_add
        · nlinarith [mul_le_mul_of_nonneg_left hrootOne
            (mul_nonneg hprimeConstant.le hheightPos.le)]
        · have hlogSum : 1 + Real.log scale ≤ 1 + Real.log height := by linarith
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hlogSum (mul_nonneg hmeanConstant.le hscalePos.le)
  have harchBound :
      |(∫ ordinate in 0..height,
          ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2) -
          height * (Real.log height) ^ 2 / scale ^ 2| ≤ 2 * archConstant * decay := by
    rw [intervalIntegral_archimedeanMain_sq_eq, ← sub_div,
      abs_div, abs_of_nonneg (sq_nonneg scale)]
    calc
      |(4 * Real.pi ^ 2) * (∫ ordinate in 0..height, Zeta23.mu ordinate ^ 2) -
          height * (Real.log height) ^ 2| / scale ^ 2 ≤
          (archConstant * height * (1 + Real.log height)) / scale ^ 2 :=
        div_le_div_of_nonneg_right (harch height hheight) (sq_nonneg scale)
      _ ≤ (archConstant * height * (2 * Real.log height)) / scale ^ 2 := by
        gcongr
        linarith
      _ ≤ (archConstant * height * (2 * Real.log height)) / scale :=
        div_le_div_of_nonneg_left (by positivity) hscalePos hscaleSquare
      _ ≤ (archConstant * height * (2 * Real.log height) *
          Real.sqrt (Real.log height)) / scale := by
        apply div_le_div_of_nonneg_right _ hscalePos.le
        exact le_mul_of_one_le_right (by positivity) hrootOne
      _ = 2 * archConstant * decay := by dsimp only [decay]; ring
  let totalEnergy : ℝ := ∫ ordinate in 0..height,
    ‖fullZeroPoleTerm scale ordinate - fullZeroPrimeTerm scale ordinate +
      fullZeroArchimedeanTerm scale ordinate‖ ^ 2
  let primeEnergy : ℝ := ∫ ordinate in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2
  let archEnergy : ℝ := ∫ ordinate in 0..height,
    ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2
  have htotal :
      |totalEnergy - (height * Real.log scale +
          height * (Real.log height) ^ 2 / scale ^ 2)| ≤
        |totalEnergy - (primeEnergy + archEnergy)| +
          |primeEnergy - height * Real.log scale| +
          |archEnergy - height * (Real.log height) ^ 2 / scale ^ 2| := by
    calc
      |totalEnergy - (height * Real.log scale +
          height * (Real.log height) ^ 2 / scale ^ 2)| =
          |(totalEnergy - (primeEnergy + archEnergy)) +
            (primeEnergy - height * Real.log scale) +
            (archEnergy - height * (Real.log height) ^ 2 / scale ^ 2)| := by
        congr 1
        ring
      _ ≤ |(totalEnergy - (primeEnergy + archEnergy)) +
            (primeEnergy - height * Real.log scale)| +
          |archEnergy - height * (Real.log height) ^ 2 / scale ^ 2| := abs_add_le _ _
      _ ≤ |totalEnergy - (primeEnergy + archEnergy)| +
          |primeEnergy - height * Real.log scale| +
          |archEnergy - height * (Real.log height) ^ 2 / scale ^ 2| := by
        gcongr
        exact abs_add_le _ _
  rw [windowedFullZeroSecondMoment_eq_ofReal_norm_sq_integral
    scale height hscale hheightPos.le, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  change |totalEnergy - (height * Real.log scale +
      height * (Real.log height) ^ 2 / scale ^ 2)| ≤ constant * (base + decay + growth)
  calc
    |totalEnergy - (height * Real.log scale +
        height * (Real.log height) ^ 2 / scale ^ 2)| ≤
        interactionConstant * (base + decay) +
          (primeConstant * base + meanConstant * growth) + 2 * archConstant * decay :=
      htotal.trans (add_le_add
        (add_le_add (hinteraction scale height hscale hscaleHeight hheight) hprimeBound)
        harchBound)
    _ = (interactionConstant + primeConstant) * base +
        (interactionConstant + 2 * archConstant) * decay + meanConstant * growth := by ring
    _ ≤ constant * base + constant * decay + constant * growth := by
      apply add_le_add
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_right _ hbase
          dsimp only [constant]
          linarith
        · apply mul_le_mul_of_nonneg_right _ hdecay
          dsimp only [constant]
          linarith
      · apply mul_le_mul_of_nonneg_right _ hgrowth
        dsimp only [constant]
        linarith
    _ = constant * (base + decay + growth) := by ring

theorem finitePairModel_secondMoment_eq_real_model
    (height exponent : ℝ) (hheight : 0 < height) :
    ((2 * Real.pi : ℝ) : ℂ) * pairNormalization height *
        (finitePairModel height exponent : ℂ) =
      ((height * Real.log (height ^ exponent) +
        height * (Real.log height) ^ 2 / (height ^ exponent) ^ 2 : ℝ) : ℂ) := by
  have hnegative : height ^ (-2 * exponent) = ((height ^ exponent) ^ 2)⁻¹ := by
    rw [show -2 * exponent = -(exponent * (2 : ℝ)) by ring,
      Real.rpow_neg hheight.le]
    congr 1
    simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hheight.le exponent 2
  rw [pairNormalization, finitePairModel, hnegative, Real.log_rpow hheight]
  push_cast
  field_simp
  ring

theorem integratedFullZeroModelSecondMoment : IntegratedFullZeroModelSecondMoment := by
  obtain ⟨constant, hconstant, hpointwise⟩ := exists_fullZeroMoment_pointwise_error_bound
  refine ⟨4 * constant, by positivity, max 2 (Real.exp 1), ?_⟩
  intro test lipschitz htest hlipschitz hatZero height hheight
  have hheightTwo : 2 ≤ height := (le_max_left _ _).trans hheight
  have hheightExp : Real.exp 1 ≤ height := (le_max_right _ _).trans hheight
  have hheightPos : 0 < height := (Real.exp_pos 1).trans_le hheightExp
  have hheightOne : 1 ≤ height := by linarith
  have hlogOne : 1 ≤ Real.log height :=
    (Real.le_log_iff_exp_le hheightPos).2 hheightExp
  have hlogNonneg : 0 ≤ Real.log height := zero_le_one.trans hlogOne
  have hrootPos : 0 < Real.sqrt (Real.log height) :=
    Real.sqrt_pos.2 (zero_lt_one.trans_le hlogOne)
  let error : ℝ → ℂ := fun exponent =>
    windowedFullZeroSecondMoment (height ^ exponent) height -
      ((2 * Real.pi : ℝ) : ℂ) * pairNormalization height *
        (finitePairModel height exponent : ℂ)
  have hmodelContinuous : Continuous (fun exponent : ℝ =>
      ((2 * Real.pi : ℝ) : ℂ) * pairNormalization height *
        (finitePairModel height exponent : ℂ)) :=
    continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_finitePairModel height hheightPos))
  have herrorMeasurable : AEStronglyMeasurable error
      (volume.restrict (Set.Icc 0 1)) :=
    (aestronglyMeasurable_windowedFullZeroSecondMoment_rpow height hheightTwo).sub
      hmodelContinuous.aestronglyMeasurable
  have herror : ∀ exponent ∈ Set.Icc (0 : ℝ) 1,
      ‖error exponent‖ ≤ constant * fullZeroMomentErrorEnvelope height exponent := by
    intro exponent hexponent
    have hscale : 1 ≤ height ^ exponent := Real.one_le_rpow hheightOne hexponent.1
    have hscaleHeight : height ^ exponent ≤ height := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hheightOne hexponent.2
    have henvelope :
        height * Real.sqrt (Real.log height) +
          height * Real.log height * Real.sqrt (Real.log height) / (height ^ exponent) +
          height ^ exponent * (1 + Real.log height) =
        fullZeroMomentErrorEnvelope height exponent := by
      unfold fullZeroMomentErrorEnvelope
      rw [Real.rpow_neg hheightPos.le]
      ring
    dsimp only [error]
    rw [finitePairModel_secondMoment_eq_real_model height exponent hheightPos,
      ← henvelope]
    exact hpointwise (height ^ exponent) height hscale hscaleHeight hheightExp
  obtain ⟨hintegrable, hintegral⟩ := test_mul_errorEnvelope_integral_bound
    test htest lipschitz hlipschitz hatZero error herrorMeasurable
    constant height hconstant.le hheightExp herror
  refine ⟨hintegrable, ?_⟩
  have habsIntegral : 0 ≤ ∫ exponent in (0 : ℝ)..1, |test exponent| :=
    intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => abs_nonneg _)
  have htestSize : |test 0| + lipschitz ≤ integratedTestSize test lipschitz := by
    unfold integratedTestSize
    linarith
  have hnormalization : 2 * Real.pi * ‖pairNormalization height‖ =
      height * Real.log height := by
    rw [pairNormalization, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    · field_simp
    · positivity
  calc
    ‖∫ exponent in (0 : ℝ)..1, (test exponent : ℂ) *
        (windowedFullZeroSecondMoment (height ^ exponent) height -
          ((2 * Real.pi : ℝ) : ℂ) * pairNormalization height *
            (finitePairModel height exponent : ℂ))‖ ≤
        4 * constant * (|test 0| + lipschitz) * height *
          Real.sqrt (Real.log height) := hintegral
    _ ≤ 4 * constant * integratedTestSize test lipschitz * height *
        Real.sqrt (Real.log height) := by gcongr
    _ = height * Real.log height *
        ((4 * constant) * integratedTestSize test lipschitz / Real.sqrt (Real.log height)) := by
      field_simp [hrootPos.ne']
      ring_nf
      rw [Real.sq_sqrt hlogNonneg]
    _ = 2 * Real.pi * ‖pairNormalization height‖ *
        ((4 * constant) * integratedTestSize test lipschitz / Real.sqrt (Real.log height)) := by
      rw [hnormalization]

end ZetaZeros.Unconditional.PairCorrelationProof
