/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationHighTail
import ZetaZeros.Unconditional.PairCorrelationFullZeroAssembly
import ZetaZeros.Unconditional.PairCorrelationArchimedeanCumulative

/-!
# Pointwise energy of the windowed full-zero model

The Archimedean term has square energy of order `T * (log T)^2 / x^2`.
This file retains that term explicitly and records the range in which it is
absorbed by `T * log T`.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set Filter
open scoped BigOperators Interval Topology ComplexConjugate

/-- The elementary three-term square estimate applied after the exact explicit
formula decomposition. -/
theorem windowedFullZero_energy_le_three_terms
    (x T : ℝ) (hx : 1 ≤ x) (hT : 0 ≤ T) :
    (∫ t in Set.Ioc 0 T, ‖windowedFullZeroSum x T t‖ ^ 2) ≤
      3 * ((∫ t : ℝ in 0..T, ‖fullZeroPoleTerm x t‖ ^ 2) +
        (∫ t : ℝ in 0..T, ‖fullZeroPrimeTerm x t‖ ^ 2) +
        ∫ t : ℝ in 0..T, ‖fullZeroArchimedeanTerm x t‖ ^ 2) := by
  have hp := integrableOn_norm_fullZeroPoleTerm_sq_Ioc x T
  have hq := integrableOn_norm_fullZeroPrimeTerm_sq_Ioc x T hx
  have ha := integrableOn_norm_fullZeroArchimedeanTerm_sq_Ioc x T hx
  have hexplicit := integrableOn_norm_fullZeroExplicitTerm_sq_Ioc x T hx
  have hwindow : IntegrableOn
      (fun t : ℝ => ‖windowedFullZeroSum x T t‖ ^ 2) (Set.Ioc 0 T) := by
    refine hexplicit.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [windowedFullZeroSum, Set.indicator_of_mem ht,
      phaseCorrectedFullZeroSum_eq_terms x hx t, norm_mul,
      norm_cpow_I_mul x (zero_lt_one.trans_le hx) t, one_mul]
  have hmajor : IntegrableOn (fun t : ℝ =>
      3 * (‖fullZeroPoleTerm x t‖ ^ 2 +
        ‖fullZeroPrimeTerm x t‖ ^ 2 +
        ‖fullZeroArchimedeanTerm x t‖ ^ 2)) (Set.Ioc 0 T) :=
    ((hp.add hq).add ha).const_mul 3
  have hpoint : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      ‖windowedFullZeroSum x T t‖ ^ 2 ≤
        3 * (‖fullZeroPoleTerm x t‖ ^ 2 +
          ‖fullZeroPrimeTerm x t‖ ^ 2 +
          ‖fullZeroArchimedeanTerm x t‖ ^ 2) := by
    intro t ht
    rw [windowedFullZeroSum, Set.indicator_of_mem ht,
      phaseCorrectedFullZeroSum_eq_terms x hx t, norm_mul,
      norm_cpow_I_mul x (zero_lt_one.trans_le hx) t, one_mul]
    have htri :
        ‖fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
            fullZeroArchimedeanTerm x t‖ ≤
          ‖fullZeroPoleTerm x t‖ + ‖fullZeroPrimeTerm x t‖ +
            ‖fullZeroArchimedeanTerm x t‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using
        (norm_add₃_le (a := fullZeroPoleTerm x t)
          (b := -fullZeroPrimeTerm x t)
          (c := fullZeroArchimedeanTerm x t))
    have hz : 0 ≤ ‖fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
        fullZeroArchimedeanTerm x t‖ := norm_nonneg _
    have hp0 : 0 ≤ ‖fullZeroPoleTerm x t‖ := norm_nonneg _
    have hq0 : 0 ≤ ‖fullZeroPrimeTerm x t‖ := norm_nonneg _
    have ha0 : 0 ≤ ‖fullZeroArchimedeanTerm x t‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖fullZeroPoleTerm x t‖ - ‖fullZeroPrimeTerm x t‖),
      sq_nonneg (‖fullZeroPrimeTerm x t‖ - ‖fullZeroArchimedeanTerm x t‖),
      sq_nonneg (‖fullZeroArchimedeanTerm x t‖ - ‖fullZeroPoleTerm x t‖)]
  calc
    (∫ t in Set.Ioc 0 T, ‖windowedFullZeroSum x T t‖ ^ 2) ≤
        ∫ t in Set.Ioc 0 T,
          3 * (‖fullZeroPoleTerm x t‖ ^ 2 +
            ‖fullZeroPrimeTerm x t‖ ^ 2 +
            ‖fullZeroArchimedeanTerm x t‖ ^ 2) :=
      MeasureTheory.setIntegral_mono_on hwindow hmajor measurableSet_Ioc hpoint
    _ = 3 * ((∫ t in Set.Ioc 0 T, ‖fullZeroPoleTerm x t‖ ^ 2) +
          (∫ t in Set.Ioc 0 T, ‖fullZeroPrimeTerm x t‖ ^ 2) +
          ∫ t in Set.Ioc 0 T, ‖fullZeroArchimedeanTerm x t‖ ^ 2) := by
      have hpq :
          (∫ t in Set.Ioc 0 T,
              (‖fullZeroPoleTerm x t‖ ^ 2 +
                ‖fullZeroPrimeTerm x t‖ ^ 2)) =
            (∫ t in Set.Ioc 0 T, ‖fullZeroPoleTerm x t‖ ^ 2) +
              ∫ t in Set.Ioc 0 T, ‖fullZeroPrimeTerm x t‖ ^ 2 := by
        simpa only [Pi.add_apply] using
          (MeasureTheory.integral_add hp hq)
      have hpqa :
          (∫ t in Set.Ioc 0 T,
              ((‖fullZeroPoleTerm x t‖ ^ 2 +
                ‖fullZeroPrimeTerm x t‖ ^ 2) +
                ‖fullZeroArchimedeanTerm x t‖ ^ 2)) =
            (∫ t in Set.Ioc 0 T,
              (‖fullZeroPoleTerm x t‖ ^ 2 +
                ‖fullZeroPrimeTerm x t‖ ^ 2)) +
              ∫ t in Set.Ioc 0 T,
                ‖fullZeroArchimedeanTerm x t‖ ^ 2 := by
        simpa only [Pi.add_apply] using
          (MeasureTheory.integral_add (hp.add hq) ha)
      rw [MeasureTheory.integral_const_mul, hpqa, hpq]
    _ = 3 * ((∫ t : ℝ in 0..T, ‖fullZeroPoleTerm x t‖ ^ 2) +
          (∫ t : ℝ in 0..T, ‖fullZeroPrimeTerm x t‖ ^ 2) +
          ∫ t : ℝ in 0..T, ‖fullZeroArchimedeanTerm x t‖ ^ 2) := by
      rw [intervalIntegral.integral_of_le hT,
        intervalIntegral.integral_of_le hT,
        intervalIntegral.integral_of_le hT]

/-- Exact square integral of the logarithmic Archimedean main term. -/
theorem intervalIntegral_archimedeanMain_sq_eq
    (x T : ℝ) :
    (∫ t : ℝ in 0..T,
        ‖(2 * Real.pi * Zeta23.mu t / x : ℂ)‖ ^ 2) =
      ((4 * Real.pi ^ 2) *
        (∫ t : ℝ in 0..T, Zeta23.mu t ^ 2)) / x ^ 2 := by
  have hpoint : (fun t : ℝ =>
      ‖(2 * Real.pi * Zeta23.mu t / x : ℂ)‖ ^ 2) =
      fun t : ℝ => (4 * Real.pi ^ 2 / x ^ 2) * Zeta23.mu t ^ 2 := by
    funext t
    have hcast :
        (2 * Real.pi * Zeta23.mu t / x : ℂ) =
          ((2 * Real.pi * Zeta23.mu t / x : ℝ) : ℂ) := by
      norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [div_pow, mul_pow, mul_pow]
    norm_num [div_eq_mul_inv]
    ac_rfl
  rw [hpoint, intervalIntegral.integral_const_mul]
  ring

theorem exists_intervalIntegral_archimedeanMain_sq_le :
    ∃ bound : ℝ, 0 < bound ∧ ∀ scale height : ℝ, Real.exp 1 ≤ height →
      (∫ ordinate : ℝ in 0..height,
        ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2) ≤
        bound * height * (Real.log height) ^ 2 / scale ^ 2 := by
  obtain ⟨densityConstant, densityConstant_pos, densityBound⟩ :=
    cumulative_archimedeanDensity_sq
  refine ⟨1 + 2 * densityConstant, by positivity, ?_⟩
  intro scale height height_large
  have height_pos : 0 < height := (Real.exp_pos 1).trans_le height_large
  have log_one : 1 ≤ Real.log height :=
    (Real.le_log_iff_exp_le height_pos).2 height_large
  have log_error : 1 + Real.log height ≤ 2 * (Real.log height) ^ 2 := by
    nlinarith [sq_nonneg (Real.log height - 1)]
  have density_upper := (abs_le.mp (densityBound height height_large)).2
  have numerator_bound :
      (4 * Real.pi ^ 2) * (∫ ordinate : ℝ in 0..height, Zeta23.mu ordinate ^ 2) ≤
        (1 + 2 * densityConstant) * height * (Real.log height) ^ 2 := by
    calc
      (4 * Real.pi ^ 2) * (∫ ordinate : ℝ in 0..height, Zeta23.mu ordinate ^ 2) ≤
          height * (Real.log height) ^ 2 +
            densityConstant * height * (1 + Real.log height) := by linarith
      _ ≤ height * (Real.log height) ^ 2 +
          densityConstant * height * (2 * (Real.log height) ^ 2) := by
        gcongr
      _ = (1 + 2 * densityConstant) * height * (Real.log height) ^ 2 := by ring
  rw [intervalIntegral_archimedeanMain_sq_eq]
  exact div_le_div_of_nonneg_right numerator_bound (sq_nonneg scale)

theorem exists_intervalIntegral_fullZeroPrimeTerm_sq_le :
    ∃ bound : ℝ, 0 < bound ∧ ∀ scale height : ℝ,
      1 ≤ scale → scale ≤ height → Real.exp 1 ≤ height →
      (∫ ordinate : ℝ in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2) ≤
        bound * height * Real.log height := by
  obtain ⟨meanConstant, meanConstant_pos, meanBound⟩ :=
    exists_fullZeroPrimeTerm_meanValue_bound
  obtain ⟨diagonalConstant, diagonalConstant_pos, diagonalBound⟩ :=
    pairPrimeMeanSquare_bounded
  refine ⟨1 + 2 * diagonalConstant + 2 * meanConstant, by positivity, ?_⟩
  intro scale height scale_one scale_height height_large
  have scale_pos : 0 < scale := zero_lt_one.trans_le scale_one
  have height_pos : 0 < height := (Real.exp_pos 1).trans_le height_large
  have log_one : 1 ≤ Real.log height :=
    (Real.le_log_iff_exp_le height_pos).2 height_large
  have log_scale_nonneg : 0 ≤ Real.log scale := Real.log_nonneg scale_one
  have log_scale_le : Real.log scale ≤ Real.log height :=
    Real.log_le_log scale_pos scale_height
  have diagonal_upper : pairPrimeMeanSquare scale ≤ Real.log scale + diagonalConstant := by
    linarith [(abs_le.mp (diagonalBound scale scale_one)).2]
  have base_upper : pairPrimeMeanSquare 1 ≤ diagonalConstant := by
    have base_bound := (abs_le.mp (diagonalBound 1 le_rfl)).2
    simpa only [Real.log_one, sub_zero] using base_bound
  have scale_sq_one : 1 ≤ scale ^ 2 := by nlinarith
  have negative_upper : pairPrimeMeanSquare 1 / scale ^ 2 ≤ diagonalConstant := by
    apply (div_le_iff₀ (sq_pos_of_pos scale_pos)).2
    exact base_upper.trans
      (le_mul_of_one_le_right diagonalConstant_pos.le scale_sq_one)
  have mean_upper := (abs_le.mp (meanBound scale scale_one height)).2
  rw [primePositiveCoeff_sq_tsum_eq scale scale_one,
    primeNegativeCoeff_sq_tsum_eq scale scale_one] at mean_upper
  have diagonal_sum_upper :
      pairPrimeMeanSquare scale + pairPrimeMeanSquare 1 / scale ^ 2 ≤
        Real.log height + 2 * diagonalConstant := by linarith
  have log_diagonal_upper : Real.log height + 2 * diagonalConstant ≤
      (1 + 2 * diagonalConstant) * Real.log height := by
    nlinarith [mul_le_mul_of_nonneg_left log_one
      (by positivity : 0 ≤ 2 * diagonalConstant)]
  calc
    (∫ ordinate : ℝ in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2) ≤
        height * (pairPrimeMeanSquare scale + pairPrimeMeanSquare 1 / scale ^ 2) +
          meanConstant * scale * (1 + Real.log scale) := by linarith
    _ ≤ height * (Real.log height + 2 * diagonalConstant) +
        meanConstant * height * (1 + Real.log height) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left diagonal_sum_upper height_pos.le
      · gcongr
    _ ≤ height * ((1 + 2 * diagonalConstant) * Real.log height) +
        meanConstant * height * (2 * Real.log height) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left log_diagonal_upper height_pos.le
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = (1 + 2 * diagonalConstant + 2 * meanConstant) * height * Real.log height := by
      ring

private theorem continuous_archimedeanMain_energy (scale : ℝ) :
    Continuous (fun ordinate : ℝ => (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)) := by
  have density_continuous : Continuous (fun ordinate : ℝ => (Zeta23.mu ordinate : ℂ)) :=
    Complex.continuous_ofReal.comp archimedeanDensity_smooth.continuous
  exact (continuous_const.mul density_continuous).div_const (scale : ℂ)

theorem exists_intervalIntegral_fullZeroArchimedeanTerm_sq_le :
    ∃ bound : ℝ, 0 < bound ∧ ∀ scale height : ℝ,
      1 ≤ scale → Real.exp 1 ≤ height →
      (∫ ordinate : ℝ in 0..height, ‖fullZeroArchimedeanTerm scale ordinate‖ ^ 2) ≤
        bound * height * (1 + (Real.log height) ^ 2 / scale ^ 2) := by
  obtain ⟨mainConstant, mainConstant_pos, mainBound⟩ :=
    exists_intervalIntegral_archimedeanMain_sq_le
  obtain ⟨remainderConstant, remainderConstant_nonneg, remainderBound⟩ :=
    montgomeryKernel_archimedeanTerm
  refine ⟨2 * remainderConstant ^ 2 + 2 * mainConstant, by positivity, ?_⟩
  intro scale height scale_one height_large
  have height_pos : 0 < height := (Real.exp_pos 1).trans_le height_large
  have main_integrable : IntervalIntegrable (fun ordinate : ℝ =>
      ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2) volume 0 height :=
    ((continuous_archimedeanMain_energy scale).norm.pow 2).intervalIntegrable 0 height
  have arch_integrable : IntervalIntegrable
      (fun ordinate : ℝ => ‖fullZeroArchimedeanTerm scale ordinate‖ ^ 2) volume 0 height :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le height_pos.le).2
      (integrableOn_norm_fullZeroArchimedeanTerm_sq_Ioc scale height scale_one)
  have major_integrable : IntervalIntegrable
      (fun ordinate : ℝ => 2 * remainderConstant ^ 2 +
        2 * ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2) volume 0 height :=
    intervalIntegrable_const.add (main_integrable.const_mul 2)
  have pointwise_bound : ∀ ordinate : ℝ,
      ‖fullZeroArchimedeanTerm scale ordinate‖ ^ 2 ≤
        2 * remainderConstant ^ 2 +
          2 * ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2 := by
    intro ordinate
    have remainder_bound : ‖fullZeroArchimedeanTerm scale ordinate -
        (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ≤ remainderConstant := by
      simpa only [fullZeroArchimedeanTerm] using remainderBound scale scale_one ordinate
    have triangle_bound : ‖fullZeroArchimedeanTerm scale ordinate‖ ≤
        remainderConstant + ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ := by
      calc
        ‖fullZeroArchimedeanTerm scale ordinate‖ =
            ‖(fullZeroArchimedeanTerm scale ordinate -
                (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)) +
              (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ := by ring_nf
        _ ≤ ‖fullZeroArchimedeanTerm scale ordinate -
              (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ +
            ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ := norm_add_le _ _
        _ ≤ remainderConstant +
            ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ :=
          add_le_add remainder_bound le_rfl
    nlinarith [norm_nonneg (fullZeroArchimedeanTerm scale ordinate),
      norm_nonneg (2 * Real.pi * Zeta23.mu ordinate / scale : ℂ),
      sq_nonneg (remainderConstant -
        ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖)]
  have ratio_nonneg : 0 ≤ (Real.log height) ^ 2 / scale ^ 2 := by positivity
  calc
    (∫ ordinate : ℝ in 0..height, ‖fullZeroArchimedeanTerm scale ordinate‖ ^ 2) ≤
        ∫ ordinate : ℝ in 0..height, 2 * remainderConstant ^ 2 +
          2 * ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2 :=
      intervalIntegral.integral_mono_on height_pos.le arch_integrable major_integrable
        (fun ordinate _ => pointwise_bound ordinate)
    _ = 2 * remainderConstant ^ 2 * height +
        2 * (∫ ordinate : ℝ in 0..height,
          ‖(2 * Real.pi * Zeta23.mu ordinate / scale : ℂ)‖ ^ 2) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const (main_integrable.const_mul 2),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      simp only [sub_zero, smul_eq_mul]
      ring
    _ ≤ 2 * remainderConstant ^ 2 * height +
        2 * (mainConstant * height * (Real.log height) ^ 2 / scale ^ 2) := by
      gcongr
      exact mainBound scale height height_large
    _ ≤ (2 * remainderConstant ^ 2 + 2 * mainConstant) * height *
        (1 + (Real.log height) ^ 2 / scale ^ 2) := by
      have first_bound := mul_le_mul_of_nonneg_left
        (show (1 : ℝ) ≤ 1 + (Real.log height) ^ 2 / scale ^ 2 by linarith)
        (show 0 ≤ 2 * remainderConstant ^ 2 * height by positivity)
      have second_bound := mul_le_mul_of_nonneg_left
        (show (Real.log height) ^ 2 / scale ^ 2 ≤
          1 + (Real.log height) ^ 2 / scale ^ 2 by linarith)
        (show 0 ≤ 2 * mainConstant * height by positivity)
      calc
        _ = (2 * remainderConstant ^ 2 * height) * 1 +
            (2 * mainConstant * height) * ((Real.log height) ^ 2 / scale ^ 2) := by ring
        _ ≤ (2 * remainderConstant ^ 2 * height) *
              (1 + (Real.log height) ^ 2 / scale ^ 2) +
            (2 * mainConstant * height) * (1 + (Real.log height) ^ 2 / scale ^ 2) :=
          add_le_add first_bound second_bound
        _ = _ := by ring

theorem exists_windowedFullZero_energy_le :
    ∃ bound : ℝ, 0 < bound ∧ ∀ scale height : ℝ,
      1 ≤ scale → scale ≤ height → Real.exp 1 ≤ height →
      (∫ ordinate in Set.Ioc 0 height, ‖windowedFullZeroSum scale height ordinate‖ ^ 2) ≤
        bound * height * (Real.log height + (Real.log height) ^ 2 / scale ^ 2) := by
  obtain ⟨primeConstant, primeConstant_pos, primeBound⟩ :=
    exists_intervalIntegral_fullZeroPrimeTerm_sq_le
  obtain ⟨archConstant, archConstant_pos, archBound⟩ :=
    exists_intervalIntegral_fullZeroArchimedeanTerm_sq_le
  refine ⟨3 * ((256 / 9 : ℝ) * Real.pi + primeConstant + archConstant), by positivity, ?_⟩
  intro scale height scale_one scale_height height_large
  have height_pos : 0 < height := (Real.exp_pos 1).trans_le height_large
  have log_one : 1 ≤ Real.log height :=
    (Real.le_log_iff_exp_le height_pos).2 height_large
  have ratio_nonneg : 0 ≤ (Real.log height) ^ 2 / scale ^ 2 := by positivity
  have factor_one : 1 ≤ Real.log height + (Real.log height) ^ 2 / scale ^ 2 := by
    linarith
  have pole_bound :
      (∫ ordinate : ℝ in 0..height, ‖fullZeroPoleTerm scale ordinate‖ ^ 2) ≤
        ((256 / 9 : ℝ) * Real.pi) * height *
          (Real.log height + (Real.log height) ^ 2 / scale ^ 2) := by
    calc
      (∫ ordinate : ℝ in 0..height, ‖fullZeroPoleTerm scale ordinate‖ ^ 2) ≤
          (256 / 9 : ℝ) * Real.pi * scale :=
        intervalIntegral_fullZeroPoleTerm_sq_le scale height scale_one height_pos.le
      _ ≤ (256 / 9 : ℝ) * Real.pi * height := by gcongr
      _ ≤ ((256 / 9 : ℝ) * Real.pi) * height *
          (Real.log height + (Real.log height) ^ 2 / scale ^ 2) :=
        le_mul_of_one_le_right (by positivity) factor_one
  have prime_bound :
      (∫ ordinate : ℝ in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2) ≤
        primeConstant * height *
          (Real.log height + (Real.log height) ^ 2 / scale ^ 2) := by
    apply (primeBound scale height scale_one scale_height height_large).trans
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ratio_nonneg) (by positivity)
  have arch_bound :
      (∫ ordinate : ℝ in 0..height, ‖fullZeroArchimedeanTerm scale ordinate‖ ^ 2) ≤
        archConstant * height *
          (Real.log height + (Real.log height) ^ 2 / scale ^ 2) := by
    apply (archBound scale height scale_one height_large).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  calc
    (∫ ordinate in Set.Ioc 0 height, ‖windowedFullZeroSum scale height ordinate‖ ^ 2) ≤
        3 * ((∫ ordinate : ℝ in 0..height, ‖fullZeroPoleTerm scale ordinate‖ ^ 2) +
          (∫ ordinate : ℝ in 0..height, ‖fullZeroPrimeTerm scale ordinate‖ ^ 2) +
          ∫ ordinate : ℝ in 0..height, ‖fullZeroArchimedeanTerm scale ordinate‖ ^ 2) :=
      windowedFullZero_energy_le_three_terms scale height scale_one height_pos.le
    _ ≤ 3 * (((256 / 9 : ℝ) * Real.pi) * height *
          (Real.log height + (Real.log height) ^ 2 / scale ^ 2) +
        primeConstant * height * (Real.log height + (Real.log height) ^ 2 / scale ^ 2) +
        archConstant * height * (Real.log height + (Real.log height) ^ 2 / scale ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add pole_bound prime_bound) arch_bound)
        (by norm_num)
    _ = (3 * ((256 / 9 : ℝ) * Real.pi + primeConstant + archConstant)) * height *
        (Real.log height + (Real.log height) ^ 2 / scale ^ 2) := by ring

end ZetaZeros.Unconditional.PairCorrelationProof
