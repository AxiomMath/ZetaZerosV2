/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationAssembly
import ZetaZeros.Unconditional.PairCorrelationMeanValue
import ZetaZeros.Unconditional.PairCorrelationPrime

/-!
# The explicit-formula decomposition of the full-zero model

This file rewrites the full Lorentzian zero series as the three concrete terms which enter
Montgomery's mean-square calculation.  In particular, no zero sum remains hidden behind the
abstract `literatureRHS` notation.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set

/-- The two pole values in Montgomery's explicit formula. -/
noncomputable def fullZeroPoleTerm (x t : ℝ) : ℂ :=
  Zeta23.paperFT (montgomeryKernel x t) (Complex.I / 2) +
    Zeta23.paperFT (montgomeryKernel x t) (-Complex.I / 2)

private theorem continuous_montgomeryKernel_paperFT_pole
    (x delta : ℝ) (hdelta : |delta| ≤ (1 / 2 : ℝ)) :
    Continuous (fun t : ℝ =>
      Zeta23.paperFT (montgomeryKernel x t) (Complex.I * (delta : ℂ))) := by
  have hz : |(Complex.I * (delta : ℂ)).im| < 1 := by
    have hlt : |delta| < 1 := lt_of_le_of_lt hdelta (by norm_num)
    simpa using hlt
  rw [show (fun t : ℝ =>
      Zeta23.paperFT (montgomeryKernel x t) (Complex.I * (delta : ℂ))) =
      (fun t : ℝ =>
        2 * Complex.exp
            (Complex.I * (Complex.I * (delta : ℂ) - (t : ℂ)) * Real.log x) /
          (1 + (Complex.I * (delta : ℂ) - (t : ℂ)) ^ 2)) by
    funext t
    exact montgomeryKernel_paperFT x t (Complex.I * (delta : ℂ)) hz]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    have hshift :
        Complex.I * (delta : ℂ) - (t : ℂ) =
          ((-t : ℝ) : ℂ) + Complex.I * (delta : ℂ) := by
      push_cast
      ring
    rw [hshift]
    intro hzero
    have hnorm :
        ‖(1 : ℂ) + (((-t : ℝ) : ℂ) + Complex.I * (delta : ℂ)) ^ 2‖ = 0 := by
      rw [hzero]
      simp
    have hlower := shiftedLorentzian_norm_lower (-t) delta hdelta
    rw [hnorm] at hlower
    nlinarith [sq_nonneg t]

/-- The pole contribution varies continuously with the height parameter. -/
theorem continuous_fullZeroPoleTerm (x : ℝ) :
    Continuous (fullZeroPoleTerm x) := by
  have hplus := continuous_montgomeryKernel_paperFT_pole x (1 / 2) (by norm_num)
  have hminus := continuous_montgomeryKernel_paperFT_pole x (-1 / 2) (by norm_num)
  have hp : Complex.I / 2 = Complex.I * ((1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hm : -Complex.I / 2 = Complex.I * ((-1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  unfold fullZeroPoleTerm
  rw [hp, hm]
  exact hplus.add hminus

private theorem measurable_montgomeryKernel_paperFT_pole_joint
    (delta : ℝ) (hdelta : |delta| ≤ (1 / 2 : ℝ)) :
    Measurable (fun p : ℝ × ℝ =>
      Zeta23.paperFT (montgomeryKernel p.1 p.2)
        (Complex.I * (delta : ℂ))) := by
  have hz : |(Complex.I * (delta : ℂ)).im| < 1 := by
    have hlt : |delta| < 1 := lt_of_le_of_lt hdelta (by norm_num)
    simpa using hlt
  rw [show (fun p : ℝ × ℝ =>
      Zeta23.paperFT (montgomeryKernel p.1 p.2)
        (Complex.I * (delta : ℂ))) =
      (fun p : ℝ × ℝ =>
        2 * Complex.exp
            (Complex.I * (Complex.I * (delta : ℂ) - (p.2 : ℂ)) *
              Real.log p.1) /
          (1 + (Complex.I * (delta : ℂ) - (p.2 : ℂ)) ^ 2)) by
    funext p
    exact montgomeryKernel_paperFT p.1 p.2
      (Complex.I * (delta : ℂ)) hz]
  fun_prop

/-- The pole term is jointly measurable in the scale and height parameters. -/
theorem measurable_fullZeroPoleTerm_joint :
    Measurable (fun p : ℝ × ℝ => fullZeroPoleTerm p.1 p.2) := by
  have hplus := measurable_montgomeryKernel_paperFT_pole_joint
    (1 / 2) (by norm_num)
  have hminus := measurable_montgomeryKernel_paperFT_pole_joint
    (-1 / 2) (by norm_num)
  have hp : Complex.I / 2 = Complex.I * ((1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hm : -Complex.I / 2 = Complex.I * ((-1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  unfold fullZeroPoleTerm
  rw [hp, hm]
  exact hplus.add hminus

/-- The prime-power side of Montgomery's explicit formula. -/
noncomputable def fullZeroPrimeTerm (x t : ℝ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (montgomeryKernel x t (Real.log n) +
      montgomeryKernel x t (-Real.log n))

/-- Coefficients of the positive-frequency half of Montgomery's prime series, indexed from
zero so that the underlying prime-power index is `k + 1`. -/
noncomputable def primePositiveCoeff (x : ℝ) (k : ℕ) : ℂ :=
  (((ArithmeticFunction.vonMangoldt (k + 1) /
      Real.sqrt ((k + 1 : ℕ) : ℝ)) *
    Real.exp (-|Real.log ((k + 1 : ℕ) : ℝ) - Real.log x|) : ℝ) : ℂ)

/-- Coefficients of the negative-frequency half of Montgomery's prime series, indexed from
zero so that the underlying prime-power index is `k + 1`. -/
noncomputable def primeNegativeCoeff (x : ℝ) (k : ℕ) : ℂ :=
  (((ArithmeticFunction.vonMangoldt (k + 1) /
      Real.sqrt ((k + 1 : ℕ) : ℝ)) *
    Real.exp (-|-Real.log ((k + 1 : ℕ) : ℝ) - Real.log x|) : ℝ) : ℂ)

/-- The index-weighted squared norm of the positive-frequency coefficient is exactly the
tent-kernel summand needed in Montgomery's Hilbert error. -/
theorem primePositiveCoeff_weighted_sq
    (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    (((k + 1 : ℕ) : ℝ) * ‖primePositiveCoeff x k‖ ^ 2) =
      ArithmeticFunction.vonMangoldt (k + 1) ^ 2 *
        pairPrimeKernel x (k + 1) := by
  have hnpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsqrt : Real.sqrt (((k + 1 : ℕ) : ℝ)) ^ 2 = ((k + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt hnpos.le
  rw [primePositiveCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (Real.exp_nonneg _)), pairPrimeKernel]
  by_cases hnx : (((k + 1 : ℕ) : ℝ)) ≤ x
  · have hlog : Real.log (((k + 1 : ℕ) : ℝ)) - Real.log x ≤ 0 := by
      exact sub_nonpos.mpr (Real.log_le_log hnpos hnx)
    have hmin : min ((((k + 1 : ℕ) : ℝ)) / x)
        (x / (((k + 1 : ℕ) : ℝ))) = (((k + 1 : ℕ) : ℝ)) / x := by
      rw [min_eq_left]
      rw [div_le_div_iff₀ hxpos hnpos]
      nlinarith
    rw [hmin, abs_of_nonpos hlog, neg_neg, Real.exp_sub,
      Real.exp_log hnpos, Real.exp_log hxpos]
    field_simp [ne_of_gt hnpos, ne_of_gt hxpos,
      ne_of_gt (Real.sqrt_pos.2 hnpos)]
    nlinarith
  · have hxn : x ≤ (((k + 1 : ℕ) : ℝ)) := le_of_not_ge hnx
    have hlog : 0 ≤ Real.log (((k + 1 : ℕ) : ℝ)) - Real.log x := by
      exact sub_nonneg.mpr (Real.log_le_log hxpos hxn)
    have hmin : min ((((k + 1 : ℕ) : ℝ)) / x)
        (x / (((k + 1 : ℕ) : ℝ))) = x / (((k + 1 : ℕ) : ℝ)) := by
      rw [min_eq_right]
      rw [div_le_div_iff₀ hnpos hxpos]
      nlinarith
    rw [hmin, abs_of_nonneg hlog, Real.exp_neg, Real.exp_sub,
      Real.exp_log hnpos, Real.exp_log hxpos]
    field_simp [ne_of_gt hnpos, ne_of_gt hxpos,
      ne_of_gt (Real.sqrt_pos.2 hnpos)]
    nlinarith

/-- The negative-frequency coefficient has no larger index-weighted square than the
positive-frequency tent-kernel summand. -/
theorem primeNegativeCoeff_weighted_sq_le
    (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    (((k + 1 : ℕ) : ℝ) * ‖primeNegativeCoeff x k‖ ^ 2) ≤
      ArithmeticFunction.vonMangoldt (k + 1) ^ 2 *
        pairPrimeKernel x (k + 1) := by
  have hnOne : 1 ≤ (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hlogn : 0 ≤ Real.log (((k + 1 : ℕ) : ℝ)) := Real.log_nonneg hnOne
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have habs :
      |Real.log (((k + 1 : ℕ) : ℝ)) - Real.log x| ≤
        |-Real.log (((k + 1 : ℕ) : ℝ)) - Real.log x| := by
    calc
      |Real.log (((k + 1 : ℕ) : ℝ)) - Real.log x| ≤
          |Real.log (((k + 1 : ℕ) : ℝ))| + |Real.log x| := abs_sub _ _
      _ = Real.log (((k + 1 : ℕ) : ℝ)) + Real.log x := by
        rw [abs_of_nonneg hlogn, abs_of_nonneg hlogx]
      _ = |-Real.log (((k + 1 : ℕ) : ℝ)) - Real.log x| := by
        rw [abs_of_nonpos (by linarith)]
        ring
  have hnorm : ‖primeNegativeCoeff x k‖ ≤ ‖primePositiveCoeff x k‖ := by
    rw [primeNegativeCoeff, primePositiveCoeff, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        (Real.exp_nonneg _)),
      abs_of_nonneg (mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        (Real.exp_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg habs))
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
  rw [← primePositiveCoeff_weighted_sq x hx k]
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm)
    (Nat.cast_nonneg _)

/-- The two-sided Dirichlet-series model of the prime term in Montgomery's explicit formula. -/
noncomputable def primeModelSeries (x t : ℝ) : ℂ :=
  dirichletSeries (primePositiveCoeff x) t +
    dirichletSeries (primeNegativeCoeff x) (-t)

/-- Absolute summability of the positive-frequency coefficients. -/
theorem primePositiveCoeff_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun k : ℕ => ‖primePositiveCoeff x k‖) := by
  have hLSeries : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (((3 / 2 : ℝ) : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hnorm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (((3 / 2 : ℝ) : ℂ)) n‖) :=
    summable_norm_iff.mpr hLSeries
  have hmajor : Summable (fun k : ℕ => x *
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (((3 / 2 : ℝ) : ℂ)) (k + 1)‖) :=
    Summable.mul_left x ((summable_nat_add_iff 1).mpr hnorm)
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ hmajor
  intro k
  have hk : k + 1 ≠ 0 := by omega
  have hkOne : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hkPos : 0 < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hkOne
  have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [primePositiveCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (Real.exp_nonneg _)),
    norm_vonMangoldt_LSeries_term_three_halves (k + 1) hk]
  calc
    ArithmeticFunction.vonMangoldt (k + 1) /
          Real.sqrt ((k + 1 : ℕ) : ℝ) *
        Real.exp (-|Real.log ((k + 1 : ℕ) : ℝ) - Real.log x|) ≤
      ArithmeticFunction.vonMangoldt (k + 1) /
          Real.sqrt ((k + 1 : ℕ) : ℝ) *
        (x / ((k + 1 : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (exp_neg_abs_log_sub_log_le_div x ((k + 1 : ℕ) : ℝ) hxPos hkPos)
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    _ = x * (ArithmeticFunction.vonMangoldt (k + 1) /
        (Real.sqrt ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ))) := by
      field_simp [ne_of_gt hkPos, ne_of_gt (Real.sqrt_pos.2 hkPos)]

/-- Absolute summability of the negative-frequency coefficients. -/
theorem primeNegativeCoeff_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun k : ℕ => ‖primeNegativeCoeff x k‖) := by
  have hLSeries : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (((3 / 2 : ℝ) : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hnorm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (((3 / 2 : ℝ) : ℂ)) n‖) :=
    summable_norm_iff.mpr hLSeries
  have hmajor : Summable (fun k : ℕ => x *
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (((3 / 2 : ℝ) : ℂ)) (k + 1)‖) :=
    Summable.mul_left x ((summable_nat_add_iff 1).mpr hnorm)
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ hmajor
  intro k
  have hk : k + 1 ≠ 0 := by omega
  have hkOne : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hkPos : 0 < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hkOne
  rw [primeNegativeCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (Real.exp_nonneg _)),
    norm_vonMangoldt_LSeries_term_three_halves (k + 1) hk]
  calc
    ArithmeticFunction.vonMangoldt (k + 1) /
          Real.sqrt ((k + 1 : ℕ) : ℝ) *
        Real.exp (-|-Real.log ((k + 1 : ℕ) : ℝ) - Real.log x|) ≤
      ArithmeticFunction.vonMangoldt (k + 1) /
          Real.sqrt ((k + 1 : ℕ) : ℝ) *
        (x / ((k + 1 : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (exp_neg_abs_neg_log_sub_log_le_div x ((k + 1 : ℕ) : ℝ) hx hkOne)
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    _ = x * (ArithmeticFunction.vonMangoldt (k + 1) /
        (Real.sqrt ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ))) := by
      field_simp [ne_of_gt hkPos, ne_of_gt (Real.sqrt_pos.2 hkPos)]

/-- The index-weighted squared positive-frequency coefficients are summable. -/
theorem primePositiveCoeff_weighted_summable
    (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * ‖primePositiveCoeff x k‖ ^ 2) := by
  obtain ⟨K, hK, hall⟩ := pairWeightedPrimeMeanSquare_bound
  obtain ⟨hsum, hbound⟩ := hall x hx
  have hshift := (summable_nat_add_iff 1).mpr hsum
  apply hshift.congr
  intro k
  simpa only [Nat.cast_add, Nat.cast_one] using
    (primePositiveCoeff_weighted_sq x hx k).symm

/-- The index-weighted squared negative-frequency coefficients are summable. -/
theorem primeNegativeCoeff_weighted_summable
    (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * ‖primeNegativeCoeff x k‖ ^ 2) := by
  obtain ⟨K, hK, hall⟩ := pairWeightedPrimeMeanSquare_bound
  obtain ⟨hsum, hbound⟩ := hall x hx
  have hshift := (summable_nat_add_iff 1).mpr hsum
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (sq_nonneg _))
    (fun k => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        primeNegativeCoeff_weighted_sq_le x hx k)
    hshift

/-- The positive-frequency Hilbert weight is exactly the weighted prime mean square. -/
theorem primePositiveCoeff_weighted_tsum_eq
    (x : ℝ) (hx : 1 ≤ x) :
    (∑' k : ℕ, ((k : ℝ) + 1) * ‖primePositiveCoeff x k‖ ^ 2) =
      pairWeightedPrimeMeanSquare x := by
  obtain ⟨K, hK, hall⟩ := pairWeightedPrimeMeanSquare_bound
  obtain ⟨hsum, hbound⟩ := hall x hx
  let q : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n ^ 2 * pairPrimeKernel x n
  have hshift : (∑' k : ℕ, q (k + 1)) = ∑' n : ℕ, q n := by
    simpa only [Finset.sum_range_one, q, ArithmeticFunction.map_zero,
      CharP.cast_eq_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
      zero_add] using
      hsum.sum_add_tsum_nat_add 1
  calc
    (∑' k : ℕ, ((k : ℝ) + 1) * ‖primePositiveCoeff x k‖ ^ 2) =
        ∑' k : ℕ, q (k + 1) := by
      apply tsum_congr
      intro k
      simpa only [Nat.cast_add, Nat.cast_one, q] using
        primePositiveCoeff_weighted_sq x hx k
    _ = ∑' n : ℕ, q n := hshift
    _ = pairWeightedPrimeMeanSquare x := rfl

/-- The negative-frequency Hilbert weight is bounded by the weighted prime mean square. -/
theorem primeNegativeCoeff_weighted_tsum_le
    (x : ℝ) (hx : 1 ≤ x) :
    (∑' k : ℕ, ((k : ℝ) + 1) * ‖primeNegativeCoeff x k‖ ^ 2) ≤
      pairWeightedPrimeMeanSquare x := by
  rw [← primePositiveCoeff_weighted_tsum_eq x hx]
  exact Summable.tsum_le_tsum
    (fun k => by
      calc
        ((k : ℝ) + 1) * ‖primeNegativeCoeff x k‖ ^ 2 ≤
            ArithmeticFunction.vonMangoldt (k + 1) ^ 2 *
              pairPrimeKernel x (k + 1) := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            primeNegativeCoeff_weighted_sq_le x hx k
        _ = ((k : ℝ) + 1) * ‖primePositiveCoeff x k‖ ^ 2 := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (primePositiveCoeff_weighted_sq x hx k).symm)
    (primeNegativeCoeff_weighted_summable x hx)
    (primePositiveCoeff_weighted_summable x hx)

/-- The prime-power term is exactly the sum of its positive- and negative-frequency
Dirichlet-series halves. -/
theorem fullZeroPrimeTerm_eq_primeModelSeries
    (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    fullZeroPrimeTerm x t = primeModelSeries x t := by
  let q : ℕ → ℂ := fun n =>
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (montgomeryKernel x t (Real.log n) +
        montgomeryKernel x t (-Real.log n))
  let p : ℕ → ℂ := fun k => primePositiveCoeff x k * Complex.exp
    (-Complex.I * (((dirichletFrequency k) * t : ℝ) : ℂ))
  let m : ℕ → ℂ := fun k => primeNegativeCoeff x k * Complex.exp
    (-Complex.I * (((dirichletFrequency k) * (-t) : ℝ) : ℂ))
  have hp : Summable p := by
    apply Summable.of_norm
    simpa only [p, norm_dirichletSeries_term] using primePositiveCoeff_summable x hx
  have hm : Summable m := by
    apply Summable.of_norm
    simpa only [m, norm_dirichletSeries_term] using primeNegativeCoeff_summable x hx
  have hterm : ∀ k : ℕ, q (k + 1) = p k + m k := by
    intro k
    have hphasePos :
        Complex.exp (-Complex.I * (t : ℂ) *
            (Real.log ((k + 1 : ℕ) : ℝ) : ℂ)) =
          Complex.exp (-Complex.I *
            (((dirichletFrequency k) * t : ℝ) : ℂ)) := by
      congr 1
      simp only [dirichletFrequency, Nat.cast_add, Nat.cast_one,
        Complex.ofReal_mul]
      ring
    have hphaseNeg :
        Complex.exp (-Complex.I * (t : ℂ) *
            ((-Real.log ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ)) =
          Complex.exp (-Complex.I *
            (((dirichletFrequency k) * (-t) : ℝ) : ℂ)) := by
      congr 1
      simp only [dirichletFrequency, Nat.cast_add, Nat.cast_one,
        Complex.ofReal_mul, Complex.ofReal_neg]
      ring
    simp only [q, p, m, montgomeryKernel]
    rw [hphasePos, hphaseNeg]
    simp only [primePositiveCoeff, primeNegativeCoeff, Nat.cast_add, Nat.cast_one,
      Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    ring_nf
  have hshift : Summable (fun k => q (k + 1)) := by
    rw [summable_congr hterm]
    exact hp.add hm
  have hq : Summable q := (summable_nat_add_iff 1).mp hshift
  have hsumShift : (∑' n, q n) = ∑' k, q (k + 1) := by
    symm
    simpa only [Finset.sum_range_one, q, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
      zero_div, ofReal_zero, zero_mul, zero_add] using
      hq.sum_add_tsum_nat_add 1
  rw [fullZeroPrimeTerm, show (fun n =>
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (montgomeryKernel x t (Real.log n) +
          montgomeryKernel x t (-Real.log n))) = q from rfl,
    hsumShift]
  calc
    (∑' k, q (k + 1)) = ∑' k, (p k + m k) := tsum_congr hterm
    _ = (∑' k, p k) + ∑' k, m k := hp.tsum_add hm
    _ = primeModelSeries x t := by rfl

private theorem measurable_dirichletSeries (a : ℕ → ℂ) :
    Measurable (dirichletSeries a) := by
  unfold dirichletSeries
  apply Measurable.tsum
  intro n
  fun_prop

private theorem norm_dirichletSeries_le_tsum
    (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) (t : ℝ) :
    ‖dirichletSeries a t‖ ≤ ∑' n, ‖a n‖ := by
  unfold dirichletSeries
  calc
    ‖∑' n, a n * Complex.exp
        (-Complex.I * (((dirichletFrequency n) * t : ℝ) : ℂ))‖ ≤
      ∑' n, ‖a n * Complex.exp
        (-Complex.I * (((dirichletFrequency n) * t : ℝ) : ℂ))‖ := by
        apply norm_tsum_le_tsum_norm
        simpa only [norm_dirichletSeries_term] using ha
    _ = ∑' n, ‖a n‖ := tsum_congr fun n => norm_dirichletSeries_term a n t

/-- The two-sided prime Dirichlet series is measurable in the height variable. -/
theorem measurable_primeModelSeries (x : ℝ) :
    Measurable (primeModelSeries x) := by
  unfold primeModelSeries
  exact (measurable_dirichletSeries _).add
    ((measurable_dirichletSeries _).comp measurable_neg)

/-- The absolute coefficient sums uniformly bound the prime model. -/
theorem norm_primeModelSeries_le (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    ‖primeModelSeries x t‖ ≤
      (∑' n, ‖primePositiveCoeff x n‖) +
        ∑' n, ‖primeNegativeCoeff x n‖ := by
  unfold primeModelSeries
  calc
    ‖dirichletSeries (primePositiveCoeff x) t +
        dirichletSeries (primeNegativeCoeff x) (-t)‖ ≤
      ‖dirichletSeries (primePositiveCoeff x) t‖ +
        ‖dirichletSeries (primeNegativeCoeff x) (-t)‖ := norm_add_le _ _
    _ ≤ (∑' n, ‖primePositiveCoeff x n‖) +
        ∑' n, ‖primeNegativeCoeff x n‖ :=
      add_le_add
        (norm_dirichletSeries_le_tsum _ (primePositiveCoeff_summable x hx) t)
        (norm_dirichletSeries_le_tsum _ (primeNegativeCoeff_summable x hx) (-t))

/-- The original prime-power side inherits measurability from its Dirichlet-series model. -/
theorem measurable_fullZeroPrimeTerm (x : ℝ) (hx : 1 ≤ x) :
    Measurable (fullZeroPrimeTerm x) := by
  have hfun : fullZeroPrimeTerm x = primeModelSeries x := by
    funext t
    exact fullZeroPrimeTerm_eq_primeModelSeries x hx t
  rw [hfun]
  exact measurable_primeModelSeries x

/-- The prime-power term is jointly measurable in the scale and height parameters. -/
theorem measurable_fullZeroPrimeTerm_joint :
    Measurable (fun p : ℝ × ℝ => fullZeroPrimeTerm p.1 p.2) := by
  unfold fullZeroPrimeTerm montgomeryKernel
  apply Measurable.tsum
  intro n
  fun_prop

/-- The Archimedean side of Montgomery's explicit formula. -/
noncomputable def fullZeroArchimedeanTerm (x t : ℝ) : ℂ :=
  ∫ r : ℝ, Zeta23.paperFT (montgomeryKernel x t) r * Zeta23.mu r

private theorem continuous_fullZeroArchimedeanIntegrand (x : ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      Zeta23.paperFT (montgomeryKernel x p.1) p.2 * Zeta23.mu p.2) := by
  have hpaper : Continuous (fun p : ℝ × ℝ =>
      Zeta23.paperFT (montgomeryKernel x p.1) (p.2 : ℂ)) := by
    rw [show (fun p : ℝ × ℝ =>
        Zeta23.paperFT (montgomeryKernel x p.1) (p.2 : ℂ)) =
      (fun p : ℝ × ℝ =>
        2 * Complex.exp
            (Complex.I * ((p.2 : ℂ) - (p.1 : ℂ)) * Real.log x) /
          (1 + ((p.2 : ℂ) - (p.1 : ℂ)) ^ 2)) by
      funext p
      exact montgomeryKernel_paperFT x p.1 (p.2 : ℂ) (by simp)]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro p
      have hden :
          (1 : ℂ) + ((p.2 : ℂ) - (p.1 : ℂ)) ^ 2 =
            ((1 + (p.2 - p.1) ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hden]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
  exact hpaper.mul
    (Complex.continuous_ofReal.comp
      (archimedeanDensity_smooth.continuous.comp continuous_snd))

/-- The Archimedean contribution is measurable in the height parameter. -/
theorem measurable_fullZeroArchimedeanTerm (x : ℝ) :
    Measurable (fullZeroArchimedeanTerm x) := by
  unfold fullZeroArchimedeanTerm
  exact (continuous_fullZeroArchimedeanIntegrand x).stronglyMeasurable
    |>.integral_prod_right.measurable

private theorem measurable_montgomeryKernel_paperFT_real_joint :
    Measurable (fun p : (ℝ × ℝ) × ℝ =>
      Zeta23.paperFT (montgomeryKernel p.1.1 p.1.2) (p.2 : ℂ)) := by
  rw [show (fun p : (ℝ × ℝ) × ℝ =>
      Zeta23.paperFT (montgomeryKernel p.1.1 p.1.2) (p.2 : ℂ)) =
      (fun p : (ℝ × ℝ) × ℝ =>
        2 * Complex.exp
            (Complex.I * ((p.2 : ℂ) - (p.1.2 : ℂ)) * Real.log p.1.1) /
          (1 + ((p.2 : ℂ) - (p.1.2 : ℂ)) ^ 2)) by
    funext p
    exact montgomeryKernel_paperFT p.1.1 p.1.2 (p.2 : ℂ) (by simp)]
  fun_prop

private theorem measurable_fullZeroArchimedeanIntegrand_joint :
    Measurable (fun p : (ℝ × ℝ) × ℝ =>
      Zeta23.paperFT (montgomeryKernel p.1.1 p.1.2) p.2 * Zeta23.mu p.2) := by
  have hmu : Measurable (fun p : (ℝ × ℝ) × ℝ => (Zeta23.mu p.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (archimedeanDensity_smooth.continuous.measurable.comp measurable_snd)
  exact measurable_montgomeryKernel_paperFT_real_joint.mul hmu

/-- The Archimedean term is jointly measurable in the scale and height parameters. -/
theorem measurable_fullZeroArchimedeanTerm_joint :
    Measurable (fun p : ℝ × ℝ => fullZeroArchimedeanTerm p.1 p.2) := by
  unfold fullZeroArchimedeanTerm
  exact measurable_fullZeroArchimedeanIntegrand_joint.stronglyMeasurable
    |>.integral_prod_right'.measurable

/-- The complete pole-minus-prime-plus-Archimedean expression is measurable. -/
theorem measurable_fullZeroExplicitTerm (x : ℝ) (hx : 1 ≤ x) :
    Measurable (fun t : ℝ =>
      fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
        fullZeroArchimedeanTerm x t) := by
  exact (continuous_fullZeroPoleTerm x).measurable.sub
    (measurable_fullZeroPrimeTerm x hx) |>.add
      (measurable_fullZeroArchimedeanTerm x)

/-- The complete explicit-formula expression is jointly measurable in scale and height. -/
theorem measurable_fullZeroExplicitTerm_joint :
    Measurable (fun p : ℝ × ℝ =>
      fullZeroPoleTerm p.1 p.2 - fullZeroPrimeTerm p.1 p.2 +
        fullZeroArchimedeanTerm p.1 p.2) := by
  exact measurable_fullZeroPoleTerm_joint.sub measurable_fullZeroPrimeTerm_joint |>.add
    measurable_fullZeroArchimedeanTerm_joint

/-- The conjugate-square explicit-formula integrand is jointly measurable. -/
theorem measurable_fullZeroExplicitTerm_mul_conj_joint :
    Measurable (fun p : ℝ × ℝ =>
      (fullZeroPoleTerm p.1 p.2 - fullZeroPrimeTerm p.1 p.2 +
          fullZeroArchimedeanTerm p.1 p.2) *
        (starRingEnd ℂ)
          (fullZeroPoleTerm p.1 p.2 - fullZeroPrimeTerm p.1 p.2 +
            fullZeroArchimedeanTerm p.1 p.2)) := by
  have hstar : Measurable (fun p : ℝ × ℝ =>
      star (fullZeroPoleTerm p.1 p.2 - fullZeroPrimeTerm p.1 p.2 +
        fullZeroArchimedeanTerm p.1 p.2)) :=
    ContinuousStar.continuous_star.measurable.comp measurable_fullZeroExplicitTerm_joint
  exact measurable_fullZeroExplicitTerm_joint.mul hstar

/-- The second moment of the three explicit-formula terms is measurable in the
Montgomery scale parameter. -/
theorem measurable_fullZeroTermsSecondMoment (T : ℝ) :
    Measurable (fun x : ℝ =>
      ∫ t in Set.Ioc 0 T,
        (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
            fullZeroArchimedeanTerm x t) *
          (starRingEnd ℂ)
            (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
              fullZeroArchimedeanTerm x t)) := by
  exact measurable_fullZeroExplicitTerm_mul_conj_joint.stronglyMeasurable
    |>.integral_prod_right'.measurable

/-- The pole term has an integrable squared norm on every finite height window. -/
theorem integrableOn_norm_fullZeroPoleTerm_sq_Ioc (x T : ℝ) :
    IntegrableOn (fun t : ℝ => ‖fullZeroPoleTerm x t‖ ^ 2) (Set.Ioc 0 T) := by
  exact ((continuous_fullZeroPoleTerm x).norm.pow 2).integrableOn_Icc.mono_set
    Set.Ioc_subset_Icc_self

/-- Absolute convergence of the prime model gives finite-window square integrability. -/
theorem integrableOn_norm_fullZeroPrimeTerm_sq_Ioc
    (x T : ℝ) (hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ => ‖fullZeroPrimeTerm x t‖ ^ 2) (Set.Ioc 0 T) := by
  let B : ℝ :=
    (∑' n, ‖primePositiveCoeff x n‖) + ∑' n, ‖primeNegativeCoeff x n‖
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    ((measurable_fullZeroPrimeTerm x hx).norm.pow_const 2).aestronglyMeasurable
    (B ^ 2) ?_
  filter_upwards [] with t
  have hbound : ‖fullZeroPrimeTerm x t‖ ≤ B := by
    rw [fullZeroPrimeTerm_eq_primeModelSeries x hx t]
    exact norm_primeModelSeries_le x hx t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnorm : 0 ≤ ‖fullZeroPrimeTerm x t‖ := norm_nonneg _
  nlinarith

/-- The uniform Archimedean remainder estimate gives finite-window square integrability. -/
theorem integrableOn_norm_fullZeroArchimedeanTerm_sq_Ioc
    (x T : ℝ) (hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ => ‖fullZeroArchimedeanTerm x t‖ ^ 2)
      (Set.Ioc 0 T) := by
  obtain ⟨C, hC, harch⟩ := montgomeryKernel_archimedeanTerm
  let main : ℝ → ℂ := fun t => (2 * Real.pi * Zeta23.mu t / x : ℂ)
  let major : ℝ → ℝ := fun t => 2 * C ^ 2 + 2 * ‖main t‖ ^ 2
  have hmain : Continuous main := by
    have hmu : Continuous (fun t : ℝ => (Zeta23.mu t : ℂ)) :=
      Complex.continuous_ofReal.comp archimedeanDensity_smooth.continuous
    simpa only [main, Pi.mul_apply, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_div] using
      (continuous_const.mul hmu).div_const (x : ℂ)
  have hmajor : IntegrableOn major (Set.Ioc 0 T) := by
    exact ((continuous_const.mul (hmain.norm.pow 2)).const_add _).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  apply hmajor.mono'
  · exact ((measurable_fullZeroArchimedeanTerm x).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [] with t
    have hrem : ‖fullZeroArchimedeanTerm x t - main t‖ ≤ C := by
      simpa only [fullZeroArchimedeanTerm, main] using harch x hx t
    have htri : ‖fullZeroArchimedeanTerm x t‖ ≤ C + ‖main t‖ := by
      calc
        ‖fullZeroArchimedeanTerm x t‖ =
            ‖(fullZeroArchimedeanTerm x t - main t) + main t‖ := by ring_nf
        _ ≤ ‖fullZeroArchimedeanTerm x t - main t‖ + ‖main t‖ := norm_add_le _ _
        _ ≤ C + ‖main t‖ := add_le_add hrem (le_refl _)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    dsimp only [major]
    have hz : 0 ≤ ‖fullZeroArchimedeanTerm x t‖ := norm_nonneg _
    have hm : 0 ≤ ‖main t‖ := norm_nonneg _
    nlinarith [sq_nonneg (C - ‖main t‖)]

/-- The complete pole/prime/Archimedean side of the explicit formula has an
integrable squared norm on every bounded Montgomery window. -/
theorem integrableOn_norm_fullZeroExplicitTerm_sq_Ioc
    (x T : ℝ) (hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ =>
      ‖fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
        fullZeroArchimedeanTerm x t‖ ^ 2) (Set.Ioc 0 T) := by
  have hp := integrableOn_norm_fullZeroPoleTerm_sq_Ioc x T
  have hq := integrableOn_norm_fullZeroPrimeTerm_sq_Ioc x T hx
  have ha := integrableOn_norm_fullZeroArchimedeanTerm_sq_Ioc x T hx
  have hmajor : IntegrableOn (fun t : ℝ => 3 *
      (‖fullZeroPoleTerm x t‖ ^ 2 + ‖fullZeroPrimeTerm x t‖ ^ 2 +
        ‖fullZeroArchimedeanTerm x t‖ ^ 2)) (Set.Ioc 0 T) := by
    exact ((hp.add hq).add ha).const_mul 3
  apply hmajor.mono'
  · exact ((measurable_fullZeroExplicitTerm x hx).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [] with t
    have htri :
        ‖fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
            fullZeroArchimedeanTerm x t‖ ≤
          ‖fullZeroPoleTerm x t‖ + ‖fullZeroPrimeTerm x t‖ +
            ‖fullZeroArchimedeanTerm x t‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using
        (norm_add₃_le (a := fullZeroPoleTerm x t)
          (b := -fullZeroPrimeTerm x t) (c := fullZeroArchimedeanTerm x t))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hz : 0 ≤ ‖fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
        fullZeroArchimedeanTerm x t‖ := norm_nonneg _
    have hp0 : 0 ≤ ‖fullZeroPoleTerm x t‖ := norm_nonneg _
    have hq0 : 0 ≤ ‖fullZeroPrimeTerm x t‖ := norm_nonneg _
    have ha0 : 0 ≤ ‖fullZeroArchimedeanTerm x t‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖fullZeroPoleTerm x t‖ - ‖fullZeroPrimeTerm x t‖),
      sq_nonneg (‖fullZeroPrimeTerm x t‖ - ‖fullZeroArchimedeanTerm x t‖),
      sq_nonneg (‖fullZeroArchimedeanTerm x t‖ - ‖fullZeroPoleTerm x t‖)]

/-- Complex conjugate-product form of square-integrability for the complete
explicit-formula side. -/
theorem integrableOn_fullZeroExplicitTerm_mul_conj_Ioc
    (x T : ℝ) (hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ =>
      (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
          fullZeroArchimedeanTerm x t) *
        (starRingEnd ℂ)
          (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
            fullZeroArchimedeanTerm x t)) (Set.Ioc 0 T) := by
  have h : IntegrableOn (fun t : ℝ =>
      ((‖fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
        fullZeroArchimedeanTerm x t‖ ^ 2 : ℝ) : ℂ)) (Set.Ioc 0 T) :=
    (integrableOn_norm_fullZeroExplicitTerm_sq_Ioc x T hx).ofReal
  refine h.congr ?_
  filter_upwards [] with t
  rw [RCLike.mul_conj]
  norm_cast

/-- The full Lorentzian zero series is exactly the literature side of the explicit formula. -/
theorem fullZeroLorentzianSum_eq_literatureRHS (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    fullZeroLorentzianSum x t =
      Zeta23.EF.literatureRHS (montgomeryKernel x t) := by
  rw [fullZeroLorentzianSum]
  simp_rw [fullZeroLorentzianSummand]
  rw [← montgomeryKernel_zero_tsum x hx t]
  exact (montgomeryKernel_explicitFormula x hx t).2

/-- Exact pole/prime/Archimedean decomposition of the full-zero model. -/
theorem fullZeroLorentzianSum_eq_terms (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    fullZeroLorentzianSum x t =
      fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
        fullZeroArchimedeanTerm x t := by
  rw [fullZeroLorentzianSum_eq_literatureRHS x hx t]
  simp only [Zeta23.EF.literatureRHS, Zeta23.EF.gamma_term,
    fullZeroPoleTerm, fullZeroPrimeTerm, fullZeroArchimedeanTerm]

/-- Exact decomposition after removing the common phase from the zero side. -/
theorem phaseCorrectedFullZeroSum_eq_terms (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    phaseCorrectedFullZeroSum x t =
      (x : ℂ) ^ (Complex.I * t) *
        (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
          fullZeroArchimedeanTerm x t) := by
  rw [phaseCorrectedFullZeroSum, fullZeroLorentzianSum_eq_terms x hx t]

/-- The explicit-formula decomposition preserves the squared norm of the full-zero model. -/
theorem phaseCorrectedFullZeroSum_mul_conj_eq_terms
    (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    phaseCorrectedFullZeroSum x t *
        (starRingEnd ℂ) (phaseCorrectedFullZeroSum x t) =
      (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
          fullZeroArchimedeanTerm x t) *
        (starRingEnd ℂ)
          (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
            fullZeroArchimedeanTerm x t) := by
  rw [RCLike.mul_conj, RCLike.mul_conj]
  rw [phaseCorrectedFullZeroSum_eq_terms x hx t, norm_mul,
    norm_cpow_I_mul x (zero_lt_one.trans_le hx) t, one_mul]

/-- The phase-corrected full-zero conjugate product is integrable on every
bounded Montgomery window. -/
theorem integrableOn_phaseCorrectedFullZeroSum_mul_conj_Ioc
    (x T : ℝ) (hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ =>
      phaseCorrectedFullZeroSum x t *
        (starRingEnd ℂ) (phaseCorrectedFullZeroSum x t)) (Set.Ioc 0 T) := by
  refine (integrableOn_fullZeroExplicitTerm_mul_conj_Ioc x T hx).congr ?_
  filter_upwards [] with t
  exact (phaseCorrectedFullZeroSum_mul_conj_eq_terms x hx t).symm

/-- The conjugate product defining the windowed full-zero second moment is
globally integrable. -/
theorem integrable_windowedFullZeroSum_mul_conj
    (x T : ℝ) (hx : 1 ≤ x) :
    Integrable (fun t : ℝ =>
      windowedFullZeroSum x T t *
        (starRingEnd ℂ) (windowedFullZeroSum x T t)) := by
  have hindicator :=
    (integrableOn_phaseCorrectedFullZeroSum_mul_conj_Ioc x T hx).integrable_indicator
      measurableSet_Ioc
  rw [windowedFullZeroSum]
  refine hindicator.congr ?_
  filter_upwards [] with t
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) T
  · simp only [Set.indicator_of_mem ht]
  · simp only [Set.indicator_of_notMem ht, map_zero, mul_zero]

/-- The windowed full-zero second moment is exactly the second moment of the three
explicit-formula terms on `(0, T]`. -/
theorem windowedFullZeroSecondMoment_eq_setIntegral_terms
    (x T : ℝ) (hx : 1 ≤ x) :
    windowedFullZeroSecondMoment x T =
      ∫ t in Set.Ioc 0 T,
        (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
            fullZeroArchimedeanTerm x t) *
          (starRingEnd ℂ)
            (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
              fullZeroArchimedeanTerm x t) := by
  rw [windowedFullZeroSecondMoment, windowedFullZeroSum]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) T
  · simp only [Set.indicator_of_mem ht]
    exact phaseCorrectedFullZeroSum_mul_conj_eq_terms x hx t
  · simp [Set.indicator_of_notMem ht]

/-- Interval-integral form of the exact three-term decomposition. -/
theorem windowedFullZeroSecondMoment_eq_intervalIntegral_terms
    (x T : ℝ) (hx : 1 ≤ x) (hT : 0 ≤ T) :
    windowedFullZeroSecondMoment x T =
      ∫ t : ℝ in 0..T,
        (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
            fullZeroArchimedeanTerm x t) *
          (starRingEnd ℂ)
            (fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
              fullZeroArchimedeanTerm x t) := by
  rw [intervalIntegral.integral_of_le hT]
  exact windowedFullZeroSecondMoment_eq_setIntegral_terms x T hx

/-- On the closed exponent range used by Montgomery's argument, the windowed
full-zero second moment is almost-everywhere strongly measurable. -/
theorem aestronglyMeasurable_windowedFullZeroSecondMoment_rpow
    (T : ℝ) (hT : 2 ≤ T) :
    AEStronglyMeasurable
      (fun a : ℝ => windowedFullZeroSecondMoment (T ^ a) T)
      (volume.restrict (Set.Icc 0 1)) := by
  have hmodel : Measurable (fun a : ℝ =>
      ∫ t in Set.Ioc 0 T,
        (fullZeroPoleTerm (T ^ a) t - fullZeroPrimeTerm (T ^ a) t +
            fullZeroArchimedeanTerm (T ^ a) t) *
          (starRingEnd ℂ)
            (fullZeroPoleTerm (T ^ a) t - fullZeroPrimeTerm (T ^ a) t +
              fullZeroArchimedeanTerm (T ^ a) t)) :=
    (measurable_fullZeroTermsSecondMoment T).comp
      (measurable_id.const_pow T)
  refine hmodel.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
  have hx : 1 ≤ T ^ a :=
    Real.one_le_rpow (by linarith [hT]) ha.1
  exact (windowedFullZeroSecondMoment_eq_setIntegral_terms
    (T ^ a) T hx).symm

open Complex MeasureTheory Filter
open scoped BigOperators ComplexConjugate Interval Topology

noncomputable def twoSidedDirichletFrequency {N : ℕ} :
    Sum (Fin N) (Fin N) → ℝ
  | Sum.inl n => dirichletFrequency (n.1 + 1)
  | Sum.inr n => -dirichletFrequency (n.1 + 1)

noncomputable def twoSidedDirichletGap {N : ℕ} :
    Sum (Fin N) (Fin N) → ℝ
  | Sum.inl n => dirichletGap (n.1 + 1)
  | Sum.inr n => dirichletGap (n.1 + 1)

theorem shifted_dirichletFrequency_pos (n : ℕ) :
    0 < dirichletFrequency (n + 1) := by
  unfold dirichletFrequency
  exact Real.log_pos (by exact_mod_cast (show 1 < n + 1 + 1 by omega))

theorem dirichletGap_le_shifted_frequency (n : ℕ) :
    dirichletGap (n + 1) ≤ dirichletFrequency (n + 1) := by
  have h := dirichletGap_le_abs_frequency_sub (n + 1) 0 (by omega)
  have hzero : dirichletFrequency 0 = 0 := by simp [dirichletFrequency]
  rw [hzero, sub_zero,
    abs_of_nonneg (le_of_lt (shifted_dirichletFrequency_pos n))] at h
  exact h

theorem twoSidedDirichletFrequency_injective {N : ℕ} :
    Function.Injective (twoSidedDirichletFrequency (N := N)) := by
  intro r s h
  cases r with
  | inl r =>
      cases s with
      | inl s =>
          simp only [twoSidedDirichletFrequency] at h
          have hrs : r.1 + 1 = s.1 + 1 := dirichletFrequency_injective h
          have : r = s := Fin.ext (by omega)
          exact congrArg Sum.inl this
      | inr s =>
          simp only [twoSidedDirichletFrequency] at h
          have hr := shifted_dirichletFrequency_pos r.1
          have hs := shifted_dirichletFrequency_pos s.1
          exfalso
          linarith
  | inr r =>
      cases s with
      | inl s =>
          simp only [twoSidedDirichletFrequency] at h
          have hr := shifted_dirichletFrequency_pos r.1
          have hs := shifted_dirichletFrequency_pos s.1
          exfalso
          linarith
      | inr s =>
          simp only [twoSidedDirichletFrequency, neg_inj] at h
          have hrs : r.1 + 1 = s.1 + 1 := dirichletFrequency_injective h
          have : r = s := Fin.ext (by omega)
          exact congrArg Sum.inr this

theorem twoSidedDirichletGap_pos {N : ℕ} (r : Sum (Fin N) (Fin N)) :
    0 < twoSidedDirichletGap r := by
  cases r <;> simp only [twoSidedDirichletGap, dirichletGap] <;> positivity

theorem twoSidedDirichletGap_le_abs_frequency_sub {N : ℕ}
    (r s : Sum (Fin N) (Fin N)) (hrs : r ≠ s) :
    twoSidedDirichletGap r ≤
      |twoSidedDirichletFrequency r - twoSidedDirichletFrequency s| := by
  cases r with
  | inl r =>
      cases s with
      | inl s =>
          have hvals : r.1 + 1 ≠ s.1 + 1 := by
            intro h
            apply hrs
            congr 1
            apply Fin.ext
            omega
          simpa only [twoSidedDirichletGap, twoSidedDirichletFrequency] using
            dirichletGap_le_abs_frequency_sub (r.1 + 1) (s.1 + 1) hvals
      | inr s =>
          simp only [twoSidedDirichletGap, twoSidedDirichletFrequency, sub_neg_eq_add]
          rw [abs_of_pos (add_pos (shifted_dirichletFrequency_pos r.1)
            (shifted_dirichletFrequency_pos s.1))]
          exact (dirichletGap_le_shifted_frequency r.1).trans
            (le_add_of_nonneg_right (le_of_lt (shifted_dirichletFrequency_pos s.1)))
  | inr r =>
      cases s with
      | inl s =>
          simp only [twoSidedDirichletGap, twoSidedDirichletFrequency]
          rw [show -dirichletFrequency (r.1 + 1) - dirichletFrequency (s.1 + 1) =
            -(dirichletFrequency (r.1 + 1) + dirichletFrequency (s.1 + 1)) by ring,
            abs_neg,
            abs_of_pos (add_pos (shifted_dirichletFrequency_pos r.1)
              (shifted_dirichletFrequency_pos s.1))]
          exact (dirichletGap_le_shifted_frequency r.1).trans
            (le_add_of_nonneg_right (le_of_lt (shifted_dirichletFrequency_pos s.1)))
      | inr s =>
          have hvals : r.1 + 1 ≠ s.1 + 1 := by
            intro h
            apply hrs
            congr 1
            apply Fin.ext
            omega
          simp only [twoSidedDirichletGap, twoSidedDirichletFrequency, neg_sub_neg]
          rw [abs_sub_comm]
          exact dirichletGap_le_abs_frequency_sub (r.1 + 1) (s.1 + 1) hvals

noncomputable def finiteTwoSidedDirichletPolynomial {N : ℕ}
    (a b : ℕ → ℂ) (t : ℝ) : ℂ :=
  finiteExponentialPolynomial (twoSidedDirichletFrequency (N := N))
    (Sum.elim (fun n : Fin N => a (n.1 + 1))
      (fun n : Fin N => b (n.1 + 1))) t

theorem mvN2_twoSidedDirichletGap {N : ℕ} (a b : ℕ → ℂ) :
    Zeta23.MV.N2 (twoSidedDirichletGap (N := N))
        (Sum.elim (fun n : Fin N => a (n.1 + 1))
          (fun n : Fin N => b (n.1 + 1))) =
      2 * ((∑ n : Fin N, (n.1 + 2 : ℝ) * ‖a (n.1 + 1)‖ ^ 2) +
        ∑ n : Fin N, (n.1 + 2 : ℝ) * ‖b (n.1 + 1)‖ ^ 2) := by
  unfold Zeta23.MV.N2
  rw [Fintype.sum_sum_type]
  simp only [twoSidedDirichletGap, Sum.elim_inl, Sum.elim_inr,
    dirichletGap]
  rw [show (∑ x : Fin N, ‖a (x.1 + 1)‖ ^ 2 /
      (1 / (2 * ((x.1 + 1 : ℕ) + 1)))) =
      2 * ∑ x : Fin N, (x.1 + 2 : ℝ) * ‖a (x.1 + 1)‖ ^ 2 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        push_cast
        field_simp
        ring,
    show (∑ x : Fin N, ‖b (x.1 + 1)‖ ^ 2 /
      (1 / (2 * ((x.1 + 1 : ℕ) + 1)))) =
      2 * ∑ x : Fin N, (x.1 + 2 : ℝ) * ‖b (x.1 + 1)‖ ^ 2 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        push_cast
        field_simp
        ring]
  ring

/-- A mean-value estimate for finite positive and negative logarithmic frequencies, with
the common zero frequency omitted. -/
theorem finiteTwoSidedDirichletPolynomial_meanValue_bound_real
    {C : ℝ} (hMV : Zeta23.MVHilbert C) {N : ℕ}
    (a b : ℕ → ℂ) (T : ℝ) :
    |(∫ t : ℝ in 0..T, ‖finiteTwoSidedDirichletPolynomial (N := N) a b t‖ ^ 2) -
        T * ((∑ n : Fin N, ‖a (n.1 + 1)‖ ^ 2) +
          ∑ n : Fin N, ‖b (n.1 + 1)‖ ^ 2)| ≤
      4 * C * ((∑ n : Fin N, (n.1 + 2 : ℝ) * ‖a (n.1 + 1)‖ ^ 2) +
        ∑ n : Fin N, (n.1 + 2 : ℝ) * ‖b (n.1 + 1)‖ ^ 2) := by
  let coeff : Sum (Fin N) (Fin N) → ℂ :=
    Sum.elim (fun n : Fin N => a (n.1 + 1))
      (fun n : Fin N => b (n.1 + 1))
  have h := finiteExponentialPolynomial_meanValue_bound hMV
    (twoSidedDirichletFrequency (N := N))
    (twoSidedDirichletGap (N := N)) coeff T
    twoSidedDirichletFrequency_injective
    twoSidedDirichletGap_pos
    twoSidedDirichletGap_le_abs_frequency_sub
  have heq :
      (∫ t : ℝ in 0..T,
          finiteTwoSidedDirichletPolynomial (N := N) a b t *
            conj (finiteTwoSidedDirichletPolynomial (N := N) a b t)) -
          (T : ℂ) * ∑ r : Sum (Fin N) (Fin N), coeff r * conj (coeff r) =
        (((∫ t : ℝ in 0..T,
            ‖finiteTwoSidedDirichletPolynomial (N := N) a b t‖ ^ 2) -
          T * ((∑ n : Fin N, ‖a (n.1 + 1)‖ ^ 2) +
            ∑ n : Fin N, ‖b (n.1 + 1)‖ ^ 2) : ℝ) : ℂ) := by
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [intervalIntegral.integral_ofReal, Fintype.sum_sum_type]
    simp only [coeff, Sum.elim_inl, Sum.elim_inr]
    push_cast
    rfl
  change ‖(∫ t : ℝ in 0..T,
      finiteTwoSidedDirichletPolynomial (N := N) a b t *
        conj (finiteTwoSidedDirichletPolynomial (N := N) a b t)) -
      (T : ℂ) * ∑ r : Sum (Fin N) (Fin N), coeff r * conj (coeff r)‖ ≤
    2 * C * Zeta23.MV.N2 (twoSidedDirichletGap (N := N)) coeff at h
  rw [heq, Complex.norm_real, Real.norm_eq_abs] at h
  rw [show Zeta23.MV.N2 (twoSidedDirichletGap (N := N)) coeff =
      2 * ((∑ n : Fin N, (n.1 + 2 : ℝ) * ‖a (n.1 + 1)‖ ^ 2) +
        ∑ n : Fin N, (n.1 + 2 : ℝ) * ‖b (n.1 + 1)‖ ^ 2) by
      exact mvN2_twoSidedDirichletGap a b] at h
  convert h using 1; ring

/-- Omitting the zero coefficient identifies the two-sided polynomial with matching
ordinary Dirichlet partial sums. -/
theorem finiteTwoSidedDirichletPolynomial_eq_partial
    {N : ℕ} (a b : ℕ → ℂ) (ha0 : a 0 = 0) (hb0 : b 0 = 0) (t : ℝ) :
    finiteTwoSidedDirichletPolynomial (N := N) a b t =
      partialDirichletSeries a (N + 1) t +
        partialDirichletSeries b (N + 1) (-t) := by
  unfold finiteTwoSidedDirichletPolynomial finiteExponentialPolynomial
  rw [Fintype.sum_sum_type]
  unfold partialDirichletSeries
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [twoSidedDirichletFrequency, Sum.elim_inl, Sum.elim_inr,
    ha0, hb0, zero_mul, add_zero]
  apply congrArg₂ (· + ·)
  · simpa only using (Fin.sum_univ_eq_sum_range
      (fun k : ℕ => a (k + 1) *
        Complex.exp (-(Complex.I) *
          ((dirichletFrequency (k + 1) * t : ℝ) : ℂ))) N)
  · rw [show (∑ n : Fin N, b (n.1 + 1) *
        Complex.exp (-(Complex.I) *
          ((-dirichletFrequency (n.1 + 1) * t : ℝ) : ℂ))) =
      ∑ k ∈ Finset.range N, b (k + 1) *
        Complex.exp (-(Complex.I) *
          ((-dirichletFrequency (k + 1) * t : ℝ) : ℂ)) by
        simpa only using (Fin.sum_univ_eq_sum_range
          (fun k : ℕ => b (k + 1) *
            Complex.exp (-(Complex.I) *
              ((-dirichletFrequency (k + 1) * t : ℝ) : ℂ))) N)]
    apply Finset.sum_congr rfl
    intro n hn
    congr 2
    congr 1
    push_cast
    ring

/-- A finite two-sided logarithmic-frequency polynomial is continuous in height. -/
theorem continuous_finiteTwoSidedDirichletPolynomial
    {N : ℕ} (a b : ℕ → ℂ) :
    Continuous (finiteTwoSidedDirichletPolynomial (N := N) a b) := by
  unfold finiteTwoSidedDirichletPolynomial finiteExponentialPolynomial
  fun_prop

/-- Dominated convergence for the two-sided logarithmic-frequency polynomials, after
omitting their common zero frequency. -/
theorem integral_finiteTwoSidedDirichletPolynomial_tendsto
    (a b : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖))
    (hb : Summable (fun n => ‖b n‖))
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (T : ℝ) :
    Tendsto
      (fun N => ∫ t : ℝ in 0..T,
        ‖finiteTwoSidedDirichletPolynomial (N := N) a b t‖ ^ 2)
      atTop
      (nhds (∫ t : ℝ in 0..T,
        ‖dirichletSeries a t + dirichletSeries b (-t)‖ ^ 2)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => ((∑' n, ‖a n‖) + ∑' n, ‖b n‖) ^ 2)
  · filter_upwards [] with N
    exact ((continuous_finiteTwoSidedDirichletPolynomial a b).norm.pow 2).aestronglyMeasurable
  · filter_upwards [] with N
    filter_upwards [] with t
    intro _ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      finiteTwoSidedDirichletPolynomial_eq_partial a b ha0 hb0 t]
    have hna := norm_partialDirichletSeries_le_tsum a ha (N + 1) t
    have hnb := norm_partialDirichletSeries_le_tsum b hb (N + 1) (-t)
    have hadd := norm_add_le (partialDirichletSeries a (N + 1) t)
      (partialDirichletSeries b (N + 1) (-t))
    have hsa : 0 ≤ ∑' n, ‖a n‖ := tsum_nonneg fun n => norm_nonneg _
    have hsb : 0 ≤ ∑' n, ‖b n‖ := tsum_nonneg fun n => norm_nonneg _
    nlinarith [norm_nonneg
      (partialDirichletSeries a (N + 1) t +
        partialDirichletSeries b (N + 1) (-t))]
  · exact continuous_const.intervalIntegrable 0 T
  · filter_upwards [] with t
    intro _ht
    simpa only [finiteTwoSidedDirichletPolynomial_eq_partial a b ha0 hb0 t,
      Function.comp_apply] using
      ((((partialDirichletSeries_tendsto a ha t).comp
        (Filter.tendsto_add_atTop_nat 1)).add
      ((partialDirichletSeries_tendsto b hb (-t)).comp
        (Filter.tendsto_add_atTop_nat 1))).norm.pow 2)

/-- The Montgomery--Vaughan estimate for finite positive and negative logarithmic
frequencies passes to absolutely convergent two-sided Dirichlet series. -/
theorem twoSidedDirichletSeries_meanValue_bound_real
    {C : ℝ} (hMV : Zeta23.MVHilbert C)
    (a b : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖))
    (hb : Summable (fun n => ‖b n‖))
    (haw : Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖a n‖ ^ 2))
    (hbw : Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖b n‖ ^ 2))
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (T : ℝ) :
    |(∫ t in 0..T, ‖dirichletSeries a t + dirichletSeries b (-t)‖ ^ 2) -
        T * ((∑' n, ‖a n‖ ^ 2) + ∑' n, ‖b n‖ ^ 2)| ≤
      4 * C * ((∑' n : ℕ, ((n : ℝ) + 1) * ‖a n‖ ^ 2) +
        ∑' n : ℕ, ((n : ℝ) + 1) * ‖b n‖ ^ 2) := by
  have hsa : Summable fun n => ‖a n‖ ^ 2 := by
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg ‖a n‖) _ haw
    intro n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 :=
      le_add_of_nonneg_left (Nat.cast_nonneg n)
    nlinarith [sq_nonneg ‖a n‖]
  have hsb : Summable fun n => ‖b n‖ ^ 2 := by
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg ‖b n‖) _ hbw
    intro n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 :=
      le_add_of_nonneg_left (Nat.cast_nonneg n)
    nlinarith [sq_nonneg ‖b n‖]
  have hN : ∀ N : ℕ,
      |(∫ t in 0..T, ‖finiteTwoSidedDirichletPolynomial (N := N) a b t‖ ^ 2) -
          T * ((∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2) +
            ∑ n ∈ Finset.range (N + 1), ‖b n‖ ^ 2)| ≤
        4 * C * ((∑ n ∈ Finset.range (N + 1),
            ((n : ℝ) + 1) * ‖a n‖ ^ 2) +
          ∑ n ∈ Finset.range (N + 1),
            ((n : ℝ) + 1) * ‖b n‖ ^ 2) := by
    intro N
    have h := finiteTwoSidedDirichletPolynomial_meanValue_bound_real
      (N := N) hMV a b T
    have hsaN : (∑ n : Fin N, ‖a (n.1 + 1)‖ ^ 2) =
        ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
      calc
        _ = ∑ n ∈ Finset.range N, ‖a (n + 1)‖ ^ 2 := by
          simpa only using (Fin.sum_univ_eq_sum_range
            (fun n : ℕ => ‖a (n + 1)‖ ^ 2) N)
        _ = _ := by rw [Finset.sum_range_succ']; simp [ha0]
    have hsbN : (∑ n : Fin N, ‖b (n.1 + 1)‖ ^ 2) =
        ∑ n ∈ Finset.range (N + 1), ‖b n‖ ^ 2 := by
      calc
        _ = ∑ n ∈ Finset.range N, ‖b (n + 1)‖ ^ 2 := by
          simpa only using (Fin.sum_univ_eq_sum_range
            (fun n : ℕ => ‖b (n + 1)‖ ^ 2) N)
        _ = _ := by rw [Finset.sum_range_succ']; simp [hb0]
    have hwaN : (∑ n : Fin N,
        (n.1 + 2 : ℝ) * ‖a (n.1 + 1)‖ ^ 2) =
        ∑ n ∈ Finset.range (N + 1),
          ((n : ℝ) + 1) * ‖a n‖ ^ 2 := by
      calc
        _ = ∑ n ∈ Finset.range N,
            (n + 2 : ℝ) * ‖a (n + 1)‖ ^ 2 := by
          simpa only using (Fin.sum_univ_eq_sum_range
            (fun n : ℕ => (n + 2 : ℝ) * ‖a (n + 1)‖ ^ 2) N)
        _ = _ := by
          rw [Finset.sum_range_succ']
          simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, zero_add, one_mul]
          rw [ha0, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]
          apply Finset.sum_congr rfl
          intro n hn
          ring
    have hwbN : (∑ n : Fin N,
        (n.1 + 2 : ℝ) * ‖b (n.1 + 1)‖ ^ 2) =
        ∑ n ∈ Finset.range (N + 1),
          ((n : ℝ) + 1) * ‖b n‖ ^ 2 := by
      calc
        _ = ∑ n ∈ Finset.range N,
            (n + 2 : ℝ) * ‖b (n + 1)‖ ^ 2 := by
          simpa only using (Fin.sum_univ_eq_sum_range
            (fun n : ℕ => (n + 2 : ℝ) * ‖b (n + 1)‖ ^ 2) N)
        _ = _ := by
          rw [Finset.sum_range_succ']
          simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, zero_add, one_mul]
          rw [hb0, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]
          apply Finset.sum_congr rfl
          intro n hn
          ring
    rwa [hsaN, hsbN, hwaN, hwbN] at h
  apply le_of_tendsto_of_tendsto'
    ((integral_finiteTwoSidedDirichletPolynomial_tendsto
      a b ha hb ha0 hb0 T).sub
      (tendsto_const_nhds.mul
        (((hsa.tendsto_sum_tsum_nat.comp (Filter.tendsto_add_atTop_nat 1)).add
          (hsb.tendsto_sum_tsum_nat.comp (Filter.tendsto_add_atTop_nat 1))))) |>.abs)
    (tendsto_const_nhds.mul
      (((haw.tendsto_sum_tsum_nat.comp (Filter.tendsto_add_atTop_nat 1)).add
        (hbw.tendsto_sum_tsum_nat.comp (Filter.tendsto_add_atTop_nat 1)))))
  exact hN

/-- The positive prime-model coefficient at the common zero frequency vanishes. -/
theorem primePositiveCoeff_zero (x : ℝ) :
    primePositiveCoeff x 0 = 0 := by
  simp [primePositiveCoeff]

/-- The negative prime-model coefficient at the common zero frequency vanishes. -/
theorem primeNegativeCoeff_zero (x : ℝ) :
    primeNegativeCoeff x 0 = 0 := by
  simp [primeNegativeCoeff]

/-- The complete positive-plus-negative prime model has its Montgomery--Vaughan
mean-square error bounded by the weighted prime mean square. -/
theorem exists_primeModelSeries_meanValue_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 1 ≤ x → ∀ T : ℝ,
      |(∫ t in 0..T, ‖primeModelSeries x t‖ ^ 2) -
          T * ((∑' k, ‖primePositiveCoeff x k‖ ^ 2) +
            ∑' k, ‖primeNegativeCoeff x k‖ ^ 2)| ≤
        M * x * (1 + Real.log x) := by
  obtain ⟨C, hC, hMV⟩ := Zeta23.MV.mv_hilbert
  obtain ⟨K, hK, hprime⟩ := pairWeightedPrimeMeanSquare_bound
  refine ⟨8 * C * K, by positivity, ?_⟩
  intro x hx T
  obtain ⟨hweighted, hweightedBound⟩ := hprime x hx
  have h := twoSidedDirichletSeries_meanValue_bound_real hMV
    (primePositiveCoeff x) (primeNegativeCoeff x)
    (primePositiveCoeff_summable x hx)
    (primeNegativeCoeff_summable x hx)
    (primePositiveCoeff_weighted_summable x hx)
    (primeNegativeCoeff_weighted_summable x hx)
    (primePositiveCoeff_zero x) (primeNegativeCoeff_zero x) T
  have hsum :
      ((∑' k : ℕ, ((k : ℝ) + 1) * ‖primePositiveCoeff x k‖ ^ 2) +
        ∑' k : ℕ, ((k : ℝ) + 1) * ‖primeNegativeCoeff x k‖ ^ 2) ≤
      2 * pairWeightedPrimeMeanSquare x := by
    rw [primePositiveCoeff_weighted_tsum_eq x hx]
    linarith [primeNegativeCoeff_weighted_tsum_le x hx]
  calc
    |(∫ t in 0..T, ‖primeModelSeries x t‖ ^ 2) -
        T * ((∑' k, ‖primePositiveCoeff x k‖ ^ 2) +
          ∑' k, ‖primeNegativeCoeff x k‖ ^ 2)| ≤
      4 * C *
        ((∑' k : ℕ, ((k : ℝ) + 1) * ‖primePositiveCoeff x k‖ ^ 2) +
          ∑' k : ℕ, ((k : ℝ) + 1) * ‖primeNegativeCoeff x k‖ ^ 2) := by
            simpa only [primeModelSeries] using h
    _ ≤ 4 * C * (2 * pairWeightedPrimeMeanSquare x) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 4 * C * (2 * (K * x * (1 + Real.log x))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hweightedBound (by norm_num))
        (by positivity)
    _ = (8 * C * K) * x * (1 + Real.log x) := by ring

/-- The prime term occurring in the full-zero explicit formula inherits the
two-sided Montgomery--Vaughan mean-square estimate. -/
theorem exists_fullZeroPrimeTerm_meanValue_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 1 ≤ x → ∀ T : ℝ,
      |(∫ t in 0..T, ‖fullZeroPrimeTerm x t‖ ^ 2) -
          T * ((∑' k, ‖primePositiveCoeff x k‖ ^ 2) +
            ∑' k, ‖primeNegativeCoeff x k‖ ^ 2)| ≤
        M * x * (1 + Real.log x) := by
  obtain ⟨M, hM, hmean⟩ := exists_primeModelSeries_meanValue_bound
  refine ⟨M, hM, ?_⟩
  intro x hx T
  simpa only [fullZeroPrimeTerm_eq_primeModelSeries x hx] using hmean x hx T

end ZetaZeros.Unconditional.PairCorrelationProof
