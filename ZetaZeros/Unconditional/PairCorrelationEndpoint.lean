/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationEstimate
import Mathlib.Analysis.SumIntegralExpDecay

/-!
# The endpoint contribution in Montgomery's pair-correlation argument

The main term in the uniform finite-pair-function estimate contains the approximate identity
`2 log T * exp (-2 a log T)`.  This file records a quantitative endpoint lemma which extracts
the value of a Lipschitz test function at zero.  It is the endpoint step in
`blueprint/unconditional.tex`, Section `sec_pair_correlation`.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open MeasureTheory

/-- The elementary integral of the exponential kernel on `[0, 1]`. -/
theorem integral_exp_neg_two_mul (L : ℝ) (hL : 0 < L) :
    (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a))) =
      (1 - Real.exp (-(2 * L))) / (2 * L) := by
  have hc : (-2 * (L : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hL))
  have h := integral_exp_mul_complex (a := (0 : ℝ)) (b := (1 : ℝ)) hc
  rw [show (fun x : ℝ => Complex.exp ((-2 * (L : ℂ)) * x)) =
      fun x : ℝ => (Real.exp (-(2 * L * x)) : ℂ) by
        funext x
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring,
    intervalIntegral.integral_ofReal] at h
  have hcast :
      (((∫ a : ℝ in 0..1, Real.exp (-(2 * L * a))) : ℝ) : ℂ) =
        (((1 - Real.exp (-(2 * L))) / (2 * L) : ℝ) : ℂ) := by
    calc
      (((∫ a : ℝ in 0..1, Real.exp (-(2 * L * a))) : ℝ) : ℂ) =
          (Complex.exp (-2 * (L : ℂ) * (1 : ℂ)) -
            Complex.exp (-2 * (L : ℂ) * (0 : ℂ))) / (-2 * (L : ℂ)) := h
      _ = (((1 - Real.exp (-(2 * L))) / (2 * L) : ℝ) : ℂ) := by
        norm_num
        field_simp
        ring
  exact Complex.ofReal_injective hcast

/-- The tail of the exponential kernel is at most `1 / L` once `L ≥ 1`. -/
theorem exp_neg_two_mul_le_inv (L : ℝ) (hL : 1 ≤ L) :
    Real.exp (-(2 * L)) ≤ 1 / L := by
  rw [Real.exp_neg]
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hexp : L ≤ Real.exp (2 * L) := by
    have h := Real.add_one_le_exp (2 * L)
    linarith
  simpa [one_div] using one_div_le_one_div_of_le hLpos hexp

/-- A quantitative approximate-identity estimate for the endpoint `a = 0`. -/
theorem approximate_identity_bound (f : ℝ → ℝ) (hf : Integrable f)
    (C : ℝ) (hC : ∀ x, |f x - f 0| ≤ C * |x|)
    (L : ℝ) (hL : 1 ≤ L) :
    |2 * L * (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * f a) - f 0| ≤
      (C / 2 + |f 0|) / L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hCnonneg : 0 ≤ C := by
    have h := hC 1
    norm_num only [abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hkernel : Continuous fun a : ℝ => Real.exp (-(2 * L * a)) := by fun_prop
  have hfi : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable
  have hfdiff : IntervalIntegrable (fun a => f a - f 0) volume 0 1 :=
    hfi.sub intervalIntegrable_const
  have hweightedDiff : IntervalIntegrable
      (fun a => Real.exp (-(2 * L * a)) * (f a - f 0)) volume 0 1 := by
    simpa [mul_comm] using hfdiff.mul_continuousOn hkernel.continuousOn
  have hnorm :
      |∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * (f a - f 0)| ≤
        C / (2 * L) ^ 2 := by
    calc
      |∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * (f a - f 0)| ≤
          ∫ a : ℝ in 0..1, C * a * Real.exp (-(2 * L * a)) := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_of_norm_le (E := ℝ) (by norm_num)
            (by
              filter_upwards [] with a ha
              simp only [Set.mem_Ioc] at ha
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
              calc
                Real.exp (-(2 * L * a)) * |f a - f 0| ≤
                    Real.exp (-(2 * L * a)) * (C * a) := by
                  gcongr
                  simpa [abs_of_nonneg (by linarith : 0 ≤ a)] using hC a
                _ = C * a * Real.exp (-(2 * L * a)) := by ring)
            ((by fun_prop : Continuous
              (fun a : ℝ => C * a * Real.exp (-(2 * L * a)))).intervalIntegrable 0 1))
      _ = C * (∫ a : ℝ in 0..1, a * Real.exp (-(2 * L * a))) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext a
        ring
      _ ≤ C * (1 / (2 * L) ^ 2) := by
        gcongr
        simpa [pow_two] using
          (intervalIntegral_pow_mul_exp_neg_le (k := 1) (M := (1 : ℝ))
            (by norm_num) (by positivity : 0 < 2 * L))
      _ = C / (2 * L) ^ 2 := by ring
  have hdecomp :
      2 * L * (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * f a) - f 0 =
        2 * L * (∫ a : ℝ in 0..1,
          Real.exp (-(2 * L * a)) * (f a - f 0)) -
          f 0 * Real.exp (-(2 * L)) := by
    have hconst : IntervalIntegrable
        (fun a : ℝ => f 0 * Real.exp (-(2 * L * a))) volume 0 1 :=
      (continuous_const.mul hkernel).intervalIntegrable 0 1
    have hsplit :
        (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * f a) =
          (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * (f a - f 0)) +
            f 0 * (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a))) := by
      rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_add hweightedDiff hconst]
      apply intervalIntegral.integral_congr
      intro a _
      ring
    rw [hsplit, integral_exp_neg_two_mul L hLpos]
    field_simp
    ring
  rw [hdecomp]
  calc
    |2 * L * (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * (f a - f 0)) -
        f 0 * Real.exp (-(2 * L))| ≤
        2 * L * |∫ a : ℝ in 0..1,
          Real.exp (-(2 * L * a)) * (f a - f 0)| +
          |f 0| * Real.exp (-(2 * L)) := by
      calc
        |2 * L * (∫ a : ℝ in 0..1,
            Real.exp (-(2 * L * a)) * (f a - f 0)) -
            f 0 * Real.exp (-(2 * L))| ≤
            |2 * L * (∫ a : ℝ in 0..1,
              Real.exp (-(2 * L * a)) * (f a - f 0))| +
              |f 0 * Real.exp (-(2 * L))| := abs_sub _ _
        _ = 2 * L * |∫ a : ℝ in 0..1,
              Real.exp (-(2 * L * a)) * (f a - f 0)| +
              |f 0| * Real.exp (-(2 * L)) := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * L),
            abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ 2 * L * (C / (2 * L) ^ 2) + |f 0| * (1 / L) := by
      gcongr
      exact exp_neg_two_mul_le_inv L hL
    _ = (C / 2 + |f 0|) / L := by
      field_simp

end ZetaZeros.Unconditional.PairCorrelationProof
