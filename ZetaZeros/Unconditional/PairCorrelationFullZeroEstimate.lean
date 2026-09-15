/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationIntegratedAssembly
import ZetaZeros.Unconditional.PairCorrelationArchimedeanCumulative
import ZetaZeros.Unconditional.PairCorrelationFullZeroMoment

/-!
# The integrated full-zero second moment

This file evaluates Montgomery's full-zero second moment after integration in the
logarithmic scale parameter.  In particular, the Montgomery--Vaughan endpoint loss is
integrated rather than replaced by a false pointwise-uniform estimate.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set Filter
open scoped BigOperators Interval Topology ComplexConjugate

/-- Removing the harmless index weight preserves square summability. -/
theorem primePositiveCoeff_sq_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun k : ℕ => ‖primePositiveCoeff x k‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _
    (primePositiveCoeff_weighted_summable x hx)
  intro k
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    exact_mod_cast (show 1 ≤ k + 1 by omega)
  nlinarith [sq_nonneg ‖primePositiveCoeff x k‖]

/-- Removing the harmless index weight preserves square summability. -/
theorem primeNegativeCoeff_sq_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun k : ℕ => ‖primeNegativeCoeff x k‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _
    (primeNegativeCoeff_weighted_summable x hx)
  intro k
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    exact_mod_cast (show 1 ≤ k + 1 by omega)
  nlinarith [sq_nonneg ‖primeNegativeCoeff x k‖]

/-- The unweighted positive-frequency diagonal is the smoothed prime mean square. -/
theorem primePositiveCoeff_sq_tsum_eq (x : ℝ) (hx : 1 ≤ x) :
    (∑' k : ℕ, ‖primePositiveCoeff x k‖ ^ 2) = pairPrimeMeanSquare x := by
  let q : ℕ → ℝ := fun n =>
    pairDirichletCoefficient n * pairPrimeKernel x n
  have hterm : ∀ k : ℕ,
      ‖primePositiveCoeff x k‖ ^ 2 = q (k + 1) := by
    intro k
    have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
    have h := primePositiveCoeff_weighted_sq x hx k
    dsimp only [q, pairDirichletCoefficient]
    calc
      ‖primePositiveCoeff x k‖ ^ 2 =
          (((k + 1 : ℕ) : ℝ) * ‖primePositiveCoeff x k‖ ^ 2) /
            ((k + 1 : ℕ) : ℝ) := by field_simp
      _ = (ArithmeticFunction.vonMangoldt (k + 1) ^ 2 *
            pairPrimeKernel x (k + 1)) / ((k + 1 : ℕ) : ℝ) := by rw [h]
      _ = ArithmeticFunction.vonMangoldt (k + 1) ^ 2 /
            ((k + 1 : ℕ) : ℝ) * pairPrimeKernel x (k + 1) := by ring
  have hshiftSummable : Summable (fun k : ℕ => q (k + 1)) :=
    (primePositiveCoeff_sq_summable x hx).congr hterm
  have hq : Summable q := (summable_nat_add_iff 1).mp hshiftSummable
  have hshift : (∑' k : ℕ, q (k + 1)) = ∑' n : ℕ, q n := by
    simpa only [Finset.sum_range_one, q, pairDirichletCoefficient,
      ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Nat.cast_zero, div_zero, zero_mul, zero_add] using
      hq.sum_add_tsum_nat_add 1
  calc
    (∑' k : ℕ, ‖primePositiveCoeff x k‖ ^ 2) =
        ∑' k : ℕ, q (k + 1) := tsum_congr hterm
    _ = ∑' n : ℕ, q n := hshift
    _ = pairPrimeMeanSquare x := rfl

/-- The negative-frequency diagonal is an exact scaled copy of the positive diagonal at
unit scale. -/
theorem primeNegativeCoeff_sq_eq_inv_sq_mul
    (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    ‖primeNegativeCoeff x k‖ ^ 2 =
      x⁻¹ ^ 2 * ‖primePositiveCoeff 1 k‖ ^ 2 := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hn : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hnpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := zero_lt_one.trans_le hn
  have hlogn : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) := Real.log_nonneg hn
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hexp :
      Real.exp (-Real.log ((k + 1 : ℕ) : ℝ) - Real.log x) =
        x⁻¹ * Real.exp (-Real.log ((k + 1 : ℕ) : ℝ)) := by
    rw [show -Real.log ((k + 1 : ℕ) : ℝ) - Real.log x =
        -Real.log x + -Real.log ((k + 1 : ℕ) : ℝ) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log hxpos]
  rw [primeNegativeCoeff, primePositiveCoeff, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (Real.exp_nonneg _)),
    abs_of_nonneg (mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (Real.exp_nonneg _)), Real.log_one, sub_zero,
    abs_of_nonneg hlogn, abs_of_nonpos (by linarith :
      -Real.log ((k + 1 : ℕ) : ℝ) - Real.log x ≤ 0),
    neg_neg, hexp]
  ring

/-- The complete negative-frequency diagonal has the same exact scaling. -/
theorem primeNegativeCoeff_sq_tsum_eq (x : ℝ) (hx : 1 ≤ x) :
    (∑' k : ℕ, ‖primeNegativeCoeff x k‖ ^ 2) =
      pairPrimeMeanSquare 1 / x ^ 2 := by
  rw [show pairPrimeMeanSquare 1 / x ^ 2 = x⁻¹ ^ 2 * pairPrimeMeanSquare 1 by
    rw [inv_pow]; ring]
  rw [← primePositiveCoeff_sq_tsum_eq 1 le_rfl, ← tsum_mul_left]
  exact tsum_congr (primeNegativeCoeff_sq_eq_inv_sq_mul x hx)

end ZetaZeros.Unconditional.PairCorrelationProof
