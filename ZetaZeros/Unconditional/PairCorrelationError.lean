/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationEndpoint

/-!
# Elementary error bounds for pair correlation

This file records the two real-variable estimates used to put the integrated endpoint error
in the `1 / sqrt (log T)` scale of the unconditional pair-correlation statement.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open MeasureTheory

/-- The absolute-value version of the weighted endpoint estimate. -/
theorem integral_exp_neg_two_mul_abs_le (f : ℝ → ℝ) (hf : Integrable f)
    (C : ℝ) (hC : ∀ x, |f x - f 0| ≤ C * |x|)
    (L : ℝ) (hL : 1 ≤ L) :
    (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * |f a|) ≤
      (|f 0| / 2 + C / 4) / L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hCnonneg : 0 ≤ C := by
    have h := hC 1
    norm_num only [abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hkernel : Continuous fun a : ℝ => Real.exp (-(2 * L * a)) := by fun_prop
  have hlhs : IntervalIntegrable
      (fun a : ℝ => Real.exp (-(2 * L * a)) * |f a|) volume 0 1 := by
    simpa [mul_comm] using
      hf.abs.intervalIntegrable.mul_continuousOn hkernel.continuousOn
  have hrhs : IntervalIntegrable
      (fun a : ℝ => Real.exp (-(2 * L * a)) * (|f 0| + C * a)) volume 0 1 :=
    (by fun_prop : Continuous
      (fun a : ℝ => Real.exp (-(2 * L * a)) * (|f 0| + C * a))).intervalIntegrable 0 1
  have hmono :
      (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * |f a|) ≤
        ∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * (|f 0| + C * a) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hlhs hrhs
    intro a ha
    have ha0 : 0 ≤ a := ha.1
    have hfa : |f a| ≤ |f 0| + C * a := by
      calc
        |f a| = |(f a - f 0) + f 0| := by rw [sub_add_cancel]
        _ ≤ |f a - f 0| + |f 0| := abs_add_le _ _
        _ ≤ C * a + |f 0| := by
          gcongr
          simpa [abs_of_nonneg ha0] using hC a
        _ = |f 0| + C * a := by ring
    exact mul_le_mul_of_nonneg_left hfa (Real.exp_pos _).le
  have hfirst : IntervalIntegrable
      (fun a : ℝ => |f 0| * Real.exp (-(2 * L * a))) volume 0 1 :=
    (by fun_prop : Continuous
      (fun a : ℝ => |f 0| * Real.exp (-(2 * L * a)))).intervalIntegrable 0 1
  have hsecond : IntervalIntegrable
      (fun a : ℝ => C * (a * Real.exp (-(2 * L * a)))) volume 0 1 :=
    (by fun_prop : Continuous
      (fun a : ℝ => C * (a * Real.exp (-(2 * L * a))))).intervalIntegrable 0 1
  have hsplit :
      (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * (|f 0| + C * a)) =
        |f 0| * (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a))) +
          C * (∫ a : ℝ in 0..1, a * Real.exp (-(2 * L * a))) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add hfirst hsecond]
    apply intervalIntegral.integral_congr
    intro a _
    ring
  have hkernelBound :
      (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a))) ≤ 1 / (2 * L) := by
    rw [integral_exp_neg_two_mul L hLpos]
    have hden : 0 < 2 * L := by positivity
    apply (div_le_div_iff₀ hden hden).2
    nlinarith [Real.exp_pos (-(2 * L))]
  have hlinearBound :
      (∫ a : ℝ in 0..1, a * Real.exp (-(2 * L * a))) ≤ 1 / (2 * L) ^ 2 := by
    simpa [pow_two] using
      (intervalIntegral_pow_mul_exp_neg_le (k := 1) (M := (1 : ℝ))
        (by norm_num) (by positivity : 0 < 2 * L))
  have hinvSq : 1 / (2 * L) ^ 2 ≤ 1 / (4 * L) := by
    have hleft : 0 < (2 * L) ^ 2 := by positivity
    have hright : 0 < 4 * L := by positivity
    apply (div_le_div_iff₀ hleft hright).2
    nlinarith
  calc
    (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * |f a|) ≤
        ∫ a : ℝ in 0..1, Real.exp (-(2 * L * a)) * (|f 0| + C * a) := hmono
    _ = |f 0| * (∫ a : ℝ in 0..1, Real.exp (-(2 * L * a))) +
        C * (∫ a : ℝ in 0..1, a * Real.exp (-(2 * L * a))) := hsplit
    _ ≤ |f 0| * (1 / (2 * L)) + C * (1 / (2 * L) ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hkernelBound (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hlinearBound hCnonneg)
    _ ≤ |f 0| * (1 / (2 * L)) + C * (1 / (4 * L)) := by
      gcongr
    _ = (|f 0| / 2 + C / 4) / L := by
      field_simp

/-- Above one, reciprocal decay is stronger than reciprocal-square-root decay. -/
theorem inv_le_inv_sqrt (L : ℝ) (hL : 1 ≤ L) :
    1 / L ≤ 1 / Real.sqrt L := by
  have hsqrtPos : 0 < Real.sqrt L := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hL)
  apply one_div_le_one_div_of_le hsqrtPos
  exact Real.sqrt_le_self_iff.2 (Or.inr hL)

end ZetaZeros.Unconditional.PairCorrelationProof
