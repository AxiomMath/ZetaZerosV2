/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationExplicit

/-!
# Cumulative second moment of the Archimedean density

This file records the cumulative form of Stirling's estimate needed when the
full-zero second moment is integrated over Montgomery's window.  The leading
term is obtained by integrating the square of the logarithmic Stirling main
term; the remainder is deliberately estimated coarsely by `O(T log T)`.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open MeasureTheory intervalIntegral

/-- The square of the Archimedean density is integrable on every bounded interval. -/
theorem intervalIntegrable_archimedeanDensity_sq (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Zeta23.mu t ^ 2) volume a b :=
  (Zeta23.mu_smooth.continuous.pow 2).intervalIntegrable a b

private noncomputable def logSquarePrimitive (x : ℝ) : ℝ :=
  x * (Real.log (x / (2 * Real.pi)) ^ 2 -
    2 * Real.log (x / (2 * Real.pi)) + 2)

/-- FTC identity for the square of the logarithmic Stirling main term. -/
private lemma integral_log_div_sq_eq_sub {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in 1..T, Real.log (t / (2 * Real.pi)) ^ 2) =
      logSquarePrimitive T - logSquarePrimitive 1 := by
  have hftc : ∀ t ∈ Set.uIcc (1 : ℝ) T,
      HasDerivAt logSquarePrimitive (Real.log (t / (2 * Real.pi)) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
    have hdiv : HasDerivAt (fun x : ℝ => x / (2 * Real.pi))
        (1 / (2 * Real.pi)) t :=
      (hasDerivAt_id t).div_const _
    have hlog : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)))
        (1 / t) t := by
      have h := (Real.hasDerivAt_log (by positivity : t / (2 * Real.pi) ≠ 0)).comp t hdiv
      have heq : 1 / t = (t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)) := by
        rw [inv_div]
        field_simp
      rw [heq]
      exact h
    have hlogSq : HasDerivAt
        (fun x : ℝ => Real.log (x / (2 * Real.pi)) ^ 2)
        (2 * Real.log (t / (2 * Real.pi)) * (1 / t)) t := by
      have h : HasDerivAt
          (fun x : ℝ => Real.log (x / (2 * Real.pi)) ^ 2)
          ((2 : ℕ) * Real.log (t / (2 * Real.pi)) ^ (2 - 1) * (1 / t)) t :=
        hlog.pow 2
      convert h using 1
      norm_num
    have hinterior : HasDerivAt
        (fun x : ℝ => Real.log (x / (2 * Real.pi)) ^ 2 -
          2 * Real.log (x / (2 * Real.pi)) + 2)
        (2 * Real.log (t / (2 * Real.pi)) * (1 / t) - 2 * (1 / t)) t := by
      exact (hlogSq.sub (hlog.const_mul 2)).add_const 2
    have hmul := (hasDerivAt_id t).mul hinterior
    have heq : Real.log (t / (2 * Real.pi)) ^ 2 =
        1 * (Real.log (t / (2 * Real.pi)) ^ 2 -
          2 * Real.log (t / (2 * Real.pi)) + 2) +
        t * (2 * Real.log (t / (2 * Real.pi)) * (1 / t) - 2 * (1 / t)) := by
      field_simp
      ring
    unfold logSquarePrimitive
    rw [heq]
    exact hmul
  have hint : IntervalIntegrable
      (fun t : ℝ => Real.log (t / (2 * Real.pi)) ^ 2) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
    exact (((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _)).pow 2).continuousWithinAt
  exact integral_eq_sub_of_hasDerivAt hftc hint

private lemma stirling_square_error_le
    {C T t : ℝ} (hC0 : 0 ≤ C)
    (hst : ∀ u : ℝ, 1 ≤ |u| →
      |Zeta23.mu u - (1 / (2 * Real.pi)) *
        Real.log (|u| / (2 * Real.pi))| ≤ C / u ^ 2)
    (hT : Real.exp 1 ≤ T) (ht : t ∈ Set.Icc (1 : ℝ) T) :
    |Zeta23.mu t ^ 2 -
        ((1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) ^ 2| ≤
      C * (2 * (Real.log T + |Real.log (2 * Real.pi)|) + C) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have htAbs : |t| = t := abs_of_pos ht0
  have herr0 := hst t (by simpa only [htAbs] using ht.1)
  rw [htAbs] at herr0
  have htSq : (0 : ℝ) < t ^ 2 := by positivity
  have htSqOne : (1 : ℝ) ≤ t ^ 2 := by
    nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht.1)]
  have herr : |Zeta23.mu t -
      (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))| ≤ C := by
    refine herr0.trans ?_
    rw [div_le_iff₀ htSq]
    nlinarith
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (le_trans ht.1 ht.2)
  have hlogt : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht.1
  have hlogle : Real.log t ≤ Real.log T :=
    Real.log_le_log ht0 ht.2
  have hqOne : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hcoef : |1 / (2 * Real.pi)| ≤ 1 := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    exact (div_le_one (by positivity)).2 hqOne
  have hlogdiv : Real.log (t / (2 * Real.pi)) =
      Real.log t - Real.log (2 * Real.pi) := by
    rw [Real.log_div ht0.ne' (by positivity)]
  have hmain : |(1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))| ≤
      Real.log T + |Real.log (2 * Real.pi)| := by
    rw [hlogdiv, abs_mul]
    calc
      |1 / (2 * Real.pi)| * |Real.log t - Real.log (2 * Real.pi)| ≤
          1 * (|Real.log t| + |Real.log (2 * Real.pi)|) := by
            exact mul_le_mul hcoef (abs_sub _ _) (abs_nonneg _) zero_le_one
      _ = Real.log t + |Real.log (2 * Real.pi)| := by
            rw [abs_of_nonneg hlogt, one_mul]
      _ ≤ Real.log T + |Real.log (2 * Real.pi)| := by linarith
  have hmu : |Zeta23.mu t| ≤
      Real.log T + |Real.log (2 * Real.pi)| + C := by
    have habs := abs_sub_abs_le_abs_sub (Zeta23.mu t)
      ((1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)))
    linarith
  have hsum : |Zeta23.mu t +
      (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))| ≤
      2 * (Real.log T + |Real.log (2 * Real.pi)|) + C := by
    calc
      |Zeta23.mu t +
          (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))| ≤
          |Zeta23.mu t| +
            |(1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))| :=
        abs_add_le _ _
      _ ≤ 2 * (Real.log T + |Real.log (2 * Real.pi)|) + C := by
        linarith
  rw [show Zeta23.mu t ^ 2 -
      ((1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) ^ 2 =
        (Zeta23.mu t -
          (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) *
        (Zeta23.mu t +
          (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) by ring,
    abs_mul]
  exact mul_le_mul herr hsum (abs_nonneg _) (by positivity)

private lemma logSquarePrimitive_main_error_le
    {T : ℝ} (hT : Real.exp 1 ≤ T) :
    |logSquarePrimitive T - T * Real.log T ^ 2| ≤
      T * ((|Real.log (2 * Real.pi)| + 2) ^ 2 * (1 + Real.log T)) := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hlogOne : (1 : ℝ) ≤ Real.log T :=
    (Real.le_log_iff_exp_le hT0).2 hT
  have hlogdiv : Real.log (T / (2 * Real.pi)) =
      Real.log T - Real.log (2 * Real.pi) := by
    rw [Real.log_div hT0.ne' (by positivity)]
  set L : ℝ := Real.log T with hL
  set d : ℝ := Real.log (2 * Real.pi) with hd
  set D : ℝ := |d| with hD
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hdLower : -D ≤ d := by rw [hD]; exact neg_abs_le d
  have hdUpper : d ≤ D := by rw [hD]; exact le_abs_self d
  have hLdLower : -(L * D) ≤ L * d := by
    nlinarith [mul_le_mul_of_nonneg_left hdLower hL0]
  have hLdUpper : L * d ≤ L * D :=
    mul_le_mul_of_nonneg_left hdUpper hL0
  have hdsq : d ^ 2 = D ^ 2 := by
    rw [hD, sq_abs]
  have hpositive : 0 ≤ D ^ 2 + 2 * D + 2 := by
    nlinarith [sq_nonneg D]
  have hEbound :
      |-2 * L * d + d ^ 2 - 2 * L + 2 * d + 2| ≤
        (D + 2) ^ 2 * (1 + L) := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg D, mul_nonneg hpositive hL0]
  have heq : logSquarePrimitive T - T * Real.log T ^ 2 =
      T * (-2 * L * d + d ^ 2 - 2 * L + 2 * d + 2) := by
    unfold logSquarePrimitive
    rw [hlogdiv]
    ring
  rw [heq, abs_mul, abs_of_pos hT0]
  exact mul_le_mul_of_nonneg_left hEbound hT0.le

/-- Cumulative second moment of the Archimedean density, with the exact leading
coefficient needed in the integrated full-zero assembly. -/
theorem cumulative_archimedeanDensity_sq :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, Real.exp 1 ≤ T →
      |(4 * Real.pi ^ 2) * (∫ t : ℝ in 0..T, Zeta23.mu t ^ 2) -
          T * Real.log T ^ 2| ≤
        K * T * (1 + Real.log T) := by
  obtain ⟨C, hst⟩ := archimedeanDensity_stirling
  have hC0 : 0 ≤ C := by
    have h := hst 1 (by norm_num)
    have habs := abs_nonneg
      (Zeta23.mu 1 - (1 / (2 * Real.pi)) *
        Real.log (|(1 : ℝ)| / (2 * Real.pi)))
    nlinarith
  let D : ℝ := |Real.log (2 * Real.pi)|
  let B : ℝ := C * (2 + 2 * D + C)
  let A : ℝ := (D + 2) ^ 2
  let J : ℝ := (4 * Real.pi ^ 2) *
      (∫ t : ℝ in 0..1, Zeta23.mu t ^ 2) - logSquarePrimitive 1
  let K : ℝ := |J| + (4 * Real.pi ^ 2) * B + A + 1
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hT1 : (1 : ℝ) ≤ T := by
    exact le_trans (Real.one_le_exp (by norm_num)) hT
  have hL1 : (1 : ℝ) ≤ Real.log T :=
    (Real.le_log_iff_exp_le hT0).2 hT
  have hL0 : (0 : ℝ) ≤ Real.log T := le_trans zero_le_one hL1
  have hfactor0 : 0 ≤ 1 + Real.log T := by linarith
  have honeFactor : (1 : ℝ) ≤ T * (1 + Real.log T) := by
    have := mul_le_mul hT1 (show (1 : ℝ) ≤ 1 + Real.log T by linarith)
      zero_le_one hT0.le
    simpa using this
  let m : ℝ → ℝ := fun t =>
    (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))
  let e : ℝ → ℝ := fun t => Zeta23.mu t ^ 2 - m t ^ 2
  have hintMu1T : IntervalIntegrable (fun t : ℝ => Zeta23.mu t ^ 2) volume 1 T :=
    intervalIntegrable_archimedeanDensity_sq 1 T
  have hintMain : IntervalIntegrable (fun t : ℝ => m t ^ 2) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT1]
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
    exact ((continuousAt_const.mul
      ((Real.continuousAt_log (by positivity)).comp
        (continuousAt_id.div_const _))).pow 2).continuousWithinAt
  have hintError : IntervalIntegrable e volume 1 T := by
    exact hintMu1T.sub hintMain
  have hinner :
      2 * (Real.log T + D) + C ≤
        (2 + 2 * D + C) * (1 + Real.log T) := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * D + C by positivity) hL0]
  have hpoint : ∀ t ∈ Set.uIoc (1 : ℝ) T,
      ‖e t‖ ≤ B * (1 + Real.log T) := by
    intro t ht
    rw [Set.uIoc_of_le hT1] at ht
    rw [Real.norm_eq_abs]
    dsimp only [e, m, B]
    apply (stirling_square_error_le hC0 hst hT ⟨ht.1.le, ht.2⟩).trans
    simpa [D, mul_assoc] using mul_le_mul_of_nonneg_left hinner hC0
  have herrorIntegral0 :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have herrorIntegral : |∫ t : ℝ in 1..T, e t| ≤
      B * (1 + Real.log T) * T := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 1)] at herrorIntegral0
    calc
      |∫ t : ℝ in 1..T, e t| ≤
          B * (1 + Real.log T) * (T - 1) := herrorIntegral0
      _ ≤ B * (1 + Real.log T) * T := by
        gcongr
        linarith
  have hsplit1T : (∫ t : ℝ in 1..T, Zeta23.mu t ^ 2) =
      (∫ t : ℝ in 1..T, m t ^ 2) + ∫ t : ℝ in 1..T, e t := by
    rw [← intervalIntegral.integral_add hintMain hintError]
    congr 1
    funext t
    dsimp [e]
    ring
  have hmainIntegral :
      (4 * Real.pi ^ 2) * (∫ t : ℝ in 1..T, m t ^ 2) =
        logSquarePrimitive T - logSquarePrimitive 1 := by
    have hm : (fun t : ℝ => m t ^ 2) = fun t : ℝ =>
        (1 / (4 * Real.pi ^ 2)) * Real.log (t / (2 * Real.pi)) ^ 2 := by
      funext t
      dsimp [m]
      field_simp
      ring
    rw [hm, intervalIntegral.integral_const_mul,
      integral_log_div_sq_eq_sub hT1]
    field_simp
  have hsplit0T :
      (∫ t : ℝ in 0..1, Zeta23.mu t ^ 2) +
          (∫ t : ℝ in 1..T, Zeta23.mu t ^ 2) =
        ∫ t : ℝ in 0..T, Zeta23.mu t ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_archimedeanDensity_sq 0 1) hintMu1T
  have hdecomp :
      (4 * Real.pi ^ 2) * (∫ t : ℝ in 0..T, Zeta23.mu t ^ 2) -
          T * Real.log T ^ 2 =
        J + (4 * Real.pi ^ 2) * (∫ t : ℝ in 1..T, e t) +
          (logSquarePrimitive T - T * Real.log T ^ 2) := by
    rw [← hsplit0T, hsplit1T, mul_add, mul_add, hmainIntegral]
    dsimp [J]
    ring
  rw [hdecomp]
  have hJbound : |J| ≤ |J| * (T * (1 + Real.log T)) := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left honeFactor (abs_nonneg J))
  have herrorScaled :
      |(4 * Real.pi ^ 2) * (∫ t : ℝ in 1..T, e t)| ≤
        ((4 * Real.pi ^ 2) * B) * (T * (1 + Real.log T)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi ^ 2)]
    calc
      (4 * Real.pi ^ 2) * |∫ t : ℝ in 1..T, e t| ≤
          (4 * Real.pi ^ 2) * (B * (1 + Real.log T) * T) :=
        mul_le_mul_of_nonneg_left herrorIntegral (by positivity)
      _ = ((4 * Real.pi ^ 2) * B) * (T * (1 + Real.log T)) := by ring
  have hmainError := logSquarePrimitive_main_error_le hT
  have hmainError' :
      |logSquarePrimitive T - T * Real.log T ^ 2| ≤
        A * (T * (1 + Real.log T)) := by
    dsimp [A, D]
    nlinarith
  calc
    |J + (4 * Real.pi ^ 2) * (∫ t : ℝ in 1..T, e t) +
        (logSquarePrimitive T - T * Real.log T ^ 2)| ≤
        |J| + |(4 * Real.pi ^ 2) * (∫ t : ℝ in 1..T, e t)| +
          |logSquarePrimitive T - T * Real.log T ^ 2| := by
      calc
        |J + (4 * Real.pi ^ 2) * (∫ t : ℝ in 1..T, e t) +
            (logSquarePrimitive T - T * Real.log T ^ 2)| ≤
            |J + (4 * Real.pi ^ 2) * (∫ t : ℝ in 1..T, e t)| +
              |logSquarePrimitive T - T * Real.log T ^ 2| := abs_add_le _ _
        _ ≤ |J| + |(4 * Real.pi ^ 2) * (∫ t : ℝ in 1..T, e t)| +
              |logSquarePrimitive T - T * Real.log T ^ 2| := by
          linarith [abs_add_le J
            ((4 * Real.pi ^ 2) * (∫ t : ℝ in 1..T, e t))]
    _ ≤ |J| * (T * (1 + Real.log T)) +
          ((4 * Real.pi ^ 2) * B) * (T * (1 + Real.log T)) +
          A * (T * (1 + Real.log T)) :=
      add_le_add (add_le_add hJbound herrorScaled) hmainError'
    _ ≤ K * T * (1 + Real.log T) := by
      dsimp [K]
      nlinarith [mul_nonneg hfactor0 hT0.le]

end ZetaZeros.Unconditional.PairCorrelationProof
