/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationLorentzian
import Zeta23.WeilEF.ZeroSummability

/-!
# Absolute convergence of the pair-correlation zero sum

This file transfers the vendored quadratic zero-summability estimate to a Lorentzian centered at
an arbitrary real ordinate.  The elementary critical-strip denominator estimate then proves
absolute convergence of the complex zero sum used in the pair-correlation explicit formula.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex

/-- The multiplicity-weighted Lorentzian centered at any fixed ordinate is summable. -/
theorem shiftedZeroLorentzian_summable (t : ℝ) :
    Summable (fun ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
      (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)) := by
  let C : ℝ := 2 * (1 + t ^ 2)
  have hbase := Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) (hbase.mul_left C)
  have hstrip := (Zeta23.zetaZeros Zeta23.zetaSeam).strip (ρ : ℂ) ρ.2
  have hgamma :
      1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)) ≤
        (5 / 4 : ℝ) + (ρ : ℂ).im ^ 2 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    nlinarith [sq_nonneg ((ρ : ℂ).re - 1 / 2)]
  have him :
      (ρ : ℂ).im ^ 2 ≤ 2 * t ^ 2 + 2 * (t - (ρ : ℂ).im) ^ 2 := by
    nlinarith [sq_nonneg (2 * t - (ρ : ℂ).im)]
  have hden :
      1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)) ≤
        C * (1 + (t - (ρ : ℂ).im) ^ 2) := by
    have hprod : 0 ≤ t ^ 2 * (t - (ρ : ℂ).im) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    dsimp [C]
    nlinarith
  have hshift : 0 < 1 + (t - (ρ : ℂ).im) ^ 2 := by positivity
  have hgammaPos : 0 < 1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)) := by
    linarith [Complex.normSq_nonneg (Zeta23.gammaOf (ρ : ℂ))]
  have hinv :
      1 / (1 + (t - (ρ : ℂ).im) ^ 2) ≤
        C / (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ))) := by
    rw [div_le_div_iff₀ hshift hgammaPos]
    simpa only [one_mul] using hden
  have hm : (0 : ℝ) ≤ Zeta23.zeroMult (ρ : ℂ) := Nat.cast_nonneg _
  calc
    (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) =
        (Zeta23.zeroMult ρ : ℝ) *
          (1 / (1 + (t - (ρ : ℂ).im) ^ 2)) := by ring
    _ ≤ (Zeta23.zeroMult ρ : ℝ) *
          (C / (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)))) :=
      mul_le_mul_of_nonneg_left hinv hm
    _ = C * ((Zeta23.zeroMult ρ : ℝ) /
          (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)))) := by ring

/-- Pointwise majorant for the Lorentzian zero summand in the explicit-formula argument. -/
theorem zeroLorentzianSummand_norm_le (x : ℝ) (hx : 1 ≤ x) (t : ℝ)
    (ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier) :
    ‖(2 * Zeta23.zeroMult ρ : ℂ) *
          (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - Complex.I * t) /
          (1 - ((ρ : ℂ) - 1 / 2 - Complex.I * t) ^ 2)‖ ≤
      (8 / 3 : ℝ) * Real.sqrt x * Zeta23.zeroMult ρ /
        (1 + (t - (ρ : ℂ).im) ^ 2) := by
  let z : ℂ := (ρ : ℂ) - 1 / 2 - Complex.I * t
  let u : ℝ := t - (ρ : ℂ).im
  let δ : ℝ := (ρ : ℂ).re - 1 / 2
  have hstrip := (Zeta23.zetaZeros Zeta23.zetaSeam).strip (ρ : ℂ) ρ.2
  have hδ : |δ| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    dsimp [δ]
    constructor <;> linarith [hstrip.1, hstrip.2]
  have hdenom :
      (1 : ℂ) - z ^ 2 =
        1 + ((u : ℂ) + Complex.I * (δ : ℂ)) ^ 2 := by
    apply Complex.ext <;>
      simp only [z, u, δ, pow_two, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    · norm_num
      ring
    · norm_num
      ring
  have hdenLower :
      (3 / 4 : ℝ) * (1 + u ^ 2) ≤ ‖(1 : ℂ) - z ^ 2‖ := by
    rw [hdenom]
    exact shiftedLorentzian_norm_lower u δ hδ
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hzre : z.re ≤ (1 / 2 : ℝ) := by
    dsimp [z]
    norm_num [Complex.mul_re]
    linarith [hstrip.2]
  have hpow : ‖(x : ℂ) ^ z‖ ≤ Real.sqrt x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx hzre
  have huPos : 0 < 1 + u ^ 2 := by positivity
  have hdenPos : 0 < ‖(1 : ℂ) - z ^ 2‖ := by
    have : 0 < (3 / 4 : ℝ) * (1 + u ^ 2) := mul_pos (by norm_num) huPos
    exact this.trans_le hdenLower
  have hinv :
      1 / ‖(1 : ℂ) - z ^ 2‖ ≤ (4 / 3 : ℝ) / (1 + u ^ 2) := by
    rw [div_le_div_iff₀ hdenPos huPos]
    nlinarith
  have hm : (0 : ℝ) ≤ Zeta23.zeroMult (ρ : ℂ) := Nat.cast_nonneg _
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  change
    ‖(2 * Zeta23.zeroMult ρ : ℂ) * (x : ℂ) ^ z / (1 - z ^ 2)‖ ≤
      (8 / 3 : ℝ) * Real.sqrt x * Zeta23.zeroMult ρ / (1 + u ^ 2)
  calc
    ‖(2 * Zeta23.zeroMult ρ : ℂ) * (x : ℂ) ^ z / (1 - z ^ 2)‖ =
        (2 * (Zeta23.zeroMult ρ : ℝ)) * ‖(x : ℂ) ^ z‖ *
          (1 / ‖(1 : ℂ) - z ^ 2‖) := by
      rw [norm_div, norm_mul, norm_mul]
      norm_num [Complex.norm_natCast]
      ring
    _ ≤ (2 * (Zeta23.zeroMult ρ : ℝ)) * Real.sqrt x *
          (1 / ‖(1 : ℂ) - z ^ 2‖) := by
      gcongr
    _ ≤ (2 * (Zeta23.zeroMult ρ : ℝ)) * Real.sqrt x *
          ((4 / 3 : ℝ) / (1 + u ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hinv (mul_nonneg (by positivity) hsqrt)
    _ = (8 / 3 : ℝ) * Real.sqrt x * Zeta23.zeroMult ρ / (1 + u ^ 2) := by ring

/-- The full Lorentzian zero summand is absolutely summable. -/
theorem zeroLorentzianSummand_summable (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    Summable (fun ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
      (2 * Zeta23.zeroMult ρ : ℂ) *
        (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - Complex.I * t) /
        (1 - ((ρ : ℂ) - 1 / 2 - Complex.I * t) ^ 2)) := by
  refine Summable.of_norm_bounded
    ((shiftedZeroLorentzian_summable t).mul_left ((8 / 3 : ℝ) * Real.sqrt x)) ?_
  intro ρ
  simpa only [mul_div_assoc] using zeroLorentzianSummand_norm_le x hx t ρ

end ZetaZeros.Unconditional.PairCorrelationProof
