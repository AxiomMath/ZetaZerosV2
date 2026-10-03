/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import ZetaZeros.ZeroCount.ThetaAsymptotic
public import ZetaZeros.Analytic.Xi

/-!
# The logarithmic derivative of `ζ` on `re s = -1/2`, and the truncated Perron formula

This file proves two estimates used to shift a Perron contour to the left.

The first is a bound for `ζ' / ζ` on the line `re s = -1/2`:

`(ζ' / ζ)(-1/2 + it) = -log (|t| + 2) + O(1)`,

with an absolute constant.

The second is the **truncated Perron formula** for the kernel `x ^ s / s`: for `x > 0` with
`x ≠ 1`, `c > 0` and `T > 0`,

`|(1 / 2πi) ∫_{c - iT}^{c + iT} x ^ s / s ds - [x > 1]| ≤ x ^ c / (π T |log x|)`.

## Main definitions

* `ZetaZeros.perronTruncated`: the truncated Perron integral
  `(1 / 2πi) ∫_{c - iT}^{c + iT} x ^ s / s ds`.

## Main results

* `ZetaZeros.exists_norm_deriv_riemannZeta_div_le_of_re_eq_three_halves`: `ζ' / ζ` is bounded on
  the line `re s = 3/2`, by `∑ Λ n / n ^ (3/2)`.
* `ZetaZeros.logDeriv_riemannXi_eq_of_re_neg_two_lt`: the decomposition
  `(ξ'/ξ)(s) = 1/(s-1) - log π / 2 + ψ(s/2 + 1)/2 + (ζ'/ζ)(s)` on the half-plane `-2 < re s`.
* `ZetaZeros.riemannZeta_ne_zero_of_re_eq_neg_half`: `ζ` does not vanish on `re s = -1/2`.
* `ZetaZeros.deriv_riemannZeta_div_neg_half_eq`: the exact reflection identity
  `(ζ'/ζ)(-1/2 + it) = log π + 1/s + 1/w - ψ(3/4 + it/2)/2 - ψ(3/4 - it/2)/2
  - (3/4 - it/2)⁻¹/2 - (ζ'/ζ)(3/2 - it)`, where `s = -1/2 + it` and `w = 3/2 - it`.
* `ZetaZeros.exists_norm_deriv_riemannZeta_div_add_log_le`:
  `|(ζ'/ζ)(-1/2 + it) + log (|t| + 2)| ≤ C`.
* `ZetaZeros.perronTruncated_eq_two_pi_inv_mul_integral`: `perronTruncated x c T` is `(2π)⁻¹` times
  the integral of the kernel along the segment.
* `ZetaZeros.norm_perronTruncated_sub_indicator_le`: the truncated Perron formula,
  `|perronTruncated x c T - [x > 1]| ≤ x ^ c / (π T |log x|)`.
* `ZetaZeros.tendsto_perronTruncated_atTop`: `perronTruncated x c T` tends to `[x > 1]` as
  `T → ∞`.
-/

@[expose] public section

namespace ZetaZeros

open Complex
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-! ## `ζ' / ζ` on a line of absolute convergence -/

/-- **`ζ' / ζ` is bounded on the line `re s = 3/2`.** There the Dirichlet series
`-ζ'/ζ (s) = ∑ Λ(n) n^{-s}` converges absolutely, and the sum of the moduli of its terms depends
only on `re s`; the bound is `∑ Λ(n) n^{-3/2}`. -/
theorem exists_norm_deriv_riemannZeta_div_le_of_re_eq_three_halves :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, s.re = 3 / 2 →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ A := by
  have hre : ((3 / 2 : ℂ)).re = 3 / 2 := by simp
  have hsum0 : Summable fun n : ℕ => ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (3 / 2 : ℂ))
      (by rw [hre]; norm_num)).norm
  have hA0 : 0 ≤ ∑' n : ℕ, ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  refine ⟨(∑' n : ℕ, ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖) + 1, by linarith, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  have hle : ∀ n : ℕ, ‖LSeries.term ↗Λ s n‖ ≤ ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ := fun n =>
    LSeries.norm_term_le_of_re_le_re ↗Λ (by rw [hre, hs]) n
  have hsum : Summable fun n : ℕ => ‖LSeries.term ↗Λ s n‖ :=
    hsum0.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  have hneg : deriv riemannZeta s / riemannZeta s = -LSeries ↗Λ s := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1, neg_div, neg_neg]
  rw [hneg, norm_neg, show LSeries ↗Λ s = ∑' n : ℕ, LSeries.term ↗Λ s n from rfl]
  calc ‖∑' n : ℕ, LSeries.term ↗Λ s n‖
      ≤ ∑' n : ℕ, ‖LSeries.term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ := Summable.tsum_le_tsum hle hsum hsum0
    _ ≤ _ := by linarith

/-! ## The split of `ξ' / ξ` on the half-plane `-2 < re s` -/

/-- `π ^ (-w / 2)`, written as an exponential, as in `Kadiri.zetaPiFactor`. -/
private lemma cpow_pi_neg_div_two_eq_exp (w : ℂ) :
    (Real.pi : ℂ) ^ (-w / 2) = Complex.exp (-(w / 2) * (Real.log Real.pi : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero),
    ← Complex.ofReal_log Real.pi_nonneg, neg_div,
    mul_comm ((Real.log Real.pi : ℝ) : ℂ)]

/-- On `-2 < re w` the shifted argument of `Γ` has positive real part. -/
private lemma re_div_two_add_one_pos' {w : ℂ} (hw : -2 < w.re) : 0 < (w / 2 + 1).re := by
  simp only [Complex.add_re, Complex.one_re, Complex.div_re]
  norm_num
  linarith

/-- **The split of `ξ' / ξ` into its four factors, on the whole half-plane `-2 < re s`.** For
`-2 < re s`, `s ≠ 1` and `ζ s ≠ 0`,
`(ξ'/ξ)(s) = 1/(s-1) - log π / 2 + ψ(s/2 + 1)/2 + (ζ'/ζ)(s)`. -/
theorem logDeriv_riemannXi_eq_of_re_neg_two_lt {s : ℂ} (hs : -2 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = 1 / (s - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ)
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) + deriv riemannZeta s / riemannZeta s := by
  have hne : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    intro m h
    have hpos := re_div_two_add_one_pos' hs
    rw [h] at hpos
    simp only [Complex.neg_re, Complex.natCast_re] at hpos
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hΓ : Kadiri.zetaGammaFactor s ≠ 0 :=
    Gamma_ne_zero_of_re_pos (re_div_two_add_one_pos' hs)
  have heq : riemannXi =ᶠ[nhds s] Kadiri.completedZetaFactor := by
    have hU : IsOpen ({w : ℂ | -2 < w.re} \ {1}) :=
      (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
    filter_upwards [hU.mem_nhds ⟨hs, by simpa using hs1⟩] with w hw
    rw [riemannXi_eq_mul_riemannZeta (by simpa using hw.2) hw.1, cpow_pi_neg_div_two_eq_exp w]
    unfold Kadiri.completedZetaFactor Kadiri.zetaPoleFactor Kadiri.zetaPiFactor
      Kadiri.zetaGammaFactor
    ring
  have hlog : logDeriv riemannXi s = logDeriv Kadiri.completedZetaFactor s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  rw [hlog, Kadiri.logDeriv_completedZetaFactor s hs1 hne hΓ hζ]

/-! ## The reflection identity -/

/-- `ξ' (1 - s) = -ξ' (s)`, the derivative of the functional equation. -/
private lemma deriv_riemannXi_one_sub' (s : ℂ) :
    deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have hcomp : HasDerivAt (fun w : ℂ => riemannXi (1 - w))
      (deriv riemannXi (1 - s) * -1) s :=
    (Complex.differentiable_riemannXi (1 - s)).hasDerivAt.comp s h1
  rw [funext fun w : ℂ => riemannXi_functional_equation w] at hcomp
  rw [hcomp.deriv]
  ring

/-- `(ξ' / ξ)(1 - s) = -(ξ' / ξ)(s)`. -/
private lemma logDeriv_riemannXi_one_sub' (s : ℂ) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_one_sub' s,
    riemannXi_functional_equation s, neg_div]

/-- **`ζ` does not vanish on the line `re s = -1/2`.** -/
theorem riemannZeta_ne_zero_of_re_eq_neg_half {s : ℂ} (hs : s.re = -(1 / 2)) :
    riemannZeta s ≠ 0 := by
  have hre : -2 < s.re := by rw [hs]; norm_num
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hxi : riemannXi s ≠ 0 := by
    intro h
    obtain ⟨-, h0, -⟩ := (riemannXi_eq_zero_iff hre).mp h
    rw [hs] at h0
    norm_num at h0
  intro hz
  rw [riemannXi_eq_mul_riemannZeta hs1 hre, hz, mul_zero] at hxi
  exact hxi rfl

/-- **The reflection identity for `ζ' / ζ` across the critical strip.** With `s = -1/2 + it` and
`w = 1 - s = 3/2 - it`,
`(ζ'/ζ)(s) = log π + 1/s + 1/w - ψ(3/4 + it/2)/2 - ψ(3/4 - it/2)/2 - (3/4 - it/2)⁻¹/2 - (ζ'/ζ)(w)`.
-/
theorem deriv_riemannZeta_div_neg_half_eq (t : ℝ) :
    deriv riemannZeta (-(1 / 2 : ℂ) + (t : ℂ) * I)
        / riemannZeta (-(1 / 2 : ℂ) + (t : ℂ) * I)
      = (Real.log Real.pi : ℂ) + 1 / (-(1 / 2 : ℂ) + (t : ℂ) * I)
        + 1 / ((3 / 2 : ℂ) - (t : ℂ) * I)
        - (1 / 2 : ℂ) * digamma ((3 / 4 : ℂ) + (t : ℂ) / 2 * I)
        - (1 / 2 : ℂ) * digamma ((3 / 4 : ℂ) - (t : ℂ) / 2 * I)
        - (1 / 2 : ℂ) * ((3 / 4 : ℂ) - (t : ℂ) / 2 * I)⁻¹
        - deriv riemannZeta ((3 / 2 : ℂ) - (t : ℂ) * I)
            / riemannZeta ((3 / 2 : ℂ) - (t : ℂ) * I) := by
  set s : ℂ := -(1 / 2 : ℂ) + (t : ℂ) * I with hsdef
  set w : ℂ := (3 / 2 : ℂ) - (t : ℂ) * I with hwdef
  have hsre : s.re = -(1 / 2) := by simp [hsdef]
  have hwre : w.re = 3 / 2 := by simp [hwdef]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsre
    norm_num at hsre
  have hw1 : w ≠ 1 := by
    intro h
    rw [h] at hwre
    norm_num at hwre
  have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_re_eq_neg_half hsre
  have hζw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hwre]; norm_num)
  have hsw : (1 : ℂ) - w = s := by rw [hsdef, hwdef]; ring
  have hlog : logDeriv riemannXi s = -logDeriv riemannXi w := by
    have h := logDeriv_riemannXi_one_sub' w
    rw [hsw] at h
    exact h
  rw [logDeriv_riemannXi_eq_of_re_neg_two_lt (by rw [hsre]; norm_num) hs1 hζs,
    logDeriv_riemannXi_eq_of_re_neg_two_lt (by rw [hwre]; norm_num) hw1 hζw] at hlog
  have hz : s / 2 + 1 = (3 / 4 : ℂ) + (t : ℂ) / 2 * I := by rw [hsdef]; ring
  have hzc : w / 2 + 1 = ((3 / 4 : ℂ) - (t : ℂ) / 2 * I) + 1 := by rw [hwdef]; ring
  have hcne : ∀ m : ℕ, ((3 / 4 : ℂ) - (t : ℂ) / 2 * I) ≠ -(m : ℂ) := by
    intro m h
    have hre : ((3 / 4 : ℂ) - (t : ℂ) / 2 * I).re = 3 / 4 := by simp
    rw [h] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [hz, hzc, digamma_apply_add_one _ hcne] at hlog
  have hsub1 : s - 1 = -w := by rw [hsdef, hwdef]; ring
  have hsub2 : w - 1 = -s := by rw [hsdef, hwdef]; ring
  rw [hsub1, hsub2, div_neg, div_neg] at hlog
  linear_combination hlog

/-! ## The digamma pair at conjugate points -/

/-- `log z + log z̄ = 2 log ‖z‖` in the right half-plane. -/
private lemma log_add_log_conj {z : ℂ} (hz : 0 < z.re) :
    Complex.log z + Complex.log ((starRingEnd ℂ) z) = 2 * (Real.log ‖z‖ : ℂ) := by
  have harg : z.arg ≠ Real.pi := fun h => by
    have := Complex.arg_eq_pi_iff.mp h
    linarith [this.1]
  rw [Complex.log_conj z harg, Complex.add_conj, Complex.log_re]
  push_cast
  ring

/-- The modulus of `3/4 + it/2` is comparable to `|t| + 2`, within the absolute factors `3/16` and
`3/4`. -/
private lemma norm_three_quarters_add_le (t : ℝ) :
    3 / 16 * (|t| + 2) ≤ ‖(3 / 4 : ℂ) + (t : ℂ) / 2 * I‖ ∧
      ‖(3 / 4 : ℂ) + (t : ℂ) / 2 * I‖ ≤ |t| + 2 := by
  set z : ℂ := (3 / 4 : ℂ) + (t : ℂ) / 2 * I with hzdef
  have hre : z.re = 3 / 4 := by simp [hzdef]
  have him : z.im = t / 2 := by simp [hzdef]
  have h1 : (3 : ℝ) / 4 ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [hre] at this
    calc (3 : ℝ) / 4 = |(3 : ℝ) / 4| := by rw [abs_of_nonneg]; norm_num
      _ ≤ ‖z‖ := this
  have h2 : |t| / 2 ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rw [him, abs_div] at this
    simpa using this
  have hI : ‖(t : ℂ) / 2 * I‖ = |t| / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_div]
    simp
  have h34 : ‖(3 / 4 : ℂ)‖ = 3 / 4 := by norm_num
  have h3 : ‖z‖ ≤ 3 / 4 + |t| / 2 :=
    calc ‖z‖ ≤ ‖(3 / 4 : ℂ)‖ + ‖(t : ℂ) / 2 * I‖ := by rw [hzdef]; exact norm_add_le _ _
      _ = 3 / 4 + |t| / 2 := by rw [hI, h34]
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  exact ⟨by linarith, by linarith⟩

/-- **The digamma pair, against `log (|t| + 2)`.** There is an absolute constant `C` with
`|ψ(3/4 + it/2)/2 + ψ(3/4 - it/2)/2 - log (|t| + 2)| ≤ C` for every real `t`. -/
private lemma exists_norm_digamma_pair_sub_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(1 / 2 : ℂ) * digamma ((3 / 4 : ℂ) + (t : ℂ) / 2 * I)
        + (1 / 2 : ℂ) * digamma ((3 / 4 : ℂ) - (t : ℂ) / 2 * I)
        - (Real.log (|t| + 2) : ℂ)‖ ≤ C := by
  obtain ⟨C₁, hC₁, hstir⟩ := exists_norm_digamma_sub_log_le
  obtain ⟨C₂, hC₂, hgrow⟩ := Complex.exists_norm_digamma_le_log (a := 3 / 4) (b := 3 / 4) (by
    norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogc : Real.log (3 / 16) < 0 := Real.log_neg (by norm_num) (by norm_num)
  refine ⟨C₁ + -Real.log (3 / 16) + C₂ * Real.log 3 + Real.log 4 + 1, ?_, fun t => ?_⟩
  · have := mul_nonneg hC₂.le hlog3
    linarith
  set z : ℂ := (3 / 4 : ℂ) + (t : ℂ) / 2 * I with hzdef
  set zc : ℂ := (3 / 4 : ℂ) - (t : ℂ) / 2 * I with hzcdef
  have hzre : z.re = 3 / 4 := by simp [hzdef]
  have hzim : z.im = t / 2 := by simp [hzdef]
  have hzcre : zc.re = 3 / 4 := by simp [hzcdef]
  have hzcim : zc.im = -(t / 2) := by simp [hzcdef]
  have hconj : zc = (starRingEnd ℂ) z := by
    refine Complex.ext ?_ ?_
    · rw [Complex.conj_re, hzre, hzcre]
    · rw [Complex.conj_im, hzim, hzcim]
  have hzabs : |z.im| = |t| / 2 := by rw [hzim, abs_div]; norm_num
  have hzcabs : |zc.im| = |t| / 2 := by rw [hzcim, abs_neg, abs_div]; norm_num
  rcases le_or_gt 2 |t| with ht | ht
  · have hzi : 1 ≤ |z.im| := by rw [hzabs]; linarith
    have hzci : 1 ≤ |zc.im| := by rw [hzcabs]; linarith
    have h1 : ‖digamma z - Complex.log z‖ ≤ C₁ := by
      refine (hstir z (by rw [hzre]; norm_num) hzi).trans ?_
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < |z.im|)]
      nlinarith
    have h2 : ‖digamma zc - Complex.log zc‖ ≤ C₁ := by
      refine (hstir zc (by rw [hzcre]; norm_num) hzci).trans ?_
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < |zc.im|)]
      nlinarith
    have hpair : Complex.log z + Complex.log zc = 2 * (Real.log ‖z‖ : ℂ) := by
      rw [hconj]
      exact log_add_log_conj (by rw [hzre]; norm_num)
    obtain ⟨hlow, hhigh⟩ := norm_three_quarters_add_le t
    rw [← hzdef] at hlow hhigh
    have ht2 : (0 : ℝ) < |t| + 2 := by linarith [abs_nonneg t]
    have hzpos : (0 : ℝ) < ‖z‖ := by nlinarith
    have hd1 : Real.log ‖z‖ ≤ Real.log (|t| + 2) := Real.log_le_log hzpos hhigh
    have hd2 : Real.log (3 / 16) + Real.log (|t| + 2) ≤ Real.log ‖z‖ := by
      have := Real.log_le_log (by positivity : (0 : ℝ) < 3 / 16 * (|t| + 2)) hlow
      rwa [Real.log_mul (by norm_num) (by positivity)] at this
    have hdiff : ‖(Real.log ‖z‖ : ℂ) - (Real.log (|t| + 2) : ℂ)‖ ≤ -Real.log (3 / 16) := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hrw : (1 / 2 : ℂ) * digamma z + (1 / 2 : ℂ) * digamma zc
        - (Real.log (|t| + 2) : ℂ)
        = (1 / 2 : ℂ) * (digamma z - Complex.log z)
          + (1 / 2 : ℂ) * (digamma zc - Complex.log zc)
          + ((Real.log ‖z‖ : ℂ) - (Real.log (|t| + 2) : ℂ)) := by
      linear_combination (1 / 2 : ℂ) * hpair
    rw [hrw]
    calc ‖(1 / 2 : ℂ) * (digamma z - Complex.log z)
            + (1 / 2 : ℂ) * (digamma zc - Complex.log zc)
            + ((Real.log ‖z‖ : ℂ) - (Real.log (|t| + 2) : ℂ))‖
        ≤ ‖(1 / 2 : ℂ) * (digamma z - Complex.log z)
            + (1 / 2 : ℂ) * (digamma zc - Complex.log zc)‖
          + ‖(Real.log ‖z‖ : ℂ) - (Real.log (|t| + 2) : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖(1 / 2 : ℂ) * (digamma z - Complex.log z)‖
          + ‖(1 / 2 : ℂ) * (digamma zc - Complex.log zc)‖
          + ‖(Real.log ‖z‖ : ℂ) - (Real.log (|t| + 2) : ℂ)‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ _ := by
            have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
            rw [norm_mul, norm_mul, hhalf]
            nlinarith [hdiff]
  · have h1 : ‖digamma z‖ ≤ C₂ * Real.log 3 := by
      refine (hgrow z (by rw [hzre]) (by rw [hzre])).trans ?_
      have hb : |z.im| + 2 ≤ 3 := by rw [hzabs]; linarith
      have hp : (0 : ℝ) < |z.im| + 2 := by positivity
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hp hb) hC₂.le
    have h2 : ‖digamma zc‖ ≤ C₂ * Real.log 3 := by
      refine (hgrow zc (by rw [hzcre]) (by rw [hzcre])).trans ?_
      have hb : |zc.im| + 2 ≤ 3 := by rw [hzcabs]; linarith
      have hp : (0 : ℝ) < |zc.im| + 2 := by positivity
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hp hb) hC₂.le
    have h3 : ‖(Real.log (|t| + 2) : ℂ)‖ ≤ Real.log 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by linarith [abs_nonneg t]))]
      exact Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    calc ‖(1 / 2 : ℂ) * digamma z + (1 / 2 : ℂ) * digamma zc - (Real.log (|t| + 2) : ℂ)‖
        ≤ ‖(1 / 2 : ℂ) * digamma z + (1 / 2 : ℂ) * digamma zc‖
          + ‖(Real.log (|t| + 2) : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖(1 / 2 : ℂ) * digamma z‖ + ‖(1 / 2 : ℂ) * digamma zc‖
          + ‖(Real.log (|t| + 2) : ℂ)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by
            rw [norm_mul, norm_mul, hhalf]
            nlinarith
/-! ## The logarithmic derivative on the line `re s = -1/2` -/

/-- **The logarithmic derivative on the line `re s = -1/2`.** There is an absolute constant `C`
with `|(ζ'/ζ)(-1/2 + it) + log(|t| + 2)| ≤ C` for every real `t`. -/
@[zz_tag "lem_zeta_logderiv_left"]
theorem exists_norm_deriv_riemannZeta_div_add_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖deriv riemannZeta (-(1 / 2 : ℂ) + (t : ℂ) * I)
          / riemannZeta (-(1 / 2 : ℂ) + (t : ℂ) * I) + (Real.log (|t| + 2) : ℂ)‖ ≤ C := by
  obtain ⟨A, hA, hAb⟩ := exists_norm_deriv_riemannZeta_div_le_of_re_eq_three_halves
  obtain ⟨C₃, hC₃, hC₃b⟩ := exists_norm_digamma_pair_sub_log_le
  refine ⟨|Real.log Real.pi| + 2 + 1 + 1 + A + C₃, by positivity, fun t => ?_⟩
  set s : ℂ := -(1 / 2 : ℂ) + (t : ℂ) * I with hsdef
  set w : ℂ := (3 / 2 : ℂ) - (t : ℂ) * I with hwdef
  set z : ℂ := (3 / 4 : ℂ) + (t : ℂ) / 2 * I with hzdef
  set zc : ℂ := (3 / 4 : ℂ) - (t : ℂ) / 2 * I with hzcdef
  have hsre : s.re = -(1 / 2) := by simp [hsdef]
  have hwre : w.re = 3 / 2 := by simp [hwdef]
  have hzcre : zc.re = 3 / 4 := by simp [hzcdef]
  have hpi : ‖(Real.log Real.pi : ℂ)‖ = |Real.log Real.pi| := Complex.norm_real _
  have hs : ‖1 / s‖ ≤ 2 := by
    have h1 : (1 : ℝ) / 2 ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rw [hsre] at this
      calc (1 : ℝ) / 2 = |(-(1 / 2) : ℝ)| := by rw [abs_of_nonpos] <;> norm_num
        _ ≤ ‖s‖ := this
    rw [norm_div, norm_one]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖s‖)]
    linarith
  have hw : ‖1 / w‖ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w
      rw [hwre] at this
      calc (1 : ℝ) ≤ |(3 / 2 : ℝ)| := by
            rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]; norm_num
        _ ≤ ‖w‖ := this
    rw [norm_div, norm_one]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖w‖)]
    linarith
  have hzc : ‖(1 / 2 : ℂ) * zc⁻¹‖ ≤ 1 := by
    have h1 : (3 : ℝ) / 4 ≤ ‖zc‖ := by
      have := Complex.abs_re_le_norm zc
      rw [hzcre] at this
      calc (3 : ℝ) / 4 = |(3 / 4 : ℝ)| := by
            rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
        _ ≤ ‖zc‖ := this
    have h2 : ‖zc‖⁻¹ ≤ 4 / 3 :=
      calc ‖zc‖⁻¹ ≤ ((3 : ℝ) / 4)⁻¹ := by
            simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 4) h1
        _ = 4 / 3 := by norm_num
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [norm_mul, hhalf, norm_inv]
    linarith
  have hzeta : ‖deriv riemannZeta w / riemannZeta w‖ ≤ A := hAb w hwre
  have hpair := hC₃b t
  rw [← hzdef, ← hzcdef] at hpair
  rw [deriv_riemannZeta_div_neg_half_eq t, ← hsdef, ← hwdef, ← hzdef, ← hzcdef]
  have hsplit : (Real.log Real.pi : ℂ) + 1 / s + 1 / w - (1 / 2 : ℂ) * digamma z
        - (1 / 2 : ℂ) * digamma zc - (1 / 2 : ℂ) * zc⁻¹
        - deriv riemannZeta w / riemannZeta w + (Real.log (|t| + 2) : ℂ)
      = ((Real.log Real.pi : ℂ) + 1 / s + 1 / w - (1 / 2 : ℂ) * zc⁻¹
          - deriv riemannZeta w / riemannZeta w)
        - ((1 / 2 : ℂ) * digamma z + (1 / 2 : ℂ) * digamma zc
            - (Real.log (|t| + 2) : ℂ)) := by ring
  rw [hsplit]
  calc ‖((Real.log Real.pi : ℂ) + 1 / s + 1 / w - (1 / 2 : ℂ) * zc⁻¹
          - deriv riemannZeta w / riemannZeta w)
        - ((1 / 2 : ℂ) * digamma z + (1 / 2 : ℂ) * digamma zc
            - (Real.log (|t| + 2) : ℂ))‖
      ≤ ‖(Real.log Real.pi : ℂ) + 1 / s + 1 / w - (1 / 2 : ℂ) * zc⁻¹
          - deriv riemannZeta w / riemannZeta w‖
        + ‖(1 / 2 : ℂ) * digamma z + (1 / 2 : ℂ) * digamma zc
            - (Real.log (|t| + 2) : ℂ)‖ := norm_sub_le _ _
    _ ≤ (|Real.log Real.pi| + 2 + 1 + 1 + A) + C₃ := by
          refine add_le_add ?_ hpair
          have n1 := norm_sub_le ((Real.log Real.pi : ℂ) + 1 / s + 1 / w - (1 / 2 : ℂ) * zc⁻¹)
            (deriv riemannZeta w / riemannZeta w)
          have n2 := norm_sub_le ((Real.log Real.pi : ℂ) + 1 / s + 1 / w) ((1 / 2 : ℂ) * zc⁻¹)
          have n3 := norm_add_le ((Real.log Real.pi : ℂ) + 1 / s) (1 / w)
          have n4 := norm_add_le (Real.log Real.pi : ℂ) (1 / s)
          rw [hpi] at n4
          linarith
    _ ≤ _ := by linarith

/-! ## The truncated Perron formula -/

open Filter Topology

/-- `(x : ℂ) ^ s` as an exponential, for a positive real base. -/
private lemma cpow_ofReal_eq_exp {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]

/-- `((x⁻¹ : ℝ) : ℂ) ^ s = (x : ℂ) ^ (-s)`: inverting a positive real base negates the exponent. -/
private lemma cpow_inv_ofReal {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  rw [cpow_ofReal_eq_exp (inv_pos.mpr hx), cpow_ofReal_eq_exp hx, Real.log_inv]
  push_cast
  ring_nf

/-- The modulus of the Perron kernel depends on `s` only through `re s` and `‖s‖`. -/
private lemma norm_cpow_ofReal_div {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖(x : ℂ) ^ s / s‖ = x ^ s.re / ‖s‖ := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- The Perron kernel is holomorphic away from the origin. -/
private lemma differentiableAt_cpow_ofReal_div {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ w / w) s := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  exact ((differentiable_id.const_cpow (Or.inl hx0)) s).div differentiableAt_id hs

/-- Cauchy's theorem on the axis-parallel rectangle `[a, b] × [y₁, y₂]`. -/
private lemma integral_boundary_eq_zero {f : ℂ → ℂ} {a b y₁ y₂ : ℝ}
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc y₁ y₂)) :
    ((∫ σ in a..b, f ((σ : ℂ) + (y₁ : ℂ) * I)) - ∫ σ in a..b, f ((σ : ℂ) + (y₂ : ℂ) * I))
      + I * (∫ y in y₁..y₂, f ((b : ℂ) + (y : ℂ) * I))
      - I * (∫ y in y₁..y₂, f ((a : ℂ) + (y : ℂ) * I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + (y₁ : ℂ) * I) ((b : ℂ) + (y₂ : ℂ) * I) (by simpa using hf)
  simpa [smul_eq_mul] using h

private lemma log_ne_zero_of_ne_one {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) : Real.log x ≠ 0 :=
  fun h => hx1 (Real.eq_one_of_pos_of_log_eq_zero hx h)

private lemma continuous_rpow_const_base {x : ℝ} (hx : 0 < x) :
    Continuous fun σ : ℝ => x ^ σ := by
  simp only [Real.rpow_def_of_pos hx]
  exact Real.continuous_exp.comp (by fun_prop)

/-- `∫_a^b x ^ σ dσ = (x ^ b - x ^ a) / log x`. -/
private lemma integral_rpow_const_base {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) (a b : ℝ) :
    (∫ σ in a..b, x ^ σ) = (x ^ b - x ^ a) / Real.log x := by
  have hL := log_ne_zero_of_ne_one hx hx1
  have hderiv : ∀ σ ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => x ^ u / Real.log x) (x ^ σ) σ := by
    intro σ _
    have h := ((hasDerivAt_id σ).const_rpow hx).div_const (Real.log x)
    have he : Real.log x * 1 * x ^ σ / Real.log x = x ^ σ := by
      rw [mul_one]
      field_simp
    simpa only [id_eq, he] using h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_rpow_const_base hx).intervalIntegrable (μ := MeasureTheory.volume) a b)]
  ring

/-- **The horizontal edge.** On the line `im s = y` the kernel is at most `x ^ σ / |y|`, so the
horizontal integral is at most `(∫ x ^ σ) / |y|`. -/
private lemma norm_integral_horizontal_le {x : ℝ} (hx : 0 < x) {a b y : ℝ} (hab : a ≤ b)
    (hy : y ≠ 0) :
    ‖∫ σ in a..b, (x : ℂ) ^ ((σ : ℂ) + (y : ℂ) * I) / ((σ : ℂ) + (y : ℂ) * I)‖
      ≤ (∫ σ in a..b, x ^ σ) / |y| := by
  have hy' : 0 < |y| := abs_pos.mpr hy
  have hbound : ∀ σ : ℝ, σ ∈ Set.Ioc a b →
      ‖(x : ℂ) ^ ((σ : ℂ) + (y : ℂ) * I) / ((σ : ℂ) + (y : ℂ) * I)‖ ≤ x ^ σ / |y| := by
    intro σ _
    rw [norm_cpow_ofReal_div hx]
    have hre : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
    have hnorm : |y| ≤ ‖(σ : ℂ) + (y : ℂ) * I‖ := by
      have h := Complex.abs_im_le_norm ((σ : ℂ) + (y : ℂ) * I)
      simpa using h
    rw [hre]
    gcongr
  have hc : Continuous fun σ : ℝ => x ^ σ / |y| :=
    (continuous_rpow_const_base hx).div_const _
  have h := intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall hbound)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) a b)
  rwa [intervalIntegral.integral_div] at h

/-- **The far vertical edge.** On the line `re s = σ` the kernel is at most `x ^ σ / |σ|`. -/
private lemma norm_integral_vertical_le {x : ℝ} (hx : 0 < x) {σ T : ℝ} (hσ : σ ≠ 0) :
    ‖∫ t in (-T)..T, (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) / ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ x ^ σ / |σ| * |T - -T| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => ?_)
  rw [norm_cpow_ofReal_div hx]
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have hnorm : |σ| ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := by
    have h := Complex.abs_re_le_norm ((σ : ℂ) + (t : ℂ) * I)
    simpa using h
  have hσ' : 0 < |σ| := abs_pos.mpr hσ
  rw [hre]
  gcongr

/-- **The case `0 < x < 1`.** For `0 < x < 1`, `c > 0` and `T > 0`, the integral of `x ^ s / s`
along the segment `re s = c`, `|im s| ≤ T`, has modulus at most `2 x ^ c / (T |log x|)`. -/
private lemma norm_integral_segment_le_of_lt_one {x c T : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖
      ≤ 2 * x ^ c / (T * |Real.log x|) := by
  set logx := Real.log x with hlogxdef
  have hL : logx < 0 := Real.log_neg hx hx1
  have hlogxpos : 0 < |logx| := abs_pos.mpr (ne_of_lt hL)
  have hlogxabs : |logx| = -logx := abs_of_neg hL
  have hx1' : x ≠ 1 := ne_of_lt hx1
  set K : ℝ := 2 * x ^ c / (T * |logx|) with hK
  have key : ∀ U : ℝ, max c 1 ≤ U →
      ‖∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖
        ≤ K + 2 * T * x ^ U := by
    intro U hU
    have hcU : c ≤ U := le_trans (le_max_left _ _) hU
    have hU1 : (1 : ℝ) ≤ U := le_trans (le_max_right _ _) hU
    have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU1
    have hdiff : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s / s)
        (Set.uIcc c U ×ℂ Set.uIcc (-T) T) := by
      intro s hs
      have hre : s.re ∈ Set.uIcc c U := hs.1
      rw [Set.uIcc_of_le hcU] at hre
      have hs0 : s ≠ 0 := by
        intro h
        rw [h] at hre
        simp only [Complex.zero_re, Set.mem_Icc] at hre
        linarith [hre.1]
      exact (differentiableAt_cpow_ofReal_div hx hs0).differentiableWithinAt
    have hrect := integral_boundary_eq_zero (f := fun s : ℂ => (x : ℂ) ^ s / s)
      (a := c) (b := U) (y₁ := -T) (y₂ := T) hdiff
    set Hb : ℂ := ∫ σ in c..U, (x : ℂ) ^ ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)
      / ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) with hHb
    set Ht : ℂ := ∫ σ in c..U, (x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I)
      / ((σ : ℂ) + (T : ℂ) * I) with hHt
    set VU : ℂ := ∫ y in (-T)..T, (x : ℂ) ^ ((U : ℂ) + (y : ℂ) * I)
      / ((U : ℂ) + (y : ℂ) * I) with hVU
    set Vc : ℂ := ∫ y in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (y : ℂ) * I)
      / ((c : ℂ) + (y : ℂ) * I) with hVc
    have hVceq : (I : ℂ) * Vc = Hb - Ht + I * VU := by linear_combination -hrect
    have hnormle : ‖Vc‖ ≤ ‖Hb‖ + ‖Ht‖ + ‖VU‖ := by
      have hI : ‖(I : ℂ) * Vc‖ = ‖Vc‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      rw [← hI, hVceq]
      calc ‖Hb - Ht + I * VU‖ ≤ ‖Hb - Ht‖ + ‖(I : ℂ) * VU‖ := norm_add_le _ _
        _ ≤ ‖Hb‖ + ‖Ht‖ + ‖VU‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]
            have := norm_sub_le Hb Ht
            linarith
    have hint : (∫ σ in c..U, x ^ σ) = (x ^ U - x ^ c) / logx :=
      integral_rpow_const_base hx hx1' c U
    have hxU : x ^ U ≤ x ^ c := Real.rpow_le_rpow_of_exponent_ge hx hx1.le hcU
    have hxU0 : (0 : ℝ) ≤ x ^ U := Real.rpow_nonneg hx.le U
    have hintle : (∫ σ in c..U, x ^ σ) ≤ x ^ c / |logx| := by
      rw [hint]
      have e1 : (x ^ U - x ^ c) / logx = (x ^ c - x ^ U) / |logx| := by
        rw [hlogxabs]; field_simp; ring
      rw [e1]
      gcongr
      linarith
    have hHbnorm : ‖Hb‖ ≤ x ^ c / |logx| / T := by
      have h := norm_integral_horizontal_le (x := x) hx (a := c) (b := U) (y := -T) hcU
        (by linarith)
      rw [← hHb] at h
      have habs : |(-T : ℝ)| = T := by rw [abs_neg, abs_of_pos hT]
      rw [habs] at h
      refine h.trans ?_
      gcongr
    have hHtnorm : ‖Ht‖ ≤ x ^ c / |logx| / T := by
      have h := norm_integral_horizontal_le (x := x) hx (a := c) (b := U) (y := T) hcU
        (by linarith)
      rw [← hHt] at h
      rw [abs_of_pos hT] at h
      refine h.trans ?_
      gcongr
    have hVUnorm : ‖VU‖ ≤ 2 * T * x ^ U := by
      have h := norm_integral_vertical_le (x := x) hx (σ := U) (T := T) (by linarith)
      rw [← hVU] at h
      refine h.trans ?_
      have habs : |U| = U := abs_of_pos hU0
      have h2 : x ^ U / |U| ≤ x ^ U := by rw [habs]; exact div_le_self hxU0 hU1
      have h3 : |T - -T| = 2 * T := by
        rw [show T - -T = 2 * T by ring, abs_of_pos (by linarith)]
      rw [h3]
      calc x ^ U / |U| * (2 * T) ≤ x ^ U * (2 * T) := by gcongr
        _ = 2 * T * x ^ U := by ring
    have hKeq : x ^ c / |logx| / T + x ^ c / |logx| / T = K := by
      rw [hK]; field_simp; ring
    linarith
  have hlim : Tendsto (fun U : ℝ => K + 2 * T * x ^ U) atTop (𝓝 (K + 0)) := by
    refine tendsto_const_nhds.add ?_
    have h := (tendsto_rpow_atTop_of_base_lt_one x (by linarith) hx1).const_mul (2 * T)
    simpa using h
  have := ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨max c 1, key⟩)
  simpa using this

/-- **The pole at the origin.** `x ^ s / s` has a simple pole at `s = 0` with residue `x ^ 0 = 1`,
so the rectangle with corners `-c - iT` and `c + iT` has normalised rectangle integral `1`. -/
private lemma rectangleIntegral'_cpow_ofReal_div_eq_one {x c T : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hT : 0 < T) :
    RectangleIntegral' (fun s : ℂ => (x : ℂ) ^ s / s)
        (((-c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) (((c : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I) = 1 := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set z : ℂ := ((-c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I with hzdef
  set w : ℂ := ((c : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I with hwdef
  have hzre : z.re = -c := by simp [hzdef]
  have hzim : z.im = -T := by simp [hzdef]
  have hwre : w.re = c := by simp [hwdef]
  have hwim : w.im = T := by simp [hwdef]
  refine ResidueTheoremOnRectangleWithSimplePole' (p := 0) (A := 1)
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith) ?_ ?_ ?_
  · rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, hzre, hzim, hwre, hwim]
    have huc : Set.uIoo (-c) c = Set.Ioo (-c) c := by
      rw [Set.uIoo, inf_of_le_left (by linarith), sup_of_le_right (by linarith)]
    have huT : Set.uIoo (-T) T = Set.Ioo (-T) T := by
      rw [Set.uIoo, inf_of_le_left (by linarith), sup_of_le_right (by linarith)]
    rw [huc, huT]
    simp only [Complex.zero_re, Complex.zero_im, Set.mem_Ioo]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · intro s hs
    exact (differentiableAt_cpow_ofReal_div hx (by simpa using hs.2)).differentiableWithinAt
  · have hd : HasDerivAt (fun s : ℂ => (x : ℂ) ^ s) ((Real.log x : ℂ)) 0 := by
      have h := (Complex.hasStrictDerivAt_const_cpow (x := (x : ℂ)) (y := 0)
        (Or.inl hx0)).hasDerivAt
      rwa [Complex.cpow_zero, one_mul, ← Complex.ofReal_log hx.le] at h
    have hbig : (fun s : ℂ => ((x : ℂ) ^ s - 1) / s) =O[nhdsWithin 0 {(0 : ℂ)}ᶜ]
        (1 : ℂ → ℂ) := by
      refine Filter.Tendsto.isBigO_one ℂ (Filter.Tendsto.congr ?_ hd.tendsto_slope)
      intro s
      simp [slope_def_field, Complex.cpow_zero]
    refine hbig.congr' ?_ (by rfl)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := hs
    simp only [Pi.sub_apply, sub_zero]
    field_simp

/-- **The reflection identity.** For `x, c, T > 0`, the integrals of `x ^ s / s` and of
`(x⁻¹) ^ s / s` along the segment `re s = c`, `|im s| ≤ T`, add up to `2 π` plus `i⁻¹` times the
difference of the integrals of `x ^ s / s` along the horizontal segments `im s = T` and
`im s = -T`, `|re s| ≤ c`. -/
private lemma integral_segment_add_integral_segment_inv {x c T : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hT : 0 < T) :
    (∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))
      + (∫ t in (-T)..T, ((x⁻¹ : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))
      - 2 * (Real.pi : ℂ)
    = ((∫ σ in (-c)..c, (x : ℂ) ^ ((σ : ℂ) + ((T : ℝ) : ℂ) * I) / ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
        - ∫ σ in (-c)..c, (x : ℂ) ^ ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)
            / ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) / I := by
  have hres := rectangleIntegral'_cpow_ofReal_div_eq_one hx hc hT
  have hpi : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false]
    simp [hpi]
  have hsm : (1 / (2 * (Real.pi : ℂ) * I))
      * RectangleIntegral (fun s : ℂ => (x : ℂ) ^ s / s)
        (((-c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) (((c : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I) = 1 := by
    simpa [smul_eq_mul] using hres
  have hR : RectangleIntegral (fun s : ℂ => (x : ℂ) ^ s / s)
      (((-c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) (((c : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I)
      = 2 * (Real.pi : ℂ) * I := by
    calc RectangleIntegral (fun s : ℂ => (x : ℂ) ^ s / s)
          (((-c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) (((c : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I)
        = (2 * (Real.pi : ℂ) * I) * ((1 / (2 * (Real.pi : ℂ) * I))
            * RectangleIntegral (fun s : ℂ => (x : ℂ) ^ s / s)
              (((-c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) (((c : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I)) := by
          rw [← mul_assoc, mul_one_div, div_self h2pi, one_mul]
      _ = 2 * (Real.pi : ℂ) * I := by rw [hsm, mul_one]
  rw [ZetaZeros.rectangleIntegral_eq_boundary_integrals
    (fun s : ℂ => (x : ℂ) ^ s / s) (-c) c (-T) T] at hR
  have hVl : (∫ y in (-T)..T, (x : ℂ) ^ (((-c : ℝ) : ℂ) + (y : ℂ) * I)
        / (((-c : ℝ) : ℂ) + (y : ℂ) * I))
      = -∫ y in (-T)..T, ((x⁻¹ : ℝ) : ℂ) ^ ((c : ℂ) + (y : ℂ) * I)
          / ((c : ℂ) + (y : ℂ) * I) := by
    have hpt : ∀ y : ℝ, (x : ℂ) ^ (((-c : ℝ) : ℂ) + (y : ℂ) * I)
          / (((-c : ℝ) : ℂ) + (y : ℂ) * I)
        = -(((x⁻¹ : ℝ) : ℂ) ^ ((c : ℂ) + ((-y : ℝ) : ℂ) * I)
            / ((c : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
      intro y
      rw [cpow_inv_ofReal hx]
      have e1 : -((c : ℂ) + ((-y : ℝ) : ℂ) * I) = ((-c : ℝ) : ℂ) + (y : ℂ) * I := by
        push_cast; ring
      have e2 : ((c : ℂ) + ((-y : ℝ) : ℂ) * I) = -(((-c : ℝ) : ℂ) + (y : ℂ) * I) := by
        push_cast; ring
      rw [e1, e2, div_neg, neg_neg]
    calc (∫ y in (-T)..T, (x : ℂ) ^ (((-c : ℝ) : ℂ) + (y : ℂ) * I)
            / (((-c : ℝ) : ℂ) + (y : ℂ) * I))
        = ∫ y in (-T)..T, -(((x⁻¹ : ℝ) : ℂ) ^ ((c : ℂ) + ((-y : ℝ) : ℂ) * I)
            / ((c : ℂ) + ((-y : ℝ) : ℂ) * I)) := by simp_rw [hpt]
      _ = -∫ y in (-T)..T, ((x⁻¹ : ℝ) : ℂ) ^ ((c : ℂ) + ((-y : ℝ) : ℂ) * I)
            / ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := intervalIntegral.integral_neg
      _ = -∫ u in (-T)..T, ((x⁻¹ : ℝ) : ℂ) ^ ((c : ℂ) + (u : ℂ) * I)
            / ((c : ℂ) + (u : ℂ) * I) := by
          rw [intervalIntegral.integral_comp_neg
            (fun u : ℝ => ((x⁻¹ : ℝ) : ℂ) ^ ((c : ℂ) + (u : ℂ) * I) / ((c : ℂ) + (u : ℂ) * I))]
          norm_num
  rw [hVl] at hR
  rw [eq_div_iff Complex.I_ne_zero]
  linear_combination hR

/-! ### The formula -/

/-- **The truncated Perron integral** `(1 / 2πi) ∫_{c - iT}^{c + iT} x ^ s / s ds`, the contour
being the vertical segment `s = c + it` with `t` running over `[-T, T]`, so that `ds = i dt`. -/
@[zz_tag "def_perron_truncated"]
noncomputable def perronTruncated (x c T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) * (I * ∫ t in (-T)..T,
    (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))

/-- `ZetaZeros.perronTruncated` is `VIntegral'` of the kernel `x ^ s / s`. -/
private theorem perronTruncated_eq_VIntegral' (x c T : ℝ) :
    perronTruncated x c T = VIntegral' (fun s : ℂ => (x : ℂ) ^ s / s) c (-T) T := by
  rw [perronTruncated, VIntegral', VIntegral, smul_eq_mul, smul_eq_mul]

/-- The two factors of `i` cancel: the truncated Perron integral is `(2π)⁻¹` times the integral of
the kernel along the segment. -/
theorem perronTruncated_eq_two_pi_inv_mul_integral (x c T : ℝ) :
    perronTruncated x c T = (1 / (2 * (Real.pi : ℂ)))
      * ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I) := by
  have hpi : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [perronTruncated]
  field_simp

/-- **The truncated Perron formula.** For `x > 0` with `x ≠ 1`, `c > 0` and `T > 0`,

`|(1 / 2πi) ∫_{c - iT}^{c + iT} x ^ s / s ds - [x > 1]| ≤ x ^ c / (π T |log x|)`. -/
@[zz_tag "lem_perron_truncated"]
theorem norm_perronTruncated_sub_indicator_le {x c T : ℝ} (hx : 0 < x) (hx1 : x ≠ 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronTruncated x c T - (if 1 < x then 1 else 0)‖
      ≤ x ^ c / (Real.pi * T * |Real.log x|) := by
  rw [perronTruncated_eq_two_pi_inv_mul_integral]
  have hpi := Real.pi_pos
  have hpine : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx c
  have hconst : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    norm_num
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · have hif : (if 1 < x then (1 : ℂ) else 0) = 0 := by
      simp [show ¬ (1 < x) from by linarith]
    rw [hif, sub_zero, norm_mul, hconst]
    have hseg := norm_integral_segment_le_of_lt_one hx hlt hc hT
    have hL : 0 < |Real.log x| := abs_pos.mpr (log_ne_zero_of_ne_one hx hx1)
    calc 1 / (2 * Real.pi)
          * ‖∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖
        ≤ 1 / (2 * Real.pi) * (2 * x ^ c / (T * |Real.log x|)) :=
          mul_le_mul_of_nonneg_left hseg (by positivity)
      _ = x ^ c / (Real.pi * T * |Real.log x|) := by field_simp
  · have hif : (if 1 < x then (1 : ℂ) else 0) = 1 := by simp [hgt]
    rw [hif]
    set logx := Real.log x with hlogxdef
    have hL : 0 < logx := Real.log_pos hgt
    have hlogxabs : |logx| = logx := abs_of_pos hL
    set V : ℂ := ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      / ((c : ℂ) + (t : ℂ) * I) with hV
    set V' : ℂ := ∫ t in (-T)..T, ((x⁻¹ : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      / ((c : ℂ) + (t : ℂ) * I) with hV'
    set Ht : ℂ := ∫ σ in (-c)..c, (x : ℂ) ^ ((σ : ℂ) + ((T : ℝ) : ℂ) * I)
      / ((σ : ℂ) + ((T : ℝ) : ℂ) * I) with hHt
    set Hb : ℂ := ∫ σ in (-c)..c, (x : ℂ) ^ ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)
      / ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) with hHb
    have hrefl := integral_segment_add_integral_segment_inv hx hc hT
    rw [← hV, ← hV', ← hHt, ← hHb] at hrefl
    have hstep : V - 2 * (Real.pi : ℂ) = (Ht - Hb) / I - V' := by linear_combination hrefl
    have hid : (1 / (2 * (Real.pi : ℂ))) * V - 1
        = (1 / (2 * (Real.pi : ℂ))) * ((Ht - Hb) / I - V') := by
      rw [← hstep]; field_simp
    rw [hid, norm_mul, hconst]
    have hintval : (∫ σ in (-c)..c, x ^ σ) = (x ^ c - (x ^ c)⁻¹) / logx := by
      rw [integral_rpow_const_base hx hx1 (-c) c, Real.rpow_neg hx.le]
    have hnHt : ‖Ht‖ ≤ (x ^ c - (x ^ c)⁻¹) / logx / T := by
      have h := norm_integral_horizontal_le (x := x) hx (a := -c) (b := c) (y := T)
        (by linarith) (by linarith)
      rw [← hHt, hintval, abs_of_pos hT] at h
      exact h
    have hnHb : ‖Hb‖ ≤ (x ^ c - (x ^ c)⁻¹) / logx / T := by
      have h := norm_integral_horizontal_le (x := x) hx (a := -c) (b := c) (y := -T)
        (by linarith) (by linarith)
      rw [← hHb, hintval, abs_neg, abs_of_pos hT] at h
      exact h
    have hnV' : ‖V'‖ ≤ 2 * (x ^ c)⁻¹ / (T * logx) := by
      have hxi : (0 : ℝ) < x⁻¹ := inv_pos.mpr hx
      have hxi1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
      have h := norm_integral_segment_le_of_lt_one hxi hxi1 hc hT
      rw [← hV', Real.inv_rpow hx.le, Real.log_inv, abs_neg, hlogxabs] at h
      exact h
    have hnR : ‖(Ht - Hb) / I - V'‖ ≤ ‖Ht‖ + ‖Hb‖ + ‖V'‖ := by
      calc ‖(Ht - Hb) / I - V'‖ ≤ ‖(Ht - Hb) / I‖ + ‖V'‖ := norm_sub_le _ _
        _ = ‖Ht - Hb‖ + ‖V'‖ := by rw [norm_div, Complex.norm_I, div_one]
        _ ≤ ‖Ht‖ + ‖Hb‖ + ‖V'‖ := by have := norm_sub_le Ht Hb; linarith
    calc 1 / (2 * Real.pi) * ‖(Ht - Hb) / I - V'‖
        ≤ 1 / (2 * Real.pi) * ((x ^ c - (x ^ c)⁻¹) / logx / T + (x ^ c - (x ^ c)⁻¹) / logx / T
            + 2 * (x ^ c)⁻¹ / (T * logx)) := by
          gcongr
          linarith
      _ = x ^ c / (Real.pi * T * |logx|) := by
          rw [hlogxabs]
          field_simp
          ring

/-- **The Perron formula.** For `x > 0` with `x ≠ 1` and `c > 0`, the truncated Perron integral
`perronTruncated x c T` tends to the indicator of `x > 1` as `T → ∞`. -/
theorem tendsto_perronTruncated_atTop {x c : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) (hc : 0 < c) :
    Tendsto (fun T : ℝ => perronTruncated x c T) atTop (𝓝 (if 1 < x then 1 else 0)) := by
  have hpi := Real.pi_pos
  have hL : 0 < |Real.log x| := abs_pos.mpr (log_ne_zero_of_ne_one hx hx1)
  have hg : Tendsto (fun T : ℝ => x ^ c / (Real.pi * T * |Real.log x|)) atTop (𝓝 0) := by
    have h : Tendsto (fun T : ℝ => (x ^ c / (Real.pi * |Real.log x|)) * T⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (x ^ c / (Real.pi * |Real.log x|))
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    field_simp
  refine tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm' ?_ hg)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact norm_perronTruncated_sub_indicator_le hx hx1 hc hT

end ZetaZeros
