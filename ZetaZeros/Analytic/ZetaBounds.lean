/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity
public import ZetaZeros.Meta.Attr

/-!
# Elementary bounds for the zeta function

Facts about the Riemann zeta function that need nothing beyond the Dirichlet series and Abel
summation.

For `re s > 1` the series `∑ n⁻ˢ` is the Stieltjes integral of `u ↦ u^{-s}` against the counting
measure of the positive integers, and integrating by parts turns it into `s ∫₁^∞ ⌊u⌋ u^{-s-1} du`;
the integral converges absolutely because `⌊u⌋ ≤ u`.

Writing `⌊u⌋ = u - {u}` and integrating the `u` half explicitly turns that into
`ζ(s) = s/(s-1) - s ∫₁^∞ {u} u^{-s-1} du`, an identity whose right-hand side is analytic wherever
`re s > 0` and `s ≠ 1`, so it continues `ζ` past the pole. Bounding the two terms crudely on the
strip `1/4 ≤ re s ≤ 4` away from the real axis gives `|ζ(s)| ≤ 13 |im s|`.

On `re s ≥ 2` the Dirichlet series is dominated term by term by `∑ n⁻²`, whose tail from `n = 2` on
telescopes below `3/4`; so `ζ(s)` stays within `3/4` of its first term `1` and `re ζ(s) ≥ 1/4`.

## Main results

* `ZetaZeros.tsum_one_div_nat_cpow_eq_mul_integral_floor`: the Abel integral for `∑ n⁻ˢ`.
* `ZetaZeros.riemannZeta_eq_div_sub_mul_integral_fract`: the fractional-part integral
  representation of `ζ` to the right of the line `re s = 1/10`.
* `ZetaZeros.norm_riemannZeta_le_thirteen_mul_abs_im`: `|ζ(s)| ≤ 13 |im s|` in the strip.
* `ZetaZeros.one_quarter_le_riemannZeta_re`: `re ζ(s) ≥ 1/4` for `re s ≥ 2`.
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter MeasureTheory Set Topology
open scoped ComplexOrder

/-! ### The Abel integral for the Dirichlet series -/

/-- Abel summation for the Dirichlet series of `ζ`: for `re s > 1`,
`∑ n⁻ˢ = s ∫₁^∞ ⌊u⌋ u^{-s-1} du`. -/
@[zz_tag "lem_zeta_series_integral"]
theorem tsum_one_div_nat_cpow_eq_mul_integral_floor {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, 1 / (n : ℂ) ^ s = s * ∫ u in Ioi (1 : ℝ), (⌊u⌋ : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hns : (-s) ≠ 0 := neg_ne_zero.2 hs0
  have hns1 : (-s - 1) ≠ 0 := by
    intro h
    have h1 : (-s - 1).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re] at h1
    linarith
  have hIcc : ∀ n : ℕ, Finset.Icc 0 n = Finset.range (n + 1) := by
    intro n; ext x; simp
  set c : ℕ → ℂ := fun n => if n = 0 then 0 else 1 with hc
  set f : ℝ → ℂ := fun t : ℝ => (t : ℂ) ^ (-s) with hfdef
  have hsumc : ∀ n : ℕ, ∑ k ∈ Finset.Icc 0 n, c k = (n : ℂ) := by
    intro n
    induction n with
    | zero => simp [hc]
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (Nat.zero_le _), ih]
        simp [hc]
  have hderiv : ∀ t : ℝ, t ≠ 0 → HasDerivAt f (-s * (t : ℂ) ^ (-s - 1)) t := fun t ht =>
    hasDerivAt_ofReal_cpow_const ht hns
  have hderiv' : ∀ t : ℝ, 1 ≤ t → deriv f t = -s * (t : ℂ) ^ (-s - 1) := fun t ht =>
    (hderiv t (ne_of_gt (lt_of_lt_of_le zero_lt_one ht))).deriv
  have hdiff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ f t := fun t ht =>
    (hderiv t (ne_of_gt (lt_of_lt_of_le zero_lt_one ht))).differentiableAt
  have hcont : ContinuousOn (deriv f) (Ici (1 : ℝ)) := by
    refine ContinuousOn.congr (f := fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) ?_ ?_
    · intro t ht
      have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
      exact (((hasDerivAt_ofReal_cpow_const ht0 hns1).continuousAt).const_mul
        (-s)).continuousWithinAt
    · intro t ht; exact hderiv' t ht
  have hlocint : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) :=
    hcont.locallyIntegrableOn measurableSet_Ici
  have hlim : Tendsto (fun n : ℕ => f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (𝓝 0) := by
    simp only [hsumc]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h0 : Tendsto (fun x : ℝ => x ^ (-(s.re - 1))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    refine Tendsto.congr' ?_ (h0.comp tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have key : ((n : ℝ)) ^ (-s.re) * (n : ℝ) = ((n : ℝ)) ^ (-(s.re - 1)) := by
      rw [show -(s.re - 1) = -s.re + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
    calc ((n : ℝ)) ^ (-(s.re - 1)) = ((n : ℝ)) ^ (-s.re) * (n : ℝ) := key.symm
      _ = ‖f n‖ * ‖(n : ℂ)‖ := by
          have h5 : ‖f ((n : ℕ) : ℝ)‖ = ((n : ℝ)) ^ ((-s).re) := by
            rw [hfdef]; exact Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-s)
          rw [h5, Complex.neg_re, Complex.norm_natCast]
      _ = ‖f n * (n : ℂ)‖ := (norm_mul _ _).symm
  have hg : (fun t : ℝ => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
      (fun t : ℝ => t ^ (-s.re)) := by
    refine Asymptotics.IsBigO.of_bound ‖s‖ ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
    rw [hsumc, hderiv' t ht]
    have h1 : ‖(-s) * (t : ℂ) ^ (-s - 1) * (⌊t⌋₊ : ℂ)‖
        = ‖s‖ * (t ^ (-s.re - 1) * (⌊t⌋₊ : ℝ)) := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.neg_re, Complex.one_re]
      ring
    have h2 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have h4 : t ^ (-s.re - 1) * t = t ^ (-s.re) := by
      rw [← Real.rpow_add_one (ne_of_gt ht0) (-s.re - 1)]
      congr 1
      ring
    have h3 : t ^ (-s.re - 1) * (⌊t⌋₊ : ℝ) ≤ t ^ (-s.re) :=
      le_of_le_of_eq (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht0.le _)) h4
    rw [h1, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_mul_of_nonneg_left h3 (norm_nonneg s)
  have hgint : IntegrableAtFilter (fun t : ℝ => t ^ (-s.re)) atTop :=
    ⟨Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one⟩
  have main := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c (by simp [hc]) hdiff hlocint hlim
    hg hgint
  have hsummable : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.2 hs
  have hterm : ∀ k : ℕ, f k * c k = 1 / (k : ℂ) ^ s := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hc, hfdef, Complex.zero_cpow hs0]
    · have hcz : c k = 1 := by simp [hc, hk]
      simp only [hcz, hfdef, mul_one, Complex.ofReal_natCast, Complex.cpow_neg, one_div]
  have hlim2 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, f k * c k) atTop
      (𝓝 (∑' n : ℕ, 1 / (n : ℂ) ^ s)) := by
    simp only [hterm]
    refine ((hsummable.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
    simp only [Function.comp_apply, hIcc]
  have heq := tendsto_nhds_unique hlim2 main
  have hint : ∫ t in Ioi (1 : ℝ), deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
      = (-s) * ∫ u in Ioi (1 : ℝ), (⌊u⌋ : ℂ) * (u : ℂ) ^ (-s - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have ht0 : (0 : ℝ) ≤ t := by linarith
    have hfl : ((⌊t⌋₊ : ℕ) : ℂ) = ((⌊t⌋ : ℤ) : ℂ) := by
      rw [← Int.natCast_floor_eq_floor ht0]
      push_cast
      ring
    rw [hsumc, hderiv' t ht1, hfl]
    ring
  rw [heq, hint]
  ring

/-! ### The fractional-part integral representation and the strip bound -/

/-- The integral representation of `ζ` to the right of the line `re s = 1/10`: for `s ≠ 1` with
`re s > 1/10`, `ζ(s) = s/(s-1) - s ∫₁^∞ {u} u^{-s-1} du`, where `{u}` is the fractional part. -/
@[zz_tag "lem_zeta_integral_repr"]
theorem riemannZeta_eq_div_sub_mul_integral_fract {s : ℂ} (hs : s ≠ 1) (hs' : 1 / 10 < s.re) :
    riemannZeta s
      = s / (s - 1) - s * ∫ u in Ioi (1 : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.2 hs
  have hlow : zetaAbelContinuationReLower < s.re := by
    change (1 / 10 : ℝ) < s.re
    exact hs'
  have key : s / (s - 1) = 1 + 1 / (s - 1) := by
    field_simp
    ring
  rw [riemannZeta_eq_zetaAbelContinuationFormula s ⟨hs, hlow⟩, zetaAbelContinuationFormula, key]
  simp only [zetaAbelFractKernel]

/-- Polynomial growth in the strip: for `1/4 ≤ re s ≤ 4` and `|im s| ≥ 2` one has
`‖ζ s‖ ≤ 13 |im s|`. -/
@[zz_tag "lem_zeta_strip_bound"]
theorem norm_riemannZeta_le_thirteen_mul_abs_im {s : ℂ} (hre : 1 / 4 ≤ s.re) (hre' : s.re ≤ 4)
    (him : 2 ≤ |s.im|) : ‖riemannZeta s‖ ≤ 13 * |s.im| := by
  have hne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_im, abs_zero] at him
    linarith
  have hlow : zetaAbelContinuationReLower < s.re := by
    change (1 / 10 : ℝ) < s.re
    linarith
  have hmain := norm_riemannZeta_le s ⟨hne, hlow⟩
  have hs1 : (2 : ℝ) ≤ ‖s - 1‖ :=
    him.trans (by simpa [Complex.sub_im, Complex.one_im] using Complex.abs_im_le_norm (s - 1))
  have hinv : ‖1 / (s - 1)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by norm_num) hs1
  have hrepos : (0 : ℝ) < s.re := by linarith
  have hnorm : ‖s‖ ≤ 3 * |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    have habs : |s.re| ≤ 4 := abs_le.2 ⟨by linarith, hre'⟩
    linarith
  have haux : 0 ≤ |s.im| * (4 * s.re - 1) := mul_nonneg (abs_nonneg _) (by linarith)
  have hdiv : ‖s‖ / s.re ≤ 12 * |s.im| := by
    rw [div_le_iff₀ hrepos]
    nlinarith
  linarith

/-! ### The lower bound for `re ζ` on `re s ≥ 2` -/

/-- The tail of `∑ n⁻²` from `n = 2` on is at most `3/4`: the term `n = 2` contributes `1/4` and
the terms from `n = 3` on telescope below `1/2`. -/
private lemma sum_range_succ_one_div_add_two_sq_le (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / ((i : ℝ) + 2) ^ 2 ≤ 3 / 4 - 1 / ((M : ℝ) + 2) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hx : (0 : ℝ) < (M : ℝ) + 2 := by positivity
      have hy : (0 : ℝ) < (M : ℝ) + 3 := by positivity
      have h1 : (1 : ℝ) / ((M : ℝ) + 3) ^ 2 ≤ 1 / ((M : ℝ) + 2) - 1 / ((M : ℝ) + 3) := by
        have h2 : 1 / ((M : ℝ) + 2) - 1 / ((M : ℝ) + 3) = 1 / (((M : ℝ) + 2) * ((M : ℝ) + 3)) := by
          field_simp
          ring
        rw [h2]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have h3 : ((M : ℝ) + 1) + 2 = (M : ℝ) + 3 := by ring
      push_cast
      rw [h3]
      linarith

private lemma sum_range_one_div_add_two_sq_le (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 2) ^ 2 ≤ 3 / 4 := by
  cases N with
  | zero => norm_num
  | succ M =>
      have h := sum_range_succ_one_div_add_two_sq_le M
      have h0 : (0 : ℝ) < 1 / ((M : ℝ) + 2) := by positivity
      linarith

private lemma summable_one_div_add_two_sq :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2) ^ 2) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) :=
    Real.summable_one_div_nat_pow.2 one_lt_two
  have h2 := (summable_nat_add_iff 2).2 h
  simpa using h2

/-- On `re s ≥ 2` the Dirichlet series of `ζ` is within `3/4` of its first term, so the real part
of `ζ` is at least `1/4`. -/
@[zz_tag "lem_zeta_two_re_lower"]
theorem one_quarter_le_riemannZeta_re {s : ℂ} (hs : 2 ≤ s.re) : 1 / 4 ≤ (riemannZeta s).re := by
  have hs1 : (1 : ℝ) < s.re := by linarith
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hfdef
  have hsum : Summable f := by
    have h := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs1)
    simpa [hfdef] using h
  have hz : riemannZeta s = ∑' n : ℕ, f n := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hf0 : f 0 = 1 := by simp [hfdef]
  have hzT : riemannZeta s = 1 + ∑' n : ℕ, f (n + 1) := by
    rw [hz, hsum.tsum_eq_zero_add, hf0]
  have hbound : ∀ n : ℕ, ‖f (n + 1)‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
    intro n
    have hb : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hcast : f (n + 1) = 1 / ((((n : ℝ) + 2 : ℝ) : ℂ)) ^ s := by
      simp only [hfdef]
      push_cast
      ring_nf
    have hnorm : ‖f (n + 1)‖ = ((n : ℝ) + 2) ^ (-s.re) := by
      rw [hcast, norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos hb, one_div,
        ← Real.rpow_neg hb.le]
    have h2 : ((n : ℝ) + 2) ^ (-s.re) ≤ ((n : ℝ) + 2) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : ((n : ℝ) + 2) ^ (-2 : ℝ) = 1 / ((n : ℝ) + 2) ^ 2 := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hb.le, Real.rpow_natCast,
        one_div]
    rw [hnorm, ← h3]
    exact h2
  have hnormsum : Summable (fun n : ℕ => ‖f (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound summable_one_div_add_two_sq
  have hTnorm : ‖∑' n : ℕ, f (n + 1)‖ ≤ 3 / 4 := by
    calc ‖∑' n : ℕ, f (n + 1)‖ ≤ ∑' n : ℕ, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hnormsum
      _ ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 2) ^ 2 :=
          hnormsum.tsum_le_tsum hbound summable_one_div_add_two_sq
      _ ≤ 3 / 4 := Real.tsum_le_of_sum_range_le (fun n => by positivity)
          sum_range_one_div_add_two_sq_le
  have hre : (riemannZeta s).re = 1 + (∑' n : ℕ, f (n + 1)).re := by rw [hzT]; simp
  have hlow : -‖∑' n : ℕ, f (n + 1)‖ ≤ (∑' n : ℕ, f (n + 1)).re :=
    neg_le_of_abs_le (Complex.abs_re_le_norm _)
  rw [hre]
  linarith

end ZetaZeros

end
