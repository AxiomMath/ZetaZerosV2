/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Landau.Kernel

/-!
# The left edge of the Landau contour

The left edge `re w = -(2N + 1)` of the rectangle of
`ZetaZeros.rectangleIntegral_landauKernel_eq`, at height `U`. For `x > 1` the factor
`‖x^{w-s}‖ = x^{-(2N+1) - re s}` decays geometrically in `N`, the edge has length `2U`, and
`ZetaZeros.exists_norm_deriv_riemannZeta_div_le_of_re_eq_neg_odd` bounds `ζ'/ζ` by `log (‖w‖ + 2)`
at every height on this line. The odd abscissa carries no trivial zero, since those sit at the even
negative integers.

## Main results

* `ZetaZeros.norm_integral_landauKernel_left_le`: **the explicit bound**,
  `‖∫_{-U}^{U} K (-(2N+1) + iy) dy‖ ≤ 2U ⬝ C (2N + 3 + U) ⬝ x^{-(2N+1) - re s}`.
* `ZetaZeros.tendsto_integral_landauKernel_left`: **the left edge vanishes** as `N → ∞` at fixed
  `U`.
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter Topology

/-! ### The left edge -/

/-- On the line `re w = -(2N+1)` the kernel is continuous: an odd negative abscissa carries no
trivial zero (those sit at the even ones), the pole of `ζ` is to the right, and so is `s`. -/
private lemma continuous_landauKernel_left {x : ℝ} (hx : 0 < x) {s : ℂ} {N : ℕ}
    (hNs : -(2 * (N : ℝ) + 1) < s.re) :
    Continuous fun y : ℝ =>
      landauKernel x s ((-(2 * (N : ℝ) + 1) : ℝ) + (y : ℂ) * I) := by
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hre : (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (y : ℂ) * I).re = -(2 * (N : ℝ) + 1) := by simp
  have h1 : ((-(2 * (N : ℝ) + 1) : ℝ) + (y : ℂ) * I) ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hre; linarith
  have hz : riemannZeta ((-(2 * (N : ℝ) + 1) : ℝ) + (y : ℂ) * I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_re_nonpos (by rw [hre]; linarith) fun n hn => ?_
    have hn' : -(2 * (N : ℝ) + 1) = -2 * ((n : ℝ) + 1) := by
      have h := congrArg Complex.re hn
      rw [hre] at h
      simpa using h
    have hcast : 2 * N + 1 = 2 * n + 2 := by
      have h2 : 2 * (N : ℝ) + 1 = 2 * (n : ℝ) + 2 := by linarith
      exact_mod_cast h2
    omega
  have hs : ((-(2 * (N : ℝ) + 1) : ℝ) + (y : ℂ) * I) ≠ s := fun h => by
    rw [h] at hre; linarith
  exact (analyticAt_landauKernel hx h1 hz hs).continuousAt.comp
    (f := fun y : ℝ => ((-(2 * (N : ℝ) + 1) : ℝ) + (y : ℂ) * I)) (by fun_prop)

/-- **The explicit bound for the left edge.** For `x > 1`, a height `U ≥ 0` and `N` large enough
that the line `re w = -(2N+1)` lies to the left of `s`,

`‖∫_{-U}^{U} K (-(2N+1) + iy) dy‖ ≤ 2U ⬝ C (2N + 3 + U) ⬝ x^{-(2N+1) - re s}`,

`C` being the constant of
`ZetaZeros.exists_norm_deriv_riemannZeta_div_le_of_re_eq_neg_odd`. -/
theorem norm_integral_landauKernel_left_le {x : ℝ} (hx : 1 < x) {s : ℂ} {U : ℝ} (hU : 0 ≤ U)
    {N : ℕ} (hN : |s.re| + 1 ≤ (N : ℝ)) {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ (m : ℕ) (w : ℂ), w.re = -(2 * (m : ℝ) + 1) →
      ‖deriv riemannZeta w / riemannZeta w‖ ≤ C * Real.log (‖w‖ + 2)) :
    ‖∫ y in (-U)..U, landauKernel x s ((-(2 * (N : ℝ) + 1) : ℝ) + (y : ℂ) * I)‖
      ≤ 2 * U * (C * (2 * (N : ℝ) + 3 + U)) * x ^ (-(2 * (N : ℝ) + 1) - s.re) := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsre : -s.re ≤ |s.re| := neg_le_abs _
  have hD1 : (1 : ℝ) ≤ s.re + (2 * (N : ℝ) + 1) := by linarith
  have hCbnd : ∀ y : ℝ, |y| ≤ U →
      ‖landauKernel x s ((-(2 * (N : ℝ) + 1) : ℝ) + (y : ℂ) * I)‖
        ≤ C * (2 * (N : ℝ) + 3 + U) * x ^ (-(2 * (N : ℝ) + 1) - s.re) := by
    intro y hy
    set w : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (y : ℂ) * I with hw
    have hre : w.re = -(2 * (N : ℝ) + 1) := by rw [hw]; simp
    have him : w.im = y := by rw [hw]; simp
    have hsubre : (w - s).re = -(2 * (N : ℝ) + 1) - s.re := by rw [Complex.sub_re, hre]
    have hDw : s.re + (2 * (N : ℝ) + 1) ≤ ‖w - s‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm (w - s))
      rw [hsubre, abs_of_nonpos (by linarith)]
      linarith
    have hzeta : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C * (2 * (N : ℝ) + 3 + U) := by
      refine le_trans (hC N w hre) ?_
      have hw2 : ‖w‖ ≤ 2 * (N : ℝ) + 1 + U := by
        refine le_trans (Complex.norm_le_abs_re_add_abs_im w) ?_
        rw [hre, him, abs_of_nonpos (by linarith)]
        linarith [abs_nonneg y]
      have hlog : Real.log (‖w‖ + 2) ≤ 2 * (N : ℝ) + 3 + U := by
        refine le_trans (Real.log_le_sub_one_of_pos (by positivity)) ?_
        linarith
      exact mul_le_mul_of_nonneg_left hlog hC0.le
    refine le_trans (norm_landauKernel_le hx0 hzeta (by linarith) hDw) ?_
    rw [hsubre, div_le_iff₀ (by linarith)]
    have hE : (0 : ℝ) ≤ C * (2 * (N : ℝ) + 3 + U) * x ^ (-(2 * (N : ℝ) + 1) - s.re) :=
      mul_nonneg (mul_nonneg hC0.le (by linarith)) (Real.rpow_pos_of_pos hx0 _).le
    exact le_mul_of_one_le_right hE hD1
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := C * (2 * (N : ℝ) + 3 + U) * x ^ (-(2 * (N : ℝ) + 1) - s.re)) fun y hy => ?_) ?_
  · refine hCbnd y ?_
    rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hy
    exact abs_le.2 ⟨hy.1.le, hy.2⟩
  · rw [show |U - -U| = 2 * U from by
      rw [show U - -U = 2 * U from by ring, abs_of_nonneg (by linarith)]]
    apply le_of_eq
    ring

/-- **The left edge of the contour vanishes.** For `x > 1`, any `s` and any fixed height `U ≥ 0`,

`∫_{-U}^{U} K (-(2N+1) + iy) dy → 0` as `N → ∞`. -/
theorem tendsto_integral_landauKernel_left {x : ℝ} (hx : 1 < x) (s : ℂ) {U : ℝ} (hU : 0 ≤ U)
    :
    Tendsto (fun N : ℕ =>
        ∫ y in (-U)..U, landauKernel x s ((-(2 * (N : ℝ) + 1) : ℝ) + (y : ℂ) * I))
      atTop (nhds 0) := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  obtain ⟨C, hC0, hC⟩ := exists_norm_deriv_riemannZeta_div_le_of_re_eq_neg_odd
  set q : ℝ := x ^ (-2 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hx0 _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have hxpow : ∀ N : ℕ, x ^ (-(2 * (N : ℝ) + 1) - s.re) = x ^ (-1 - s.re) * q ^ N := by
    intro N
    rw [hq, ← Real.rpow_natCast (x ^ (-2 : ℝ)) N, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    ring
  have hgeo : Tendsto (fun N : ℕ => (2 * (N : ℝ) + 3 + U) * q ^ N) atTop (nhds 0) := by
    have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hq0]
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) * q ^ N) atTop (nhds 0) := by
      simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).tendsto_atTop_zero
    have h2 : Tendsto (fun N : ℕ => q ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
    have h3 := (h1.const_mul (2 : ℝ)).add (h2.const_mul (3 + U))
    rw [show (0 : ℝ) = 2 * 0 + (3 + U) * 0 from by ring]
    exact h3.congr fun N => by ring
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖∫ y in (-U)..U, landauKernel x s ((-(2 * (N : ℝ) + 1) : ℝ) + (y : ℂ) * I)‖
        ≤ 2 * U * (C * x ^ (-1 - s.re)) * ((2 * (N : ℝ) + 3 + U) * q ^ N) := by
    filter_upwards [Filter.eventually_ge_atTop (⌈|s.re|⌉₊ + 1)] with N hN
    have hNr : |s.re| + 1 ≤ (N : ℝ) := by
      have h1 : (|s.re| : ℝ) ≤ (⌈|s.re|⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈|s.re|⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.2 hN
      push_cast at h2
      linarith
    refine le_trans (norm_integral_landauKernel_left_le hx hU hNr hC0 hC) ?_
    rw [hxpow N]
    apply le_of_eq
    ring
  exact squeeze_zero_norm' hbound (by simpa using hgeo.const_mul (2 * U * (C * x ^ (-1 - s.re))))

end ZetaZeros
