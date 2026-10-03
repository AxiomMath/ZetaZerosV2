/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Landau.Kernel

/-!
# The horizontal edges of the Landau contour

The horizontal edges `im w = ± U` of the rectangle of
`ZetaZeros.rectangleIntegral_landauKernel_eq`. At a height `U` separated from every zero ordinate
by `g`, and for every left abscissa `a ≤ -1`,

`‖∫_a^b K (σ + iU) dσ‖ ≤ E ⬝ log (|U| + 3) ⬝ (1 + 1/g) / (|U| - |im s|)`,

with `E` independent of `a`; this is `ZetaZeros.exists_norm_integral_landauKernel_horizontal_le`.
At the heights of `ZetaZeros.exists_height_far_from_zeros`, where `g ≍ 1 / log U`, the right side
is `O (log² U / U)`.

## Main results

* `ZetaZeros.gap_sub_im_of_gap_abs`, `ZetaZeros.abs_im_ne_of_gap`: consequences of a height being
  separated from the zero ordinates in the sense of `ZetaZeros.exists_height_far_from_zeros`.
* `ZetaZeros.exists_norm_logDeriv_riemannZeta_le_of_gap`: **`ζ'/ζ` on a gapped horizontal line**,
  `≪ log (|im w| + 3) (1 + 1/g)` on `-1 ≤ re w ≤ 3/2`.
* `ZetaZeros.integral_rpow_le`, `ZetaZeros.integral_sub_mul_rpow_le`:
  `∫_a^b x^σ dσ ≤ x^b / log x` and `∫_a^b (b - σ) x^σ dσ ≤ x^b / log² x`, neither depending on `a`.
* `ZetaZeros.exists_norm_integral_landauKernel_horizontal_le`: **the horizontal edges**,
  `≪ log (|U| + 3) (1 + 1/g) / (|U| - |im s|)`, uniformly in the left abscissa.
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter Topology

/-! ### Heights separated from the zero ordinates -/

/-- **The single gap statement covers both horizontal edges.** Let `|U| ≥ 3` and suppose every
zero `ρ` of the strip satisfies `g ≤ |(|U| - |im ρ|)|`. Then every `ρ ∈ 𝒩*` with
`|U - im ρ| ≤ 1` satisfies `g ≤ |U - im ρ|`. -/
theorem gap_sub_im_of_gap_abs {U g : ℝ} (hU : 3 ≤ |U|)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → g ≤ |(|U| - |ρ.im|)|)
    {ρ : ℂ} (hρ : ρ ∈ allZeros) (hwin : |U - ρ.im| ≤ 1) : g ≤ |U - ρ.im| := by
  obtain ⟨hz, h0, h1⟩ := hρ
  have hg := hgap ρ hz h0 h1
  obtain ⟨hw₁, hw₂⟩ := abs_le.1 hwin
  rcases abs_cases U with ⟨hUa, hUpos⟩ | ⟨hUa, hUneg⟩
  · have hρim : 0 < ρ.im := by rw [hUa] at hU; linarith
    rwa [hUa, abs_of_pos hρim] at hg
  · have hρim : ρ.im < 0 := by rw [hUa] at hU; linarith
    rw [hUa, abs_of_neg hρim, show -U - -ρ.im = -(U - ρ.im) from by ring, abs_neg] at hg
    exact hg

/-- **`ζ` does not vanish on a gapped horizontal line.** If `|U| ≥ 3`, `g > 0` and every zero `ρ`
of the strip satisfies `g ≤ |(|U| - |im ρ|)|`, then `ζ` has no zero on the line `im w = U`. -/
private theorem riemannZeta_ne_zero_of_gap {U g : ℝ} (hU : 3 ≤ |U|) (hg : 0 < g)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → g ≤ |(|U| - |ρ.im|)|)
    {w : ℂ} (hw : w.im = U) : riemannZeta w ≠ 0 := by
  intro hz
  rcases le_or_gt 1 w.re with hre | hre
  · exact riemannZeta_ne_zero_of_one_le_re hre hz
  rcases le_or_gt w.re 0 with hre0 | hre0
  · obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hre0).1 hz
    have him : w.im = 0 := by rw [hn]; simp
    rw [hw] at him
    rw [him] at hU
    norm_num at hU
  · have := hgap w hz hre0 hre
    rw [hw, sub_self, abs_zero] at this
    linarith

/-- **`ζ'/ζ` on a horizontal line separated from the ordinates.** If every zero of the strip has
`g ≤ |(|im w| - |im ρ|)|`, then on the part of the line lying in `-1 ≤ re w ≤ 3/2`

`‖(ζ'/ζ) (w)‖ ≤ C ⬝ log (|im w| + 3) ⬝ (1 + 1/g)`,

with an absolute `C`. -/
theorem exists_norm_logDeriv_riemannZeta_le_of_gap :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ, 0 < g → ∀ w : ℂ, 3 ≤ |w.im| → -1 ≤ w.re → w.re ≤ 3 / 2 →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → g ≤ |(|w.im| - |ρ.im|)|) →
        ‖deriv riemannZeta w / riemannZeta w‖
          ≤ C * Real.log (|w.im| + 3) * (1 + 1 / g) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_deriv_riemannZeta_div_sub_tsum_near_le
  obtain ⟨C₂, hC₂, h₂⟩ := exists_summable_poissonWeight_tsum_le
  refine ⟨C₁ + 2 * C₂, by linarith, fun g hg w him hre₁ hre₂ hgap => ?_⟩
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_gap him hg hgap rfl
  have hL : 0 < Real.log (|w.im| + 3) := Real.log_pos (by linarith)
  obtain ⟨hsum, hbnd⟩ := h₂ w.im
  have key := h₁ w him hre₁ hre₂ hzw
  set S : Set allZeros := {ρ : allZeros | |w.im - (ρ : ℂ).im| ≤ 1} with hS
  have hSfin : S.Finite := by
    refine (heightWindow_finite (|w.im| + 1)).subset fun ρ hρ => ?_
    have h1 : |((ρ : ℂ)).im| - |w.im| ≤ |((ρ : ℂ)).im - w.im| :=
      abs_sub_abs_le_abs_sub _ _
    have h2 : |((ρ : ℂ)).im - w.im| = |w.im - ((ρ : ℂ)).im| := abs_sub_comm _ _
    have h3 : |w.im - ((ρ : ℂ)).im| ≤ 1 := hρ
    exact Set.mem_ofPred_eq ▸ by linarith
  have : Finite S := hSfin.to_subtype
  have hterm : ∀ ρ : S,
      ‖(zeroMultiplicity (((ρ : allZeros)) : ℂ) : ℂ) / (w - (((ρ : allZeros)) : ℂ))‖
        ≤ 2 / g * ((zeroMultiplicity (((ρ : allZeros)) : ℂ) : ℝ)
            / (1 + (w.im - (((ρ : allZeros)) : ℂ).im) ^ 2)) := by
    intro ρ
    have hwin : |w.im - (((ρ : allZeros)) : ℂ).im| ≤ 1 := ρ.2
    have hgap' : g ≤ |w.im - (((ρ : allZeros)) : ℂ).im| :=
      gap_sub_im_of_gap_abs him hgap ((ρ : allZeros)).2 hwin
    have hnorm : g ≤ ‖w - (((ρ : allZeros)) : ℂ)‖ := by
      refine le_trans hgap' ?_
      have h := Complex.abs_im_le_norm (w - (((ρ : allZeros)) : ℂ))
      rwa [Complex.sub_im] at h
    obtain ⟨hw₁, hw₂⟩ := abs_le.1 hwin
    have hd : (w.im - (((ρ : allZeros)) : ℂ).im) ^ 2 ≤ 1 := by nlinarith
    have hm0 : (0 : ℝ) ≤ (zeroMultiplicity (((ρ : allZeros)) : ℂ) : ℝ) := Nat.cast_nonneg _
    rw [norm_div, Complex.norm_natCast]
    refine le_trans (div_le_div_of_nonneg_left hm0 hg hnorm) ?_
    rw [div_mul_div_comm, div_le_div_iff₀ hg (by positivity)]
    nlinarith [mul_nonneg hm0 hg.le]
  have hwindow : ‖∑' ρ : S, (zeroMultiplicity (((ρ : allZeros)) : ℂ) : ℂ)
      / (w - (((ρ : allZeros)) : ℂ))‖ ≤ 2 / g * (C₂ * Real.log (|w.im| + 3)) := by
    refine le_trans (norm_tsum_le_tsum_norm (Summable.of_finite)) ?_
    refine le_trans (Summable.tsum_le_tsum hterm Summable.of_finite Summable.of_finite) ?_
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hbnd) (by positivity)
    exact Summable.tsum_subtype_le _ S
      (fun ρ => by positivity) hsum
  have hAB : ‖deriv riemannZeta w / riemannZeta w‖
      ≤ ‖deriv riemannZeta w / riemannZeta w
          - ∑' ρ : S, (zeroMultiplicity (((ρ : allZeros)) : ℂ) : ℂ)
              / (w - (((ρ : allZeros)) : ℂ))‖
        + ‖∑' ρ : S, (zeroMultiplicity (((ρ : allZeros)) : ℂ) : ℂ)
              / (w - (((ρ : allZeros)) : ℂ))‖ := by
    simpa using norm_add_le (deriv riemannZeta w / riemannZeta w
        - ∑' ρ : S, (zeroMultiplicity (((ρ : allZeros)) : ℂ) : ℂ) / (w - (((ρ : allZeros)) : ℂ)))
      (∑' ρ : S, (zeroMultiplicity (((ρ : allZeros)) : ℂ) : ℂ) / (w - (((ρ : allZeros)) : ℂ)))
  refine le_trans hAB (le_trans (add_le_add key hwindow) ?_)
  have hginv : 0 < 1 / g := by positivity
  have hle₁ : C₁ * Real.log (|w.im| + 3)
      ≤ (C₁ + 2 * C₂) * Real.log (|w.im| + 3) := by nlinarith
  have hle₂ : 2 / g * (C₂ * Real.log (|w.im| + 3))
      ≤ (C₁ + 2 * C₂) * Real.log (|w.im| + 3) * (1 / g) := by
    rw [div_mul_eq_mul_div, mul_comm ((C₁ + 2 * C₂) * Real.log (|w.im| + 3)) (1 / g),
      one_div, inv_mul_eq_div, div_le_div_iff₀ hg hg]
    nlinarith [mul_pos (mul_pos hC₁ hL) hg]
  have hexp : (C₁ + 2 * C₂) * Real.log (|w.im| + 3) * (1 + 1 / g)
      = (C₁ + 2 * C₂) * Real.log (|w.im| + 3)
        + (C₁ + 2 * C₂) * Real.log (|w.im| + 3) * (1 / g) := by ring
  linarith

/-! ### The horizontal edges -/

/-- `log (A + u) ≤ log A + u` for `A ≥ 1` and `u ≥ 0`. -/
private lemma log_add_le {A u : ℝ} (hA : 1 ≤ A) (hu : 0 ≤ u) :
    Real.log (A + u) ≤ Real.log A + u := by
  have hA0 : (0 : ℝ) < A := by linarith
  rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add, Real.exp_log hA0]
  nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp u) hA0.le,
    mul_nonneg (sub_nonneg.2 hA) hu]

/-- `∫_a^b x^σ dσ ≤ x^b / log x` for `x > 1` and all real `a`, `b`. -/
theorem integral_rpow_le {x : ℝ} (hx : 1 < x) (a b : ℝ) :
    (∫ σ in a..b, x ^ σ) ≤ x ^ b / Real.log x := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hcont : Continuous fun σ : ℝ => x ^ σ := by
    simp only [Real.rpow_def_of_pos hx0]
    fun_prop
  have hderiv : ∀ σ ∈ Set.uIcc a b,
      HasDerivAt (fun σ : ℝ => x ^ σ / Real.log x) (x ^ σ) σ := by
    intro σ _
    have h := ((Real.hasStrictDerivAt_const_rpow hx0 σ).hasDerivAt).div_const (Real.log x)
    rwa [mul_div_assoc, div_self hlog.ne', mul_one] at h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)]
  have h2 : 0 ≤ x ^ a / Real.log x := by positivity
  linarith

/-- `∫_a^b (b - σ) x^σ dσ ≤ x^b / log² x` for `x > 1` and `a ≤ b`. -/
theorem integral_sub_mul_rpow_le {x : ℝ} (hx : 1 < x) {a b : ℝ} (hab : a ≤ b) :
    (∫ σ in a..b, (b - σ) * x ^ σ) ≤ x ^ b / Real.log x ^ 2 := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hrc : Continuous fun σ : ℝ => x ^ σ := by
    simp only [Real.rpow_def_of_pos hx0]
    fun_prop
  have hcont : Continuous fun σ : ℝ => (b - σ) * x ^ σ := by fun_prop
  have hderiv : ∀ σ ∈ Set.uIcc a b,
      HasDerivAt (fun σ : ℝ => (b - σ) * x ^ σ / Real.log x + x ^ σ / Real.log x ^ 2)
        ((b - σ) * x ^ σ) σ := by
    intro σ _
    have h0 : HasDerivAt (fun σ : ℝ => x ^ σ) (x ^ σ * Real.log x) σ :=
      (Real.hasStrictDerivAt_const_rpow hx0 σ).hasDerivAt
    have h1 : HasDerivAt (fun σ : ℝ => (b - σ) * x ^ σ)
        ((0 - 1) * x ^ σ + (b - σ) * (x ^ σ * Real.log x)) σ :=
      ((hasDerivAt_const σ b).sub (hasDerivAt_id σ)).mul h0
    have h2 := (h1.div_const (Real.log x)).add (h0.div_const (Real.log x ^ 2))
    refine h2.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)]
  have hxa : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx0 a
  have h3 : 0 ≤ (b - a) * x ^ a / Real.log x :=
    div_nonneg (mul_nonneg (by linarith) hxa.le) hlog.le
  have h4 : 0 < x ^ a / Real.log x ^ 2 := div_pos hxa (pow_pos hlog 2)
  simp only [sub_self, zero_mul, zero_div, zero_add]
  linarith

/-- **On a gapped horizontal line the kernel is continuous.** The line `im w = U` with `|U| ≥ 3`
carries no zero of `ζ` (`ZetaZeros.riemannZeta_ne_zero_of_gap`), not the pole (whose ordinate is
`0`), and not `s` (whose ordinate is smaller in absolute value). -/
private lemma continuous_landauKernel_horizontal {x : ℝ} (hx : 0 < x) {s : ℂ} {U gp : ℝ}
    (hU : 3 ≤ |U|) (hgp : 0 < gp) (hsU : |s.im| < |U|)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → gp ≤ |(|U| - |ρ.im|)|) :
    Continuous fun σ : ℝ => landauKernel x s ((σ : ℂ) + (U : ℂ) * I) := by
  refine continuous_iff_continuousAt.2 fun σ => ?_
  have him : (((σ : ℝ) : ℂ) + (U : ℂ) * I).im = U := by simp
  have hU0 : U ≠ 0 := fun h => by rw [h] at hU; norm_num at hU
  have h1 : (((σ : ℝ) : ℂ) + (U : ℂ) * I) ≠ 1 := fun h => by
    rw [h, Complex.one_im] at him; exact hU0 him.symm
  have hz : riemannZeta (((σ : ℝ) : ℂ) + (U : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_gap hU hgp hgap him
  have hs : (((σ : ℝ) : ℂ) + (U : ℂ) * I) ≠ s := fun h => by
    rw [h] at him
    rw [him] at hsU
    exact lt_irrefl _ hsU
  exact (analyticAt_landauKernel hx h1 hz hs).continuousAt.comp
    (f := fun σ : ℝ => (((σ : ℝ) : ℂ) + (U : ℂ) * I)) (by fun_prop)

/-- **A gapped height is the ordinate of no zero.** If every zero of the strip satisfies
`gp ≤ |(|U| - |im ρ|)|` with `gp > 0`, then no zero of `ζ` at all has `|im ρ| = U`. -/
theorem abs_im_ne_of_gap {U gp : ℝ} (hU : 3 ≤ U) (hgp : 0 < gp)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → gp ≤ |(|U| - |ρ.im|)|)
    {ρ : ℂ} (hz : riemannZeta ρ = 0) : |ρ.im| ≠ U := by
  intro him
  rcases le_or_gt 1 ρ.re with hre | hre
  · exact riemannZeta_ne_zero_of_one_le_re hre hz
  rcases le_or_gt ρ.re 0 with hre0 | hre0
  · obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hre0).1 hz
    have h0 : ρ.im = 0 := by rw [hn]; simp
    rw [h0, abs_zero] at him
    linarith
  · have h := hgap ρ hz hre0 hre
    rw [him, abs_of_nonneg (by linarith : (0 : ℝ) ≤ U), sub_self, abs_zero] at h
    linarith

/-- **The horizontal edges of the contour.** For `x > 1`, a right abscissa `b ≥ 3/2` and a height
`U` separated from every zero ordinate by `gp`,

`‖∫_a^b K (σ + iU) dσ‖ ≤ E ⬝ log (|U| + 3) ⬝ (1 + 1/gp) / (|U| - |im s|)`,

with `E` depending on `x`, `s` and `b` but **not on the left abscissa `a`**. -/
theorem exists_norm_integral_landauKernel_horizontal_le {x : ℝ} (hx : 1 < x) (s : ℂ) {b : ℝ}
    (hb : 3 / 2 ≤ b) :
    ∃ E : ℝ, 0 < E ∧ ∀ U gp a : ℝ, 3 ≤ |U| → 0 < gp → |s.im| + 1 ≤ |U| → a ≤ -1 →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → gp ≤ |(|U| - |ρ.im|)|) →
        ‖∫ σ in a..b, landauKernel x s ((σ : ℂ) + (U : ℂ) * I)‖
          ≤ E * Real.log (|U| + 3) * (1 + 1 / gp) / (|U| - |s.im|) := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hLx : 0 < Real.log x := Real.log_pos hx
  have hrpowc : Continuous fun σ : ℝ => x ^ σ := by
    simp only [Real.rpow_def_of_pos hx0]
    fun_prop
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_deriv_riemannZeta_div_le_of_re_le_neg_one
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_logDeriv_riemannZeta_le_of_gap
  obtain ⟨A₀, hA₀, h₃⟩ := exists_norm_deriv_riemannZeta_div_le_of_three_halves_le_re
  set X : ℝ := x ^ (-s.re) with hXdef
  have hX0 : 0 < X := Real.rpow_pos_of_pos hx0 _
  set P₁ : ℝ := C₁ * X * x ^ (-1 : ℝ) * (1 / Real.log x + 1 / Real.log x ^ 2) with hP₁def
  set P₂ : ℝ := C₂ * X * x ^ (3 / 2 : ℝ) / Real.log x with hP₂def
  set P₃ : ℝ := A₀ * X * x ^ b / Real.log x with hP₃def
  have hP₁ : 0 < P₁ := by
    rw [hP₁def]
    exact mul_pos (mul_pos (mul_pos hC₁ hX0) (Real.rpow_pos_of_pos hx0 _))
      (add_pos (one_div_pos.2 hLx) (one_div_pos.2 (pow_pos hLx 2)))
  have hP₂ : 0 < P₂ :=
    hP₂def ▸ div_pos (mul_pos (mul_pos hC₂ hX0) (Real.rpow_pos_of_pos hx0 _)) hLx
  have hP₃ : 0 < P₃ :=
    hP₃def ▸ div_pos (mul_pos (mul_pos hA₀ hX0) (Real.rpow_pos_of_pos hx0 _)) hLx
  refine ⟨P₁ + P₂ + P₃, by linarith, fun U gp a hU hgp hsU ha hgap => ?_⟩
  have hsU' : |s.im| < |U| := by linarith
  have hD : (0 : ℝ) < |U| - |s.im| := by linarith
  have hLU : (1 : ℝ) ≤ Real.log (|U| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hgp1 : (1 : ℝ) ≤ 1 + 1 / gp := by
    have h : 0 < 1 / gp := by positivity
    linarith
  have hcont : Continuous fun σ : ℝ => landauKernel x s ((σ : ℂ) + (U : ℂ) * I) :=
    continuous_landauKernel_horizontal hx0 hU hgp hsU' hgap
  have hint : ∀ p q : ℝ, IntervalIntegrable
      (fun σ : ℝ => landauKernel x s ((σ : ℂ) + (U : ℂ) * I)) MeasureTheory.volume p q :=
    fun p q => hcont.intervalIntegrable p q
  have hwre : ∀ σ : ℝ, ((σ : ℂ) + (U : ℂ) * I).re = σ := fun σ => by simp
  have hwim : ∀ σ : ℝ, ((σ : ℂ) + (U : ℂ) * I).im = U := fun σ => by simp
  have hker : ∀ σ A' : ℝ, ‖deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I)
        / riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ A' →
      ‖landauKernel x s ((σ : ℂ) + (U : ℂ) * I)‖ ≤ A' * (x ^ σ * X) / (|U| - |s.im|) := by
    intro σ A' hA'
    have hsubim : ((σ : ℂ) + (U : ℂ) * I - s).im = U - s.im := by simp
    have hsubre : ((σ : ℂ) + (U : ℂ) * I - s).re = σ - s.re := by simp
    have hDw : |U| - |s.im| ≤ ‖(σ : ℂ) + (U : ℂ) * I - s‖ := by
      have hh := Complex.abs_im_le_norm ((σ : ℂ) + (U : ℂ) * I - s)
      rw [hsubim] at hh
      linarith [abs_sub_abs_le_abs_sub U s.im]
    have hpow : x ^ ((σ : ℂ) + (U : ℂ) * I - s).re = x ^ σ * X := by
      rw [hsubre, hXdef, show σ - s.re = σ + -s.re from by ring, Real.rpow_add hx0]
    have hh := norm_landauKernel_le hx0 hA' hD hDw
    rwa [hpow] at hh
  have hnorm : ∀ (p q : ℝ) (G : ℝ → ℝ), p ≤ q → Continuous G →
      (∀ σ ∈ Set.Icc p q, ‖landauKernel x s ((σ : ℂ) + (U : ℂ) * I)‖ ≤ G σ) →
      ‖∫ σ in p..q, landauKernel x s ((σ : ℂ) + (U : ℂ) * I)‖ ≤ ∫ σ in p..q, G σ :=
    fun p q G hpq hGc hG => intervalIntegral.norm_integral_le_of_norm_le hpq
      (Filter.Eventually.of_forall fun t ht => hG t (Set.Ioc_subset_Icc_self ht))
      (hGc.intervalIntegrable p q)
  have hpor1 : ‖∫ σ in a..(-1 : ℝ), landauKernel x s ((σ : ℂ) + (U : ℂ) * I)‖
      ≤ P₁ * Real.log (|U| + 3) / (|U| - |s.im|) := by
    have hpt : ∀ σ ∈ Set.Icc a (-1 : ℝ),
        ‖landauKernel x s ((σ : ℂ) + (U : ℂ) * I)‖
          ≤ C₁ * (Real.log (|U| + 3) + (-1 - σ)) * (x ^ σ * X) / (|U| - |s.im|) := by
      intro σ hσ
      refine hker σ _ ?_
      have hz := h₁ ((σ : ℂ) + (U : ℂ) * I) (by rw [hwre]; exact hσ.2) (by rw [hwim]; linarith)
      refine le_trans hz (mul_le_mul_of_nonneg_left ?_ hC₁.le)
      have hnw : ‖(σ : ℂ) + (U : ℂ) * I‖ ≤ -σ + |U| := by
        refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
        rw [hwre, hwim, abs_of_nonpos (by linarith [hσ.2])]
      have hstep : ‖(σ : ℂ) + (U : ℂ) * I‖ + 2 ≤ |U| + 3 + (-1 - σ) := by linarith
      refine le_trans (Real.log_le_log (by positivity) hstep) ?_
      exact log_add_le (by linarith [abs_nonneg U]) (by linarith [hσ.2])
    refine le_trans (hnorm a (-1 : ℝ)
      (fun σ => C₁ * (Real.log (|U| + 3) + (-1 - σ)) * (x ^ σ * X) / (|U| - |s.im|))
      (by linarith) (by fun_prop) hpt) ?_
    have hc1 : Continuous fun σ : ℝ => Real.log (|U| + 3) * x ^ σ := by fun_prop
    have hc2 : Continuous fun σ : ℝ => (-1 - σ) * x ^ σ := by fun_prop
    have hrw : (fun σ : ℝ => C₁ * (Real.log (|U| + 3) + (-1 - σ)) * (x ^ σ * X)
          / (|U| - |s.im|))
        = fun σ : ℝ => C₁ * X / (|U| - |s.im|)
            * (Real.log (|U| + 3) * x ^ σ + (-1 - σ) * x ^ σ) := by
      funext σ; ring
    rw [hrw, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hc1.intervalIntegrable a (-1 : ℝ))
        (hc2.intervalIntegrable a (-1 : ℝ)), intervalIntegral.integral_const_mul]
    have hxm : (0 : ℝ) < x ^ (-1 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hstep : Real.log (|U| + 3) * (∫ σ in a..(-1 : ℝ), x ^ σ)
        + (∫ σ in a..(-1 : ℝ), (-1 - σ) * x ^ σ)
        ≤ Real.log (|U| + 3) * (x ^ (-1 : ℝ) * (1 / Real.log x + 1 / Real.log x ^ 2)) := by
      have e1 : Real.log (|U| + 3) * (∫ σ in a..(-1 : ℝ), x ^ σ)
          ≤ Real.log (|U| + 3) * (x ^ (-1 : ℝ) / Real.log x) :=
        mul_le_mul_of_nonneg_left (integral_rpow_le hx a (-1 : ℝ)) (by linarith)
      have e2 : (∫ σ in a..(-1 : ℝ), (-1 - σ) * x ^ σ)
          ≤ Real.log (|U| + 3) * (x ^ (-1 : ℝ) / Real.log x ^ 2) := by
        refine le_trans (integral_sub_mul_rpow_le hx ha) ?_
        nlinarith [mul_nonneg (sub_nonneg.2 hLU) (div_pos hxm (pow_pos hLx 2)).le]
      have e3 : Real.log (|U| + 3) * (x ^ (-1 : ℝ) / Real.log x)
          + Real.log (|U| + 3) * (x ^ (-1 : ℝ) / Real.log x ^ 2)
          = Real.log (|U| + 3) * (x ^ (-1 : ℝ) * (1 / Real.log x + 1 / Real.log x ^ 2)) := by
        ring
      linarith [e1, e2, e3]
    refine le_trans (mul_le_mul_of_nonneg_left hstep
      (div_nonneg (mul_nonneg hC₁.le hX0.le) hD.le)) (le_of_eq ?_)
    rw [hP₁def]
    ring
  have hpor2 : ‖∫ σ in (-1 : ℝ)..(3 / 2 : ℝ), landauKernel x s ((σ : ℂ) + (U : ℂ) * I)‖
      ≤ P₂ * Real.log (|U| + 3) * (1 + 1 / gp) / (|U| - |s.im|) := by
    have hc0 : (0 : ℝ) ≤ C₂ * Real.log (|U| + 3) * (1 + 1 / gp) :=
      mul_nonneg (mul_nonneg hC₂.le (by linarith)) (by linarith)
    have hpt : ∀ σ ∈ Set.Icc (-1 : ℝ) (3 / 2 : ℝ),
        ‖landauKernel x s ((σ : ℂ) + (U : ℂ) * I)‖
          ≤ C₂ * Real.log (|U| + 3) * (1 + 1 / gp) * (x ^ σ * X) / (|U| - |s.im|) := by
      intro σ hσ
      refine hker σ _ ?_
      have hz := h₂ gp hgp ((σ : ℂ) + (U : ℂ) * I) (by rw [hwim]; exact hU)
        (by rw [hwre]; exact hσ.1) (by rw [hwre]; exact hσ.2)
        (fun ρ hρ₁ hρ₂ hρ₃ => by rw [hwim]; exact hgap ρ hρ₁ hρ₂ hρ₃)
      rwa [hwim] at hz
    refine le_trans (hnorm (-1 : ℝ) (3 / 2 : ℝ)
      (fun σ => C₂ * Real.log (|U| + 3) * (1 + 1 / gp) * (x ^ σ * X) / (|U| - |s.im|))
      (by norm_num) (by fun_prop) hpt) ?_
    have hrw : (fun σ : ℝ => C₂ * Real.log (|U| + 3) * (1 + 1 / gp) * (x ^ σ * X)
          / (|U| - |s.im|))
        = fun σ : ℝ => C₂ * Real.log (|U| + 3) * (1 + 1 / gp) * X / (|U| - |s.im|) * x ^ σ := by
      funext σ; ring
    rw [hrw, intervalIntegral.integral_const_mul, hP₂def]
    refine le_trans (mul_le_mul_of_nonneg_left (integral_rpow_le hx (-1 : ℝ) (3 / 2 : ℝ))
      (div_nonneg (mul_nonneg hc0 hX0.le) hD.le)) (le_of_eq (by ring))
  have hpor3 : ‖∫ σ in (3 / 2 : ℝ)..b, landauKernel x s ((σ : ℂ) + (U : ℂ) * I)‖
      ≤ P₃ / (|U| - |s.im|) := by
    refine le_trans (hnorm (3 / 2 : ℝ) b (fun σ => A₀ * (x ^ σ * X) / (|U| - |s.im|)) hb
      (by fun_prop) (fun σ hσ => hker σ A₀ (h₃ _ (by rw [hwre]; exact hσ.1)))) ?_
    have hrw : (fun σ : ℝ => A₀ * (x ^ σ * X) / (|U| - |s.im|))
        = fun σ : ℝ => A₀ * X / (|U| - |s.im|) * x ^ σ := by
      funext σ; ring
    rw [hrw, intervalIntegral.integral_const_mul, hP₃def]
    refine le_trans (mul_le_mul_of_nonneg_left (integral_rpow_le hx (3 / 2 : ℝ) b)
      (div_nonneg (mul_nonneg hA₀.le hX0.le) hD.le)) (le_of_eq (by ring))
  have hsplit : (∫ σ in a..b, landauKernel x s ((σ : ℂ) + (U : ℂ) * I))
      = ((∫ σ in a..(-1 : ℝ), landauKernel x s ((σ : ℂ) + (U : ℂ) * I))
          + ∫ σ in (-1 : ℝ)..(3 / 2 : ℝ), landauKernel x s ((σ : ℂ) + (U : ℂ) * I))
        + ∫ σ in (3 / 2 : ℝ)..b, landauKernel x s ((σ : ℂ) + (U : ℂ) * I) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint a (-1 : ℝ))
        (hint (-1 : ℝ) (3 / 2 : ℝ)),
      intervalIntegral.integral_add_adjacent_intervals (hint a (3 / 2 : ℝ)) (hint (3 / 2 : ℝ) b)]
  rw [hsplit]
  refine le_trans (le_trans (norm_add_le _ _)
    (add_le_add (le_trans (norm_add_le _ _) (add_le_add hpor1 hpor2)) hpor3)) ?_
  rw [← add_div, ← add_div, div_le_div_iff_of_pos_right hD]
  have hLUG : (1 : ℝ) ≤ Real.log (|U| + 3) * (1 + 1 / gp) := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hP₁.le (by linarith : (0 : ℝ) ≤ Real.log (|U| + 3)))
      (sub_nonneg.2 hgp1), mul_nonneg hP₃.le (sub_nonneg.2 hLUG)]

end ZetaZeros
