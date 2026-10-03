/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
public import ZetaZeros.Meta.Attr

/-!
# Stirling's asymptotic for the Riemann--Siegel theta function

The asymptotic `θ T = (T / 2) log (T / 2π) - T / 2 + O(log T)` for the Riemann--Siegel theta
function, derived from the partial-fraction series for the digamma function.

## Main definitions

* `ZetaZeros.logGamma`: the branch `ℒ` of `log Γ` on the right half-plane normalised by `ℒ 1 = 0`,
  realised as the integral of the digamma function along the segment from `1`.
* `ZetaZeros.theta`: the Riemann--Siegel theta function `θ t = im (ℒ (1/4 + i t/2)) - (t/2) log π`.

## Main results

* `ZetaZeros.hasDerivAt_logGamma`: `ℒ` has derivative `digamma` on the open right half-plane.
* `ZetaZeros.exists_norm_digamma_sub_log_le`: Stirling's asymptotic on vertical lines,
  `‖digamma z - log z‖ ≤ C / |im z|` for `re z ≥ 1/4` and `|im z| ≥ 1`.
* `ZetaZeros.exists_abs_theta_sub_le`: `|θ T - ((T/2) log (T/2π) - T/2)| ≤ C log T` for `T ≥ 2`.
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter Topology Set

/-! ## A logarithm of `Γ` on the right half-plane -/

/-- `ℒ`, a branch of `log Γ` on the open right half-plane, normalised by `ℒ 1 = 0`: the integral
of the digamma function along the segment from `1` to `z`. -/
@[zz_tag "def_logGamma"]
noncomputable def logGamma (z : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..1, (z - 1) * Complex.digamma (1 + (u : ℂ) * (z - 1))

/-! ## `ℒ` is a primitive of the digamma function -/

/-- Every truncated closed substrip `{a ≤ re z} ∩ {‖z‖ ≤ R}` of the open right half-plane is
contained in an open disc which is itself contained in the open right half-plane. -/
private theorem exists_ball_subset_re_pos {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    ∃ (M r : ℝ), 0 < r ∧ Metric.ball (M : ℂ) r ⊆ {z : ℂ | 0 < z.re} ∧
      ∀ w : ℂ, a ≤ w.re → ‖w‖ ≤ R → w ∈ Metric.ball (M : ℂ) r := by
  have hR : 0 < R := lt_of_lt_of_le ha haR
  refine ⟨R ^ 2 / a + 1, R ^ 2 / a + 1 - a / 2, ?_, ?_, ?_⟩
  · have h1 : R ≤ R ^ 2 / a := by
      rw [le_div_iff₀ ha]
      nlinarith
    nlinarith
  · intro w hw
    simp only [Metric.mem_ball, Complex.dist_eq] at hw
    have h := Complex.abs_re_le_norm (w - (R ^ 2 / a + 1 : ℝ))
    simp only [Complex.sub_re, Complex.ofReal_re] at h
    change (0 : ℝ) < w.re
    have := abs_le.1 h
    nlinarith [this.1, this.2]
  · intro w hwa hwR
    set M : ℝ := R ^ 2 / a + 1 with hM
    have hM0 : 0 < M := by positivity
    have hMa : R ^ 2 + a ≤ M * a := by
      rw [hM, add_mul, div_mul_cancel₀ _ ha.ne']
      simp
    have hr0 : 0 < M - a / 2 := by
      have h1 : R ≤ R ^ 2 / a := by
        rw [le_div_iff₀ ha]
        nlinarith
      have : a ≤ R := haR
      nlinarith
    simp only [Metric.mem_ball, Complex.dist_eq]
    have hnorm : ‖w - (M : ℂ)‖ ^ 2 = ‖w‖ ^ 2 - 2 * M * w.re + M ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      ring
    refine lt_of_pow_lt_pow_left₀ 2 hr0.le ?_
    rw [hnorm]
    have hw2 : ‖w‖ ^ 2 ≤ R ^ 2 := by
      have := norm_nonneg w
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hwa hM0.le]

/-- On the open right half-plane `ℒ` has derivative `digamma`. -/
@[zz_tag "lem_logGamma_deriv"]
theorem hasDerivAt_logGamma {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt logGamma (Complex.digamma z) z := by
  obtain ⟨M, r, hr, hball, hmem⟩ :=
    exists_ball_subset_re_pos (a := min 1 (z.re / 2)) (R := ‖z‖ + 2)
      (lt_min one_pos (by linarith)) (by
        have := norm_nonneg z
        exact (min_le_left _ _).trans (by linarith))
  have hdiff : DifferentiableOn ℂ Complex.digamma (Metric.ball (M : ℂ) r) := fun w hw =>
    (differentiableAt_digamma_of_re_pos (hball hw)).differentiableWithinAt
  obtain ⟨F, hF⟩ := hdiff.isExactOn_ball
  have hz' : z ∈ Metric.ball (M : ℂ) r :=
    hmem z ((min_le_right _ _).trans (by linarith)) (by linarith)
  have h1' : (1 : ℂ) ∈ Metric.ball (M : ℂ) r := by
    refine hmem 1 (by simp only [Complex.one_re]; exact min_le_left (1 : ℝ) (z.re / 2)) ?_
    have := norm_nonneg z
    simp only [norm_one]
    linarith
  have key : ∀ w ∈ Metric.ball (M : ℂ) r, logGamma w = F w - F 1 := by
    intro w hw
    have hseg : ∀ t : ℝ, t ∈ uIcc (0 : ℝ) 1 →
        (1 : ℂ) + (t : ℂ) * (w - 1) ∈ Metric.ball (M : ℂ) r := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hc := (convex_ball (M : ℂ) r) h1' hw (a := 1 - t) (b := t)
        (by linarith [ht.2]) ht.1 (by ring)
      have hrw : (1 - t) • (1 : ℂ) + t • w = 1 + (t : ℂ) * (w - 1) := by
        simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      rwa [hrw] at hc
    have hderiv : ∀ t : ℝ, t ∈ uIcc (0 : ℝ) 1 →
        HasDerivAt (fun s : ℝ => F (1 + (s : ℂ) * (w - 1)))
          ((w - 1) * Complex.digamma (1 + (t : ℂ) * (w - 1))) t := by
      intro t ht
      have hline : HasDerivAt (fun s : ℂ => (1 : ℂ) + s * (w - 1)) (w - 1) (t : ℂ) := by
        simpa using ((hasDerivAt_id ((t : ℂ))).mul_const (w - 1)).const_add 1
      have hcomp := (hF _ (hseg t ht)).comp ((t : ℂ)) hline
      rw [mul_comm] at hcomp
      exact hcomp.comp_ofReal
    have hcont : ContinuousOn (fun t : ℝ => (w - 1) * Complex.digamma (1 + (t : ℂ) * (w - 1)))
        (uIcc (0 : ℝ) 1) := by
      intro t ht
      refine ContinuousAt.continuousWithinAt ?_
      have hline : ContinuousAt (fun s : ℝ => (1 : ℂ) + (s : ℂ) * (w - 1)) t := by fun_prop
      have hdg : ContinuousAt (fun s : ℝ => Complex.digamma (1 + (s : ℂ) * (w - 1))) t :=
        ContinuousAt.comp (g := Complex.digamma)
          (differentiableAt_digamma_of_re_pos (hball (hseg t ht))).continuousAt hline
      exact continuousAt_const.mul hdg
    rw [logGamma, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    norm_num
  have hFz : HasDerivAt (fun w => F w - F 1) (Complex.digamma z) z := (hF z hz').sub_const _
  refine hFz.congr_of_eventuallyEq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hz'] with w hw using key w hw

/-- `ℒ` is analytic on the open right half-plane. -/
@[zz_tag "lem_logGamma_deriv"]
private theorem analyticOnNhd_logGamma : AnalyticOnNhd ℂ logGamma {z : ℂ | 0 < z.re} := by
  have h : DifferentiableOn ℂ logGamma {z : ℂ | 0 < z.re} :=
    fun z hz => (hasDerivAt_logGamma hz).differentiableAt.differentiableWithinAt
  exact h.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-! ## A sum of inverse squares along a vertical line -/

/-- The squared distance from `-n` to a point of a vertical line, in terms of its coordinates. -/
private theorem norm_add_natCast_sq {z : ℂ} (n : ℕ) :
    ‖z + (n : ℂ)‖ ^ 2 = (z.re + n) ^ 2 + |z.im| ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, add_zero]
  rw [sq_abs]
  ring

/-- The partial sums of `∑ 1 / ‖z + n‖ ^ 2` are bounded by `6 / |im z|`, uniformly in the number
of terms. -/
private theorem sum_range_one_div_norm_add_natCast_sq_le {z : ℂ} (hre : 1 / 4 ≤ z.re)
    (him : 1 / 2 ≤ |z.im|) (N : ℕ) :
    ∑ i ∈ Finset.range N, 1 / ‖z + (i : ℂ)‖ ^ 2 ≤ 6 / |z.im| := by
  set y : ℝ := |z.im| with hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) him
  have hsq : ∀ n : ℕ, ‖z + (n : ℂ)‖ ^ 2 = (z.re + n) ^ 2 + y ^ 2 := fun n =>
    norm_add_natCast_sq n
  set u : ℕ → ℝ := fun n => ((n : ℝ) + z.re + y)⁻¹ with hu
  have hupos : ∀ n : ℕ, 0 < (n : ℝ) + z.re + y := by
    intro n
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hterm : ∀ n : ℕ, 1 / ‖z + (n : ℂ)‖ ^ 2 ≤ 9 / 2 * (u n - u (n + 1)) := by
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 := hupos n
    have h2 := hupos (n + 1)
    have hdiff : u n - u (n + 1) =
        (((n : ℝ) + z.re + y) * ((n : ℝ) + 1 + z.re + y))⁻¹ := by
      rw [hu]
      push_cast
      rw [inv_sub_inv (by linarith) (by linarith)]
      ring
    have hD : (0 : ℝ) < (z.re + n) ^ 2 + y ^ 2 := by positivity
    have hAB : (0 : ℝ) < ((n : ℝ) + z.re + y) * ((n : ℝ) + 1 + z.re + y) := by
      apply mul_pos h1; linarith
    rw [hsq n, hdiff, ← div_eq_mul_inv, div_le_div_iff₀ hD hAB]
    nlinarith [sq_nonneg ((n : ℝ) + z.re - y), sq_nonneg (5 * ((n : ℝ) + z.re) - 1),
      sq_nonneg (2 * y - 1), mul_nonneg hn0 hy0.le]
  have hsum : ∑ i ∈ Finset.range N, 1 / ‖z + (i : ℂ)‖ ^ 2 ≤
      9 / 2 * ∑ i ∈ Finset.range N, (u i - u (i + 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hterm i
  rw [Finset.sum_range_sub' u N] at hsum
  have huN : 0 ≤ u N := by rw [hu]; positivity
  have hu0 : u 0 = (z.re + y)⁻¹ := by rw [hu]; norm_num
  have h1 : (z.re + y)⁻¹ ≤ y⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hy0 (by linarith : y ≤ z.re + y)
  have h3 : (0 : ℝ) < y⁻¹ := by positivity
  calc ∑ i ∈ Finset.range N, 1 / ‖z + (i : ℂ)‖ ^ 2 ≤ 9 / 2 * (u 0 - u N) := hsum
    _ ≤ 9 / 2 * y⁻¹ := by rw [hu0]; linarith
    _ ≤ 6 * y⁻¹ := by linarith
    _ = 6 / y := (div_eq_mul_inv 6 y).symm

/-- Along a vertical line in the right half-plane the inverse squares `‖z + n‖⁻¹ ^ 2` sum to at
most `6 / |im z|`. -/
@[zz_tag "lem_inv_sq_sum_bound"]
private theorem tsum_one_div_norm_add_natCast_sq_le {z : ℂ} (hre : 1 / 4 ≤ z.re)
    (him : 1 / 2 ≤ |z.im|) :
    ∑' n : ℕ, 1 / ‖z + (n : ℂ)‖ ^ 2 ≤ 6 / |z.im| :=
  Real.tsum_le_of_sum_range_le (fun _ => by positivity)
    (sum_range_one_div_norm_add_natCast_sq_le hre him)

/-! ## Stirling's asymptotic for the digamma function on vertical lines -/

/-- For `0 < re w` and `103 / 100 ≤ ‖w‖`, `w⁻¹` differs from `log (w + 1) - log w` by
`O(‖w‖⁻¹ ^ 2)`. -/
private theorem norm_inv_sub_log_sub_log_le {w : ℂ} (hw : (103 / 100 : ℝ) ≤ ‖w‖) (hwre : 0 < w.re) :
    ‖w⁻¹ - (Complex.log (w + 1) - Complex.log w)‖ ≤ 18 * (1 / ‖w‖ ^ 2) := by
  have hn : (0 : ℝ) < ‖w‖ := by linarith
  have hwne : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    linarith
  have h1re : 0 < (w + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have h1ne : w + 1 ≠ 0 := fun h => by rw [h] at h1re; simp at h1re
  have hargw : Complex.arg w ≠ Real.pi := by
    have h := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hwre)
    intro hh
    rw [hh, abs_of_pos Real.pi_pos] at h
    linarith [Real.pi_pos]
  have hlog : Complex.log (w + 1) - Complex.log w = Complex.log (1 + w⁻¹) := by
    have harg := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hwre))
    have harg1 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h1re))
    have hmem : Complex.arg (w + 1) + Complex.arg w⁻¹ ∈ Set.Ioc (-Real.pi) Real.pi := by
      rw [Complex.arg_inv, ite_eq_right hargw, Set.mem_Ioc]
      constructor <;> linarith
    have hfac : (1 : ℂ) + w⁻¹ = (w + 1) * w⁻¹ := by field_simp
    rw [hfac, Complex.log_mul h1ne (inv_ne_zero hwne) hmem, Complex.log_inv w hargw]
    ring
  have hu : ‖w⁻¹‖ ≤ 100 / 103 := by
    have h' : 1 / ‖w‖ ≤ 1 / ((103 : ℝ) / 100) := one_div_le_one_div_of_le (by norm_num) hw
    rw [norm_inv, ← one_div]
    calc 1 / ‖w‖ ≤ 1 / ((103 : ℝ) / 100) := h'
      _ = 100 / 103 := by norm_num
  have hlt : ‖w⁻¹‖ < 1 := by
    have : (100 : ℝ) / 103 < 1 := by norm_num
    linarith
  have hbnd := Complex.norm_log_one_add_sub_self_le hlt
  rw [hlog, show w⁻¹ - Complex.log (1 + w⁻¹) = -(Complex.log (1 + w⁻¹) - w⁻¹) from by ring,
    norm_neg]
  refine hbnd.trans ?_
  rw [norm_inv] at hu ⊢
  have hs : (0 : ℝ) < 1 - ‖w‖⁻¹ := by linarith
  have hinvle : (1 - ‖w‖⁻¹)⁻¹ ≤ 103 / 3 := by
    rw [inv_le_comm₀ hs (by norm_num)]
    have h103 : ((103 : ℝ) / 3)⁻¹ = 3 / 103 := by norm_num
    rw [h103]
    linarith
  have hP : (0 : ℝ) < 1 / ‖w‖ ^ 2 := by positivity
  have hsq : ‖w‖⁻¹ ^ 2 = 1 / ‖w‖ ^ 2 := by rw [inv_pow, one_div]
  rw [hsq]
  nlinarith [mul_le_mul_of_nonneg_left hinvle hP.le]

/-- **Stirling's asymptotic for the digamma function on vertical lines.** On `re z ≥ 1/4` with
`|im z| ≥ 1`, `digamma z` agrees with `log z` to within `C / |im z|`. -/
@[zz_tag "lem_digamma_vertical_asymp"]
theorem exists_norm_digamma_sub_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 4 ≤ z.re → 1 ≤ |z.im| →
      ‖Complex.digamma z - Complex.log z‖ ≤ C / |z.im| := by
  refine ⟨108, by norm_num, fun z hre him => ?_⟩
  set y : ℝ := |z.im| with hy
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos him
  have hre0 : 0 < z.re := by linarith
  set S : ℕ → ℂ := fun N => ∑ i ∈ Finset.range N, (z + (i : ℂ))⁻¹ with hS
  have hlb : ∀ n : ℕ, (103 / 100 : ℝ) ≤ ‖z + (n : ℂ)‖ := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : ((103 : ℝ) / 100) ^ 2 ≤ ‖z + (n : ℂ)‖ ^ 2 := by
      rw [norm_add_natCast_sq n, ← hy]
      nlinarith
    nlinarith [norm_nonneg (z + (n : ℂ))]
  have hre' : ∀ n : ℕ, 0 < (z + (n : ℂ)).re := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hsum : ∀ N : ℕ, ‖S N - (Complex.log (z + (N : ℂ)) - Complex.log z)‖ ≤ 108 / y := by
    intro N
    have htel : ∑ i ∈ Finset.range N,
        (Complex.log (z + ((i : ℂ) + 1)) - Complex.log (z + (i : ℂ)))
          = Complex.log (z + (N : ℂ)) - Complex.log z := by
      have h := Finset.sum_range_sub (fun i : ℕ => Complex.log (z + (i : ℂ))) N
      simpa using h
    have hstep : ∀ i ∈ Finset.range N,
        ‖(z + (i : ℂ))⁻¹ - (Complex.log (z + ((i : ℂ) + 1)) - Complex.log (z + (i : ℂ)))‖
          ≤ 18 * (1 / ‖z + (i : ℂ)‖ ^ 2) := by
      intro i _
      have h := norm_inv_sub_log_sub_log_le (hlb i) (hre' i)
      rw [show z + (i : ℂ) + 1 = z + ((i : ℂ) + 1) from by ring] at h
      exact h
    calc ‖S N - (Complex.log (z + (N : ℂ)) - Complex.log z)‖
        = ‖∑ i ∈ Finset.range N, ((z + (i : ℂ))⁻¹
            - (Complex.log (z + ((i : ℂ) + 1)) - Complex.log (z + (i : ℂ))))‖ := by
          rw [Finset.sum_sub_distrib, htel, hS]
      _ ≤ ∑ i ∈ Finset.range N, ‖(z + (i : ℂ))⁻¹
            - (Complex.log (z + ((i : ℂ) + 1)) - Complex.log (z + (i : ℂ)))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range N, 18 * (1 / ‖z + (i : ℂ)‖ ^ 2) := Finset.sum_le_sum hstep
      _ = 18 * ∑ i ∈ Finset.range N, 1 / ‖z + (i : ℂ)‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 18 * (6 / y) := by
          have h := sum_range_one_div_norm_add_natCast_sq_le hre (by rw [← hy]; linarith) N
          rw [← hy] at h
          linarith
      _ = 108 / y := by ring
  have hpoles : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n h
    rw [h] at hre0
    simp only [Complex.neg_re, Complex.natCast_re] at hre0
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hpart := (Complex.hasSum_digamma hpoles).tendsto_sum_nat
  have hsplit : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))
      = ((harmonic N : ℚ) : ℂ) - S N := by
    intro N
    rw [Finset.sum_sub_distrib, hS]
    congr 1
    · simpa [one_div] using Complex.sum_inv_natCast_add_one N
    · exact Finset.sum_congr rfl fun i _ => by rw [one_div, add_comm]
  have h1 : Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℂ) - S N) atTop
      (𝓝 (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ))) :=
    Filter.Tendsto.congr hsplit hpart
  have hrealC : Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℂ) - ((Real.log N : ℝ) : ℂ)) atTop
      (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
    simpa [Function.comp_def, Complex.ofReal_sub] using h
  have h3 : Tendsto (fun N : ℕ => ((Real.log N : ℝ) : ℂ) - S N) atTop
      (𝓝 (Complex.digamma z)) := by
    have h := h1.sub hrealC
    have he : ∀ N : ℕ, (((harmonic N : ℚ) : ℂ) - S N)
        - (((harmonic N : ℚ) : ℂ) - ((Real.log N : ℝ) : ℂ))
          = ((Real.log N : ℝ) : ℂ) - S N := fun N => by ring
    have hv : Complex.digamma z + (Real.eulerMascheroniConstant : ℂ)
        - ((Real.eulerMascheroniConstant : ℝ) : ℂ) = Complex.digamma z := by ring
    rw [← hv]
    exact Filter.Tendsto.congr he h
  have hzN : ∀ N : ℕ, 1 ≤ N → Complex.log (z + (N : ℂ))
      = ((Real.log N : ℝ) : ℂ) + Complex.log (1 + z / (N : ℂ)) := by
    intro N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hxre : (1 + z / (N : ℂ)).re = 1 + z.re / N := by
      rw [div_eq_inv_mul, show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) from by push_cast; ring]
      simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul]
      rw [div_eq_inv_mul]
    have hxne : (1 : ℂ) + z / (N : ℂ) ≠ 0 := by
      intro h
      rw [h] at hxre
      simp only [Complex.zero_re] at hxre
      have : 0 < z.re / N := div_pos hre0 hN0
      linarith
    have hfac : (((N : ℝ) : ℂ)) * (1 + z / (N : ℂ)) = z + (N : ℂ) := by
      have hNne : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      push_cast
      field_simp
      ring
    rw [← hfac, Complex.log_ofReal_mul hN0 hxne]
  have htend0 : Tendsto (fun N : ℕ => Complex.log (1 + z / (N : ℂ))) atTop (𝓝 0) := by
    have hz0 : Tendsto (fun N : ℕ => z / (N : ℂ)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_div, Complex.norm_natCast]
      exact tendsto_const_div_atTop_nhds_zero_nat ‖z‖
    have h1' : Tendsto (fun N : ℕ => (1 : ℂ) + z / (N : ℂ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hz0
    simpa using h1'.clog Complex.one_mem_slitPlane
  have hg : Tendsto (fun N : ℕ => Complex.log (z + (N : ℂ)) - Complex.log z - S N) atTop
      (𝓝 (Complex.digamma z - Complex.log z)) := by
    have h := (h3.add htend0).sub_const (Complex.log z)
    rw [show Complex.digamma z + 0 - Complex.log z
      = Complex.digamma z - Complex.log z from by ring] at h
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [hzN N hN]
    ring
  refine le_of_tendsto hg.norm ?_
  filter_upwards with N
  rw [show Complex.log (z + (N : ℂ)) - Complex.log z - S N
      = -(S N - (Complex.log (z + (N : ℂ)) - Complex.log z)) from by ring, norm_neg]
  exact hsum N

/-! ## The Riemann--Siegel theta function -/

/-- The Riemann--Siegel theta function `θ t = im (ℒ (1/4 + i t / 2)) - (t / 2) * log π`. -/
@[zz_tag "def_theta"]
noncomputable def theta (t : ℝ) : ℝ :=
  (logGamma (1 / 4 + (t : ℂ) / 2 * Complex.I)).im - t / 2 * Real.log Real.pi

/-! ## An elementary logarithmic integral -/

/-- The derivative of `v ↦ log (v ^ 2 + 1/4)`. -/
private theorem hasDerivAt_log_sq_add_quarter (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.log (v ^ 2 + 1 / 4)) (2 * u / (u ^ 2 + 1 / 4)) u := by
  have hpos : (0 : ℝ) < u ^ 2 + 1 / 4 := by positivity
  have hq : HasDerivAt (fun v : ℝ => v ^ 2 + 1 / 4) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (1 / 4 : ℝ)
  exact hq.log hpos.ne'

/-- `v ↦ v * log (v ^ 2 + 1/4) - 2 * v + arctan (2 * v)` is an exact primitive of
`v ↦ log (v ^ 2 + 1/4)`. -/
private theorem hasDerivAt_log_sq_add_quarter_primitive (u : ℝ) :
    HasDerivAt (fun v : ℝ => v * Real.log (v ^ 2 + 1 / 4) - 2 * v + Real.arctan (2 * v))
      (Real.log (u ^ 2 + 1 / 4)) u := by
  have hpos : (0 : ℝ) < u ^ 2 + 1 / 4 := by positivity
  have hlin : HasDerivAt (fun v : ℝ => 2 * v) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have harctan : HasDerivAt (fun v : ℝ => Real.arctan (2 * v)) (2 / (1 + (2 * u) ^ 2)) u := by
    have h := (Real.hasDerivAt_arctan (2 * u)).comp u hlin
    simp only [Function.comp_def] at h
    exact h.congr_deriv (by ring)
  have h := (((hasDerivAt_id u).mul (hasDerivAt_log_sq_add_quarter u)).sub hlin).add harctan
  refine h.congr_deriv ?_
  have h4 : (0 : ℝ) < 1 + (2 * u) ^ 2 := by positivity
  simp only [id_eq]
  field_simp
  ring

/-- The modulus of `1/4 + i u / 2`, logarithmically. -/
private theorem log_norm_quarter_add_halfMul_I (u : ℝ) :
    Real.log ‖(1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I‖
      = 1 / 2 * Real.log (u ^ 2 + 1 / 4) - Real.log 2 := by
  have hrw : (1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I
      = ((1 / 4 : ℝ) : ℂ) + ((u / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hpos : (0 : ℝ) < u ^ 2 + 1 / 4 := by positivity
  rw [hrw, Complex.norm_add_mul_I, Real.log_sqrt (by positivity),
    show ((1 / 4 : ℝ) ^ 2 + (u / 2) ^ 2) = (u ^ 2 + 1 / 4) / 4 by ring,
    Real.log_div hpos.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- **An elementary logarithmic integral.** `∫ u in 0..T, log ‖1/4 + i u / 2‖` agrees with
`T * log (T / 2) - T` to within an absolute constant, for `T ≥ 2`. -/
@[zz_tag "lem_log_modulus_integral"]
private theorem exists_abs_integral_log_norm_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |(∫ u in (0 : ℝ)..T, Real.log ‖(1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I‖)
        - (T * Real.log (T / 2) - T)| ≤ C := by
  have hcont : Continuous (fun u : ℝ => Real.log (u ^ 2 + 1 / 4)) :=
    continuous_iff_continuousAt.2 fun u =>
      (hasDerivAt_log_sq_add_quarter u).differentiableAt.continuousAt
  refine ⟨2, by norm_num, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hTsq : (0 : ℝ) < T ^ 2 + 1 / 4 := by positivity
  have hprim : (∫ u in (0 : ℝ)..T, Real.log (u ^ 2 + 1 / 4))
      = T * Real.log (T ^ 2 + 1 / 4) - 2 * T + Real.arctan (2 * T) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hasDerivAt_log_sq_add_quarter_primitive u) (hcont.intervalIntegrable 0 T)]
    norm_num
  have hint : (∫ u in (0 : ℝ)..T, Real.log ‖(1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I‖)
      = 1 / 2 * (T * Real.log (T ^ 2 + 1 / 4) - 2 * T + Real.arctan (2 * T))
        - T * Real.log 2 := by
    rw [intervalIntegral.integral_congr
      (g := fun u : ℝ => 1 / 2 * Real.log (u ^ 2 + 1 / 4) - Real.log 2)
      fun u _ => log_norm_quarter_add_halfMul_I u]
    rw [intervalIntegral.integral_sub ((hcont.const_mul _).intervalIntegrable 0 T)
      intervalIntegrable_const, intervalIntegral.integral_const_mul, hprim,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hlogT : T * Real.log (T / 2) = T / 2 * Real.log (T ^ 2) - T * Real.log 2 := by
    rw [Real.log_div hT0.ne' (by norm_num), show (T : ℝ) ^ 2 = T * T by ring,
      Real.log_mul hT0.ne' hT0.ne']
    ring
  have hsplit : T / 2 * Real.log (T ^ 2 + 1 / 4) - T / 2 * Real.log (T ^ 2)
      = T / 2 * Real.log (1 + 1 / (4 * T ^ 2)) := by
    rw [← mul_sub, ← Real.log_div hTsq.ne' (by positivity)]
    congr 2
    field_simp
  have hdiff : (∫ u in (0 : ℝ)..T, Real.log ‖(1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I‖)
      - (T * Real.log (T / 2) - T)
      = T / 2 * Real.log (1 + 1 / (4 * T ^ 2)) + 1 / 2 * Real.arctan (2 * T) := by
    rw [hint, hlogT, ← hsplit]
    ring
  rw [hdiff, abs_le]
  have harc0 : 0 ≤ Real.arctan (2 * T) := Real.arctan_nonneg.2 (by linarith)
  have harc1 : Real.arctan (2 * T) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hlog0 : 0 ≤ Real.log (1 + 1 / (4 * T ^ 2)) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) < 1 / (4 * T ^ 2) := by positivity
    linarith
  have hlog1 : Real.log (1 + 1 / (4 * T ^ 2)) ≤ 1 / (4 * T ^ 2) := by
    have h := Real.log_le_sub_one_of_pos (x := 1 + 1 / (4 * T ^ 2)) (by positivity)
    simpa using h
  have hTge : (4 : ℝ) ≤ T ^ 2 := by nlinarith
  have hkey : T / 2 * Real.log (1 + 1 / (4 * T ^ 2)) ≤ 1 / 16 := by
    have h1 : T / 2 * Real.log (1 + 1 / (4 * T ^ 2)) ≤ T / 2 * (1 / (4 * T ^ 2)) := by
      have : (0 : ℝ) ≤ T / 2 := by linarith
      nlinarith
    have h2 : T / 2 * (1 / (4 * T ^ 2)) = 1 / (8 * T) := by
      field_simp
      ring
    have h3 : 1 / (8 * T) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith [h1, h2.le, h3]
  have hnn : (0 : ℝ) ≤ T / 2 * Real.log (1 + 1 / (4 * T ^ 2)) :=
    mul_nonneg (by linarith) hlog0
  constructor
  · linarith
  · linarith

/-! ## The asymptotic for the theta function -/

/-- The real part of a point of the line the theta function is read off. -/
private theorem re_quarter_add_mul_I (u : ℝ) :
    ((1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I).re = 1 / 4 := by simp

/-- The imaginary part of a point of the line the theta function is read off. -/
private theorem im_quarter_add_mul_I (u : ℝ) :
    ((1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I).im = u / 2 := by simp

/-- The points of the line `re z = 1/4` are never `0`. -/
private theorem norm_quarter_add_mul_I_pos (u : ℝ) :
    (0 : ℝ) < ‖(1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I‖ := by
  rw [norm_pos_iff]
  intro h
  have hre := re_quarter_add_mul_I u
  rw [h] at hre
  norm_num at hre

/-- The digamma function is continuous along the line `re z = 1/4`. -/
private theorem continuous_digamma_quarter_line :
    Continuous (fun u : ℝ => Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I)) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  have hre : (0 : ℝ) < ((1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I).re := by
    rw [re_quarter_add_mul_I]
    norm_num
  exact ContinuousAt.comp (g := Complex.digamma)
    (differentiableAt_digamma_of_re_pos hre).continuousAt (by fun_prop)

/-- The derivative of `ℒ` restricted to the line `re z = 1/4`. -/
private theorem hasDerivAt_logGamma_quarter_line (u : ℝ) :
    HasDerivAt (fun v : ℝ => logGamma (1 / 4 + (v : ℂ) / 2 * Complex.I))
      (Complex.I / 2 * Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I)) u := by
  have hre : (0 : ℝ) < ((1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I).re := by
    rw [re_quarter_add_mul_I]
    norm_num
  have hline : HasDerivAt (fun s : ℂ => 1 / 4 + s / 2 * Complex.I) (Complex.I / 2) ((u : ℂ)) := by
    have h : HasDerivAt (fun s : ℂ => s / 2 * Complex.I) (Complex.I / 2) ((u : ℂ)) := by
      simpa [div_eq_mul_inv, mul_comm] using
        ((hasDerivAt_id ((u : ℂ))).div_const 2).mul_const Complex.I
    simpa using h.const_add (1 / 4 : ℂ)
  have hcomp := (hasDerivAt_logGamma hre).comp ((u : ℂ)) hline
  rw [mul_comm] at hcomp
  exact hcomp.comp_ofReal

/-- The fundamental theorem of calculus along the line `re z = 1/4`. -/
private theorem logGamma_quarter_line_sub (T : ℝ) :
    logGamma (1 / 4 + (T : ℂ) / 2 * Complex.I) - logGamma (1 / 4)
      = ∫ u in (0 : ℝ)..T, Complex.I / 2 * Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_logGamma_quarter_line u)
    ((continuous_const.mul continuous_digamma_quarter_line).intervalIntegrable 0 T)]
  norm_num

/-- **The asymptotic for the theta function.** `θ T` agrees with the main term
`(T / 2) * log (T / 2π) - T / 2` of the zero-counting formula to within `C * log T`, for `T ≥ 2`.
-/
@[zz_tag "lem_theta_asymp"]
theorem exists_abs_theta_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |theta T - (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)| ≤ C * Real.log T := by
  obtain ⟨C₁, hC₁, hstir⟩ := exists_norm_digamma_sub_log_le
  obtain ⟨C₃, hC₃, hlogint⟩ := exists_abs_integral_log_norm_sub_le
  have hcontD : Continuous
      (fun u : ℝ => (Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I)).re) :=
    Complex.continuous_re.comp continuous_digamma_quarter_line
  have hcontL : Continuous
      (fun u : ℝ => Real.log ‖(1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I‖) := by
    refine Real.continuousOn_log.comp_continuous (by fun_prop) fun u => ?_
    exact (norm_quarter_add_mul_I_pos u).ne'
  set φ : ℝ → ℝ := fun u => (Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I)).re
    - Real.log ‖(1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I‖ with hφ
  have hcontφ : Continuous φ := hcontD.sub hcontL
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcontφ.continuousOn
  have hK0 : (0 : ℝ) ≤ K := le_trans (norm_nonneg _) (hK 0 (by norm_num))
  have hφstir : ∀ u : ℝ, 2 ≤ u → |φ u| ≤ 2 * C₁ * (1 / u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hre : (1 : ℝ) / 4 ≤ ((1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I).re := by
      rw [re_quarter_add_mul_I]
    have him : (1 : ℝ) ≤ |((1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I).im| := by
      rw [im_quarter_add_mul_I, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u / 2)]
      linarith
    have h := hstir _ hre him
    rw [im_quarter_add_mul_I, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u / 2)] at h
    have hle : |φ u| ≤ ‖Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I)
        - Complex.log (1 / 4 + (u : ℂ) / 2 * Complex.I)‖ := by
      rw [hφ]
      simp only
      rw [← Complex.log_re, ← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    refine hle.trans (h.trans ?_)
    rw [show C₁ / (u / 2) = 2 * C₁ * (1 / u) from by field_simp]
  have hsplit : ∀ T : ℝ, 2 ≤ T →
      |∫ u in (0 : ℝ)..T, φ u| ≤ 2 * K + 2 * C₁ * Real.log T := by
    intro T hT
    have hT0 : (0 : ℝ) < T := by linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcontφ.intervalIntegrable 0 2) (hcontφ.intervalIntegrable 2 T)]
    refine (abs_add_le _ _).trans ?_
    have h1 : |∫ u in (0 : ℝ)..2, φ u| ≤ 2 * K := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := φ) (a := (0 : ℝ)) (b := 2) (C := K) fun x hx => by
          refine hK x ?_
          rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hx
          exact ⟨hx.1.le, hx.2⟩
      simp only [Real.norm_eq_abs] at h
      calc |∫ u in (0 : ℝ)..2, φ u| ≤ K * |(2 : ℝ) - 0| := h
        _ = 2 * K := by rw [show |(2 : ℝ) - 0| = 2 by norm_num]; ring
    have h2 : |∫ u in (2 : ℝ)..T, φ u| ≤ 2 * C₁ * Real.log T := by
      have hzero : (0 : ℝ) ∉ Set.uIcc (2 : ℝ) T := by
        rw [Set.uIcc_of_le hT]
        intro h
        linarith [h.1]
      have hinv : IntervalIntegrable (fun u : ℝ => 2 * C₁ * (1 / u)) MeasureTheory.volume 2 T := by
        refine ContinuousOn.intervalIntegrable (continuousOn_const.mul ?_)
        refine ContinuousOn.div continuousOn_const continuousOn_id fun x hx => ?_
        rw [Set.uIcc_of_le hT] at hx
        exact ne_of_gt (by linarith [hx.1])
      have hmono : ∫ u in (2 : ℝ)..T, |φ u| ≤ ∫ u in (2 : ℝ)..T, 2 * C₁ * (1 / u) :=
        intervalIntegral.integral_mono_on hT (hcontφ.abs.intervalIntegrable 2 T) hinv
          fun x hx => hφstir x hx.1
      have hval : (∫ u in (2 : ℝ)..T, 2 * C₁ * (1 / u)) = 2 * C₁ * Real.log (T / 2) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div hzero]
      have hlog : Real.log (T / 2) ≤ Real.log T := by
        rw [Real.log_div hT0.ne' (by norm_num)]
        linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      calc |∫ u in (2 : ℝ)..T, φ u| ≤ ∫ u in (2 : ℝ)..T, |φ u| :=
            intervalIntegral.abs_integral_le_integral_abs hT
        _ ≤ 2 * C₁ * Real.log (T / 2) := by rw [← hval]; exact hmono
        _ ≤ 2 * C₁ * Real.log T := by
            have : (0 : ℝ) ≤ 2 * C₁ := by linarith
            nlinarith
    linarith
  have hIm : ∀ T : ℝ, (∫ u in (0 : ℝ)..T,
      Complex.I / 2 * Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I)).im
        = ∫ u in (0 : ℝ)..T,
            1 / 2 * (Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I)).re := by
    intro T
    have hinteg : IntervalIntegrable
        (fun u : ℝ => Complex.I / 2 * Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I))
        MeasureTheory.volume 0 T :=
      (continuous_const.mul continuous_digamma_quarter_line).intervalIntegrable 0 T
    have h := Complex.imCLM.intervalIntegral_comp_comm hinteg
    simp only [Complex.imCLM_apply] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp [Complex.mul_im]
  set A : ℝ := |(logGamma (1 / 4 : ℂ)).im| + C₃ / 2 + K with hA
  have hA0 : (0 : ℝ) ≤ A := by
    have := abs_nonneg (logGamma (1 / 4 : ℂ)).im
    rw [hA]
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨A / Real.log 2 + C₁, by positivity, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hth : theta T = (logGamma (1 / 4 : ℂ)).im
      + (∫ u in (0 : ℝ)..T, 1 / 2 * (Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I)).re)
      - T / 2 * Real.log Real.pi := by
    rw [theta, ← hIm T, ← logGamma_quarter_line_sub T, Complex.sub_im]
    ring
  have hRL : (∫ u in (0 : ℝ)..T, (Complex.digamma (1 / 4 + (u : ℂ) / 2 * Complex.I)).re)
      = (∫ u in (0 : ℝ)..T, Real.log ‖(1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I‖)
        + ∫ u in (0 : ℝ)..T, φ u := by
    rw [hφ, intervalIntegral.integral_sub (hcontD.intervalIntegrable 0 T)
      (hcontL.intervalIntegrable 0 T)]
    ring
  have hπ : Real.log (T / (2 * Real.pi)) = Real.log (T / 2) - Real.log Real.pi := by
    rw [show T / (2 * Real.pi) = T / 2 / Real.pi from by rw [div_div],
      Real.log_div (by positivity) Real.pi_ne_zero]
  have hfinal : theta T - (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)
      = (logGamma (1 / 4 : ℂ)).im
        + 1 / 2 * ((∫ u in (0 : ℝ)..T, Real.log ‖(1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I‖)
            - (T * Real.log (T / 2) - T))
        + 1 / 2 * ∫ u in (0 : ℝ)..T, φ u := by
    rw [hth, hπ, intervalIntegral.integral_const_mul, hRL]
    ring
  rw [hfinal, abs_le]
  obtain ⟨he1, he2⟩ := abs_le.1 (hlogint T hT)
  obtain ⟨hd1, hd2⟩ := abs_le.1 (hsplit T hT)
  have hc1 := le_abs_self (logGamma (1 / 4 : ℂ)).im
  have hc2 := neg_abs_le (logGamma (1 / 4 : ℂ)).im
  have hstep : A ≤ A / Real.log 2 * Real.log T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith [mul_le_mul_of_nonneg_left hlogT hA0]
  have hC₁T : (0 : ℝ) ≤ C₁ * Real.log T := by
    have : (0 : ℝ) ≤ Real.log T := le_trans hlog2.le hlogT
    positivity
  rw [hA] at hstep
  constructor
  · nlinarith
  · nlinarith

end ZetaZeros
