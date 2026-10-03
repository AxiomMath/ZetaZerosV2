/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
public import ZetaZeros.Landau.Formula
public import ZetaZeros.Landau.Perron

/-!
# The zeta function and its logarithmic derivative outside the critical strip

The zeros of `ζ` in the closed half-plane `re s ≤ 0`, bounds for `ζ' / ζ` to the left of the
critical strip and on `re s ≥ 3/2`, and the Hadamard partial fraction for `ζ' / ζ` on the
half-plane `-2 < re s`, together with its truncation to the zeros near a given height.

## The trivial zeros of `ζ`

The asymmetric functional equation `ζ (1 - w) = 2 (2π)^(-w) Γ w cos (π w / 2) ζ w`
(`riemannZeta_one_sub`) writes `ζ (1 - w)` as `cos (π w / 2)` times a factor that is analytic and
nonvanishing on `re w > 1`. Hence on `re s ≤ 0` the zeros of `ζ` are exactly the negative even
integers, and each is simple.

## Main results

* `ZetaZeros.riemannZeta_eq_zero_iff_of_re_nonpos`: for `re s ≤ 0`, `ζ s = 0 ↔ ∃ n : ℕ,
  s = -2 * (n + 1)`.
* `ZetaZeros.riemannZeta_ne_zero_of_re_nonpos`: away from the negative even integers, `ζ` does not
  vanish in `re s ≤ 0`.
* `ZetaZeros.deriv_riemannZeta_neg_two_mul_ne_zero`,
  `ZetaZeros.analyticOrderAt_riemannZeta_neg_two_mul`: each trivial zero is simple.
* `ZetaZeros.deriv_riemannZeta_div_eq_of_re_neg`: the reflection formula for `ζ' / ζ`.
* `ZetaZeros.exists_norm_deriv_riemannZeta_div_le_of_re_eq_neg_odd`,
  `ZetaZeros.exists_norm_deriv_riemannZeta_div_le_of_re_le_neg_one`:
  `‖(ζ'/ζ)(s)‖ ≪ log (‖s‖ + 2)` on the lines `re s = -(2m+1)`, and on all of `re s ≤ -1` once
  `|im s| ≥ 1`.
* `ZetaZeros.exists_norm_digamma_le_log_of_two_le_re`: `‖digamma w‖ ≪ log (‖w‖ + 2)` on `re w ≥ 2`.
* `ZetaZeros.exists_norm_deriv_riemannZeta_div_le_of_three_halves_le_re`: `ζ' / ζ` is bounded on
  the closed half-plane `re s ≥ 3/2`.
* `ZetaZeros.exists_logDeriv_riemannZeta_eq_add_tsum_allZeros_of_re_neg_two_lt`: the Hadamard
  partial fraction for `ζ' / ζ` on the half-plane `-2 < re s`.
* `ZetaZeros.exists_norm_deriv_riemannZeta_div_sub_tsum_allZeros_le`: for `|im s| ≥ 3` and
  `-1 ≤ re s ≤ 3/2`, that partial fraction minus its sum over zeros is `O(log |im s|)`.
* `ZetaZeros.exists_norm_deriv_riemannZeta_div_sub_tsum_near_le`: in the same region, `ζ' / ζ` is
  the sum of `m_ρ / (s - ρ)` over the zeros with `|im ρ - im s| ≤ 1`, up to `O(log |im s|)`.
-/

@[expose] public section

namespace ZetaZeros

open Complex
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-- A point of the open right half-plane is not a nonpositive integer. -/
private lemma ne_neg_natCast_of_re_pos {w : ℂ} (hw : 0 < w.re) (m : ℕ) : w ≠ -m := by
  rintro rfl
  simp only [neg_re, natCast_re] at hw
  linarith [Nat.cast_nonneg (α := ℝ) m]

private lemma ne_one_of_one_lt_re {w : ℂ} (hw : 1 < w.re) : w ≠ 1 := fun h => by
  rw [h] at hw; simp at hw

private lemma two_mul_pi_cast_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

/-- The factor `zetaReflectionFactor w` with `ζ (1 - w) = zetaReflectionFactor w * cos (π w / 2)`
in the functional equation `riemannZeta_one_sub`. -/
private noncomputable def zetaReflectionFactor (w : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w * riemannZeta w

private lemma zetaReflectionFactor_ne_zero {w : ℂ} (hw : 1 ≤ w.re) :
    zetaReflectionFactor w ≠ 0 := by
  have hwpos : 0 < w.re := lt_of_lt_of_le one_pos hw
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_)
    (Complex.Gamma_ne_zero (ne_neg_natCast_of_re_pos hwpos)))
    (riemannZeta_ne_zero_of_one_le_re hw)
  exact fun h => two_mul_pi_cast_ne_zero ((Complex.cpow_eq_zero_iff _ _).mp h).1

private lemma differentiableAt_zetaReflectionFactor {w : ℂ} (hw : 1 < w.re) :
    DifferentiableAt ℂ zetaReflectionFactor w := by
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_
    (Complex.differentiableAt_Gamma w (ne_neg_natCast_of_re_pos (lt_trans one_pos hw))))
    (differentiableAt_riemannZeta (ne_one_of_one_lt_re hw))
  exact (DifferentiableAt.const_cpow differentiableAt_id.neg
    (Or.inl two_mul_pi_cast_ne_zero)).const_mul 2

/-- The functional equation, with the cosine factored out. -/
private lemma riemannZeta_one_sub_eq {w : ℂ} (hw : 1 < w.re) :
    riemannZeta (1 - w) = zetaReflectionFactor w * Complex.cos (Real.pi * w / 2) := by
  rw [riemannZeta_one_sub (ne_neg_natCast_of_re_pos (lt_trans one_pos hw))
    (ne_one_of_one_lt_re hw), zetaReflectionFactor]
  ring

/-- **The trivial-zero inventory.** In the closed half-plane `re s ≤ 0` the zeros of `ζ` are
exactly the negative even integers `-2, -4, -6, …`. -/
@[zz_tag "lem_zeta_zero_nonpos"]
theorem riemannZeta_eq_zero_iff_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  refine ⟨fun hζ => ?_, fun ⟨n, hn⟩ => hn ▸ riemannZeta_neg_two_mul_nat_add_one n⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hζ
    norm_num at hζ
  set w : ℂ := 1 - s with hwdef
  have hwre : 1 ≤ w.re := by simp only [hwdef, sub_re, one_re]; linarith
  have hw1 : w ≠ 1 := by
    simp only [hwdef]
    exact fun h => hs0 (by linear_combination -h)
  have hwn : ∀ n : ℕ, w ≠ -n := ne_neg_natCast_of_re_pos (lt_of_lt_of_le one_pos hwre)
  have hsw : (1 : ℂ) - w = s := by simp [hwdef]
  have key := riemannZeta_one_sub hwn hw1
  rw [hsw, hζ] at key
  have hcos : Complex.cos (Real.pi * w / 2) = 0 := by
    have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
    have hz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
    have hp : ((2 * (Real.pi : ℂ))) ^ (-w) ≠ 0 := fun h =>
      two_mul_pi_cast_ne_zero ((Complex.cpow_eq_zero_iff _ _).mp h).1
    rcases mul_eq_zero.mp key.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · exact absurd h hp
        · exact absurd h hG
      · exact h
    · exact absurd h hz
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hwk : w = 2 * (k : ℂ) + 1 := mul_left_cancel₀ hpi (by linear_combination 2 * hk)
  have hsk : s = -2 * (k : ℂ) := by rw [← hsw, hwk]; ring
  have hkre : s.re = -2 * (k : ℝ) := by rw [hsk]; simp
  have hk0 : 0 ≤ k := by
    have h1 : -2 * (k : ℝ) ≤ 0 := hkre ▸ hs
    have h2 : (0 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast h2
  have hkne : k ≠ 0 := by
    rintro rfl
    exact hs0 (by simpa using hsk)
  refine ⟨(k - 1).toNat, ?_⟩
  have hcast : (((k - 1).toNat : ℤ) : ℂ) = (k : ℂ) - 1 := by
    rw [Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  rw [hsk]
  push_cast at hcast ⊢
  rw [hcast]
  ring

/-- In `re s ≤ 0`, `ζ` vanishes nowhere except at the negative even integers. -/
theorem riemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0)
    (h : ∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1)) : riemannZeta s ≠ 0 := fun hζ => by
  obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hs).mp hζ
  exact h n hn

/-- **Each trivial zero is simple.** The derivative of `ζ` at `-2 (n + 1)` is nonzero. -/
theorem deriv_riemannZeta_neg_two_mul_ne_zero (n : ℕ) :
    deriv riemannZeta (-2 * ((n : ℂ) + 1)) ≠ 0 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set w₀ : ℂ := 2 * (n : ℂ) + 3 with hw₀
  have hw₀re : w₀.re = 2 * (n : ℝ) + 3 := by simp [hw₀]
  have hw₀lt : 1 < w₀.re := by rw [hw₀re]; linarith
  have hsw : (1 : ℂ) - w₀ = -2 * ((n : ℂ) + 1) := by rw [hw₀]; ring
  have hcos0 : Complex.cos (Real.pi * w₀ / 2) = 0 := by
    refine Complex.cos_eq_zero_iff.mpr ⟨(n : ℤ) + 1, ?_⟩
    rw [hw₀]; push_cast; ring
  have hsin : Complex.sin (Real.pi * w₀ / 2) ≠ 0 := by
    intro h
    have h2 := Complex.sin_sq_add_cos_sq (Real.pi * w₀ / 2)
    rw [h, hcos0] at h2
    norm_num at h2
  have hζd : DifferentiableAt ℂ riemannZeta (1 - w₀) := by
    refine differentiableAt_riemannZeta ?_
    rw [hsw]
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hL : HasDerivAt (fun w : ℂ => riemannZeta (1 - w))
      (deriv riemannZeta (1 - w₀) * (-1)) w₀ := by
    have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) w₀ := by
      simpa using (hasDerivAt_id w₀).const_sub 1
    exact HasDerivAt.comp w₀ hζd.hasDerivAt h1
  have hcosD : HasDerivAt (fun w : ℂ => Complex.cos (Real.pi * w / 2))
      (-Complex.sin (Real.pi * w₀ / 2) * ((Real.pi : ℂ) / 2)) w₀ := by
    have h1 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w / 2) ((Real.pi : ℂ) / 2) w₀ := by
      simpa using ((hasDerivAt_id w₀).const_mul (Real.pi : ℂ)).div_const 2
    exact HasDerivAt.comp w₀ (Complex.hasDerivAt_cos _) h1
  have hR : HasDerivAt (fun w : ℂ => zetaReflectionFactor w * Complex.cos (Real.pi * w / 2))
      (deriv zetaReflectionFactor w₀ * Complex.cos (Real.pi * w₀ / 2)
        + zetaReflectionFactor w₀
          * (-Complex.sin (Real.pi * w₀ / 2) * ((Real.pi : ℂ) / 2))) w₀ :=
    (differentiableAt_zetaReflectionFactor hw₀lt).hasDerivAt.mul hcosD
  have hev : (fun w : ℂ => zetaReflectionFactor w * Complex.cos (Real.pi * w / 2))
      =ᶠ[nhds w₀] (fun w : ℂ => riemannZeta (1 - w)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw₀lt] with w hw
    exact (riemannZeta_one_sub_eq hw).symm
  have huniq := (hL.congr_of_eventuallyEq hev).unique hR
  rw [hcos0] at huniq
  rw [← hsw]
  intro h0
  rw [h0] at huniq
  simp only [zero_mul, mul_zero, zero_add] at huniq
  exact (mul_ne_zero (zetaReflectionFactor_ne_zero hw₀lt.le)
    (mul_ne_zero (neg_ne_zero.mpr hsin)
      (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero))) huniq.symm

/-- `ζ` is analytic away from `1`. -/
private lemma analyticAt_riemannZeta' {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  refine DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 1}) (fun z hz => ?_) ?_
  · exact (differentiableAt_riemannZeta hz).differentiableWithinAt
  · exact (isOpen_ne).mem_nhds hs

/-- **Each trivial zero is simple**, stated as an order: the analytic order of `ζ` at
`-2 (n + 1)` is `1`. -/
@[zz_tag "lem_zeta_trivial_zero_simple"]
theorem analyticOrderAt_riemannZeta_neg_two_mul (n : ℕ) :
    analyticOrderAt riemannZeta (-2 * ((n : ℂ) + 1)) = 1 := by
  have hne : (-2 * ((n : ℂ) + 1)) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (analyticAt_riemannZeta' hne).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (riemannZeta_neg_two_mul_nat_add_one n) (deriv_riemannZeta_neg_two_mul_ne_zero n)

/-!
## `ζ' / ζ` far to the left

For `re s < 0` away from the trivial zeros, with `w = 1 - s`,

`(ζ'/ζ)(s) = log (2π) - digamma w - (ζ'/ζ)(w) + (π/2) ⬝ cos (π s / 2) / sin (π s / 2)`.
-/

/-- `ζ' / ζ` is bounded on the closed half-plane `re s ≥ 3/2`. -/
theorem exists_norm_deriv_riemannZeta_div_le_of_three_halves_le_re :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, 3 / 2 ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ A := by
  have hre : ((3 / 2 : ℂ)).re = 3 / 2 := by simp
  have hsum0 : Summable fun n : ℕ => ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (3 / 2 : ℂ))
      (by rw [hre]; norm_num)).norm
  have hA0 : 0 ≤ ∑' n : ℕ, ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  refine ⟨(∑' n : ℕ, ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖) + 1, by linarith, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  have hle : ∀ n : ℕ, ‖LSeries.term ↗Λ s n‖ ≤ ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ := fun n =>
    LSeries.norm_term_le_of_re_le_re ↗Λ (by rw [hre]; exact hs) n
  have hsum : Summable fun n : ℕ => ‖LSeries.term ↗Λ s n‖ :=
    hsum0.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  have hneg : deriv riemannZeta s / riemannZeta s = -LSeries ↗Λ s := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1, neg_div, neg_neg]
  rw [hneg, norm_neg, show LSeries ↗Λ s = ∑' n : ℕ, LSeries.term ↗Λ s n from rfl]
  calc ‖∑' n : ℕ, LSeries.term ↗Λ s n‖
      ≤ ∑' n : ℕ, ‖LSeries.term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ := Summable.tsum_le_tsum hle hsum hsum0
    _ ≤ _ := by linarith

private lemma logDeriv_const_cpow_neg {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    logDeriv (fun z : ℂ => a ^ (-z)) w = -Complex.log a := by
  have hd : HasDerivAt (fun z : ℂ => a ^ (-z)) (a ^ (-w) * Complex.log a * (-1)) w :=
    HasDerivAt.const_cpow (hasDerivAt_neg w) (Or.inl ha)
  have hne : a ^ (-w) ≠ 0 := fun h => ha ((Complex.cpow_eq_zero_iff _ _).mp h).1
  rw [logDeriv_apply, hd.deriv]
  field_simp

private lemma log_two_mul_pi :
    Complex.log (2 * (Real.pi : ℂ)) = (Real.log (2 * Real.pi) : ℂ) := by
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
  exact (Complex.ofReal_log (by positivity)).symm

private lemma logDeriv_zetaReflectionFactor {w : ℂ} (hw : 1 < w.re) :
    logDeriv zetaReflectionFactor w
      = -(Real.log (2 * Real.pi) : ℂ) + digamma w + deriv riemannZeta w / riemannZeta w := by
  have hwn : ∀ m : ℕ, w ≠ -m := ne_neg_natCast_of_re_pos (lt_trans one_pos hw)
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
  have hz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw.le
  have hcp : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := fun h =>
    two_mul_pi_cast_ne_zero ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hdG : DifferentiableAt ℂ Complex.Gamma w := Complex.differentiableAt_Gamma w hwn
  have hdz : DifferentiableAt ℂ riemannZeta w :=
    differentiableAt_riemannZeta (ne_one_of_one_lt_re hw)
  set F : ℂ → ℂ := fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z) with hFdef
  have hdF : DifferentiableAt ℂ F w :=
    (DifferentiableAt.const_cpow differentiableAt_id.neg
      (Or.inl two_mul_pi_cast_ne_zero)).const_mul 2
  have hFne : F w ≠ 0 := mul_ne_zero two_ne_zero hcp
  have hfun : zetaReflectionFactor = (F * Complex.Gamma) * riemannZeta := by
    funext z; simp [zetaReflectionFactor, hFdef, Pi.mul_apply]
  have hFG : (F * Complex.Gamma) w ≠ 0 := by
    simpa [Pi.mul_apply] using mul_ne_zero hFne hG
  rw [hfun, logDeriv_mul w hFG hz (hdF.mul hdG) hdz,
    logDeriv_mul (f := F) (g := Complex.Gamma) w hFne hG hdF hdG,
    hFdef, logDeriv_const_mul w 2 two_ne_zero, logDeriv_const_cpow_neg two_mul_pi_cast_ne_zero,
    ← Complex.digamma_def, logDeriv_apply, log_two_mul_pi]

private lemma differentiableAt_cos_half (w : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.cos (Real.pi * z / 2)) w :=
  (Complex.differentiable_cos _).comp w ((differentiableAt_id.const_mul _).div_const 2)

private lemma logDeriv_cos_half {w : ℂ} (hc : Complex.cos (Real.pi * w / 2) ≠ 0) :
    logDeriv (fun z : ℂ => Complex.cos (Real.pi * z / 2)) w
      = -((Real.pi : ℂ) / 2)
        * (Complex.sin (Real.pi * w / 2) / Complex.cos (Real.pi * w / 2)) := by
  have h1 : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z / 2) ((Real.pi : ℂ) / 2) w := by
    simpa using ((hasDerivAt_id w).const_mul (Real.pi : ℂ)).div_const 2
  have hd : HasDerivAt (fun z : ℂ => Complex.cos (Real.pi * z / 2))
      (-Complex.sin (Real.pi * w / 2) * ((Real.pi : ℂ) / 2)) w :=
    HasDerivAt.comp w (Complex.hasDerivAt_cos _) h1
  rw [logDeriv_apply, hd.deriv]
  field_simp

private lemma logDeriv_riemannZeta_one_sub_comp {w : ℂ} (hw : 1 < w.re) :
    logDeriv (fun z : ℂ => riemannZeta (1 - z)) w
      = -(deriv riemannZeta (1 - w) / riemannZeta (1 - w)) := by
  have hone : (1 : ℂ) - w ≠ 1 := by
    intro h
    have hre : ((1 : ℂ) - w).re = (1 : ℂ).re := by rw [h]
    simp only [sub_re, one_re] at hre
    linarith
  have hcomp := logDeriv_comp (f := riemannZeta) (g := fun z : ℂ => 1 - z) (x := w)
    (differentiableAt_riemannZeta hone) (by fun_prop)
  simp only [Function.comp_def] at hcomp
  have hdv : deriv (fun z : ℂ => 1 - z) w = -1 := by simp
  rw [hcomp, logDeriv_apply, hdv]
  ring

/-- **The reflection formula for `ζ' / ζ`.** For `re s < 0`,

`(ζ'/ζ)(s) = log (2π) - digamma (1 - s) - (ζ'/ζ)(1 - s)
  + (π/2) ⬝ cos (π s / 2) / sin (π s / 2)`,

provided `sin (π s / 2) ≠ 0`, that is, `s` is not an even integer. -/
theorem deriv_riemannZeta_div_eq_of_re_neg {s : ℂ} (hs : s.re < 0)
    (hsin : Complex.sin (Real.pi * s / 2) ≠ 0) :
    deriv riemannZeta s / riemannZeta s
      = (Real.log (2 * Real.pi) : ℂ) - digamma (1 - s)
        - deriv riemannZeta (1 - s) / riemannZeta (1 - s)
        + (Real.pi : ℂ) / 2
          * (Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)) := by
  set w : ℂ := 1 - s with hwdef
  have hw : 1 < w.re := by simp only [hwdef, sub_re, one_re]; linarith
  have hsw : (1 : ℂ) - w = s := by simp [hwdef]
  have harg : Real.pi * w / 2 = (Real.pi : ℂ) / 2 - Real.pi * s / 2 := by rw [hwdef]; ring
  have hcos : Complex.cos (Real.pi * w / 2) = Complex.sin (Real.pi * s / 2) := by
    rw [harg, Complex.cos_pi_div_two_sub]
  have hsn : Complex.sin (Real.pi * w / 2) = Complex.cos (Real.pi * s / 2) := by
    rw [harg, Complex.sin_pi_div_two_sub]
  have hc : Complex.cos (Real.pi * w / 2) ≠ 0 := hcos ▸ hsin
  have hev : (fun z : ℂ => riemannZeta (1 - z))
      =ᶠ[nhds w] (zetaReflectionFactor * fun z : ℂ => Complex.cos (Real.pi * z / 2)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with z hz
    simpa [Pi.mul_apply] using riemannZeta_one_sub_eq hz
  have hsplit : logDeriv (fun z : ℂ => riemannZeta (1 - z)) w
      = logDeriv zetaReflectionFactor w
        + logDeriv (fun z : ℂ => Complex.cos (Real.pi * z / 2)) w := by
    have h1 : logDeriv (fun z : ℂ => riemannZeta (1 - z)) w
        = logDeriv (zetaReflectionFactor * fun z : ℂ => Complex.cos (Real.pi * z / 2)) w := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [h1, logDeriv_mul w (zetaReflectionFactor_ne_zero hw.le) hc
      (differentiableAt_zetaReflectionFactor hw) (differentiableAt_cos_half w)]
  rw [logDeriv_riemannZeta_one_sub_comp hw, logDeriv_zetaReflectionFactor hw,
    logDeriv_cos_half hc, hsw, hcos, hsn] at hsplit
  linear_combination -hsplit

/-! ### The growth of `digamma` on `re w ≥ 2` -/

/-- `∑_{k < n} 1/(k+2) ≤ log (n+1)`: the harmonic tail, from `log x ≥ 1 - 1/x`. -/
private lemma sum_one_div_add_two_le_log (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 2) ≤ Real.log (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have key : Real.log (((n : ℝ) + 1) / ((n : ℝ) + 2)) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hn1.ne' hn2.ne',
      show ((n : ℝ) + 1) / ((n : ℝ) + 2) - 1 = -(1 / ((n : ℝ) + 2)) by field_simp; ring] at key
    rw [Finset.sum_range_succ]
    push_cast
    rw [show ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 by ring]
    linarith

/-- The `digamma` recurrence iterated: `ψ (w + n) = ψ w + ∑_{k < n} 1/(w + k)`. -/
private lemma digamma_add_natCast {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    digamma (w + n) = digamma w + ∑ k ∈ Finset.range n, (w + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : ∀ m : ℕ, w + (n : ℂ) ≠ -m := by
      intro m h
      have hre := congrArg Complex.re h
      simp only [add_re, natCast_re, neg_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
    rw [show w + ((n + 1 : ℕ) : ℂ) = (w + n) + 1 by push_cast; ring,
      Complex.digamma_apply_add_one _ hne, ih, Finset.sum_range_succ]
    ring

/-- **`digamma` grows like a logarithm on `re w ≥ 2`.** There is a constant `C` with
`‖digamma w‖ ≤ C log (‖w‖ + 2)` for every `w` with `re w ≥ 2`. -/
theorem exists_norm_digamma_le_log_of_two_le_re :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 2 ≤ w.re → ‖digamma w‖ ≤ C * Real.log (‖w‖ + 2) := by
  obtain ⟨C₀, hC₀, hbd⟩ := Complex.exists_norm_digamma_le_log (a := 2) (b := 3) two_pos
  refine ⟨C₀ + 1, by linarith, fun w hw => ?_⟩
  have hw0 : (0 : ℝ) ≤ w.re := by linarith
  have hnormw : w.re ≤ ‖w‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm w)
  have hlogpos : 0 ≤ Real.log (‖w‖ + 2) :=
    Real.log_nonneg (by linarith [norm_nonneg w])
  have hfl2 : 2 ≤ ⌊w.re⌋₊ := Nat.le_floor (by exact_mod_cast hw)
  have hfl_le : (⌊w.re⌋₊ : ℝ) ≤ w.re := Nat.floor_le hw0
  have hlt_fl : w.re < (⌊w.re⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one w.re
  set n : ℕ := ⌊w.re⌋₊ - 2 with hn
  have hncast : (n : ℝ) = (⌊w.re⌋₊ : ℝ) - 2 := by
    rw [hn, Nat.cast_sub hfl2]; norm_num
  set u : ℂ := w - n with hu
  have hure : u.re = w.re - n := by simp [hu]
  have huim : u.im = w.im := by simp [hu]
  have hu2 : 2 ≤ u.re := by rw [hure, hncast]; linarith
  have hu3 : u.re ≤ 3 := by rw [hure, hncast]; linarith
  have hwu : w = u + n := by rw [hu]; ring
  have hstrip : ‖digamma u‖ ≤ C₀ * Real.log (‖w‖ + 2) := by
    refine le_trans (hbd u hu2 hu3) ?_
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hC₀.le
    rw [huim]
    linarith [Complex.abs_im_le_norm w]
  have hterm : ∀ k ∈ Finset.range n, ‖(u + (k : ℂ))⁻¹‖ ≤ (1 : ℝ) / (k + 2) := by
    intro k _
    have hre : 2 + (k : ℝ) ≤ (u + (k : ℂ)).re := by
      simp only [add_re, natCast_re]
      linarith
    have hnm : (k : ℝ) + 2 ≤ ‖u + (k : ℂ)‖ :=
      le_trans (by linarith) (le_trans (le_abs_self _) (Complex.abs_re_le_norm (u + (k : ℂ))))
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hnm
  have hsum : ‖∑ k ∈ Finset.range n, (u + (k : ℂ))⁻¹‖ ≤ Real.log (‖w‖ + 2) := by
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
    refine le_trans (sum_one_div_add_two_le_log n) (Real.log_le_log (by positivity) ?_)
    rw [hncast]
    linarith
  calc ‖digamma w‖
      = ‖digamma u + ∑ k ∈ Finset.range n, (u + (k : ℂ))⁻¹‖ := by
        rw [hwu, digamma_add_natCast (lt_of_lt_of_le two_pos hu2)]
    _ ≤ ‖digamma u‖ + ‖∑ k ∈ Finset.range n, (u + (k : ℂ))⁻¹‖ := norm_add_le _ _
    _ ≤ C₀ * Real.log (‖w‖ + 2) + Real.log (‖w‖ + 2) := add_le_add hstrip hsum
    _ = (C₀ + 1) * Real.log (‖w‖ + 2) := by ring

/-! ### The cotangent factor on a line midway between trivial zeros -/

/-- On the vertical line `re s = -(2m+1)` the cotangent factor of the reflection formula is bounded
by `1`, and `sin (π s / 2)` does not vanish. -/
private lemma norm_cos_div_sin_le_one_of_re_eq_neg_odd (m : ℕ) {s : ℂ}
    (hs : s.re = -(2 * m + 1)) :
    Complex.sin (Real.pi * s / 2) ≠ 0
      ∧ ‖Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)‖ ≤ 1 := by
  set z : ℂ := Real.pi * s / 2 with hz
  have hzre : z.re = -((m : ℝ) * Real.pi) - Real.pi / 2 := by
    simp only [hz, div_re, mul_re, ofReal_re, ofReal_im]
    rw [hs]
    simp
    ring
  have hcos0 : Real.cos z.re = 0 := by
    rw [hzre, show -((m : ℝ) * Real.pi) - Real.pi / 2 = -((m : ℝ) * Real.pi + Real.pi / 2) by ring,
      Real.cos_neg, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
    simp
  have habs : |Real.sin z.re| = 1 := by
    have h1 := Real.sin_sq_add_cos_sq z.re
    rw [hcos0] at h1
    have h2 : |Real.sin z.re| ^ 2 = 1 := by rw [sq_abs]; linarith
    nlinarith [abs_nonneg (Real.sin z.re)]
  have hsinz : Complex.sin z = ((Real.sin z.re * Real.cosh z.im : ℝ) : ℂ) := by
    rw [Complex.sin_eq z, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, hcos0]
    push_cast; ring
  have hcosz : Complex.cos z = ((Real.sin z.re * Real.sinh z.im : ℝ) : ℂ) * (-I) := by
    rw [Complex.cos_eq z, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, hcos0]
    push_cast; ring
  have hcoshpos : (0 : ℝ) < Real.cosh z.im := lt_of_lt_of_le zero_lt_one (Real.one_le_cosh _)
  have hnsin : ‖Complex.sin z‖ = Real.cosh z.im := by
    rw [hsinz, Complex.norm_real, Real.norm_eq_abs, abs_mul, habs, one_mul, abs_of_pos hcoshpos]
  have hncos : ‖Complex.cos z‖ = |Real.sinh z.im| := by
    rw [hcosz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, habs, one_mul]
    simp
  refine ⟨fun h => by rw [h] at hnsin; simp at hnsin; linarith, ?_⟩
  rw [norm_div, hnsin, hncos, div_le_one hcoshpos]
  rcases abs_cases (Real.sinh z.im) with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]; exact (Real.sinh_lt_cosh _).le
  · rw [h1, ← Real.sinh_neg, ← Real.cosh_neg]; exact (Real.sinh_lt_cosh _).le

private lemma norm_sin_sq (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sin_eq z]
  simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh]
  nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq z.im]

private lemma norm_cos_sq (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.cos_eq z]
  simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh]
  nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq z.im]

/-- At height `|im w| ≥ 1` the cotangent factor is bounded by `2`, whatever `re w` is. -/
private lemma norm_cos_div_sin_le_two_of_one_le_abs_im {w : ℂ} (hw : 1 ≤ |w.im|) :
    Complex.sin (Real.pi * w / 2) ≠ 0
      ∧ ‖Complex.cos (Real.pi * w / 2) / Complex.sin (Real.pi * w / 2)‖ ≤ 2 := by
  set z : ℂ := Real.pi * w / 2 with hz
  have hzim : z.im = Real.pi * w.im / 2 := by
    simp only [hz, div_im, mul_im, ofReal_re, ofReal_im]
    simp
    ring
  have hbeta : Real.pi / 2 ≤ |z.im| := by
    rw [hzim, abs_div, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hsinh1 : (1 : ℝ) < Real.sinh |z.im| := by
    have h1 : Real.pi / 2 < Real.sinh |z.im| :=
      lt_of_lt_of_le (Real.self_lt_sinh_iff.mpr (by positivity)) (Real.sinh_le_sinh.mpr hbeta)
    linarith [Real.two_le_pi]
  have hsq : Real.sinh z.im ^ 2 = Real.sinh |z.im| ^ 2 := by
    rcases abs_cases z.im with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, Real.sinh_neg]; ring
  have hone : (1 : ℝ) ≤ Real.sinh z.im ^ 2 := by nlinarith
  have hsinsq : (1 : ℝ) ≤ ‖Complex.sin z‖ ^ 2 := by
    rw [norm_sin_sq]
    nlinarith [sq_nonneg (Real.sin z.re)]
  have hsinpos : 0 < ‖Complex.sin z‖ := by
    rcases (norm_nonneg (Complex.sin z)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hsinsq; norm_num at hsinsq
  refine ⟨fun h => by rw [h] at hsinpos; simp at hsinpos, ?_⟩
  rw [norm_div, div_le_iff₀ hsinpos]
  have hcossq : ‖Complex.cos z‖ ^ 2 ≤ (2 * ‖Complex.sin z‖) ^ 2 := by
    rw [norm_cos_sq, mul_pow, norm_sin_sq]
    nlinarith [Real.sin_sq_add_cos_sq z.re, sq_nonneg (Real.sin z.re)]
  nlinarith [norm_nonneg (Complex.cos z), hsinpos, hcossq]

/-- On `re s ≤ -1`, a bound `K` on the cotangent factor of the reflection formula gives a
logarithmic bound on `ζ' / ζ`. -/
private lemma norm_deriv_riemannZeta_div_le_aux {A C₁ K : ℝ} (hA : 0 < A) (hC₁ : 0 < C₁)
    (hK : 0 ≤ K)
    (hAbd : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ A)
    (hC₁bd : ∀ w : ℂ, 2 ≤ w.re → ‖digamma w‖ ≤ C₁ * Real.log (‖w‖ + 2))
    {s : ℂ} (hs : s.re ≤ -1) (hsin : Complex.sin (Real.pi * s / 2) ≠ 0)
    (hcot : ‖Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)‖ ≤ K) :
    ‖deriv riemannZeta s / riemannZeta s‖
      ≤ (|Real.log (2 * Real.pi)| + A + Real.pi / 2 * K + 2 * C₁) * Real.log (‖s‖ + 2) := by
  have hnorm1 : (1 : ℝ) ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    rw [abs_of_nonpos (by linarith)] at h
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (‖s‖ + 2) := by
    have h3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
    exact le_trans h3.le (Real.log_le_log (by norm_num) (by linarith))
  have hid := deriv_riemannZeta_div_eq_of_re_neg (by linarith) hsin
  have hwre : (2 : ℝ) ≤ ((1 : ℂ) - s).re := by simp only [sub_re, one_re]; linarith
  have hzright : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ A :=
    hAbd _ (by linarith)
  have hdig : ‖digamma (1 - s)‖ ≤ 2 * C₁ * Real.log (‖s‖ + 2) := by
    refine le_trans (hC₁bd _ hwre) ?_
    have hle : ‖(1 : ℂ) - s‖ + 2 ≤ (‖s‖ + 2) ^ 2 := by
      have h1 : ‖(1 : ℂ) - s‖ ≤ 1 + ‖s‖ := by simpa using norm_sub_le (1 : ℂ) s
      nlinarith [norm_nonneg s]
    have h2 : Real.log (‖(1 : ℂ) - s‖ + 2) ≤ 2 * Real.log (‖s‖ + 2) := by
      rw [show (2 : ℝ) * Real.log (‖s‖ + 2) = Real.log ((‖s‖ + 2) ^ 2) by
        rw [Real.log_pow]; push_cast; ring]
      exact Real.log_le_log (by positivity) hle
    nlinarith [hC₁, Real.log_nonneg (show (1 : ℝ) ≤ ‖s‖ + 2 by linarith)]
  have hcotterm : ‖(Real.pi : ℂ) / 2
      * (Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2))‖
      ≤ Real.pi / 2 * K := by
    rw [norm_mul, show ((Real.pi : ℂ) / 2) = (((Real.pi / 2 : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hcot (by positivity)
  have hconst : ‖((Real.log (2 * Real.pi) : ℝ) : ℂ)‖ = |Real.log (2 * Real.pi)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hstep := norm_add_le (((Real.log (2 * Real.pi) : ℝ) : ℂ) - digamma (1 - s)
    - deriv riemannZeta (1 - s) / riemannZeta (1 - s))
    ((Real.pi : ℂ) / 2 * (Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)))
  have hstep2 := norm_sub_le (((Real.log (2 * Real.pi) : ℝ) : ℂ) - digamma (1 - s))
    (deriv riemannZeta (1 - s) / riemannZeta (1 - s))
  have hstep3 := norm_sub_le ((Real.log (2 * Real.pi) : ℝ) : ℂ) (digamma (1 - s))
  have e1 : |Real.log (2 * Real.pi)|
      ≤ |Real.log (2 * Real.pi)| * Real.log (‖s‖ + 2) :=
    le_mul_of_one_le_right (abs_nonneg _) hlog1
  have e2 : A ≤ A * Real.log (‖s‖ + 2) := le_mul_of_one_le_right hA.le hlog1
  have e3 : Real.pi / 2 * K ≤ Real.pi / 2 * K * Real.log (‖s‖ + 2) :=
    le_mul_of_one_le_right (mul_nonneg (by positivity) hK) hlog1
  rw [hid]
  nlinarith [hstep, hstep2, hstep3, hconst, hdig, hzright, hcotterm, e1, e2, e3]

/-- **`ζ' / ζ` on the vertical lines midway between trivial zeros.** There is a constant `C` with

`‖(ζ'/ζ)(s)‖ ≤ C log (‖s‖ + 2)` whenever `re s = -(2m+1)` for a natural number `m`. -/
theorem exists_norm_deriv_riemannZeta_div_le_of_re_eq_neg_odd :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (s : ℂ), s.re = -(2 * m + 1) →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log (‖s‖ + 2) := by
  obtain ⟨A, hA, hAbd⟩ := exists_norm_deriv_riemannZeta_div_le_of_three_halves_le_re
  obtain ⟨C₁, hC₁, hC₁bd⟩ := exists_norm_digamma_le_log_of_two_le_re
  refine ⟨|Real.log (2 * Real.pi)| + A + Real.pi / 2 * 1 + 2 * C₁, by positivity,
    fun m s hs => ?_⟩
  obtain ⟨hsin, hcot⟩ := norm_cos_div_sin_le_one_of_re_eq_neg_odd m hs
  exact norm_deriv_riemannZeta_div_le_aux hA hC₁ zero_le_one hAbd hC₁bd
    (by rw [hs]; linarith [Nat.cast_nonneg (α := ℝ) m]) hsin hcot

/-- **`ζ' / ζ` to the left, away from the real axis.** There is a constant `C` with

`‖(ζ'/ζ)(s)‖ ≤ C log (‖s‖ + 2)` for every `s` with `re s ≤ -1` and `|im s| ≥ 1`. -/
theorem exists_norm_deriv_riemannZeta_div_le_of_re_le_neg_one :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ≤ -1 → 1 ≤ |s.im| →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log (‖s‖ + 2) := by
  obtain ⟨A, hA, hAbd⟩ := exists_norm_deriv_riemannZeta_div_le_of_three_halves_le_re
  obtain ⟨C₁, hC₁, hC₁bd⟩ := exists_norm_digamma_le_log_of_two_le_re
  refine ⟨|Real.log (2 * Real.pi)| + A + Real.pi / 2 * 2 + 2 * C₁, by positivity,
    fun s hs him => ?_⟩
  obtain ⟨hsin, hcot⟩ := norm_cos_div_sin_le_two_of_one_le_abs_im him
  exact norm_deriv_riemannZeta_div_le_aux hA hC₁ zero_le_two hAbd hC₁bd hs hsin hcot

/-!
## The partial fraction for `ζ' / ζ` past the imaginary axis
-/

/-- **The Hadamard partial fraction for `ζ' / ζ` on `-2 < re s`.** For one constant `B` and every
`s` in that half-plane which is neither `1` nor a zero of `ζ`,

`(ζ'/ζ)(s) = B + ∑_{ρ ∈ 𝒩*} m_ρ (1/(s-ρ) + 1/ρ) - 1/(s-1) + log π / 2 - digamma (s/2 + 1) / 2`.
-/
theorem exists_logDeriv_riemannZeta_eq_add_tsum_allZeros_of_re_neg_two_lt :
    ∃ B : ℂ, ∀ s : ℂ, -2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 →
      deriv riemannZeta s / riemannZeta s
        = B + (∑' ρ : allZeros, (zeroMultiplicity ρ.1 : ℂ) * (1 / (s - ρ.1) + 1 / ρ.1))
          - 1 / (s - 1) + (Real.log Real.pi : ℂ) / 2 - digamma (s / 2 + 1) / 2 := by
  obtain ⟨B, hB⟩ := exists_logDeriv_riemannXi_eq_add_tsum_allZeros
  refine ⟨B, fun s h0 h1 hζ => ?_⟩
  have hz : ∀ ρ ∈ allZeros, s ≠ ρ := fun ρ hρ h => hζ (h ▸ hρ.1)
  rw [(hB s hz).tsum_eq, logDeriv_riemannXi_eq_of_re_neg_two_lt h0 h1 hζ]
  ring

/-- The Hadamard partial fraction for `ζ' / ζ` on `-2 < re s`, as a `HasSum`. -/
private theorem exists_hasSum_logDeriv_riemannZeta_of_re_neg_two_lt :
    ∃ B : ℂ, ∀ s : ℂ, -2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 →
      HasSum (fun ρ : allZeros => (zeroMultiplicity (ρ : ℂ) : ℂ) * (1 / (s - ρ) + 1 / (ρ : ℂ)))
        (deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
          - (Real.log Real.pi : ℂ) / 2 + digamma (s / 2 + 1) / 2 - B) := by
  obtain ⟨B, hB⟩ := exists_logDeriv_riemannXi_eq_add_tsum_allZeros
  refine ⟨B, fun s h0 h1 hζ => ?_⟩
  have hz : ∀ ρ ∈ allZeros, s ≠ ρ := fun ρ hρ h => hζ (h ▸ hρ.1)
  have h := hB s hz
  rw [logDeriv_riemannXi_eq_of_re_neg_two_lt h0 h1 hζ] at h
  convert h using 2
  ring

/-- **Away from the real axis, everything in the partial fraction except the sum over zeros is
`O(log |im s|)`.** For the `B` of
`exists_logDeriv_riemannZeta_eq_add_tsum_allZeros_of_re_neg_two_lt` and a constant `C`,
whenever `|im s| ≥ 3` and `-1 ≤ re s ≤ 3/2` and `ζ s ≠ 0`,

`‖(ζ'/ζ)(s) - B - ∑_{ρ ∈ 𝒩*} m_ρ (1/(s-ρ) + 1/ρ)‖ ≤ C log (|im s| + 3)`. -/
theorem exists_norm_deriv_riemannZeta_div_sub_tsum_allZeros_le :
    ∃ (B : ℂ) (C : ℝ), 0 < C ∧ ∀ s : ℂ, 3 ≤ |s.im| → -1 ≤ s.re → s.re ≤ 3 / 2 →
      riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s - B
          - ∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℂ) * (1 / (s - ρ) + 1 / (ρ : ℂ))‖
        ≤ C * Real.log (|s.im| + 3) := by
  obtain ⟨B, hB⟩ := exists_logDeriv_riemannZeta_eq_add_tsum_allZeros_of_re_neg_two_lt
  obtain ⟨Cψ, hCψ, hψ⟩ := Complex.exists_norm_digamma_le_log (a := 1 / 2) (b := 2) (by norm_num)
  refine ⟨B, 1 / 3 + |Real.log Real.pi| / 2 + Cψ / 2, by positivity, fun s ht hlo hhi hζ => ?_⟩
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at ht
    simp at ht
    linarith
  have hid := hB s (by linarith) hs1 hζ
  have hlog1 : (1 : ℝ) ≤ Real.log (|s.im| + 3) := by
    have h3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
    exact le_trans h3.le (Real.log_le_log (by norm_num) (by linarith))
  have hsm1 : (3 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simp only [sub_im, one_im, sub_zero] at h
    linarith
  have hinv : ‖1 / (s - 1)‖ ≤ 1 / 3 := by
    rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hdig : ‖digamma (s / 2 + 1)‖ ≤ Cψ * Real.log (|s.im| + 3) := by
    refine le_trans (hψ (s / 2 + 1) (by simp; linarith) (by simp; linarith)) ?_
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hCψ.le
    rw [show (s / 2 + 1).im = s.im / 2 by simp, abs_div, show |(2 : ℝ)| = 2 by norm_num]
    linarith [abs_nonneg s.im]
  have heq : deriv riemannZeta s / riemannZeta s - B
      - ∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℂ) * (1 / (s - ρ) + 1 / (ρ : ℂ))
      = -(1 / (s - 1)) + ((Real.log Real.pi : ℝ) : ℂ) / 2 - digamma (s / 2 + 1) / 2 := by
    rw [hid]; ring
  have hc : ‖((Real.log Real.pi : ℝ) : ℂ) / 2‖ = |Real.log Real.pi| / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have hd : ‖digamma (s / 2 + 1) / 2‖ = ‖digamma (s / 2 + 1)‖ / 2 := by
    rw [norm_div]; norm_num
  rw [heq]
  have hA := norm_sub_le (-(1 / (s - 1)) + ((Real.log Real.pi : ℝ) : ℂ) / 2)
    (digamma (s / 2 + 1) / 2)
  have hB2 := norm_add_le (-(1 / (s - 1)) : ℂ) (((Real.log Real.pi : ℝ) : ℂ) / 2)
  have hneg : ‖(-(1 / (s - 1)) : ℂ)‖ = ‖(1 / (s - 1) : ℂ)‖ := norm_neg _
  nlinarith [hA, hB2, hneg, hc, hd, hinv, hdig, hlog1, hCψ, abs_nonneg (Real.log Real.pi)]

/-!
## `ζ' / ζ` near a height

Truncation of the partial fraction for `ζ' / ζ` to the zeros `ρ` with `|im ρ - im s| ≤ 1`.
-/

private noncomputable def rightPoint (s : ℂ) : ℂ := 2 + (s.im : ℂ) * I
private lemma rightPoint_re (s : ℂ) : (rightPoint s).re = 2 := by simp [rightPoint]
private lemma rightPoint_im (s : ℂ) : (rightPoint s).im = s.im := by simp [rightPoint]
private lemma rightPoint_sub_self (s : ℂ) : rightPoint s - s = ((2 - s.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [rightPoint]
private lemma rightPoint_div_two_add_one_re (s : ℂ) : (rightPoint s / 2 + 1).re = 2 := by
  simp [rightPoint]; norm_num
private lemma rightPoint_div_two_add_one_im (s : ℂ) : (rightPoint s / 2 + 1).im = s.im / 2 := by
  simp [rightPoint]
private lemma rightPoint_sub_one_im (s : ℂ) : (rightPoint s - 1).im = s.im := by simp [rightPoint]

private lemma norm_inv_sub_inv_le {s : ℂ} (hlo : -1 ≤ s.re) (hhi : s.re ≤ 3 / 2) {ρ : ℂ}
    (hfar : 1 < |s.im - ρ.im|) :
    ‖1 / (s - ρ) - 1 / (rightPoint s - ρ)‖ ≤ 6 / (1 + (s.im - ρ.im) ^ 2) := by
  have hΔsq : (1 : ℝ) < (s.im - ρ.im) ^ 2 := by
    nlinarith [abs_nonneg (s.im - ρ.im), sq_abs (s.im - ρ.im)]
  have h1 : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
    have h := Complex.abs_im_le_norm (s - ρ); simpa using h
  have h2 : |s.im - ρ.im| ≤ ‖rightPoint s - ρ‖ := by
    have h := Complex.abs_im_le_norm (rightPoint s - ρ)
    simp only [sub_im, rightPoint_im] at h
    exact h
  have hsρ : s - ρ ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith [abs_nonneg (s.im - ρ.im)]
  have hs0ρ : rightPoint s - ρ ≠ 0 := fun h => by
    rw [h, norm_zero] at h2; linarith [abs_nonneg (s.im - ρ.im)]
  have key : 1 / (s - ρ) - 1 / (rightPoint s - ρ)
      = (rightPoint s - s) / ((s - ρ) * (rightPoint s - ρ)) := by field_simp; ring
  have hprod : (s.im - ρ.im) ^ 2 ≤ ‖s - ρ‖ * ‖rightPoint s - ρ‖ := by
    have habs2 : (s.im - ρ.im) ^ 2 = |s.im - ρ.im| * |s.im - ρ.im| := by
      rw [pow_two]; exact (abs_mul_abs_self _).symm
    rw [habs2]
    exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  have habs : |2 - s.re| ≤ 3 := by rw [abs_le]; constructor <;> linarith
  rw [key, norm_div, norm_mul, rightPoint_sub_self, Complex.norm_real, Real.norm_eq_abs,
    div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right habs
    (by positivity : (0 : ℝ) ≤ 1 + (s.im - ρ.im) ^ 2), hprod, hΔsq]

private lemma norm_inv_rightPoint_le {s ρ : ℂ} (hρ1 : ρ.re < 1) (hnear : |s.im - ρ.im| ≤ 1) :
    ‖1 / (rightPoint s - ρ)‖ ≤ 2 / (1 + (s.im - ρ.im) ^ 2) := by
  have h1 : (1 : ℝ) ≤ ‖rightPoint s - ρ‖ := by
    have h := Complex.abs_re_le_norm (rightPoint s - ρ)
    simp only [sub_re, rightPoint_re] at h
    rw [abs_of_pos (by linarith)] at h
    linarith
  have hΔ : (s.im - ρ.im) ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (s.im - ρ.im), sq_abs (s.im - ρ.im)]
  rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith

private lemma norm_tsum_subtype_le {ι : Type*} (f : ι → ℂ) (P : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hP : Summable P) (hPnn : ∀ i, 0 ≤ P i) (S : Set ι)
    (hbd : ∀ i ∈ S, ‖f i‖ ≤ K * P i) :
    ‖∑' i : ↥S, f (i : ι)‖ ≤ K * ∑' i, P i := by
  have hKP : Summable (fun i : ↥S => K * P (i : ι)) := (hP.subtype _).mul_left K
  have hnorms : Summable (fun i : ↥S => ‖f (i : ι)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hbd _ i.2) hKP
  calc ‖∑' i : ↥S, f (i : ι)‖
      ≤ ∑' i : ↥S, ‖f (i : ι)‖ := norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' i : ↥S, K * P (i : ι) := Summable.tsum_le_tsum (fun i => hbd _ i.2) hnorms hKP
    _ = K * ∑' i : ↥S, P (i : ι) := tsum_mul_left
    _ ≤ K * ∑' i, P i := mul_le_mul_of_nonneg_left (hP.tsum_subtype_le P S hPnn) hK

private lemma norm_seven_le {E : Type*} [SeminormedAddCommGroup E] (a b c d e f g : E) :
    ‖a - b + c - d + e + f - g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  have h1 := norm_sub_le (a - b + c - d + e + f) g
  have h2 := norm_add_le (a - b + c - d + e) f
  have h3 := norm_add_le (a - b + c - d) e
  have h4 := norm_sub_le (a - b + c) d
  have h5 := norm_add_le (a - b) c
  have h6 := norm_sub_le a b
  linarith

/-- **`ζ' / ζ` near a height.** There is a constant `C` such that for every `s` with
`|im s| ≥ 3` and `-1 ≤ re s ≤ 3/2` which is not a zero of `ζ`,

`‖(ζ'/ζ)(s) - ∑_{ρ ∈ 𝒩*, |im ρ - im s| ≤ 1} m_ρ / (s - ρ)‖ ≤ C log (|im s| + 3)`. -/
theorem exists_norm_deriv_riemannZeta_div_sub_tsum_near_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 3 ≤ |s.im| → -1 ≤ s.re → s.re ≤ 3 / 2 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s
          - ∑' ρ : {ρ : allZeros | |s.im - (ρ : ℂ).im| ≤ 1},
              (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ) / (s - ((ρ : allZeros) : ℂ))‖
        ≤ C * Real.log (|s.im| + 3) := by
  obtain ⟨A, hA, hAbd⟩ := exists_norm_deriv_riemannZeta_div_le_of_three_halves_le_re
  obtain ⟨Cψ, hCψ, hψ⟩ := Complex.exists_norm_digamma_le_log (a := 1 / 2) (b := 2) (by norm_num)
  obtain ⟨CP, hCP, hPbd⟩ := exists_summable_poissonWeight_tsum_le
  obtain ⟨B, hB⟩ := exists_logDeriv_riemannZeta_eq_add_tsum_allZeros_of_re_neg_two_lt
  refine ⟨A + Cψ + 8 * CP + 1, by positivity, fun s ht hlo hhi hζ => ?_⟩
  set N : Set allZeros := {ρ | |s.im - (ρ : ℂ).im| ≤ 1} with hNdef
  have hs1 : s ≠ 1 := by intro h; rw [h] at ht; simp at ht; linarith
  have hs01 : rightPoint s ≠ 1 := by
    intro h
    have h2 : (rightPoint s).re = 1 := by rw [h]; simp
    rw [rightPoint_re] at h2; norm_num at h2
  have hζ0 : riemannZeta (rightPoint s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [rightPoint_re]; norm_num)
  have hlog1 : (1 : ℝ) ≤ Real.log (|s.im| + 3) := by
    have h3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
    exact le_trans h3.le (Real.log_le_log (by norm_num) (by linarith))
  obtain ⟨hPsum, hPle⟩ := hPbd s.im
  have hPnn : ∀ ρ : allZeros, 0 ≤ (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (s.im - (ρ : ℂ).im) ^ 2) :=
    fun ρ => by positivity
  have hf₁ : Summable (fun ρ : allZeros =>
      (zeroMultiplicity (ρ : ℂ) : ℂ) * (1 / (s - (ρ : ℂ)) + 1 / (ρ : ℂ))) :=
    summable_zeroMultiplicity_mul_logDerivTerm (fun ρ hρ h => hζ (h ▸ hρ.1))
  have hf₂ : Summable (fun ρ : allZeros =>
      (zeroMultiplicity (ρ : ℂ) : ℂ) * (1 / (rightPoint s - (ρ : ℂ)) + 1 / (ρ : ℂ))) :=
    summable_zeroMultiplicity_mul_logDerivTerm (fun ρ hρ h => hζ0 (h ▸ hρ.1))
  have hg : Summable (fun ρ : allZeros => (zeroMultiplicity (ρ : ℂ) : ℂ)
      * (1 / (s - (ρ : ℂ)) - 1 / (rightPoint s - (ρ : ℂ)))) :=
    (hf₁.sub hf₂).congr fun ρ => by ring
  have hsumg : (∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℂ)
        * (1 / (s - (ρ : ℂ)) - 1 / (rightPoint s - (ρ : ℂ))))
      = (∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℂ) * (1 / (s - (ρ : ℂ)) + 1 / (ρ : ℂ)))
        - ∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℂ)
            * (1 / (rightPoint s - (ρ : ℂ)) + 1 / (ρ : ℂ)) := by
    rw [← hf₁.tsum_sub hf₂]
    exact tsum_congr fun ρ => by ring
  have hnormg : ∀ ρ : allZeros, ρ ∈ Nᶜ →
      ‖(zeroMultiplicity (ρ : ℂ) : ℂ) * (1 / (s - (ρ : ℂ)) - 1 / (rightPoint s - (ρ : ℂ)))‖
        ≤ 6 * ((zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (s.im - (ρ : ℂ).im) ^ 2)) := by
    intro ρ hρ
    simp only [hNdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hρ
    rw [norm_mul, Complex.norm_natCast]
    calc (zeroMultiplicity (ρ : ℂ) : ℝ) * ‖1 / (s - (ρ : ℂ)) - 1 / (rightPoint s - (ρ : ℂ))‖
        ≤ (zeroMultiplicity (ρ : ℂ) : ℝ) * (6 / (1 + (s.im - (ρ : ℂ).im) ^ 2)) :=
          mul_le_mul_of_nonneg_left (norm_inv_sub_inv_le hlo hhi hρ) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hnormb : ∀ ρ : allZeros, ρ ∈ N →
      ‖(zeroMultiplicity (ρ : ℂ) : ℂ) / (rightPoint s - (ρ : ℂ))‖
        ≤ 2 * ((zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (s.im - (ρ : ℂ).im) ^ 2)) := by
    intro ρ hρ
    simp only [hNdef, Set.mem_ofPred_eq] at hρ
    rw [show (zeroMultiplicity (ρ : ℂ) : ℂ) / (rightPoint s - (ρ : ℂ))
        = (zeroMultiplicity (ρ : ℂ) : ℂ) * (1 / (rightPoint s - (ρ : ℂ))) by ring,
      norm_mul, Complex.norm_natCast]
    calc (zeroMultiplicity (ρ : ℂ) : ℝ) * ‖1 / (rightPoint s - (ρ : ℂ))‖
        ≤ (zeroMultiplicity (ρ : ℂ) : ℝ) * (2 / (1 + (s.im - (ρ : ℂ).im) ^ 2)) :=
          mul_le_mul_of_nonneg_left (norm_inv_rightPoint_le ρ.2.2.2 hρ) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hfarbd : ‖∑' ρ : ↥Nᶜ, (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ)
        * (1 / (s - ((ρ : allZeros) : ℂ)) - 1 / (rightPoint s - ((ρ : allZeros) : ℂ)))‖
      ≤ 6 * (CP * Real.log (|s.im| + 3)) := by
    refine le_trans (norm_tsum_subtype_le _ _ 6 (by norm_num) hPsum hPnn Nᶜ hnormg) ?_
    exact mul_le_mul_of_nonneg_left hPle (by norm_num)
  have hnearbd : ‖∑' ρ : ↥N, (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ)
        / (rightPoint s - ((ρ : allZeros) : ℂ))‖ ≤ 2 * (CP * Real.log (|s.im| + 3)) := by
    refine le_trans (norm_tsum_subtype_le _ _ 2 (by norm_num) hPsum hPnn N hnormb) ?_
    exact mul_le_mul_of_nonneg_left hPle (by norm_num)
  have hgN : Summable (fun ρ : ↥N => (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ)
      * (1 / (s - ((ρ : allZeros) : ℂ)) - 1 / (rightPoint s - ((ρ : allZeros) : ℂ)))) :=
    hg.subtype _
  have hbN : Summable (fun ρ : ↥N =>
      (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ) / (rightPoint s - ((ρ : allZeros) : ℂ))) :=
    Summable.of_norm_bounded ((hPsum.subtype _).mul_left 2) fun ρ => hnormb _ ρ.2
  have hsplit : (∑' ρ : ↥N, (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ)
        * (1 / (s - ((ρ : allZeros) : ℂ)) - 1 / (rightPoint s - ((ρ : allZeros) : ℂ))))
      + (∑' ρ : ↥Nᶜ, (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ)
        * (1 / (s - ((ρ : allZeros) : ℂ)) - 1 / (rightPoint s - ((ρ : allZeros) : ℂ))))
      = ∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℂ)
          * (1 / (s - (ρ : ℂ)) - 1 / (rightPoint s - (ρ : ℂ))) :=
    (hg.subtype _).tsum_add_tsum_compl (hg.subtype _)
  have hNa : (∑' ρ : ↥N,
        (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ) / (s - ((ρ : allZeros) : ℂ)))
      = (∑' ρ : ↥N, (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ)
          * (1 / (s - ((ρ : allZeros) : ℂ)) - 1 / (rightPoint s - ((ρ : allZeros) : ℂ))))
        + ∑' ρ : ↥N, (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ)
            / (rightPoint s - ((ρ : allZeros) : ℂ)) := by
    rw [← hgN.tsum_add hbN]
    exact tsum_congr fun ρ => by ring
  have hid_s := hB s (by linarith) hs1 hζ
  have hid_0 := hB (rightPoint s) (by rw [rightPoint_re]; norm_num) hs01 hζ0
  have hfinal : deriv riemannZeta s / riemannZeta s
      - (∑' ρ : ↥N, (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ) / (s - ((ρ : allZeros) : ℂ)))
      = deriv riemannZeta (rightPoint s) / riemannZeta (rightPoint s)
        - 1 / (s - 1) + 1 / (rightPoint s - 1)
        - digamma (s / 2 + 1) / 2 + digamma (rightPoint s / 2 + 1) / 2
        + (∑' ρ : ↥Nᶜ, (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ)
            * (1 / (s - ((ρ : allZeros) : ℂ)) - 1 / (rightPoint s - ((ρ : allZeros) : ℂ))))
        - ∑' ρ : ↥N, (zeroMultiplicity ((ρ : allZeros) : ℂ) : ℂ)
            / (rightPoint s - ((ρ : allZeros) : ℂ)) := by
    linear_combination hid_s - hid_0 - hsumg - hsplit - hNa
  have hZ0 : ‖deriv riemannZeta (rightPoint s) / riemannZeta (rightPoint s)‖ ≤ A :=
    hAbd _ (by rw [rightPoint_re]; norm_num)
  have hu : ‖1 / (s - 1)‖ ≤ 1 / 3 := by
    have h := Complex.abs_im_le_norm (s - 1)
    simp only [sub_im, one_im, sub_zero] at h
    rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hv : ‖1 / (rightPoint s - 1)‖ ≤ 1 / 3 := by
    have h := Complex.abs_im_le_norm (rightPoint s - 1)
    rw [rightPoint_sub_one_im] at h
    rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hψs : ‖digamma (s / 2 + 1) / 2‖ ≤ Cψ * Real.log (|s.im| + 3) / 2 := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine le_trans (hψ (s / 2 + 1) (by simp; linarith) (by simp; linarith)) ?_
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hCψ.le
    rw [show (s / 2 + 1).im = s.im / 2 by simp, abs_div, show |(2 : ℝ)| = 2 by norm_num]
    linarith [abs_nonneg s.im]
  have hψ0 : ‖digamma (rightPoint s / 2 + 1) / 2‖ ≤ Cψ * Real.log (|s.im| + 3) / 2 := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine le_trans (hψ (rightPoint s / 2 + 1)
      (by rw [rightPoint_div_two_add_one_re]; norm_num)
      (by rw [rightPoint_div_two_add_one_re])) ?_
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hCψ.le
    rw [rightPoint_div_two_add_one_im, abs_div, show |(2 : ℝ)| = 2 by norm_num]
    linarith [abs_nonneg s.im]
  rw [hfinal]
  refine le_trans (norm_seven_le _ _ _ _ _ _ _) ?_
  nlinarith [hZ0, hu, hv, hψs, hψ0, hfarbd, hnearbd, hlog1, hA, hCψ, hCP,
    le_mul_of_one_le_right hA.le hlog1]

end ZetaZeros
