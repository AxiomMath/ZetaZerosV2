/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
public import ZetaZeros.ZeroCount.GoodHeight
public import ZetaZeros.Analytic.Basic
public import ZetaZeros.Analytic.RealSegment

/-!
# The elementary theory of the completed zeta function

Conjugation symmetries of `ξ` and of `ξ'`, the reflection identity for `ξ' / ξ`, the
characterisation of the zeros of `ξ` in the strip, the agreement of the vanishing orders of `ξ`
and of `ζ`, the non-vanishing of `ξ` on the boundary of the counting rectangle, the identification
of the zeros of `ξ` in the rectangle with `𝒩(T)`, and the four-factor split of `ξ' / ξ`.

Several statements use the product formula `ξ s = π ^ (-s / 2) Γ (s / 2 + 1) (s - 1) ζ s`
(`ZetaZeros.riemannXi_eq_mul_riemannZeta`), which holds on `-2 < re s`.

## Main results

* `ZetaZeros.riemannXi_conj`, `ZetaZeros.deriv_riemannXi_conj`: `ξ (conj s) = conj (ξ s)` and the
  same for `ξ'`.
* `ZetaZeros.riemannXi_ne_zero_one_sub_conj`, `ZetaZeros.logDeriv_riemannXi_one_sub_conj`: the
  reflection identity `(ξ' / ξ) (1 - conj s) = - conj ((ξ' / ξ) s)`.
* `ZetaZeros.riemannXi_eq_zero_iff`: `ξ s = 0` exactly at the non-trivial zeros of `ζ`.
* `ZetaZeros.analyticOrderNatAt_riemannXi`: `ord_s ξ = m_s` in the open critical strip.
* `ZetaZeros.riemannXi_ne_zero_of_mem_rectangleBoundary`: `ξ` does not vanish on the contour.
* `ZetaZeros.riemannXi_zeros_rectangle_eq`: the zeros of `ξ` in the rectangle are `𝒩(T)`.
* `ZetaZeros.riemannXi_ne_zero_of_riemannZeta_ne_zero`, `ZetaZeros.logDeriv_riemannXi_eq`: the
  split `ξ' / ξ = 1 / s + 1 / (s - 1) - log π / 2 + digamma (s / 2) / 2 + ζ' / ζ`.
-/

@[expose] public section

namespace ZetaZeros

open Complex

/-! ## The elementary factors of `ξ` -/

/-- The product of the three elementary factors of `ξ`, so that `ξ = xiFactor * ζ` wherever the
product formula holds, with the archimedean factor written as an exponential. -/
private noncomputable def xiFactor (w : ℂ) : ℂ :=
  Complex.exp (-(w / 2) * (Real.log Real.pi : ℂ)) * Gamma (w / 2 + 1) * (w - 1)

/-- The half-plane on which the product formula for `ξ` is valid is open. -/
private lemma isOpen_re_neg_two_lt : IsOpen {w : ℂ | -2 < w.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- On `-2 < re w` the shifted argument `w / 2 + 1` of `Γ` has positive real part. -/
private lemma re_div_two_add_one_pos {w : ℂ} (hw : -2 < w.re) : 0 < (w / 2 + 1).re := by
  simp only [Complex.add_re, Complex.one_re, Complex.div_re]
  norm_num
  linarith

/-- `π ^ (-w / 2)`, written as an exponential. -/
private lemma cpow_pi_neg_div_two (w : ℂ) :
    (Real.pi : ℂ) ^ (-w / 2) = Complex.exp (-(w / 2) * (Real.log Real.pi : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero),
    ← Complex.ofReal_log Real.pi_nonneg, neg_div,
    mul_comm ((Real.log Real.pi : ℝ) : ℂ)]

/-- None of the three elementary factors vanishes. -/
private lemma xiFactor_ne_zero {w : ℂ} (hw : -2 < w.re) (hw1 : w ≠ 1) : xiFactor w ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero (Complex.exp_ne_zero _) (Gamma_ne_zero_of_re_pos (re_div_two_add_one_pos hw)))
    (sub_ne_zero.mpr hw1)

/-- The product formula, with the three elementary factors collected. -/
private lemma riemannXi_eq_xiFactor_mul {w : ℂ} (hw : -2 < w.re) (hw1 : w ≠ 1) :
    riemannXi w = xiFactor w * riemannZeta w := by
  rw [riemannXi_eq_mul_riemannZeta hw1 hw, cpow_pi_neg_div_two]
  unfold xiFactor
  ring

/-- `ξ` agrees with `xiFactor * ζ` near any point of the half-plane `-2 < re s` other than `1`. -/
private lemma riemannXi_eventuallyEq_xiFactor_mul {s : ℂ} (hs : -2 < s.re) (hs1 : s ≠ 1) :
    riemannXi =ᶠ[nhds s] xiFactor * riemannZeta := by
  have hU : IsOpen ({w : ℂ | -2 < w.re} \ {1}) :=
    isOpen_re_neg_two_lt.sdiff isClosed_singleton
  filter_upwards [hU.mem_nhds ⟨hs, by simpa using hs1⟩] with w hw
  simpa only [Pi.mul_apply] using riemannXi_eq_xiFactor_mul hw.1 (by simpa using hw.2)

/-- `ζ` is analytic away from its pole. -/
private lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticOnNhd
    (fun _ hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
    isOpen_compl_singleton s hs

/-- `xiFactor` is analytic on the half-plane. -/
private lemma analyticOnNhd_xiFactor : AnalyticOnNhd ℂ xiFactor {w : ℂ | -2 < w.re} := by
  refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_re_neg_two_lt
  have hΓ : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2 + 1)) w := by
    refine DifferentiableAt.comp (f := fun z : ℂ => z / 2 + 1) w ?_ (by fun_prop)
    refine differentiableAt_Gamma _ fun m h => ?_
    have hpos := re_div_two_add_one_pos hw
    rw [h] at hpos
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simp only [Complex.neg_re, Complex.natCast_re] at hpos
    linarith
  exact (DifferentiableAt.mul (by fun_prop) hΓ |>.mul (by fun_prop)).differentiableWithinAt

/-! ## Conjugation symmetry -/

/-- The three elementary factors are individually conjugation-symmetric. -/
private lemma xiFactor_conj (w : ℂ) :
    xiFactor ((starRingEnd ℂ) w) = (starRingEnd ℂ) (xiFactor w) := by
  unfold xiFactor
  simp only [map_mul, map_sub, map_add, map_one, map_neg, map_div₀, map_ofNat,
    ← Complex.exp_conj, ← Complex.Gamma_conj, Complex.conj_ofReal]

/-- Conjugation symmetry of `ξ` on the half-plane `-2 < re w`, away from `1`. -/
private lemma riemannXi_conj_of_re {w : ℂ} (hw : -2 < w.re) (hw1 : w ≠ 1) :
    riemannXi ((starRingEnd ℂ) w) = (starRingEnd ℂ) (riemannXi w) := by
  have hc : -2 < ((starRingEnd ℂ) w).re := by simpa using hw
  have hc1 : (starRingEnd ℂ) w ≠ 1 := fun h => hw1 (by simpa using congrArg (starRingEnd ℂ) h)
  rw [riemannXi_eq_xiFactor_mul hc hc1, riemannXi_eq_xiFactor_mul hw hw1, map_mul, xiFactor_conj,
    riemannZeta_conj]

/-- **Conjugation symmetry of `ξ`.** For every `s`, `ξ (conj s) = conj (ξ s)`. -/
@[zz_tag "lem_xi_conj"]
theorem riemannXi_conj (s : ℂ) :
    riemannXi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannXi s) := by
  have hdiff : Differentiable ℂ fun z : ℂ => (starRingEnd ℂ) (riemannXi ((starRingEnd ℂ) z)) := by
    intro z
    simpa [Function.comp_def] using (differentiable_riemannXi ((starRingEnd ℂ) z)).conj_conj
  have key : (fun z : ℂ => (starRingEnd ℂ) (riemannXi ((starRingEnd ℂ) z))) = riemannXi := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2)
      (hdiff.differentiableOn.analyticOnNhd isOpen_univ)
      (differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ) ?_
    have hV : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hV.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    have hw' : (1 : ℝ) < w.re := hw
    change (starRingEnd ℂ) (riemannXi ((starRingEnd ℂ) w)) = riemannXi w
    have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hw'; exact lt_irrefl 1 hw'
    rw [riemannXi_conj_of_re (by linarith) hw1, Complex.conj_conj]
  simpa only [Complex.conj_conj] using congrArg (starRingEnd ℂ) (congrFun key s)

/-- **Conjugation symmetry of `ξ'`.** For every `s`, `ξ' (conj s) = conj (ξ' s)`. -/
@[zz_tag "lem_xi_deriv_conj"]
theorem deriv_riemannXi_conj (s : ℂ) :
    deriv riemannXi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv riemannXi s) := by
  have h : (starRingEnd ℂ) ∘ riemannXi ∘ (starRingEnd ℂ) = riemannXi := by
    funext z
    simp only [Function.comp_apply, riemannXi_conj, Complex.conj_conj]
  have key := deriv_conj_conj (f := riemannXi)
  rw [h] at key
  have := congrFun key ((starRingEnd ℂ) s)
  simpa only [Function.comp_apply, Complex.conj_conj] using this

/-! ## The reflection identity for the logarithmic derivative -/

/-- Differentiating the functional equation `ξ (1 - w) = ξ w`. -/
private lemma deriv_riemannXi_one_sub (s : ℂ) :
    deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have hf : HasDerivAt (fun w : ℂ => 1 - w) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hcomp := (differentiable_riemannXi (1 - s)).hasDerivAt.comp s hf
  have hfun : (riemannXi ∘ fun w : ℂ => 1 - w) = riemannXi := by
    funext w
    exact riemannXi_functional_equation w
  rw [hfun] at hcomp
  rw [hcomp.deriv]
  ring

/-- **The reflection identity, first half:** `ξ` does not vanish at `1 - conj s` when it does not
vanish at `s`. -/
@[zz_tag "lem_xi_log_deriv_reflect"]
theorem riemannXi_ne_zero_one_sub_conj {s : ℂ} (hs : riemannXi s ≠ 0) :
    riemannXi (1 - (starRingEnd ℂ) s) ≠ 0 := by
  rw [riemannXi_functional_equation, riemannXi_conj]
  exact fun h => hs (by simpa using congrArg (starRingEnd ℂ) h)

/-- **The reflection identity, second half:** for every `s`,
`(ξ' / ξ) (1 - conj s) = - conj ((ξ' / ξ) s)`, with Lean's convention `x / 0 = 0`. -/
@[zz_tag "lem_xi_log_deriv_reflect"]
theorem logDeriv_riemannXi_one_sub_conj (s : ℂ) :
    logDeriv riemannXi (1 - (starRingEnd ℂ) s) = -(starRingEnd ℂ) (logDeriv riemannXi s) := by
  have hxi : riemannXi (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannXi s) := by
    rw [riemannXi_functional_equation, riemannXi_conj]
  have hd : deriv riemannXi (1 - (starRingEnd ℂ) s)
      = -(starRingEnd ℂ) (deriv riemannXi s) := by
    rw [deriv_riemannXi_one_sub, deriv_riemannXi_conj]
  rw [logDeriv_apply, logDeriv_apply, hxi, hd, map_div₀, neg_div]

/-! ## The zeros of `ξ` -/

/-- **The zeros of `ξ`.** On the half-plane `-2 < re s`, `ξ` vanishes exactly at the zeros of `ζ`
in the open critical strip `0 < re s < 1`. -/
@[zz_tag "lem_xi_zero_iff"]
theorem riemannXi_eq_zero_iff {s : ℂ} (hs : -2 < s.re) :
    riemannXi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  have hzero : ∀ w : ℂ, -2 < w.re → riemannXi w = 0 → riemannZeta w = 0 ∧ w.re < 1 := by
    intro w hw h
    have hw1 : w ≠ 1 := fun h1 => by
      rw [h1, riemannXi_one] at h; norm_num at h
    rw [riemannXi_eq_xiFactor_mul hw hw1] at h
    have hζ := (mul_eq_zero.mp h).resolve_left (xiFactor_ne_zero hw hw1)
    refine ⟨hζ, ?_⟩
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hζ, hlt⟩ := hzero s hs h
    refine ⟨hζ, ?_, hlt⟩
    by_contra hle
    push Not at hle
    have hxt : riemannXi (1 - s) = 0 := by rw [riemannXi_functional_equation]; exact h
    have htre : -2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]; linarith
    obtain ⟨-, hlt'⟩ := hzero (1 - s) htre hxt
    simp only [Complex.sub_re, Complex.one_re] at hlt'
    linarith
  · obtain ⟨hζ, h0, h1⟩ := h
    have hs1 : s ≠ 1 := fun he => by rw [he, Complex.one_re] at h1; exact lt_irrefl 1 h1
    rw [riemannXi_eq_xiFactor_mul hs hs1, hζ, mul_zero]

/-- A point of the open critical strip with vanishing imaginary part is a real point of `(0, 1)`,
where `ζ` is negative and in particular non-zero. -/
private lemma riemannZeta_ne_zero_of_im_eq_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : s.im = 0) : riemannZeta s ≠ 0 := by
  have hreal : s = ((s.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hreal]
  exact riemannZeta_ne_zero_of_pos_of_lt_one h0 h1

/-- **`ξ` does not vanish on the contour.** For a good height `T`, the boundary of the rectangle
`-1 ≤ re s ≤ 2`, `0 ≤ im s ≤ T` carries no zero of `ξ`. -/
@[zz_tag "lem_xi_ne_zero_boundary"]
theorem riemannXi_ne_zero_of_mem_rectangleBoundary {T : ℝ} (hT : IsGoodHeight T) {s : ℂ}
    (hrect : -1 ≤ s.re ∧ s.re ≤ 2 ∧ 0 ≤ s.im ∧ s.im ≤ T)
    (hbd : s.re = -1 ∨ s.re = 2 ∨ s.im = 0 ∨ s.im = T) : riemannXi s ≠ 0 := by
  intro h
  obtain ⟨hζ, h0, h1⟩ := (riemannXi_eq_zero_iff (by linarith [hrect.1])).mp h
  rcases hbd with hb | hb | hb | hb
  · rw [hb] at h0; norm_num at h0
  · rw [hb] at h1; norm_num at h1
  · exact riemannZeta_ne_zero_of_im_eq_zero h0 h1 hb hζ
  · exact hT s hζ h0 h1 hb

/-- **The zeros of `ξ` in the rectangle are `𝒩(T)`.** For every real `T`, the zeros of `ξ` in
`-1 ≤ re s ≤ 2`, `0 ≤ im s ≤ T` are exactly the set `𝒩(T)` of non-trivial zeros of `ζ` with
imaginary part in `(0, T]`. -/
@[zz_tag "lem_xi_zeros_rect_eq"]
theorem riemannXi_zeros_rectangle_eq (T : ℝ) :
    {ρ : ℂ | -1 ≤ ρ.re ∧ ρ.re ≤ 2 ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T ∧ riemannXi ρ = 0} =
      nontrivialZeros T := by
  ext ρ
  simp only [nontrivialZeros, Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hre, -, him, him', hxi⟩ := h
    obtain ⟨hζ, h0, h1⟩ := (riemannXi_eq_zero_iff (by linarith)).mp hxi
    refine ⟨hζ, h0, h1, ?_, him'⟩
    rcases eq_or_lt_of_le him with hb | hb
    · exact absurd hζ (riemannZeta_ne_zero_of_im_eq_zero h0 h1 hb.symm)
    · exact hb
  · obtain ⟨hζ, h0, h1, him, him'⟩ := h
    exact ⟨by linarith, by linarith, him.le, him',
      (riemannXi_eq_zero_iff (by linarith)).mpr ⟨hζ, h0, h1⟩⟩

/-! ## The order of vanishing -/

/-- **The orders of vanishing of `ξ` and of `ζ` agree** at every point of the open critical strip.
-/
@[zz_tag "lem_xi_order"]
theorem analyticOrderNatAt_riemannXi {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderNatAt riemannXi s = zeroMultiplicity s := by
  have hs : -2 < s.re := by linarith
  have hs1 : s ≠ 1 := fun he => by rw [he, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hxf : AnalyticAt ℂ xiFactor s := analyticOnNhd_xiFactor s hs
  have horder : analyticOrderAt riemannXi s = analyticOrderAt riemannZeta s := by
    rw [analyticOrderAt_congr (riemannXi_eventuallyEq_xiFactor_mul hs hs1),
      analyticOrderAt_mul hxf (analyticAt_riemannZeta hs1),
      hxf.analyticOrderAt_eq_zero.2 (xiFactor_ne_zero hs hs1), zero_add]
  unfold zeroMultiplicity analyticOrderNatAt
  rw [horder]

/-! ## Splitting the logarithmic derivative -/

/-- **The split, first half:** `ξ` does not vanish where `ζ` does not, to the right of the
imaginary axis. -/
@[zz_tag "lem_xi_log_deriv_split"]
theorem riemannXi_ne_zero_of_riemannZeta_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) : riemannXi s ≠ 0 := by
  rw [riemannXi_eq_xiFactor_mul (by linarith) h1]
  exact mul_ne_zero (xiFactor_ne_zero (by linarith) h1) hζ

/-- **The split, second half:** the logarithmic derivative of `ξ` is the sum of those of its four
factors,
`ξ' / ξ (s) = 1 / s + 1 / (s - 1) - log π / 2 + digamma (s / 2) / 2 + ζ' / ζ (s)`
for `0 < re s`, `s ≠ 1`, `ζ s ≠ 0`. -/
@[zz_tag "lem_xi_log_deriv_split"]
theorem logDeriv_riemannXi_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = 1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2
      + digamma (s / 2) / 2 + deriv riemannZeta s / riemannZeta s := by
  have hre : -2 < s.re := by linarith
  have hhalf : 0 < (s / 2).re := by
    simp only [Complex.div_re]
    norm_num
    linarith
  have hshift : 0 < (s / 2 + 1).re := re_div_two_add_one_pos hre
  have hne : ∀ z : ℂ, 0 < z.re → ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro z hz m h
    rw [h] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have heq : riemannXi =ᶠ[nhds s] Kadiri.completedZetaFactor := by
    have hU : IsOpen ({w : ℂ | -2 < w.re} \ {1}) :=
      isOpen_re_neg_two_lt.sdiff isClosed_singleton
    filter_upwards [hU.mem_nhds ⟨hre, by simpa using h1⟩] with w hw
    rw [riemannXi_eq_xiFactor_mul hw.1 (by simpa using hw.2)]
    unfold xiFactor Kadiri.completedZetaFactor Kadiri.zetaPoleFactor Kadiri.zetaPiFactor
      Kadiri.zetaGammaFactor
    ring
  have hlog : logDeriv riemannXi s = logDeriv Kadiri.completedZetaFactor s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  have hΓ : Kadiri.zetaGammaFactor s ≠ 0 := Gamma_ne_zero_of_re_pos hshift
  have hdig : digamma (s / 2 + 1) = digamma (s / 2) + (s / 2)⁻¹ :=
    digamma_apply_add_one _ (hne _ hhalf)
  rw [hlog, Kadiri.logDeriv_completedZetaFactor s h1 (hne _ hshift) hΓ hζ, hdig]
  ring

end ZetaZeros
