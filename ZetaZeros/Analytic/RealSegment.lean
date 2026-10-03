/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import PrimeNumberTheoremAnd.ZetaBounds
public import ZetaZeros.Meta.Attr

/-!
# No zeros on the real segment

The zeta function is strictly negative at every real point of the open unit interval. The proof
uses the first-order Euler--Maclaurin formula
`ζ s = 1 / 2 - 1 / (1 - s) + s * ∫ x in Ioi 1, (⌊x⌋ + 1 / 2 - x) / x ^ (s + 1)`, valid for
`0 < re s`, `s ≠ 1`, together with the bound `|⌊x⌋ + 1 / 2 - x| ≤ 1 / 2`, which gives
`ζ σ ≤ 1 - 1 / (1 - σ) < 0` for real `0 < σ < 1`.

## Main results

* `ZetaZeros.riemannZeta_re_neg_of_pos_of_lt_one`: `(ζ σ).re < 0` for real `0 < σ < 1`.
* `ZetaZeros.riemannZeta_neg_of_pos_of_lt_one`: the same in the complex order, `ζ σ < 0`, which
  additionally records that `ζ σ` is real there.
* `ZetaZeros.riemannZeta_ne_zero_of_pos_of_lt_one`: `ζ σ ≠ 0` for real `0 < σ < 1`.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory Set

/-- The tail integral of the first-order Euler--Maclaurin formula for `ζ`, at `N = 1` and at a real
exponent, is at most `1 / (2 σ)` in absolute value. -/
private lemma norm_integral_floor_add_half_sub_le {σ : ℝ} (h₀ : 0 < σ) :
    ‖∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ ((σ : ℂ) + 1)‖
      ≤ 1 / (2 * σ) := by
  have hint : IntegrableOn (fun x : ℝ ↦ 1 / 2 * x ^ (-σ - 1)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have hcalc : ∫ x in Ioi (1 : ℝ), 1 / 2 * x ^ (-σ - 1) = 1 / (2 * σ) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -σ - 1 + 1 = -σ by ring]
    field_simp
  refine le_trans (norm_integral_le_of_norm_le hint ?_) hcalc.le
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx ↦ ?_)
  have hx₀ : (0 : ℝ) < x := lt_trans one_pos hx
  rw [ZetaSum_aux1_4' x hx₀ (σ : ℂ), show ((σ : ℂ) + 1).re = σ + 1 by simp]
  calc ‖(⌊x⌋ : ℝ) + 1 / 2 - x‖ / x ^ (σ + 1)
      ≤ 1 / 2 / x ^ (σ + 1) := by gcongr; exact ZetaSum_aux1_3 x
    _ = 1 / 2 * x ^ (-σ - 1) := by
        rw [show -σ - 1 = -(σ + 1) by ring, Real.rpow_neg hx₀.le]; ring

/-- Euler--Maclaurin at `N = 1`: for `s` off the pole with `0 < re s`,
`ζ s = 1 / 2 - 1 / (1 - s) + s * ∫ x in Ioi 1, (⌊x⌋ + 1 / 2 - x) / x ^ (s + 1)`. -/
private lemma riemannZeta_eq_of_re_pos {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) (hre : 0 < s.re) :
    riemannZeta s
      = 1 / 2 - 1 / (1 - s) + s * ∫ x in Ioi (1 : ℝ),
          ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1) := by
  have hz := Zeta0EqZeta (N := 1) one_pos (s := s) hre hs₁
  rw [riemannZeta0] at hz
  simp only [Nat.cast_one, Nat.cast_zero, Complex.one_cpow, Complex.zero_cpow hs₀,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton] at hz
  rw [← hz]
  ring

/-- **The zeta function is negative on the open unit segment.** For every real `σ` with
`0 < σ < 1`, the real part of `ζ σ` is strictly negative. -/
@[zz_tag "lem_zeta_neg_on_open_unit"]
theorem riemannZeta_re_neg_of_pos_of_lt_one {σ : ℝ} (h₀ : 0 < σ) (h₁ : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 := by
  have hs₀ : (σ : ℂ) ≠ 0 := fun h ↦ by
    rw [← Complex.ofReal_zero, Complex.ofReal_inj] at h; linarith
  have hs₁ : (σ : ℂ) ≠ 1 := fun h ↦ by
    rw [← Complex.ofReal_one, Complex.ofReal_inj] at h; linarith
  set J : ℂ := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ ((σ : ℂ) + 1) with hJ
  have hzeta : riemannZeta (σ : ℂ) = ((1 / 2 : ℝ) : ℂ) - 1 / (1 - (σ : ℂ)) + (σ : ℂ) * J := by
    rw [hJ, riemannZeta_eq_of_re_pos hs₀ hs₁ (by simpa using h₀)]
    push_cast
    ring
  have hpole : (1 / (1 - (σ : ℂ))).re = (1 - σ)⁻¹ := by
    rw [show (1 : ℂ) - (σ : ℂ) = ((1 - σ : ℝ) : ℂ) by push_cast; ring, one_div,
      ← Complex.ofReal_inv, Complex.ofReal_re]
  have hre : (riemannZeta (σ : ℂ)).re = 1 / 2 - (1 - σ)⁻¹ + σ * J.re := by
    rw [hzeta]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hpole, zero_mul, sub_zero]
  have htail : σ * J.re ≤ 1 / 2 := by
    have hJre : J.re ≤ 1 / (2 * σ) :=
      le_trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm J))
        (norm_integral_floor_add_half_sub_le h₀)
    calc σ * J.re ≤ σ * (1 / (2 * σ)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hinv : 1 < (1 - σ)⁻¹ := by
    have hp : 0 < 1 - σ := by linarith
    nlinarith [mul_inv_cancel₀ hp.ne', inv_pos.mpr hp]
  rw [hre]
  linarith

open scoped ComplexOrder in
/-- The zeta function is negative on the open unit segment, in the complex order: for real
`0 < σ < 1` the value `ζ σ` is real and `ζ σ < 0`. -/
theorem riemannZeta_neg_of_pos_of_lt_one {σ : ℝ} (h₀ : 0 < σ) (h₁ : σ < 1) :
    riemannZeta (σ : ℂ) < 0 := by
  rw [Complex.lt_def]
  refine ⟨by simpa using riemannZeta_re_neg_of_pos_of_lt_one h₀ h₁, ?_⟩
  rw [Complex.zero_im, ← Complex.conj_eq_iff_im, ← riemannZeta_conj, Complex.conj_ofReal]

/-- The zeta function does not vanish on the open unit segment. -/
theorem riemannZeta_ne_zero_of_pos_of_lt_one {σ : ℝ} (h₀ : 0 < σ) (h₁ : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := fun h ↦ by
  have := riemannZeta_re_neg_of_pos_of_lt_one h₀ h₁
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

end ZetaZeros
