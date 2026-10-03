/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Landau.Kernel

/-!
# The right edge of the Landau contour, and the trivial-zero residues

Two limits of pieces of the residue identity `ZetaZeros.rectangleIntegral_landauKernel_eq`:

* the **right edge** `re w = b` of the rectangle is the truncated Perron sum,
  `(1/2π) ∫_{-U}^{U} K (b + iy) dy → -∑_{n ≤ x} Λ (n) n^{-s}`
  (`ZetaZeros.tendsto_integral_landauKernel_right`);
* the residues at the **trivial zeros** `-2, -4, …, -2N` inside the rectangle add up to
  `ZetaZeros.landauTrivialSum` (`ZetaZeros.tendsto_sum_landauTrivialTerm`).

## Main results

* `ZetaZeros.summable_landauTrivialTerm`, `ZetaZeros.tendsto_sum_landauTrivialTerm`: the
  trivial-zero residues converge to `ZetaZeros.landauTrivialSum`.
* `ZetaZeros.tendsto_integral_landauKernel_right`: **the right edge** is the truncated Perron sum,
  `-∑_{n ≤ x} Λ (n) n^{-s}`.
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter Topology

/-! ### The trivial-zero residues -/

/-- **The trivial-zero terms are summable.** For `x > 1` and every `s`, the family
`n ↦ x^{-2(n+1)-s} / (2(n+1) + s)` is summable. -/
theorem summable_landauTrivialTerm {x : ℝ} (hx : 1 < x) (s : ℂ) :
    Summable (fun n : ℕ => (x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - s) / (2 * ((n : ℂ) + 1) + s)) := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  set r : ℝ := x ^ (-2 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hx0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have hpow : ∀ n : ℕ, x ^ (-(2 * ((n : ℝ) + 1)) - s.re) = x ^ (-s.re) * r ^ (n + 1) := by
    intro n
    rw [hr, ← Real.rpow_natCast (x ^ (-2 : ℝ)) (n + 1), ← Real.rpow_mul hx0.le,
      ← Real.rpow_add hx0]
    congr 1
    push_cast
    ring
  have hg : Summable (fun n : ℕ => x ^ (-s.re) * r ^ (n + 1)) := by
    simp only [pow_succ']
    exact ((summable_geometric_of_lt_one hr0.le hr1).mul_left r).mul_left _
  refine hg.of_norm_bounded_eventually_nat ?_
  filter_upwards [Filter.eventually_ge_atTop (⌈(1 - s.re) / 2⌉₊)] with n hn
  have hnr : ((1 : ℝ) - s.re) / 2 ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.2 hn)
  have hden : (1 : ℝ) ≤ ‖2 * ((n : ℂ) + 1) + s‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    have hrew : (2 * ((n : ℂ) + 1) + s).re = 2 * ((n : ℝ) + 1) + s.re := by simp
    rw [hrew, abs_of_pos (by linarith)]
    linarith
  have hre : (-(2 * ((n : ℂ) + 1)) - s).re = -(2 * ((n : ℝ) + 1)) - s.re := by simp
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre, hpow n]
  exact div_le_self (by positivity) hden

/-- **The trivial-zero residues sum to `ZetaZeros.landauTrivialSum`.** The partial sums
`∑_{n=1}^{N} x^{-2n-s} / (2n + s)` tend to `ZetaZeros.landauTrivialSum x s` as `N → ∞`. -/
theorem tendsto_sum_landauTrivialTerm {x : ℝ} (hx : 1 < x) (s : ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
        (x : ℂ) ^ (-(2 * (n : ℂ)) - s) / (2 * (n : ℂ) + s))
      atTop (nhds (landauTrivialSum x s)) := by
  have hsum := (summable_landauTrivialTerm hx s).hasSum
  rw [landauTrivialSum, ← hsum.tsum_eq]
  refine hsum.tendsto_sum_nat.congr fun N => ?_
  induction N with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-! ### The right edge -/

/-- On a vertical line to the right of `re w = 1` and of `s`, the kernel is continuous: the line
carries no zero of `ζ`, not the pole, and not `s`. -/
private lemma continuous_landauKernel_vertical {x : ℝ} (hx : 0 < x) {s : ℂ} {b : ℝ}
    (hb : 1 < b) (hbs : s.re < b) :
    Continuous fun y : ℝ => landauKernel x s ((b : ℂ) + (y : ℂ) * I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hre : ((b : ℂ) + (y : ℂ) * I).re = b := by simp
  have h1 : ((b : ℂ) + (y : ℂ) * I) ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hre; linarith
  have hz : riemannZeta ((b : ℂ) + (y : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith)
  have hs : ((b : ℂ) + (y : ℂ) * I) ≠ s := fun h => by
    rw [h] at hre; linarith
  exact (analyticAt_landauKernel hx h1 hz hs).continuousAt.comp
    (f := fun y : ℝ => ((b : ℂ) + (y : ℂ) * I)) (by fun_prop)

/-- **The right edge of the contour.** For `x > 0` not a prime power and a right abscissa
`b = σ + re s` with `σ > 0` and `b ≥ 3/2`,

`(1 / 2π) ∫_{-U}^{U} K (b + iy) dy → -∑_{n ≤ x} Λ (n) n^{-s}` as `U → ∞`. -/
theorem tendsto_integral_landauKernel_right {x : ℝ} (hx : 0 < x) (hxpp : NotPrimePowerReal x)
    {s : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσs : 3 / 2 ≤ σ + s.re) :
    Tendsto (fun U : ℝ => (1 / (2 * (Real.pi : ℂ))) *
        ∫ y in (-U)..U, landauKernel x s (((σ + s.re : ℝ) : ℂ) + (y : ℂ) * I))
      atTop (nhds (-landauPrimeSum x s)) := by
  set b : ℝ := σ + s.re with hb
  set t₀ : ℝ := s.im with ht₀
  have hb32 : (3 : ℝ) / 2 ≤ b := hσs
  have hb1 : 1 < b := by linarith
  have hbs : s.re < b := by rw [hb]; linarith
  set g : ℝ → ℂ := fun y => landauKernel x s ((b : ℂ) + (y : ℂ) * I) with hg
  have hgc : Continuous g := continuous_landauKernel_vertical hx hb1 hbs
  have hgi : ∀ c d : ℝ, IntervalIntegrable g MeasureTheory.volume c d := fun c d =>
    hgc.intervalIntegrable c d
  have hper : Tendsto (fun T : ℝ => -((1 / (2 * (Real.pi : ℂ))) *
      ∫ y in (t₀ - T)..(t₀ + T), g y)) atTop (nhds (landauPrimeSum x s)) := by
    refine (tendsto_integral_logDeriv_riemannZeta_perron hx
      (fun n hn => (hxpp n hn).symm) hσ (by linarith)).congr fun T => ?_
    have hpt : ∀ v : ℝ, (-(deriv riemannZeta (s + ((σ : ℂ) + (v : ℂ) * I))
          / riemannZeta (s + ((σ : ℂ) + (v : ℂ) * I))))
        * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I)) = -g (v + t₀) := by
      intro v
      have hw : s + ((σ : ℂ) + (v : ℂ) * I) = (b : ℂ) + ((v + t₀ : ℝ) : ℂ) * I := by
        rw [hb, ht₀]
        apply Complex.ext <;> simp <;> ring
      have hws : (σ : ℂ) + (v : ℂ) * I = (b : ℂ) + ((v + t₀ : ℝ) : ℂ) * I - s := by
        rw [← hw]; ring
      simp only [hg, landauKernel, logDeriv, Pi.div_apply]
      rw [hw, hws]
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_comp_add_right (fun y => -g y) t₀,
      intervalIntegral.integral_neg]
    rw [show -T + t₀ = t₀ - T from by ring, show T + t₀ = t₀ + T from by ring]
    ring
  obtain ⟨A₀, hA₀pos, hA₀⟩ := exists_norm_deriv_riemannZeta_div_le_of_three_halves_le_re
  have hbnd : ∀ U : ℝ, 3 * |t₀| + 1 ≤ U → ∀ y : ℝ, U - 2 * |t₀| ≤ |y| →
      ‖g y‖ ≤ A₀ * x ^ (b - s.re) / (U - 3 * |t₀|) := by
    intro U hU y hy
    have hU0 : 0 < U - 3 * |t₀| := by linarith
    have hyd : U - 3 * |t₀| ≤ |y - t₀| := by
      have h1 : |y| - |t₀| ≤ |y - t₀| := by
        have := abs_sub_abs_le_abs_sub y t₀
        linarith
      linarith
    have him : ((b : ℂ) + (y : ℂ) * I - s).im = y - t₀ := by rw [ht₀]; simp
    have hre : ((b : ℂ) + (y : ℂ) * I - s).re = b - s.re := by simp
    have hd : 0 < |y - t₀| := lt_of_lt_of_le hU0 hyd
    have hDw : |y - t₀| ≤ ‖(b : ℂ) + (y : ℂ) * I - s‖ := by
      rw [← him]; exact Complex.abs_im_le_norm _
    refine le_trans (norm_landauKernel_le hx (hA₀ _ ?_) hd hDw) ?_
    · have hbre : ((b : ℂ) + (y : ℂ) * I).re = b := by simp
      rw [hbre]
      linarith
    · rw [hre]
      exact div_le_div_of_nonneg_left (by positivity) hU0 hyd
  have hdiff : Tendsto (fun U : ℝ => (1 / (2 * (Real.pi : ℂ))) *
      ((∫ y in (-U)..U, g y) - ∫ y in (t₀ - (U - |t₀|))..(t₀ + (U - |t₀|)), g y))
      atTop (nhds 0) := by
    rw [show (0 : ℂ) = (1 / (2 * (Real.pi : ℂ))) * 0 from by ring]
    refine Tendsto.const_mul _ ?_
    have hbound : ∀ᶠ U : ℝ in atTop,
        ‖(∫ y in (-U)..U, g y) - ∫ y in (t₀ - (U - |t₀|))..(t₀ + (U - |t₀|)), g y‖
          ≤ A₀ * x ^ (b - s.re) / (U - 3 * |t₀|) * (4 * |t₀|) := by
      filter_upwards [Filter.eventually_ge_atTop (3 * |t₀| + 1)] with U hU
      have hA : t₀ - (U - |t₀|) = -U + (t₀ + |t₀|) := by ring
      have hB : t₀ + (U - |t₀|) = U - (|t₀| - t₀) := by ring
      have hle₁ : -U ≤ t₀ - (U - |t₀|) := by rw [hA]; linarith [neg_abs_le t₀]
      have hle₂ : t₀ - (U - |t₀|) ≤ t₀ + (U - |t₀|) := by
        have : 0 ≤ U - |t₀| := by linarith [abs_nonneg t₀]
        linarith
      have hle₃ : t₀ + (U - |t₀|) ≤ U := by rw [hB]; linarith [le_abs_self t₀]
      have hsplit : (∫ y in (-U)..U, g y) - ∫ y in (t₀ - (U - |t₀|))..(t₀ + (U - |t₀|)), g y
          = (∫ y in (-U)..(t₀ - (U - |t₀|)), g y) + ∫ y in (t₀ + (U - |t₀|))..U, g y := by
        have e₁ := intervalIntegral.integral_add_adjacent_intervals
          (hgi (-U) (t₀ - (U - |t₀|))) (hgi (t₀ - (U - |t₀|)) (t₀ + (U - |t₀|)))
        have e₂ := intervalIntegral.integral_add_adjacent_intervals
          (hgi (-U) (t₀ + (U - |t₀|))) (hgi (t₀ + (U - |t₀|)) U)
        rw [← e₂, ← e₁]
        ring
      set C : ℝ := A₀ * x ^ (b - s.re) / (U - 3 * |t₀|) with hC
      have hC0 : 0 ≤ C := by
        have : 0 < U - 3 * |t₀| := by linarith
        positivity
      have hp₁ : ‖∫ y in (-U)..(t₀ - (U - |t₀|)), g y‖ ≤ C * (2 * |t₀|) := by
        refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := C)
          fun y hy => ?_) ?_
        · refine hbnd U hU y ?_
          rw [Set.uIoc_of_le hle₁, Set.mem_Ioc] at hy
          have : y ≤ -U + 2 * |t₀| := by rw [hA] at hy; linarith [le_abs_self t₀]
          have hyneg : y < 0 := by linarith [abs_nonneg t₀]
          rw [abs_of_neg hyneg]
          linarith
        · have : |t₀ - (U - |t₀|) - -U| ≤ 2 * |t₀| := by
            rw [hA]
            simp only [add_sub_cancel_left]
            rw [abs_of_nonneg (by linarith [neg_abs_le t₀] : (0:ℝ) ≤ t₀ + |t₀|)]
            linarith [le_abs_self t₀]
          exact mul_le_mul_of_nonneg_left this hC0
      have hp₂ : ‖∫ y in (t₀ + (U - |t₀|))..U, g y‖ ≤ C * (2 * |t₀|) := by
        refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := C)
          fun y hy => ?_) ?_
        · refine hbnd U hU y ?_
          rw [Set.uIoc_of_le hle₃, Set.mem_Ioc] at hy
          have hy1 : U - 2 * |t₀| ≤ y := by rw [hB] at hy; linarith [le_abs_self t₀]
          have hypos : 0 < y := by linarith [abs_nonneg t₀]
          rw [abs_of_pos hypos]
          exact hy1
        · have : |U - (t₀ + (U - |t₀|))| ≤ 2 * |t₀| := by
            rw [show U - (t₀ + (U - |t₀|)) = |t₀| - t₀ from by ring,
              abs_of_nonneg (by linarith [le_abs_self t₀] : (0:ℝ) ≤ |t₀| - t₀)]
            linarith [neg_abs_le t₀]
          exact mul_le_mul_of_nonneg_left this hC0
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have := add_le_add hp₁ hp₂
      linarith
    have hlim : Tendsto (fun U : ℝ => A₀ * x ^ (b - s.re) / (U - 3 * |t₀|) * (4 * |t₀|))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun U : ℝ => U - 3 * |t₀|) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_id
      simpa using ((tendsto_const_nhds.div_atTop h1).mul_const (4 * |t₀|))
    exact squeeze_zero_norm' hbound hlim
  have hcomp : Tendsto (fun U : ℝ => -((1 / (2 * (Real.pi : ℂ))) *
      ∫ y in (t₀ - (U - |t₀|))..(t₀ + (U - |t₀|)), g y)) atTop (nhds (landauPrimeSum x s)) :=
    hper.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  have := hdiff.sub hcomp
  rw [zero_sub] at this
  refine this.congr fun U => ?_
  ring

end ZetaZeros
