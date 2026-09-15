/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationFullZeroEstimate
import ZetaZeros.Unconditional.PairCorrelationEndpoint

/-!
# Assembly of the integrated full-zero second moment

This file combines the exact explicit-formula decomposition, the two-sided
Montgomery--Vaughan estimate, the prime diagonal, and the Archimedean main term.
The interaction terms are estimated with scaled forms of Young's inequality;
this keeps their endpoint loss integrable in the logarithmic scale parameter.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set Filter
open scoped BigOperators Interval Topology ComplexConjugate

/-- A division-form adapter for the scaled Young inequality used below. -/
lemma two_mul_le_scaled_sq (u v r : ℝ) (hr : 0 < r) :
    2 * u * v ≤ r * u ^ 2 + v ^ 2 / r := by
  calc
    2 * u * v ≤ r * u ^ 2 + r⁻¹ * v ^ 2 :=
      two_mul_le_add_mul_sq (a := u) (b := v) (ε := r) hr
    _ = r * u ^ 2 + v ^ 2 / r := by
      rw [div_eq_mul_inv]
      ring

/-- The two diagonal squares cancel exactly from the square of their signed sum. -/
lemma abs_norm_neg_add_sq_sub_squares_le (u v : ℂ) :
    |‖-u + v‖ ^ 2 - (‖u‖ ^ 2 + ‖v‖ ^ 2)| ≤
      2 * ‖u‖ * ‖v‖ := by
  rw [norm_add_sq_real]
  have hinner := abs_real_inner_le_norm (-u) v
  rw [norm_neg] at hinner
  calc
    |‖-u‖ ^ 2 + 2 * inner ℝ (-u) v + ‖v‖ ^ 2 -
        (‖u‖ ^ 2 + ‖v‖ ^ 2)| =
        |2 * inner ℝ (-u) v| := by
          rw [norm_neg]
          congr 1
          ring
    _ = 2 * |inner ℝ (-u) v| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ = 2 * ‖u‖ * ‖v‖ := by ring

/-- The off-diagonal part of three complex summands is controlled by the three
pairwise interactions and the square of the remainder. -/
lemma abs_norm_neg_add_add_sq_sub_squares_le (d a r : ℂ) :
    |‖-d + a + r‖ ^ 2 - (‖d‖ ^ 2 + ‖a‖ ^ 2)| ≤
      2 * ‖d‖ * ‖a‖ + 2 * ‖d‖ * ‖r‖ +
        2 * ‖a‖ * ‖r‖ + ‖r‖ ^ 2 := by
  have hperturb :
      |‖(-d + a) + r‖ ^ 2 - ‖-d + a‖ ^ 2| ≤
        2 * ‖-d + a‖ * ‖r‖ + ‖r‖ ^ 2 := by
    have hdiff : |‖(-d + a) + r‖ - ‖-d + a‖| ≤ ‖r‖ := by
      simpa [add_sub_cancel_left] using abs_norm_sub_norm_le ((-d + a) + r) (-d + a)
    have hsum : |‖(-d + a) + r‖ + ‖-d + a‖| ≤
        2 * ‖-d + a‖ + ‖r‖ := by
      rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      linarith [norm_add_le (-d + a) r]
    calc
      |‖(-d + a) + r‖ ^ 2 - ‖-d + a‖ ^ 2| =
          |‖(-d + a) + r‖ - ‖-d + a‖| *
            |‖(-d + a) + r‖ + ‖-d + a‖| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ ‖r‖ * (2 * ‖-d + a‖ + ‖r‖) :=
        mul_le_mul hdiff hsum (abs_nonneg _) (norm_nonneg _)
      _ = 2 * ‖-d + a‖ * ‖r‖ + ‖r‖ ^ 2 := by ring
  have hdiag := abs_norm_neg_add_sq_sub_squares_le d a
  have htri : ‖-d + a‖ ≤ ‖d‖ + ‖a‖ := by
    simpa only [norm_neg] using norm_add_le (-d) a
  calc
    |‖-d + a + r‖ ^ 2 - (‖d‖ ^ 2 + ‖a‖ ^ 2)| ≤
        |‖-d + a + r‖ ^ 2 - ‖-d + a‖ ^ 2| +
          |‖-d + a‖ ^ 2 - (‖d‖ ^ 2 + ‖a‖ ^ 2)| := by
      rw [show ‖-d + a + r‖ ^ 2 - (‖d‖ ^ 2 + ‖a‖ ^ 2) =
          (‖-d + a + r‖ ^ 2 - ‖-d + a‖ ^ 2) +
            (‖-d + a‖ ^ 2 - (‖d‖ ^ 2 + ‖a‖ ^ 2)) by ring]
      exact abs_add_le _ _
    _ ≤ (2 * ‖-d + a‖ * ‖r‖ + ‖r‖ ^ 2) +
          2 * ‖d‖ * ‖a‖ := add_le_add hperturb hdiag
    _ ≤ (2 * (‖d‖ + ‖a‖) * ‖r‖ + ‖r‖ ^ 2) +
          2 * ‖d‖ * ‖a‖ := by
      gcongr
    _ = 2 * ‖d‖ * ‖a‖ + 2 * ‖d‖ * ‖r‖ +
          2 * ‖a‖ * ‖r‖ + ‖r‖ ^ 2 := by ring

/-- The decaying endpoint weight has total mass at most `1 / log T`. -/
lemma intervalIntegral_const_rpow_neg_le_inv_log (T : ℝ)
    (hT : Real.exp 1 ≤ T) :
    (∫ a : ℝ in 0..1, T ^ (-a)) ≤ 1 / Real.log T := by
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hlogOne : 1 ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 hT
  have hlogPos : 0 < Real.log T := lt_of_lt_of_le zero_lt_one hlogOne
  have hinvPos : 0 < T⁻¹ := inv_pos.mpr hTpos
  have hlogInv : Real.log T⁻¹ ≠ 0 := by
    rw [Real.log_inv]
    exact neg_ne_zero.mpr hlogPos.ne'
  rw [show (fun a : ℝ => T ^ (-a)) = fun a : ℝ => T⁻¹ ^ a by
      funext a
      exact Real.rpow_neg_eq_inv_rpow T a,
    intervalIntegral_const_rpow_eq T⁻¹ hinvPos hlogInv, Real.log_inv]
  rw [show (T⁻¹ - 1) / -Real.log T = (1 - T⁻¹) / Real.log T by ring]
  exact (div_le_div_iff_of_pos_right hlogPos).2 (by linarith [inv_pos.mpr hTpos])

/-- The conjugate-product presentation of the full-zero moment is the real
integral of the squared norm of the explicit-formula side. -/
lemma windowedFullZeroSecondMoment_eq_ofReal_norm_sq_integral
    (x T : ℝ) (hx : 1 ≤ x) (hT : 0 ≤ T) :
    windowedFullZeroSecondMoment x T =
      ((∫ t : ℝ in 0..T,
        ‖fullZeroPoleTerm x t - fullZeroPrimeTerm x t +
          fullZeroArchimedeanTerm x t‖ ^ 2 : ℝ) : ℂ) := by
  rw [windowedFullZeroSecondMoment_eq_intervalIntegral_terms x T hx hT]
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [RCLike.mul_conj]
  norm_cast

/-- The pole contribution has total square energy `O(x)`, uniformly in the
upper endpoint of the height window. -/
theorem intervalIntegral_fullZeroPoleTerm_sq_le
    (x T : ℝ) (hx : 1 ≤ x) (hT : 0 ≤ T) :
    (∫ t : ℝ in 0..T, ‖fullZeroPoleTerm x t‖ ^ 2) ≤
      (256 / 9 : ℝ) * Real.pi * x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  let g : ℝ → ℝ := fun t => (256 / 9 : ℝ) * x * (1 + t ^ 2)⁻¹
  have hg : Integrable g := by
    dsimp only [g]
    exact integrable_inv_one_add_sq.const_mul ((256 / 9 : ℝ) * x)
  have hp := integrableOn_norm_fullZeroPoleTerm_sq_Ioc x T
  have hp_le : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 T),
      ‖fullZeroPoleTerm x t‖ ^ 2 ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t _
    have hpoint := montgomeryKernel_pole_terms x hx t
    have hnorm : ‖fullZeroPoleTerm x t‖ ≤
        (16 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2) := by
      unfold fullZeroPoleTerm
      exact (norm_add_le _ _).trans hpoint
    have hden : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    have hdenpos : 0 < 1 + t ^ 2 := by positivity
    have hsqrt : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
    have hnorm0 : 0 ≤ ‖fullZeroPoleTerm x t‖ := norm_nonneg _
    have hrhs0 : 0 ≤ (16 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2) := by
      positivity
    dsimp only [g]
    rw [show (256 / 9 : ℝ) = (16 / 3) ^ 2 by norm_num]
    calc
      ‖fullZeroPoleTerm x t‖ ^ 2 ≤
          ((16 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2)) ^ 2 :=
        (sq_le_sq₀ hnorm0 hrhs0).2 hnorm
      _ = (16 / 3 : ℝ) ^ 2 * x / (1 + t ^ 2) ^ 2 := by
        rw [div_pow, mul_pow, hsqrt]
      _ ≤ (16 / 3 : ℝ) ^ 2 * x / (1 + t ^ 2) := by
        have hn : 0 ≤ (16 / 3 : ℝ) ^ 2 * x := mul_nonneg (sq_nonneg _) hx0
        exact div_le_div_of_nonneg_left hn hdenpos (by nlinarith)
      _ = (16 / 3 : ℝ) ^ 2 * x * (1 + t ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_of_le hT]
  calc
    (∫ t in Set.Ioc 0 T, ‖fullZeroPoleTerm x t‖ ^ 2) ≤
        ∫ t in Set.Ioc 0 T, g t :=
      MeasureTheory.setIntegral_mono_ae_restrict hp hg.integrableOn hp_le
    _ ≤ ∫ t : ℝ, g t :=
      MeasureTheory.setIntegral_le_integral hg (by
        filter_upwards [] with t
        dsimp only [g]
        positivity)
    _ = (256 / 9 : ℝ) * Real.pi * x := by
      dsimp only [g]
      rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
      ring

/-- After removing its Lorentzian main term, the Archimedean contribution has
uniformly bounded square energy per unit height. -/
theorem exists_intervalIntegral_fullZeroArchimedeanRemainder_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x T : ℝ, 1 ≤ x → 0 ≤ T →
      (∫ t : ℝ in 0..T,
        ‖fullZeroArchimedeanTerm x t -
          (2 * Real.pi * Zeta23.mu t / x : ℂ)‖ ^ 2) ≤ C ^ 2 * T := by
  obtain ⟨C, hC, harch⟩ := montgomeryKernel_archimedeanTerm
  refine ⟨C, hC, ?_⟩
  intro x T hx hT
  have hpoint : ∀ t ∈ Set.uIoc (0 : ℝ) T,
      ‖(‖fullZeroArchimedeanTerm x t -
          (2 * Real.pi * Zeta23.mu t / x : ℂ)‖ ^ 2 : ℝ)‖ ≤ C ^ 2 := by
    intro t _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply (sq_le_sq₀ (norm_nonneg _) hC).2
    simpa only [fullZeroArchimedeanTerm] using harch x hx t
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc
    (∫ t : ℝ in 0..T,
        ‖fullZeroArchimedeanTerm x t -
          (2 * Real.pi * Zeta23.mu t / x : ℂ)‖ ^ 2) ≤
        ‖∫ t : ℝ in 0..T,
          ‖fullZeroArchimedeanTerm x t -
            (2 * Real.pi * Zeta23.mu t / x : ℂ)‖ ^ 2‖ :=
      (by rw [Real.norm_eq_abs]; exact le_abs_self _)
    _ ≤ C ^ 2 * |T - 0| := hbound
    _ = C ^ 2 * T := by rw [sub_zero, abs_of_nonneg hT]

end ZetaZeros.Unconditional.PairCorrelationProof
