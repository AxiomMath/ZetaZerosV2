/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationZeroSum
import ZetaZeros.Unconditional.PairCorrelationFourier
import Zeta23.WeilEF.Main
import Zeta23.GammaFacts.Complete
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Montgomery's explicit-formula kernel

This file exposes the compactly supported Weil explicit formula and the proved Gamma-factor facts,
then establishes the exact transform of Montgomery's translated two-sided exponential.  These are
the analytic inputs at the beginning of the pair-correlation explicit-formula chain.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Filter
open scoped ContDiff Convolution Topology

/-- The imported compactly supported, twice continuously differentiable Weil explicit formula. -/
theorem compactExplicitFormula (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) :
    Summable (fun ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
      ((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) *
        Zeta23.paperFT k (Zeta23.gammaOf ρ)) ∧
      ∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
          ((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) *
            Zeta23.paperFT k (Zeta23.gammaOf ρ) =
        Zeta23.EF.literatureRHS k :=
  Zeta23.WeilEF.EF_lit_zeta Zeta23.zetaSeam k hk hkc

/-- The complete, unconditional collection of facts about the Archimedean density `Zeta23.mu`. -/
theorem archimedeanDensity_facts : Zeta23.GammaFacts :=
  Zeta23.gammaFacts

/-- The Archimedean density is even. -/
theorem archimedeanDensity_even (u : ℝ) : Zeta23.mu (-u) = Zeta23.mu u :=
  Zeta23.mu_even u

/-- The Archimedean density is smooth. -/
theorem archimedeanDensity_smooth : ContDiff ℝ ∞ Zeta23.mu :=
  Zeta23.mu_smooth

/-- Stirling's estimate for the Archimedean density. -/
theorem archimedeanDensity_stirling :
    ∃ C : ℝ, ∀ u : ℝ, 1 ≤ |u| →
      |Zeta23.mu u - (1 / (2 * Real.pi)) *
        Real.log (|u| / (2 * Real.pi))| ≤ C / u ^ 2 :=
  Zeta23.gammaFacts.stirling

/-- The inverse-linear derivative estimate for the Archimedean density. -/
theorem archimedeanDensity_deriv_bound :
    ∃ C : ℝ, ∀ u : ℝ, 1 ≤ |u| →
      |deriv Zeta23.mu u| ≤ C / |u| :=
  Zeta23.gammaFacts.deriv_bound

/-- A global square-root growth bound for the Archimedean density. -/
theorem archimedeanDensity_sqrt_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      |Zeta23.mu u| ≤ C * (1 + |u|) ^ (1 / 2 : ℝ) :=
  Zeta23.EF.abs_mu_le_of_gammaFacts Zeta23.gammaFacts

/-- When the base point is positive and the displacement is at most half its size, the
Archimedean density has a uniformly bounded increment. -/
theorem archimedeanDensity_far_increment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t → ∀ u : ℝ, |u| ≤ t / 2 →
      |Zeta23.mu (t + u) - Zeta23.mu t| ≤ C := by
  obtain ⟨C, hC⟩ := archimedeanDensity_deriv_bound
  refine ⟨|C|, abs_nonneg C, fun t ht u hu => ?_⟩
  have ht0 : 0 < t := by linarith
  have hmvt : ‖Zeta23.mu (t + u) - Zeta23.mu t‖ ≤
      (2 * |C| / t) * ‖(t + u) - t‖ := by
    apply Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.Icc (t / 2) (3 * t / 2))
    · intro v _
      exact archimedeanDensity_smooth.contDiffAt.differentiableAt (by simp)
    · intro v hv
      have hvpos : 0 < v := by linarith [hv.1]
      have hvabs : |v| = v := abs_of_pos hvpos
      have hvone : 1 ≤ |v| := by rw [hvabs]; linarith [hv.1]
      calc
        ‖deriv Zeta23.mu v‖ = |deriv Zeta23.mu v| := Real.norm_eq_abs _
        _ ≤ C / |v| := hC v hvone
        _ ≤ |C| / |v| := by
          gcongr
          exact le_abs_self C
        _ ≤ |C| / (t / 2) := by
          apply div_le_div_of_nonneg_left (abs_nonneg C) (by positivity)
          rw [hvabs]
          exact hv.1
        _ = 2 * |C| / t := by field_simp
    · exact convex_Icc _ _
    · constructor <;> linarith
    · constructor <;> linarith [le_abs_self u, neg_abs_le u]
  simp only [add_sub_cancel_left, Real.norm_eq_abs] at hmvt
  calc
    |Zeta23.mu (t + u) - Zeta23.mu t| ≤ (2 * |C| / t) * |u| := hmvt
    _ ≤ (2 * |C| / t) * (t / 2) := by
      gcongr
    _ = |C| := by field_simp

/-- A uniform increment bound with an integrable square-root majorant.  This is slightly weaker
than the logarithmic formulation in the blueprint, but is exactly what the Archimedean integral
needs after multiplication by the Lorentzian kernel. -/
theorem archimedeanDensity_increment_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t u : ℝ,
      |Zeta23.mu (t + u) - Zeta23.mu t| ≤
        C * (1 + |u|) ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK, hmu⟩ := archimedeanDensity_sqrt_bound
  obtain ⟨M, hM, hfar⟩ := archimedeanDensity_far_increment
  refine ⟨4 * K + M, by positivity, fun t u => ?_⟩
  let w : ℝ := (1 + |u|) ^ (1 / 2 : ℝ)
  have hw : 1 ≤ w := by
    exact Real.one_le_rpow (by linarith [abs_nonneg u]) (by norm_num)
  have hw0 : 0 ≤ w := le_trans zero_le_one hw
  have hsqrt_scale : ∀ v : ℝ, |v| ≤ 3 * (1 + |u|) →
      (1 + |v|) ^ (1 / 2 : ℝ) ≤ 2 * w := by
    intro v hv
    dsimp [w]
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have huv : 0 ≤ 1 + |u| := by positivity
    have hvv : 0 ≤ 1 + |v| := by positivity
    have hsqu := Real.sq_sqrt huv
    have hsqv := Real.sq_sqrt hvv
    have hinside : 1 + |v| ≤ 4 * (1 + |u|) := by
      nlinarith [abs_nonneg u]
    nlinarith [Real.sqrt_nonneg (1 + |u|), Real.sqrt_nonneg (1 + |v|)]
  rcases le_or_gt |t| (2 * (1 + |u|)) with ht | ht
  · have htScale : |t| ≤ 3 * (1 + |u|) := by
      nlinarith [abs_nonneg u]
    have htuScale : |t + u| ≤ 3 * (1 + |u|) := by
      calc
        |t + u| ≤ |t| + |u| := abs_add_le t u
        _ ≤ 3 * (1 + |u|) := by nlinarith [abs_nonneg u]
    calc
      |Zeta23.mu (t + u) - Zeta23.mu t| ≤
          |Zeta23.mu (t + u)| + |Zeta23.mu t| := abs_sub _ _
      _ ≤ K * (1 + |t + u|) ^ (1 / 2 : ℝ) +
          K * (1 + |t|) ^ (1 / 2 : ℝ) := add_le_add (hmu _) (hmu _)
      _ ≤ K * (2 * w) + K * (2 * w) := by
        gcongr
        · exact hsqrt_scale _ htuScale
        · exact hsqrt_scale _ htScale
      _ ≤ (4 * K + M) * w := by
        nlinarith
  · have huHalf : |u| ≤ |t| / 2 := by
      nlinarith [abs_nonneg u]
    have hbase : |Zeta23.mu (t + u) - Zeta23.mu t| ≤ M := by
      rcases le_or_gt 0 t with ht0 | ht0
      · have habst : |t| = t := abs_of_nonneg ht0
        apply hfar t
        · rw [← habst]
          nlinarith [abs_nonneg u]
        · simpa only [habst] using huHalf
      · have habst : |t| = -t := abs_of_neg ht0
        have h := hfar (-t) (by rw [← habst]; nlinarith [abs_nonneg u]) (-u) (by
          simpa only [abs_neg, habst] using huHalf)
        have harg : -t + -u = -(t + u) := by ring
        rw [harg, archimedeanDensity_even, archimedeanDensity_even] at h
        exact h
    calc
      |Zeta23.mu (t + u) - Zeta23.mu t| ≤ M := hbase
      _ ≤ (4 * K + M) * w := by
        nlinarith

/-- The square-root increment weight remains integrable after division by the Lorentzian
denominator. -/
theorem archimedeanIncrementWeight_integrable :
    Integrable (fun u : ℝ ↦
      (1 + |u|) ^ (1 / 2 : ℝ) / (1 + u ^ 2)) := by
  have hbase : Integrable (fun u : ℝ ↦
      2 * (1 + ‖u‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (r := (3 / 2 : ℝ)) (by norm_num)).const_mul 2
  have hcontinuous : Continuous (fun u : ℝ ↦
      (1 + |u|) ^ (1 / 2 : ℝ) / (1 + u ^ 2)) := by
    apply Continuous.div
    · fun_prop (disch := norm_num)
    · fun_prop
    · intro u
      positivity
  refine hbase.mono' hcontinuous.aestronglyMeasurable ?_
  filter_upwards with u
  let A : ℝ := 1 + |u|
  let B : ℝ := 1 + u ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hquad : A ^ 2 ≤ 2 * B := by
    dsimp [A, B]
    nlinarith [sq_abs u, abs_nonneg u, sq_nonneg (|u| - 1)]
  have hhalf : A ^ 2 / 2 ≤ B := by nlinarith
  have hpow : A ^ (1 / 2 : ℝ) / A ^ 2 = A ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hA]
    congr 1
    norm_num
  rw [Real.norm_eq_abs]
  have hnonneg : 0 ≤ A ^ (1 / 2 : ℝ) / B :=
    div_nonneg (Real.rpow_nonneg (le_of_lt hA) _) (le_of_lt hB)
  change |A ^ (1 / 2 : ℝ) / B| ≤ 2 * A ^ (-(3 / 2 : ℝ))
  rw [abs_of_nonneg hnonneg]
  calc
    A ^ (1 / 2 : ℝ) / B ≤ A ^ (1 / 2 : ℝ) / (A ^ 2 / 2) := by
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg (le_of_lt hA) _)
        (by positivity) hhalf
    _ = 2 * (A ^ (1 / 2 : ℝ) / A ^ 2) := by
      field_simp [ne_of_gt hA]
    _ = 2 * A ^ (-(3 / 2 : ℝ)) := by rw [hpow]

/-- Fourier inversion for the Lorentzian, in the angular-frequency normalization used by
Montgomery's kernel. -/
theorem lorentzianOscillatory_integral (a : ℝ) :
    (∫ u : ℝ, 2 * Complex.exp (Complex.I * (u : ℂ) * (a : ℂ)) /
      (1 + (u : ℂ) ^ 2)) =
      2 * Real.pi * Complex.exp (-|a|) := by
  let f : ℝ → ℂ := lorentzianFourierSource 0
  have hf : Integrable f := by
    exact lorentzianFourierSource_integrable 0 (by norm_num)
  have hF : Integrable (FourierTransform.fourier f) := by
    have hscaled := (shiftedLorentzian_integrable 0 (by norm_num)).comp_mul_right'
      (show 2 * Real.pi ≠ 0 by positivity)
    apply hscaled.congr
    filter_upwards with xi
    dsimp [f]
    rw [fourier_lorentzianFourierSource 0 (by norm_num)]
    congr 4
    push_cast
    ring
  have hdouble (y : ℝ) :
      FourierTransform.fourier (FourierTransform.fourier f) y = f (-y) := by
    calc
      FourierTransform.fourier (FourierTransform.fourier f) y =
          FourierTransformInv.fourierInv (FourierTransform.fourier f) (-y) := by
        rw [Real.fourierInv_eq_fourier_neg]
        simp
      _ = f (-y) := by
        exact hf.fourierInv_fourier_eq hF
          (lorentzianFourierSource_continuous 0).continuousAt
  let q : ℝ → ℂ := fun u ↦
    2 * Complex.exp (Complex.I * (u : ℂ) * (a : ℂ)) / (1 + (u : ℂ) ^ 2)
  change (∫ u : ℝ, q u) = 2 * Real.pi * Complex.exp (-|a|)
  have hpoint (xi : ℝ) :
      q (xi * (2 * Real.pi)) =
        2 * (Complex.exp (((-2 * Real.pi * xi * (-a) : ℝ) : ℂ) * Complex.I) •
          FourierTransform.fourier f xi) := by
    dsimp [q, f]
    rw [fourier_lorentzianFourierSource 0 (by norm_num)]
    simp only [add_zero]
    have hexp :
        Complex.I * ((xi * (2 * Real.pi) : ℝ) : ℂ) * (a : ℂ) =
          ((-2 * Real.pi * xi * (-a) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have hcast :
        ((xi * (2 * Real.pi) : ℝ) : ℂ) = ((2 * Real.pi * xi : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hexp, hcast]
    ring
  have hfrequency :
      (∫ xi : ℝ, q (xi * (2 * Real.pi))) = Complex.exp (-|a|) := by
    calc
      (∫ xi : ℝ, q (xi * (2 * Real.pi))) =
          ∫ xi : ℝ, 2 *
            (Complex.exp (((-2 * Real.pi * xi * (-a) : ℝ) : ℂ) * Complex.I) •
              FourierTransform.fourier f xi) := by
        apply integral_congr_ae
        filter_upwards with xi
        exact hpoint xi
      _ = 2 * ∫ xi : ℝ,
          Complex.exp (((-2 * Real.pi * xi * (-a) : ℝ) : ℂ) * Complex.I) •
            FourierTransform.fourier f xi := by
        simpa only [smul_eq_mul] using
          (integral_const_mul (2 : ℂ) (fun xi : ℝ ↦
            Complex.exp (((-2 * Real.pi * xi * (-a) : ℝ) : ℂ) * Complex.I) *
              FourierTransform.fourier f xi))
      _ = 2 * FourierTransform.fourier (FourierTransform.fourier f) (-a) := by
        rw [Real.fourier_real_eq_integral_exp_smul]
      _ = 2 * f a := by rw [hdouble]; simp
      _ = Complex.exp (-|a|) := by
        simp [f, lorentzianFourierSource]
  have hscale := MeasureTheory.Measure.integral_comp_mul_right q (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := by positivity
  calc
    (∫ u : ℝ, q u) =
        (2 * Real.pi : ℝ) • ∫ xi : ℝ, q (xi * (2 * Real.pi)) := by
      rw [hscale, abs_of_pos (inv_pos.mpr hpi), smul_smul,
        mul_inv_cancel₀ hpi.ne', one_smul]
    _ = 2 * Real.pi * Complex.exp (-|a|) := by
      rw [hfrequency, Complex.real_smul]
      push_cast
      ring

/-- Integrability accompanying `lorentzianOscillatory_integral`. -/
theorem lorentzianOscillatory_integrable (a : ℝ) :
    Integrable (fun u : ℝ ↦
      2 * Complex.exp (Complex.I * (u : ℂ) * (a : ℂ)) / (1 + (u : ℂ) ^ 2)) := by
  have hden : Integrable (fun u : ℝ ↦ (1 : ℂ) / (1 + (u : ℂ) ^ 2)) := by
    simpa using shiftedLorentzian_integrable 0 (by norm_num)
  have h := hden.mul_bdd (c := 2)
    (g := fun u : ℝ ↦ 2 * Complex.exp (Complex.I * (u : ℂ) * (a : ℂ)))
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun u ↦ by
      rw [norm_mul, Complex.norm_exp]
      simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im]
      norm_num)
  convert h using 1
  funext u
  ring

/-- Montgomery's translated and modulated two-sided exponential kernel. -/
def montgomeryKernel (x t u : ℝ) : ℂ :=
  Complex.exp (-(|u - Real.log x| : ℝ)) *
    Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ))

/-- Montgomery's kernel is integrable. -/
theorem montgomeryKernel_integrable (x : ℝ) (t : ℝ) :
    Integrable (montgomeryKernel x t) := by
  have hbase := twoSidedExponential_integrable 1 (by norm_num) (0 : ℂ) (by norm_num)
  have hbase' : Integrable (fun u : ℝ => Complex.exp (-(|u| : ℝ))) := by
    simpa using hbase
  have htranslated : Integrable (fun u : ℝ =>
      Complex.exp (-(|u - Real.log x| : ℝ))) := by
    have h := hbase'.comp_add_right (-Real.log x)
    convert h using 1
    funext u
    rfl
  change Integrable (fun u : ℝ => Complex.exp (-(|u - Real.log x| : ℝ)) *
    Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ)))
  refine htranslated.mul_bdd (c := 1) (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Complex.norm_exp]
    simp only [mul_re, neg_re, I_re, ofReal_re, ofReal_im]
    norm_num

/-- Blueprint `lem_montgomery_kernel_ft`: exact transform of Montgomery's kernel. -/
theorem montgomeryKernel_paperFT (x : ℝ) (t : ℝ) (z : ℂ) (hz : |z.im| < 1) :
    Zeta23.paperFT (montgomeryKernel x t) z =
      2 * Complex.exp (Complex.I * (z - (t : ℂ)) * Real.log x) /
        (1 + (z - (t : ℂ)) ^ 2) := by
  let a : ℝ := Real.log x
  let q : ℂ := (t : ℂ) - z
  have hq : |q.im| < 1 := by
    simpa only [q, sub_im, ofReal_im, zero_sub, abs_neg] using hz
  have hshift :
      Zeta23.paperFT (montgomeryKernel x t) z =
        ∫ v : ℝ, montgomeryKernel x t (v + a) *
          Complex.exp (Complex.I * z * (v + a : ℝ)) := by
    unfold Zeta23.paperFT
    rw [integral_add_right_eq_self
      (fun u : ℝ => montgomeryKernel x t u * Complex.exp (Complex.I * z * (u : ℂ))) a]
  rw [hshift]
  have hpoint : ∀ v : ℝ,
      montgomeryKernel x t (v + a) *
          Complex.exp (Complex.I * z * (v + a : ℝ)) =
        Complex.exp (Complex.I * (z - (t : ℂ)) * a) *
          (Complex.exp (-(1 : ℂ) * |v|) *
            Complex.exp (-Complex.I * q * v)) := by
    intro v
    simp only [montgomeryKernel, a, add_sub_cancel_right, ← Complex.exp_add]
    congr 1
    push_cast
    dsimp [q]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hlorentz :
      (∫ v : ℝ, Complex.exp (-(1 : ℂ) * |v|) *
          Complex.exp (-Complex.I * q * v)) = 2 / (1 + q ^ 2) := by
    simpa using twoSidedExponential_integral 1 (by norm_num) q hq
  rw [hlorentz]
  dsimp [q, a]
  ring

/-- The transform on the translated real axis, in the form used by the Archimedean integral. -/
theorem montgomeryKernel_paperFT_realShift (x t u : ℝ) :
    Zeta23.paperFT (montgomeryKernel x t) ((t + u : ℝ) : ℂ) =
      2 * Complex.exp (Complex.I * (u : ℂ) * Real.log x) / (1 + (u : ℂ) ^ 2) := by
  rw [montgomeryKernel_paperFT x t ((t + u : ℝ) : ℂ) (by simp)]
  congr 2 <;> push_cast <;> ring_nf

/-- Blueprint `lem_archimedean_term`: the Archimedean integral differs from its Lorentzian main
term by an absolute constant. -/
theorem montgomeryKernel_archimedeanTerm :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ t : ℝ,
      ‖(∫ r : ℝ, Zeta23.paperFT (montgomeryKernel x t) r * Zeta23.mu r) -
          (2 * Real.pi * Zeta23.mu t / x : ℂ)‖ ≤ C := by
  obtain ⟨K, hK, hinc⟩ := archimedeanDensity_increment_sqrt
  let w : ℝ → ℝ := fun u ↦ (1 + |u|) ^ (1 / 2 : ℝ) / (1 + u ^ 2)
  let g : ℝ → ℝ := fun u ↦ (2 * K) * w u
  have hw : Integrable w := by
    simpa only [w] using archimedeanIncrementWeight_integrable
  have hg : Integrable g := by
    exact hw.const_mul (2 * K)
  have hg_nonneg : ∀ u, 0 ≤ g u := by
    intro u
    dsimp [g, w]
    positivity
  refine ⟨∫ u : ℝ, g u, integral_nonneg hg_nonneg, fun x hx t ↦ ?_⟩
  let L : ℝ → ℂ := fun u ↦
    2 * Complex.exp (Complex.I * (u : ℂ) * Real.log x) / (1 + (u : ℂ) ^ 2)
  have hL : Integrable L := by
    simpa only [L] using lorentzianOscillatory_integrable (Real.log x)
  have hLnorm (u : ℝ) : ‖L u‖ = 2 / (1 + u ^ 2) := by
    have hre : (Complex.I * (u : ℂ) * (Real.log x : ℂ)).re = 0 := by
      simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im]
      ring
    have hden : (1 : ℂ) + (u : ℂ) ^ 2 = ((1 + u ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    dsimp [L]
    rw [norm_div, norm_mul, Complex.norm_exp, hre, Real.exp_zero]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
      show ‖(1 : ℂ) + (u : ℂ) ^ 2‖ = 1 + u ^ 2 by
        rw [hden, norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < 1 + u ^ 2)]]
    norm_num
  have hmain_integrable : Integrable (fun u : ℝ ↦ L u * (Zeta23.mu t : ℂ)) :=
    hL.mul_const _
  have hrem_continuous : Continuous (fun u : ℝ ↦
      L u * ((Zeta23.mu (t + u) - Zeta23.mu t : ℝ) : ℂ)) := by
    have hLc : Continuous L := by
      dsimp [L]
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro u
        have hden : (1 : ℂ) + (u : ℂ) ^ 2 = ((1 + u ^ 2 : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hden]
        exact ofReal_ne_zero.mpr (by positivity)
    have hmuc : Continuous (fun u : ℝ ↦ Zeta23.mu (t + u) - Zeta23.mu t) :=
      (archimedeanDensity_smooth.continuous.comp (by fun_prop)).sub continuous_const
    exact hLc.mul (Complex.continuous_ofReal.comp hmuc)
  have hrem_bound (u : ℝ) :
      ‖L u * ((Zeta23.mu (t + u) - Zeta23.mu t : ℝ) : ℂ)‖ ≤ g u := by
    rw [norm_mul, hLnorm, norm_real]
    calc
      2 / (1 + u ^ 2) * |Zeta23.mu (t + u) - Zeta23.mu t| ≤
          2 / (1 + u ^ 2) * (K * (1 + |u|) ^ (1 / 2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (hinc t u) (by positivity)
      _ = g u := by
        dsimp [g, w]
        ring
  have hrem_integrable : Integrable (fun u : ℝ ↦
      L u * ((Zeta23.mu (t + u) - Zeta23.mu t : ℝ) : ℂ)) := by
    exact hg.mono' hrem_continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hrem_bound)
  have hshift :
      (∫ r : ℝ, Zeta23.paperFT (montgomeryKernel x t) r * Zeta23.mu r) =
        ∫ u : ℝ, L u * Zeta23.mu (t + u) := by
    calc
      _ = ∫ u : ℝ, Zeta23.paperFT (montgomeryKernel x t) ((u + t : ℝ) : ℂ) *
          Zeta23.mu (u + t) := (integral_add_right_eq_self
            (fun r : ℝ ↦ Zeta23.paperFT (montgomeryKernel x t) r * Zeta23.mu r) t).symm
      _ = ∫ u : ℝ, L u * Zeta23.mu (t + u) := by
        apply integral_congr_ae
        filter_upwards with u
        rw [add_comm u t, montgomeryKernel_paperFT_realShift]
  have hmain :
      (∫ u : ℝ, L u * (Zeta23.mu t : ℂ)) =
        (2 * Real.pi * Zeta23.mu t / x : ℂ) := by
    rw [integral_mul_const, show (∫ u : ℝ, L u) =
        2 * Real.pi * Complex.exp (-|Real.log x|) by
      simpa only [L] using lorentzianOscillatory_integral (Real.log x)]
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hexp : Complex.exp (-|Real.log x|) = ((1 / x : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp,
        abs_of_nonneg (Real.log_nonneg hx), Real.exp_neg, Real.exp_log hxpos]
      simp only [one_div]
    rw [hexp]
    push_cast
    field_simp
  have hsplit :
      (∫ u : ℝ, L u * Zeta23.mu (t + u)) =
        (∫ u : ℝ, L u * Zeta23.mu t) +
          ∫ u : ℝ, L u * ((Zeta23.mu (t + u) - Zeta23.mu t : ℝ) : ℂ) := by
    rw [← integral_add hmain_integrable hrem_integrable]
    apply integral_congr_ae
    filter_upwards with u
    push_cast
    ring
  rw [hshift, hsplit, hmain]
  simpa only [add_sub_cancel_left] using
    norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hrem_bound)

/-- The transform formula with its exponential phase expressed as a complex power. -/
theorem montgomeryKernel_paperFT_cpow (x : ℝ) (hx : 1 ≤ x) (t : ℝ) (z : ℂ)
    (hz : |z.im| < 1) :
    Zeta23.paperFT (montgomeryKernel x t) z =
      2 * (x : ℂ) ^ (Complex.I * (z - (t : ℂ))) /
        (1 + (z - (t : ℂ)) ^ 2) := by
  rw [montgomeryKernel_paperFT x t z hz]
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hxpos)
  rw [Complex.cpow_def_of_ne_zero hxne, ← Complex.ofReal_log (le_of_lt hxpos)]
  congr 3
  ring

/-- Multiplication by `i` identifies the vendored spectral coordinate of a zero with its
critical-line displacement. -/
theorem I_mul_gammaOf (rho : ℂ) :
    Complex.I * Zeta23.gammaOf rho = rho - 1 / 2 := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im, Complex.sub_re,
      Complex.sub_im, Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im]
  · norm_num
  · norm_num

/-- Blueprint `lem_montgomery_kernel_at_zero`: evaluation of Montgomery's transform at a
nontrivial zero, in the exact normalization used by the full zero sum. -/
theorem montgomeryKernel_paperFT_zero (x : ℝ) (hx : 1 ≤ x) (t : ℝ)
    (rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier) :
    Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho) =
      2 * (x : ℂ) ^ ((rho : ℂ) - 1 / 2 - Complex.I * t) /
        (1 - ((rho : ℂ) - 1 / 2 - Complex.I * t) ^ 2) := by
  have hstrip := (Zeta23.zetaZeros Zeta23.zetaSeam).strip (rho : ℂ) rho.2
  have hgamma : |(Zeta23.gammaOf (rho : ℂ)).im| < 1 := by
    rw [Zeta23.WeilEF.gammaOf_im, abs_lt]
    constructor <;> linarith [hstrip.1, hstrip.2]
  rw [montgomeryKernel_paperFT x t (Zeta23.gammaOf rho) hgamma]
  let w : ℂ := (rho : ℂ) - 1 / 2 - Complex.I * t
  have hw : Complex.I * (Zeta23.gammaOf (rho : ℂ) - (t : ℂ)) = w := by
    dsimp [w]
    rw [mul_sub, I_mul_gammaOf]
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hxpos)
  have hpow :
      Complex.exp (Complex.I * (Zeta23.gammaOf (rho : ℂ) - (t : ℂ)) *
          Real.log x) =
        (x : ℂ) ^ w := by
    rw [Complex.cpow_def_of_ne_zero hxne, ← Complex.ofReal_log (le_of_lt hxpos)]
    congr 1
    rw [hw]
    ring
  have hden :
      1 + (Zeta23.gammaOf (rho : ℂ) - (t : ℂ)) ^ 2 = 1 - w ^ 2 := by
    have hsquare := congrArg (fun z : ℂ => z ^ 2) hw
    rw [mul_pow] at hsquare
    norm_num at hsquare
    linear_combination -hsquare
  rw [hpow, hden]

/-- The absolutely convergent zero side of the explicit formula, written using the transformed
Montgomery kernel. -/
theorem montgomeryKernel_zeroSeries_summable (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    Summable (fun rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
      ((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ) *
        Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho)) := by
  convert zeroLorentzianSummand_summable x hx t using 1
  funext rho
  rw [montgomeryKernel_paperFT_zero x hx t rho]
  simp only [Zeta23.zetaZeros_mult]
  ring

/-- The zero side of the explicit formula is the full Lorentzian zero sum. -/
theorem montgomeryKernel_zero_tsum (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    (∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
      ((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ) *
        Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho)) =
      ∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        (2 * Zeta23.zeroMult rho : ℂ) *
          (x : ℂ) ^ ((rho : ℂ) - 1 / 2 - Complex.I * t) /
            (1 - ((rho : ℂ) - 1 / 2 - Complex.I * t) ^ 2) := by
  apply tsum_congr
  intro rho
  rw [montgomeryKernel_paperFT_zero x hx t rho]
  simp only [Zeta23.zetaZeros_mult]
  ring

/-- Uniform bound for either pole value of the transformed Montgomery kernel. -/
theorem montgomeryKernel_pole_norm_le (x : ℝ) (hx : 1 ≤ x) (t delta : ℝ)
    (hdelta : |delta| ≤ (1 / 2 : ℝ)) :
    ‖Zeta23.paperFT (montgomeryKernel x t) (Complex.I * (delta : ℂ))‖ ≤
      (8 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2) := by
  let z : ℂ := Complex.I * (delta : ℂ)
  have hz : |z.im| < 1 := by
    have hlt : |delta| < 1 := lt_of_le_of_lt hdelta (by norm_num)
    simpa only [z, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, add_zero, zero_add] using hlt
  rw [montgomeryKernel_paperFT_cpow x hx t z hz]
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hexpRe : (Complex.I * (z - (t : ℂ))).re ≤ (1 / 2 : ℝ) := by
    have hdeltaLower := (abs_le.mp hdelta).1
    dsimp [z]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    linarith
  have hpow : ‖(x : ℂ) ^ (Complex.I * (z - (t : ℂ)))‖ ≤ Real.sqrt x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx hexpRe
  have hq : z - (t : ℂ) = ((-t : ℝ) : ℂ) + Complex.I * (delta : ℂ) := by
    dsimp [z]
    push_cast
    ring
  have hdenLower :
      (3 / 4 : ℝ) * (1 + t ^ 2) ≤ ‖(1 : ℂ) + (z - (t : ℂ)) ^ 2‖ := by
    rw [hq]
    have ht : (-t) ^ 2 = t ^ 2 := by ring
    simpa only [ht] using shiftedLorentzian_norm_lower (-t) delta hdelta
  have htPos : 0 < 1 + t ^ 2 := by positivity
  have hdenPos : 0 < ‖(1 : ℂ) + (z - (t : ℂ)) ^ 2‖ := by
    have : 0 < (3 / 4 : ℝ) * (1 + t ^ 2) := mul_pos (by norm_num) htPos
    exact this.trans_le hdenLower
  have hinv :
      1 / ‖(1 : ℂ) + (z - (t : ℂ)) ^ 2‖ ≤
        (4 / 3 : ℝ) / (1 + t ^ 2) := by
    rw [div_le_div_iff₀ hdenPos htPos]
    nlinarith
  calc
    ‖2 * (x : ℂ) ^ (Complex.I * (z - (t : ℂ))) /
        (1 + (z - (t : ℂ)) ^ 2)‖ =
        2 * ‖(x : ℂ) ^ (Complex.I * (z - (t : ℂ)))‖ *
          (1 / ‖(1 : ℂ) + (z - (t : ℂ)) ^ 2‖) := by
      rw [norm_div, norm_mul]
      norm_num
      ring
    _ ≤ 2 * Real.sqrt x *
          (1 / ‖(1 : ℂ) + (z - (t : ℂ)) ^ 2‖) := by
      gcongr
    _ ≤ 2 * Real.sqrt x * ((4 / 3 : ℝ) / (1 + t ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (8 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2) := by ring

/-- Blueprint `lem_pole_terms`: the two pole values have the claimed joint decay. -/
theorem montgomeryKernel_pole_terms (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    ‖Zeta23.paperFT (montgomeryKernel x t) (Complex.I / 2)‖ +
        ‖Zeta23.paperFT (montgomeryKernel x t) (-Complex.I / 2)‖ ≤
      (16 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2) := by
  have hplus := montgomeryKernel_pole_norm_le x hx t (1 / 2) (by norm_num)
  have hminus := montgomeryKernel_pole_norm_le x hx t (-1 / 2) (by norm_num)
  have hplus' :
      ‖Zeta23.paperFT (montgomeryKernel x t) (Complex.I / 2)‖ ≤
        (8 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2) := by
    have heq : Complex.I * ((1 / 2 : ℝ) : ℂ) = Complex.I / 2 := by
      push_cast
      ring
    rw [← heq]
    exact hplus
  have hminus' :
      ‖Zeta23.paperFT (montgomeryKernel x t) (-Complex.I / 2)‖ ≤
        (8 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2) := by
    have heq : Complex.I * ((-1 / 2 : ℝ) : ℂ) = -Complex.I / 2 := by
      push_cast
      ring
    rw [← heq]
    exact hminus
  calc
    ‖Zeta23.paperFT (montgomeryKernel x t) (Complex.I / 2)‖ +
        ‖Zeta23.paperFT (montgomeryKernel x t) (-Complex.I / 2)‖ ≤
      (8 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2) +
        (8 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2) := add_le_add hplus' hminus'
    _ = (16 / 3 : ℝ) * Real.sqrt x / (1 + t ^ 2) := by ring

/-! ### Extension of the explicit formula to Montgomery's kernel -/

/-- A standard sequence of smooth bumps whose outer radii tend to zero. -/
def montgomeryBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / (2 * (n + 1 : ℝ))
  rOut := 1 / (n + 1 : ℝ)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : 0 < (n + 1 : ℝ) := by positivity
    calc
      1 / (2 * (n + 1 : ℝ)) = (1 / 2 : ℝ) * (1 / (n + 1 : ℝ)) := by
        field_simp
      _ < 1 * (1 / (n + 1 : ℝ)) :=
        mul_lt_mul_of_pos_right (by norm_num) (one_div_pos.mpr hn)
      _ = 1 / (n + 1 : ℝ) := one_mul _

/-- The normalized real mollifier associated to `montgomeryBump`. -/
def montgomeryMollifier (n : ℕ) : ℝ → ℝ :=
  (montgomeryBump n).normed volume

/-- Montgomery's kernel smoothed at scale `1/(n+1)`. -/
def montgomerySmoothed (x t : ℝ) (n : ℕ) : ℝ → ℂ :=
  montgomeryMollifier n ⋆[ContinuousLinearMap.lsmul ℝ ℝ] montgomeryKernel x t

/-- Translation distance used to cancel both exponential tails of the smoothed kernel. -/
def montgomeryCutoffRadius (n : ℕ) : ℝ := n + 1

/-- Coefficient of the right translate in the tail-cancelled approximation. -/
def montgomeryCutoffCoeffRight (t : ℝ) (n : ℕ) : ℂ :=
  -Complex.exp (-Complex.I * (t : ℂ) * montgomeryCutoffRadius n) /
    (Real.exp (montgomeryCutoffRadius n) + Real.exp (-montgomeryCutoffRadius n))

/-- Coefficient of the left translate in the tail-cancelled approximation. -/
def montgomeryCutoffCoeffLeft (t : ℝ) (n : ℕ) : ℂ :=
  -Complex.exp (Complex.I * (t : ℂ) * montgomeryCutoffRadius n) /
    (Real.exp (montgomeryCutoffRadius n) + Real.exp (-montgomeryCutoffRadius n))

/-- Montgomery's kernel with two small remote translates which cancel its exact exponential
tails. -/
def montgomeryTailCutoff (x t : ℝ) (n : ℕ) : ℝ → ℂ := fun u =>
  montgomeryKernel x t u +
    montgomeryCutoffCoeffRight t n *
      montgomeryKernel x t (u - montgomeryCutoffRadius n) +
    montgomeryCutoffCoeffLeft t n *
      montgomeryKernel x t (u + montgomeryCutoffRadius n)

/-- A smooth compactly supported approximation to Montgomery's kernel, obtained by mollifying
the exactly tail-cancelled kernel. -/
def montgomeryCompactApprox (x t : ℝ) (n : ℕ) : ℝ → ℂ := fun u =>
  (montgomeryMollifier n ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
    montgomeryTailCutoff x t n) u

theorem montgomeryBump_rOut (n : ℕ) :
    (montgomeryBump n).rOut = 1 / (n + 1 : ℝ) := rfl

theorem tendsto_montgomeryBump_rOut :
    Tendsto (fun n : ℕ => (montgomeryBump n).rOut) atTop (𝓝 0) := by
  simp only [montgomeryBump_rOut]
  simpa only [Nat.cast_add, Nat.cast_one] using
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem montgomeryKernel_continuous (x t : ℝ) :
    Continuous (montgomeryKernel x t) := by
  unfold montgomeryKernel
  fun_prop

theorem norm_montgomeryKernel (x t u : ℝ) :
    ‖montgomeryKernel x t u‖ = Real.exp (-|u - Real.log x|) := by
  unfold montgomeryKernel
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  have hmod : (-Complex.I * (t : ℂ) * (u : ℂ)).re = 0 := by simp
  rw [hmod, Real.exp_zero, mul_one]
  simp

theorem montgomeryKernel_locallyIntegrable (x t : ℝ) :
    LocallyIntegrable (montgomeryKernel x t) :=
  (montgomeryKernel_integrable x t).locallyIntegrable

theorem montgomeryTailCutoff_integrable (x t : ℝ) (n : ℕ) :
    Integrable (montgomeryTailCutoff x t n) := by
  have hbase := montgomeryKernel_integrable x t
  have hright : Integrable (fun u : ℝ =>
      montgomeryCutoffCoeffRight t n *
        montgomeryKernel x t (u - montgomeryCutoffRadius n)) := by
    have h := hbase.comp_add_right (-montgomeryCutoffRadius n)
    have h' : Integrable (fun u : ℝ =>
        montgomeryKernel x t (u - montgomeryCutoffRadius n)) := by
      simpa only [sub_eq_add_neg] using h
    exact h'.const_mul _
  have hleft : Integrable (fun u : ℝ =>
      montgomeryCutoffCoeffLeft t n *
        montgomeryKernel x t (u + montgomeryCutoffRadius n)) := by
    exact (hbase.comp_add_right (montgomeryCutoffRadius n)).const_mul _
  exact (hbase.add hright).add hleft

theorem montgomerySmoothed_contDiff (x t : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (montgomerySmoothed x t n) := by
  exact (montgomeryBump n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (montgomeryBump n).contDiff_normed
    (montgomeryKernel_locallyIntegrable x t)

theorem montgomeryCompactApprox_contDiff (x t : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (montgomeryCompactApprox x t n) := by
  have htwo : (2 : ℕ∞) ≤ ∞ := mod_cast le_top
  unfold montgomeryCompactApprox
  exact ((montgomeryBump n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (montgomeryBump n).contDiff_normed
    (montgomeryTailCutoff_integrable x t n).locallyIntegrable).of_le htwo

theorem montgomeryCutoff_coeff_right_tail (t : ℝ) (n : ℕ) :
    1 + montgomeryCutoffCoeffRight t n *
          Complex.exp ((1 + Complex.I * (t : ℂ)) * montgomeryCutoffRadius n) +
        montgomeryCutoffCoeffLeft t n *
          Complex.exp ((-1 - Complex.I * (t : ℂ)) * montgomeryCutoffRadius n) = 0 := by
  let R := montgomeryCutoffRadius n
  let D : ℝ := Real.exp R + Real.exp (-R)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hD : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hDpos.ne'
  have hA : montgomeryCutoffCoeffRight t n *
        Complex.exp ((1 + Complex.I * (t : ℂ)) * R) =
      -(Real.exp R : ℂ) / D := by
    unfold montgomeryCutoffCoeffRight
    dsimp [R, D]
    rw [div_mul_eq_mul_div, neg_mul, ← Complex.exp_add]
    congr 2
    · calc
        Complex.exp
            (-Complex.I * (t : ℂ) * montgomeryCutoffRadius n +
              (1 + Complex.I * (t : ℂ)) * montgomeryCutoffRadius n) =
            Complex.exp (montgomeryCutoffRadius n : ℂ) := by
              congr 1
              ring
        _ = (Real.exp (montgomeryCutoffRadius n) : ℂ) :=
          (Complex.ofReal_exp _).symm
    · norm_cast
  have hB : montgomeryCutoffCoeffLeft t n *
        Complex.exp ((-1 - Complex.I * (t : ℂ)) * R) =
      -(Real.exp (-R) : ℂ) / D := by
    unfold montgomeryCutoffCoeffLeft
    dsimp [R, D]
    rw [div_mul_eq_mul_div, neg_mul, ← Complex.exp_add]
    congr 2
    · calc
        Complex.exp
            (Complex.I * (t : ℂ) * montgomeryCutoffRadius n +
              (-1 - Complex.I * (t : ℂ)) * montgomeryCutoffRadius n) =
            Complex.exp ((-montgomeryCutoffRadius n : ℝ) : ℂ) := by
              congr 1
              push_cast
              ring
        _ = (Real.exp (-montgomeryCutoffRadius n) : ℂ) :=
          (Complex.ofReal_exp _).symm
    · norm_cast
  rw [hA, hB]
  push_cast [D] at hD ⊢
  field_simp
  ring

theorem montgomeryCutoff_coeff_left_tail (t : ℝ) (n : ℕ) :
    1 + montgomeryCutoffCoeffRight t n *
          Complex.exp ((-1 + Complex.I * (t : ℂ)) * montgomeryCutoffRadius n) +
        montgomeryCutoffCoeffLeft t n *
          Complex.exp ((1 - Complex.I * (t : ℂ)) * montgomeryCutoffRadius n) = 0 := by
  let R := montgomeryCutoffRadius n
  let D : ℝ := Real.exp R + Real.exp (-R)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hD : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hDpos.ne'
  have hA : montgomeryCutoffCoeffRight t n *
        Complex.exp ((-1 + Complex.I * (t : ℂ)) * R) =
      -(Real.exp (-R) : ℂ) / D := by
    unfold montgomeryCutoffCoeffRight
    dsimp [R, D]
    rw [div_mul_eq_mul_div, neg_mul, ← Complex.exp_add]
    congr 2
    · calc
        Complex.exp
            (-Complex.I * (t : ℂ) * montgomeryCutoffRadius n +
              (-1 + Complex.I * (t : ℂ)) * montgomeryCutoffRadius n) =
            Complex.exp ((-montgomeryCutoffRadius n : ℝ) : ℂ) := by
              congr 1
              push_cast
              ring
        _ = (Real.exp (-montgomeryCutoffRadius n) : ℂ) :=
          (Complex.ofReal_exp _).symm
    · norm_cast
  have hB : montgomeryCutoffCoeffLeft t n *
        Complex.exp ((1 - Complex.I * (t : ℂ)) * R) =
      -(Real.exp R : ℂ) / D := by
    unfold montgomeryCutoffCoeffLeft
    dsimp [R, D]
    rw [div_mul_eq_mul_div, neg_mul, ← Complex.exp_add]
    congr 2
    · calc
        Complex.exp
            (Complex.I * (t : ℂ) * montgomeryCutoffRadius n +
              (1 - Complex.I * (t : ℂ)) * montgomeryCutoffRadius n) =
            Complex.exp (montgomeryCutoffRadius n : ℂ) := by
              congr 1
              ring
        _ = (Real.exp (montgomeryCutoffRadius n) : ℂ) :=
          (Complex.ofReal_exp _).symm
    · norm_cast
  rw [hA, hB]
  push_cast [D] at hD ⊢
  field_simp
  ring

theorem montgomeryTailCutoff_eq_zero_of_right (x t u : ℝ) (n : ℕ)
    (hu : Real.log x + montgomeryCutoffRadius n ≤ u) :
    montgomeryTailCutoff x t n u = 0 := by
  let R := montgomeryCutoffRadius n
  have hR : 0 ≤ R := by
    dsimp [R, montgomeryCutoffRadius]
    positivity
  have hu0 : Real.log x ≤ u := by linarith
  have hsub : Real.log x ≤ u - R := by
    dsimp [R] at hu ⊢
    linarith
  have hadd : Real.log x ≤ u + R := by linarith
  have hKsub : montgomeryKernel x t (u - R) =
      montgomeryKernel x t u *
        Complex.exp ((1 + Complex.I * (t : ℂ)) * R) := by
    simp only [montgomeryKernel, abs_of_nonneg (sub_nonneg.mpr hsub),
      abs_of_nonneg (sub_nonneg.mpr hu0), ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hKadd : montgomeryKernel x t (u + R) =
      montgomeryKernel x t u *
        Complex.exp ((-1 - Complex.I * (t : ℂ)) * R) := by
    simp only [montgomeryKernel, abs_of_nonneg (sub_nonneg.mpr hadd),
      abs_of_nonneg (sub_nonneg.mpr hu0), ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcancel := montgomeryCutoff_coeff_right_tail t n
  dsimp [R] at hKsub hKadd
  unfold montgomeryTailCutoff
  rw [hKsub, hKadd]
  calc
    montgomeryKernel x t u +
          montgomeryCutoffCoeffRight t n *
            (montgomeryKernel x t u *
              Complex.exp ((1 + Complex.I * (t : ℂ)) * montgomeryCutoffRadius n)) +
        montgomeryCutoffCoeffLeft t n *
          (montgomeryKernel x t u *
            Complex.exp ((-1 - Complex.I * (t : ℂ)) * montgomeryCutoffRadius n)) =
        montgomeryKernel x t u *
          (1 + montgomeryCutoffCoeffRight t n *
              Complex.exp ((1 + Complex.I * (t : ℂ)) * montgomeryCutoffRadius n) +
            montgomeryCutoffCoeffLeft t n *
              Complex.exp ((-1 - Complex.I * (t : ℂ)) * montgomeryCutoffRadius n)) := by
          ring
    _ = 0 := by rw [hcancel, mul_zero]

theorem montgomeryTailCutoff_eq_zero_of_left (x t u : ℝ) (n : ℕ)
    (hu : u ≤ Real.log x - montgomeryCutoffRadius n) :
    montgomeryTailCutoff x t n u = 0 := by
  let R := montgomeryCutoffRadius n
  have hR : 0 ≤ R := by
    dsimp [R, montgomeryCutoffRadius]
    positivity
  have hu0 : u ≤ Real.log x := by linarith
  have hsub : u - R ≤ Real.log x := by linarith
  have hadd : u + R ≤ Real.log x := by
    dsimp [R] at hu ⊢
    linarith
  have hKsub : montgomeryKernel x t (u - R) =
      montgomeryKernel x t u *
        Complex.exp ((-1 + Complex.I * (t : ℂ)) * R) := by
    simp only [montgomeryKernel, abs_of_nonpos (sub_nonpos.mpr hsub),
      abs_of_nonpos (sub_nonpos.mpr hu0), ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hKadd : montgomeryKernel x t (u + R) =
      montgomeryKernel x t u *
        Complex.exp ((1 - Complex.I * (t : ℂ)) * R) := by
    simp only [montgomeryKernel, abs_of_nonpos (sub_nonpos.mpr hadd),
      abs_of_nonpos (sub_nonpos.mpr hu0), ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcancel := montgomeryCutoff_coeff_left_tail t n
  dsimp [R] at hKsub hKadd
  unfold montgomeryTailCutoff
  rw [hKsub, hKadd]
  calc
    montgomeryKernel x t u +
          montgomeryCutoffCoeffRight t n *
            (montgomeryKernel x t u *
              Complex.exp ((-1 + Complex.I * (t : ℂ)) * montgomeryCutoffRadius n)) +
        montgomeryCutoffCoeffLeft t n *
          (montgomeryKernel x t u *
            Complex.exp ((1 - Complex.I * (t : ℂ)) * montgomeryCutoffRadius n)) =
        montgomeryKernel x t u *
          (1 + montgomeryCutoffCoeffRight t n *
              Complex.exp ((-1 + Complex.I * (t : ℂ)) * montgomeryCutoffRadius n) +
            montgomeryCutoffCoeffLeft t n *
              Complex.exp ((1 - Complex.I * (t : ℂ)) * montgomeryCutoffRadius n)) := by
          ring
    _ = 0 := by rw [hcancel, mul_zero]

theorem montgomeryTailCutoff_hasCompactSupport (x t : ℝ) (n : ℕ) :
    HasCompactSupport (montgomeryTailCutoff x t n) := by
  apply HasCompactSupport.intro (isCompact_Icc :
    IsCompact (Set.Icc (Real.log x - montgomeryCutoffRadius n)
      (Real.log x + montgomeryCutoffRadius n)))
  intro u hu
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · exact montgomeryTailCutoff_eq_zero_of_left x t u n hu.le
  · exact montgomeryTailCutoff_eq_zero_of_right x t u n hu.le

theorem montgomeryCompactApprox_hasCompactSupport (x t : ℝ) (n : ℕ) :
    HasCompactSupport (montgomeryCompactApprox x t n) := by
  unfold montgomeryCompactApprox montgomeryMollifier
  exact (montgomeryBump n).hasCompactSupport_normed.convolution
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (montgomeryTailCutoff_hasCompactSupport x t n)

/-- The entire Fourier transform of the compactly supported mollifier. -/
def montgomeryMollifierPaperFT (n : ℕ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (montgomeryMollifier n u : ℂ) *
    Complex.exp (Complex.I * z * (u : ℂ))

theorem montgomeryTailCutoff_continuous (x t : ℝ) (n : ℕ) :
    Continuous (montgomeryTailCutoff x t n) := by
  unfold montgomeryTailCutoff
  have hbase := montgomeryKernel_continuous x t
  exact (hbase.add (continuous_const.mul
    (hbase.comp (continuous_id.sub continuous_const)))).add
      (continuous_const.mul (hbase.comp (continuous_id.add continuous_const)))

theorem montgomeryMollifierPaperFT_integrable (n : ℕ) (z : ℂ) :
    Integrable (fun u : ℝ => (montgomeryMollifier n u : ℂ) *
      Complex.exp (Complex.I * z * (u : ℂ))) := by
  have hmollContinuous : Continuous (fun u : ℝ => (montgomeryMollifier n u : ℂ)) := by
    exact Complex.continuous_ofReal.comp (montgomeryBump n).continuous_normed
  have hmollSupport : HasCompactSupport (fun u : ℝ =>
      (montgomeryMollifier n u : ℂ)) := by
    exact (montgomeryBump n).hasCompactSupport_normed.comp_left Complex.ofReal_zero
  exact (hmollContinuous.mul (by fun_prop)).integrable_of_hasCompactSupport
    hmollSupport.mul_right

theorem montgomeryTailCutoff_paperFT_integrable (x t : ℝ) (n : ℕ) (z : ℂ) :
    Integrable (fun u : ℝ => montgomeryTailCutoff x t n u *
      Complex.exp (Complex.I * z * (u : ℂ))) := by
  exact ((montgomeryTailCutoff_continuous x t n).mul (by fun_prop)).integrable_of_hasCompactSupport
    (montgomeryTailCutoff_hasCompactSupport x t n).mul_right

theorem montgomeryCompactApprox_paperFT (x t : ℝ) (n : ℕ) (z : ℂ) :
    Zeta23.paperFT (montgomeryCompactApprox x t n) z =
      montgomeryMollifierPaperFT n z *
        Zeta23.paperFT (montgomeryTailCutoff x t n) z := by
  let f : ℝ → ℂ := fun u => (montgomeryMollifier n u : ℂ) *
    Complex.exp (Complex.I * z * (u : ℂ))
  let g : ℝ → ℂ := fun u => montgomeryTailCutoff x t n u *
    Complex.exp (Complex.I * z * (u : ℂ))
  have hf : Integrable f := montgomeryMollifierPaperFT_integrable n z
  have hg : Integrable g := montgomeryTailCutoff_paperFT_integrable x t n z
  have hpoint (u : ℝ) :
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) u =
        montgomeryCompactApprox x t n u *
          Complex.exp (Complex.I * z * (u : ℂ)) := by
    unfold f g montgomeryCompactApprox montgomeryMollifier
    rw [convolution_def, convolution_def, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with v
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply,
      Complex.real_smul]
    have hexp :
        Complex.exp (Complex.I * z * (v : ℂ)) *
            Complex.exp (Complex.I * z * ((u - v : ℝ) : ℂ)) =
          Complex.exp (Complex.I * z * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hexp]
    ring
  calc
    Zeta23.paperFT (montgomeryCompactApprox x t n) z =
        ∫ u : ℝ, (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) u := by
          unfold Zeta23.paperFT
          apply integral_congr_ae
          filter_upwards with u
          exact (hpoint u).symm
    _ = (∫ u : ℝ, f u) * ∫ u : ℝ, g u := by
      exact MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hf hg
    _ = montgomeryMollifierPaperFT n z *
        Zeta23.paperFT (montgomeryTailCutoff x t n) z := rfl

theorem montgomeryKernel_paperFT_integrable (x t : ℝ) (z : ℂ) (hz : |z.im| < 1) :
    Integrable (fun u : ℝ => montgomeryKernel x t u *
      Complex.exp (Complex.I * z * (u : ℂ))) := by
  let a : ℝ := Real.log x
  let q : ℂ := (t : ℂ) - z
  have hq : |q.im| < 1 := by
    simpa only [q, sub_im, ofReal_im, zero_sub, abs_neg] using hz
  have hbase := twoSidedExponential_integrable 1 (by norm_num) q hq
  let C : ℂ := Complex.exp (Complex.I * (z - (t : ℂ)) * a)
  have hshift := (hbase.const_mul C).comp_add_right (-a)
  refine hshift.congr (Filter.Eventually.of_forall fun u => ?_)
  dsimp [C, a, q]
  simp only [montgomeryKernel, sub_eq_add_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem paperFT_translate_sub_integrable {f : ℝ → ℂ} (z : ℂ) (R : ℝ)
    (hf : Integrable (fun u : ℝ => f u *
      Complex.exp (Complex.I * z * (u : ℂ)))) :
    Integrable (fun u : ℝ => f (u - R) *
      Complex.exp (Complex.I * z * (u : ℂ))) := by
  have hshift := hf.comp_add_right (-R)
  have hmul := hshift.mul_const (Complex.exp (Complex.I * z * (R : ℂ)))
  refine hmul.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [sub_eq_add_neg]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem paperFT_translate_sub (f : ℝ → ℂ) (z : ℂ) (R : ℝ) :
    Zeta23.paperFT (fun u => f (u - R)) z =
      Complex.exp (Complex.I * z * (R : ℂ)) * Zeta23.paperFT f z := by
  unfold Zeta23.paperFT
  calc
    (∫ u : ℝ, f (u - R) * Complex.exp (Complex.I * z * (u : ℂ))) =
        ∫ u : ℝ, f ((u + R) - R) *
          Complex.exp (Complex.I * z * ((u + R : ℝ) : ℂ)) := by
            rw [integral_add_right_eq_self
              (fun u : ℝ => f (u - R) *
                Complex.exp (Complex.I * z * (u : ℂ))) R]
    _ = ∫ u : ℝ, (f u * Complex.exp (Complex.I * z * (u : ℂ))) *
          Complex.exp (Complex.I * z * (R : ℂ)) := by
            apply integral_congr_ae
            filter_upwards with u
            rw [add_sub_cancel_right]
            have hexp :
                Complex.exp (Complex.I * z * ((u + R : ℝ) : ℂ)) =
                  Complex.exp (Complex.I * z * (u : ℂ)) *
                    Complex.exp (Complex.I * z * (R : ℂ)) := by
              rw [← Complex.exp_add]
              congr 1
              push_cast
              ring
            rw [hexp]
            ring
    _ = (∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ))) *
          Complex.exp (Complex.I * z * (R : ℂ)) := by
            rw [integral_mul_const]
    _ = Complex.exp (Complex.I * z * (R : ℂ)) *
          ∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ)) := by
            ring

theorem paperFT_translate_add_integrable {f : ℝ → ℂ} (z : ℂ) (R : ℝ)
    (hf : Integrable (fun u : ℝ => f u *
      Complex.exp (Complex.I * z * (u : ℂ)))) :
    Integrable (fun u : ℝ => f (u + R) *
      Complex.exp (Complex.I * z * (u : ℂ))) := by
  simpa only [sub_neg_eq_add] using paperFT_translate_sub_integrable z (-R) hf

theorem paperFT_translate_add (f : ℝ → ℂ) (z : ℂ) (R : ℝ) :
    Zeta23.paperFT (fun u => f (u + R)) z =
      Complex.exp (-Complex.I * z * (R : ℂ)) * Zeta23.paperFT f z := by
  rw [show (fun u => f (u + R)) = (fun u => f (u - (-R))) by
    funext u
    rw [sub_neg_eq_add]]
  rw [paperFT_translate_sub]
  apply congrArg (fun w : ℂ => w * Zeta23.paperFT f z)
  apply congrArg Complex.exp
  push_cast
  ring

/-- The correction multiplier contributed by the two tail-cancelling translates. -/
def montgomeryCutoffMultiplier (t : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  1 + montgomeryCutoffCoeffRight t n *
      Complex.exp (Complex.I * z * montgomeryCutoffRadius n) +
    montgomeryCutoffCoeffLeft t n *
      Complex.exp (-Complex.I * z * montgomeryCutoffRadius n)

theorem montgomeryTailCutoff_paperFT (x t : ℝ) (n : ℕ) (z : ℂ)
    (hz : |z.im| < 1) :
    Zeta23.paperFT (montgomeryTailCutoff x t n) z =
      Zeta23.paperFT (montgomeryKernel x t) z *
        montgomeryCutoffMultiplier t n z := by
  let R := montgomeryCutoffRadius n
  let E : ℝ → ℂ := fun u => Complex.exp (Complex.I * z * (u : ℂ))
  have hbase : Integrable (fun u : ℝ => montgomeryKernel x t u * E u) :=
    montgomeryKernel_paperFT_integrable x t z hz
  have hsub : Integrable (fun u : ℝ => montgomeryKernel x t (u - R) * E u) :=
    paperFT_translate_sub_integrable z R hbase
  have hadd : Integrable (fun u : ℝ => montgomeryKernel x t (u + R) * E u) :=
    paperFT_translate_add_integrable z R hbase
  have hsubc : Integrable (fun u : ℝ => montgomeryCutoffCoeffRight t n *
      (montgomeryKernel x t (u - R) * E u)) := hsub.const_mul _
  have haddc : Integrable (fun u : ℝ => montgomeryCutoffCoeffLeft t n *
      (montgomeryKernel x t (u + R) * E u)) := hadd.const_mul _
  have hsplit :
      Zeta23.paperFT (montgomeryTailCutoff x t n) z =
        Zeta23.paperFT (montgomeryKernel x t) z +
          montgomeryCutoffCoeffRight t n *
            Zeta23.paperFT (fun u => montgomeryKernel x t (u - R)) z +
          montgomeryCutoffCoeffLeft t n *
            Zeta23.paperFT (fun u => montgomeryKernel x t (u + R)) z := by
    unfold Zeta23.paperFT montgomeryTailCutoff
    change (∫ u : ℝ,
        (montgomeryKernel x t u +
            montgomeryCutoffCoeffRight t n * montgomeryKernel x t (u - R) +
          montgomeryCutoffCoeffLeft t n * montgomeryKernel x t (u + R)) * E u) = _
    calc
      _ = ∫ u : ℝ,
          montgomeryKernel x t u * E u +
            montgomeryCutoffCoeffRight t n *
              (montgomeryKernel x t (u - R) * E u) +
            montgomeryCutoffCoeffLeft t n *
              (montgomeryKernel x t (u + R) * E u) := by
              apply integral_congr_ae
              filter_upwards with u
              ring
      _ = (∫ u : ℝ,
              montgomeryKernel x t u * E u +
                montgomeryCutoffCoeffRight t n *
                  (montgomeryKernel x t (u - R) * E u)) +
            ∫ u : ℝ, montgomeryCutoffCoeffLeft t n *
              (montgomeryKernel x t (u + R) * E u) := by
              simpa only [Pi.add_apply] using
                integral_add (hbase.add hsubc) haddc
      _ = (∫ u : ℝ, montgomeryKernel x t u * E u) +
            (∫ u : ℝ, montgomeryCutoffCoeffRight t n *
              (montgomeryKernel x t (u - R) * E u)) +
            ∫ u : ℝ, montgomeryCutoffCoeffLeft t n *
              (montgomeryKernel x t (u + R) * E u) := by
              rw [integral_add hbase hsubc]
      _ = _ := by
        rw [integral_const_mul, integral_const_mul]
  rw [hsplit, paperFT_translate_sub, paperFT_translate_add]
  unfold montgomeryCutoffMultiplier
  dsimp [R]
  ring

theorem montgomeryCompactApprox_paperFT_factor (x t : ℝ) (n : ℕ) (z : ℂ)
    (hz : |z.im| < 1) :
    Zeta23.paperFT (montgomeryCompactApprox x t n) z =
      montgomeryMollifierPaperFT n z *
        Zeta23.paperFT (montgomeryKernel x t) z *
          montgomeryCutoffMultiplier t n z := by
  rw [montgomeryCompactApprox_paperFT, montgomeryTailCutoff_paperFT x t n z hz]
  ring

theorem tendsto_montgomeryMollifierPaperFT (z : ℂ) :
    Tendsto (fun n : ℕ => montgomeryMollifierPaperFT n z) atTop (nhds 1) := by
  let g : ℝ → ℂ := fun u => Complex.exp (-Complex.I * z * (u : ℂ))
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hconv := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (φ := montgomeryBump) tendsto_montgomeryBump_rOut hg 0
  convert hconv using 1
  · funext n
    unfold montgomeryMollifierPaperFT montgomeryMollifier
    rw [convolution_def]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [g]
    simp only [zero_sub, Complex.ofReal_neg]
    congr 1
    ring_nf
  · dsimp [g]
    simp

theorem norm_montgomeryCutoffCoeffRight (t : ℝ) (n : ℕ) :
    ‖montgomeryCutoffCoeffRight t n‖ =
      1 / (Real.exp (montgomeryCutoffRadius n) +
        Real.exp (-montgomeryCutoffRadius n)) := by
  unfold montgomeryCutoffCoeffRight
  rw [norm_div, norm_neg, Complex.norm_exp]
  have hre :
      (-Complex.I * (t : ℂ) * (montgomeryCutoffRadius n : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero, ← Complex.ofReal_add, norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

theorem norm_montgomeryCutoffCoeffLeft (t : ℝ) (n : ℕ) :
    ‖montgomeryCutoffCoeffLeft t n‖ =
      1 / (Real.exp (montgomeryCutoffRadius n) +
        Real.exp (-montgomeryCutoffRadius n)) := by
  unfold montgomeryCutoffCoeffLeft
  rw [norm_div, norm_neg, Complex.norm_exp]
  have hre :
      (Complex.I * (t : ℂ) * (montgomeryCutoffRadius n : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero, ← Complex.ofReal_add, norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

theorem montgomeryCutoffRadius_nonneg (n : ℕ) :
    0 ≤ montgomeryCutoffRadius n := by
  unfold montgomeryCutoffRadius
  positivity

theorem montgomeryCutoffCoeffRight_norm_le (t : ℝ) (n : ℕ) :
    ‖montgomeryCutoffCoeffRight t n‖ ≤
      Real.exp (-montgomeryCutoffRadius n) := by
  rw [norm_montgomeryCutoffCoeffRight]
  calc
    1 / (Real.exp (montgomeryCutoffRadius n) +
          Real.exp (-montgomeryCutoffRadius n)) ≤
        1 / Real.exp (montgomeryCutoffRadius n) := by
      exact one_div_le_one_div_of_le (Real.exp_pos _)
        (le_add_of_nonneg_right (Real.exp_pos _).le)
    _ = Real.exp (-montgomeryCutoffRadius n) := by
      rw [one_div, ← Real.exp_neg]

theorem montgomeryCutoffCoeffLeft_norm_le (t : ℝ) (n : ℕ) :
    ‖montgomeryCutoffCoeffLeft t n‖ ≤
      Real.exp (-montgomeryCutoffRadius n) := by
  rw [norm_montgomeryCutoffCoeffLeft]
  calc
    1 / (Real.exp (montgomeryCutoffRadius n) +
          Real.exp (-montgomeryCutoffRadius n)) ≤
        1 / Real.exp (montgomeryCutoffRadius n) := by
      exact one_div_le_one_div_of_le (Real.exp_pos _)
        (le_add_of_nonneg_right (Real.exp_pos _).le)
    _ = Real.exp (-montgomeryCutoffRadius n) := by
      rw [one_div, ← Real.exp_neg]

theorem montgomeryCutoffRight_kernel_norm_le (x t u : ℝ) (n : ℕ) :
    ‖montgomeryCutoffCoeffRight t n *
        montgomeryKernel x t (u - montgomeryCutoffRadius n)‖ ≤
      Real.exp (-|u - Real.log x|) := by
  let R := montgomeryCutoffRadius n
  have hR : 0 ≤ R := montgomeryCutoffRadius_nonneg n
  have htri : |u - Real.log x| ≤ R + |u - R - Real.log x| := by
    calc
      |u - Real.log x| = |(u - R - Real.log x) + R| := by congr 1; ring
      _ ≤ |u - R - Real.log x| + |R| := abs_add_le _ _
      _ = R + |u - R - Real.log x| := by rw [abs_of_nonneg hR]; ring
  rw [norm_mul, norm_montgomeryKernel]
  calc
    ‖montgomeryCutoffCoeffRight t n‖ *
          Real.exp (-|u - montgomeryCutoffRadius n - Real.log x|) ≤
        Real.exp (-montgomeryCutoffRadius n) *
          Real.exp (-|u - montgomeryCutoffRadius n - Real.log x|) := by
      exact mul_le_mul_of_nonneg_right (montgomeryCutoffCoeffRight_norm_le t n)
        (Real.exp_nonneg _)
    _ = Real.exp (-R - |u - R - Real.log x|) := by
      dsimp [R]
      rw [← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-|u - Real.log x|) := by
      exact Real.exp_le_exp.mpr (by linarith)

theorem montgomeryCutoffLeft_kernel_norm_le (x t u : ℝ) (n : ℕ) :
    ‖montgomeryCutoffCoeffLeft t n *
        montgomeryKernel x t (u + montgomeryCutoffRadius n)‖ ≤
      Real.exp (-|u - Real.log x|) := by
  let R := montgomeryCutoffRadius n
  have hR : 0 ≤ R := montgomeryCutoffRadius_nonneg n
  have htri : |u - Real.log x| ≤ R + |u + R - Real.log x| := by
    calc
      |u - Real.log x| = |(u + R - Real.log x) - R| := by congr 1; ring
      _ ≤ |u + R - Real.log x| + |R| := abs_sub _ _
      _ = R + |u + R - Real.log x| := by rw [abs_of_nonneg hR]; ring
  rw [norm_mul, norm_montgomeryKernel]
  calc
    ‖montgomeryCutoffCoeffLeft t n‖ *
          Real.exp (-|u + montgomeryCutoffRadius n - Real.log x|) ≤
        Real.exp (-montgomeryCutoffRadius n) *
          Real.exp (-|u + montgomeryCutoffRadius n - Real.log x|) := by
      exact mul_le_mul_of_nonneg_right (montgomeryCutoffCoeffLeft_norm_le t n)
        (Real.exp_nonneg _)
    _ = Real.exp (-R - |u + R - Real.log x|) := by
      dsimp [R]
      rw [← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-|u - Real.log x|) := by
      exact Real.exp_le_exp.mpr (by linarith)

theorem montgomeryTailCutoff_norm_le (x t u : ℝ) (n : ℕ) :
    ‖montgomeryTailCutoff x t n u‖ ≤
      3 * Real.exp (-|u - Real.log x|) := by
  unfold montgomeryTailCutoff
  calc
    ‖montgomeryKernel x t u +
          montgomeryCutoffCoeffRight t n *
            montgomeryKernel x t (u - montgomeryCutoffRadius n) +
        montgomeryCutoffCoeffLeft t n *
          montgomeryKernel x t (u + montgomeryCutoffRadius n)‖ ≤
        ‖montgomeryKernel x t u‖ +
          ‖montgomeryCutoffCoeffRight t n *
            montgomeryKernel x t (u - montgomeryCutoffRadius n)‖ +
          ‖montgomeryCutoffCoeffLeft t n *
            montgomeryKernel x t (u + montgomeryCutoffRadius n)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ Real.exp (-|u - Real.log x|) + Real.exp (-|u - Real.log x|) +
          Real.exp (-|u - Real.log x|) := by
      exact add_le_add
        (add_le_add (le_of_eq (norm_montgomeryKernel x t u))
          (montgomeryCutoffRight_kernel_norm_le x t u n))
        (montgomeryCutoffLeft_kernel_norm_le x t u n)
    _ = 3 * Real.exp (-|u - Real.log x|) := by ring

theorem montgomeryCompactApprox_norm_le (x t u : ℝ) (n : ℕ) :
    ‖montgomeryCompactApprox x t n u‖ ≤
      3 * Real.exp 1 * Real.exp (-|u - Real.log x|) := by
  let C : ℝ := 3 * Real.exp 1 * Real.exp (-|u - Real.log x|)
  have hmollIntegrable : Integrable (montgomeryMollifier n) := by
    unfold montgomeryMollifier
    exact (montgomeryBump n).continuous_normed.integrable_of_hasCompactSupport
      (montgomeryBump n).hasCompactSupport_normed
  have hmajorant : Integrable (fun v : ℝ => C * montgomeryMollifier n v) :=
    hmollIntegrable.const_mul C
  have hpoint (v : ℝ) :
      ‖montgomeryMollifier n v • montgomeryTailCutoff x t n (u - v)‖ ≤
        C * montgomeryMollifier n v := by
    have hmollNonneg : 0 ≤ montgomeryMollifier n v :=
      (montgomeryBump n).nonneg_normed v
    by_cases hv : montgomeryMollifier n v = 0
    · simp [hv]
    · have hvSupport : v ∈ Function.support (montgomeryMollifier n) := hv
      unfold montgomeryMollifier at hvSupport
      rw [(montgomeryBump n).support_normed_eq] at hvSupport
      have hvRadius : |v| < (montgomeryBump n).rOut := by
        simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hvSupport
      have hradius : (montgomeryBump n).rOut ≤ 1 := by
        rw [montgomeryBump_rOut, div_le_iff₀ (by positivity)]
        norm_num
      have hvOne : |v| ≤ 1 := hvRadius.le.trans hradius
      have htri : |u - Real.log x| ≤ |u - v - Real.log x| + |v| := by
        calc
          |u - Real.log x| = |(u - v - Real.log x) + v| := by congr 1; ring
          _ ≤ |u - v - Real.log x| + |v| := abs_add_le _ _
      have hexp :
          Real.exp (-|u - v - Real.log x|) ≤
            Real.exp 1 * Real.exp (-|u - Real.log x|) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hmollNonneg]
      calc
        montgomeryMollifier n v * ‖montgomeryTailCutoff x t n (u - v)‖ ≤
            montgomeryMollifier n v *
              (3 * Real.exp (-|u - v - Real.log x|)) := by
          exact mul_le_mul_of_nonneg_left
            (montgomeryTailCutoff_norm_le x t (u - v) n) hmollNonneg
        _ ≤ montgomeryMollifier n v *
              (3 * (Real.exp 1 * Real.exp (-|u - Real.log x|))) := by
          gcongr
        _ = C * montgomeryMollifier n v := by
          dsimp [C]
          ring
  unfold montgomeryCompactApprox
  rw [convolution_def]
  calc
    ‖∫ v : ℝ, montgomeryMollifier n v •
        montgomeryTailCutoff x t n (u - v)‖ ≤
        ∫ v : ℝ, C * montgomeryMollifier n v :=
      norm_integral_le_of_norm_le hmajorant (Filter.Eventually.of_forall hpoint)
    _ = C * 1 := by
      rw [integral_const_mul]
      exact congrArg (fun w : ℝ => C * w) (montgomeryBump n).integral_normed
    _ = 3 * Real.exp 1 * Real.exp (-|u - Real.log x|) := by
      dsimp [C]
      ring

theorem montgomeryKernel_norm_le_one (x t u : ℝ) :
    ‖montgomeryKernel x t u‖ ≤ 1 := by
  rw [norm_montgomeryKernel, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (abs_nonneg _)

theorem montgomeryTailCutoff_sub_kernel_norm_le (x t u : ℝ) (n : ℕ) :
    ‖montgomeryTailCutoff x t n u - montgomeryKernel x t u‖ ≤
      2 * Real.exp (-montgomeryCutoffRadius n) := by
  unfold montgomeryTailCutoff
  calc
    ‖montgomeryKernel x t u +
          montgomeryCutoffCoeffRight t n *
            montgomeryKernel x t (u - montgomeryCutoffRadius n) +
        montgomeryCutoffCoeffLeft t n *
          montgomeryKernel x t (u + montgomeryCutoffRadius n) -
        montgomeryKernel x t u‖ =
        ‖montgomeryCutoffCoeffRight t n *
              montgomeryKernel x t (u - montgomeryCutoffRadius n) +
          montgomeryCutoffCoeffLeft t n *
            montgomeryKernel x t (u + montgomeryCutoffRadius n)‖ := by
      congr 1
      ring
    _ ≤ ‖montgomeryCutoffCoeffRight t n *
            montgomeryKernel x t (u - montgomeryCutoffRadius n)‖ +
          ‖montgomeryCutoffCoeffLeft t n *
            montgomeryKernel x t (u + montgomeryCutoffRadius n)‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (-montgomeryCutoffRadius n) * 1 +
          Real.exp (-montgomeryCutoffRadius n) * 1 := by
      rw [norm_mul, norm_mul]
      exact add_le_add
        (mul_le_mul (montgomeryCutoffCoeffRight_norm_le t n)
          (montgomeryKernel_norm_le_one x t _) (norm_nonneg _) (Real.exp_nonneg _))
        (mul_le_mul (montgomeryCutoffCoeffLeft_norm_le t n)
          (montgomeryKernel_norm_le_one x t _) (norm_nonneg _) (Real.exp_nonneg _))
    _ = 2 * Real.exp (-montgomeryCutoffRadius n) := by ring

theorem montgomeryCompactApprox_sub_smoothed_norm_le (x t u : ℝ) (n : ℕ) :
    ‖montgomeryCompactApprox x t n u - montgomerySmoothed x t n u‖ ≤
      2 * Real.exp (-montgomeryCutoffRadius n) := by
  let C : ℝ := 2 * Real.exp (-montgomeryCutoffRadius n)
  have hmollIntegrable : Integrable (montgomeryMollifier n) := by
    unfold montgomeryMollifier
    exact (montgomeryBump n).continuous_normed.integrable_of_hasCompactSupport
      (montgomeryBump n).hasCompactSupport_normed
  have happIntegrable : Integrable (fun v : ℝ =>
      montgomeryMollifier n v • montgomeryTailCutoff x t n (u - v)) := by
    exact ((montgomeryBump n).continuous_normed.smul
      ((montgomeryTailCutoff_continuous x t n).comp
        (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (montgomeryBump n).hasCompactSupport_normed.smul_right
  have hsmoothIntegrable : Integrable (fun v : ℝ =>
      montgomeryMollifier n v • montgomeryKernel x t (u - v)) := by
    exact ((montgomeryBump n).continuous_normed.smul
      ((montgomeryKernel_continuous x t).comp
        (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (montgomeryBump n).hasCompactSupport_normed.smul_right
  have hmajorant : Integrable (fun v : ℝ => C * montgomeryMollifier n v) :=
    hmollIntegrable.const_mul C
  have hpoint (v : ℝ) :
      ‖montgomeryMollifier n v • montgomeryTailCutoff x t n (u - v) -
          montgomeryMollifier n v • montgomeryKernel x t (u - v)‖ ≤
        C * montgomeryMollifier n v := by
    have hmollNonneg : 0 ≤ montgomeryMollifier n v :=
      (montgomeryBump n).nonneg_normed v
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hmollNonneg]
    simpa only [C, mul_comm] using mul_le_mul_of_nonneg_left
      (montgomeryTailCutoff_sub_kernel_norm_le x t (u - v) n) hmollNonneg
  unfold montgomeryCompactApprox montgomerySmoothed
  rw [convolution_def, convolution_def]
  change ‖(∫ v : ℝ,
      montgomeryMollifier n v • montgomeryTailCutoff x t n (u - v)) -
        ∫ v : ℝ, montgomeryMollifier n v • montgomeryKernel x t (u - v)‖ ≤ _
  rw [← integral_sub happIntegrable hsmoothIntegrable]
  calc
    ‖∫ v : ℝ,
        montgomeryMollifier n v • montgomeryTailCutoff x t n (u - v) -
          montgomeryMollifier n v • montgomeryKernel x t (u - v)‖ ≤
        ∫ v : ℝ, C * montgomeryMollifier n v :=
      norm_integral_le_of_norm_le hmajorant (Filter.Eventually.of_forall hpoint)
    _ = C * 1 := by
      rw [integral_const_mul]
      exact congrArg (fun w : ℝ => C * w) (montgomeryBump n).integral_normed
    _ = 2 * Real.exp (-montgomeryCutoffRadius n) := by
      dsimp [C]
      ring

theorem tendsto_montgomeryCompactApprox (x t u : ℝ) :
    Tendsto (fun n : ℕ => montgomeryCompactApprox x t n u) atTop
      (nhds (montgomeryKernel x t u)) := by
  have hsmoothed : Tendsto (fun n : ℕ => montgomerySmoothed x t n u) atTop
      (nhds (montgomeryKernel x t u)) := by
    exact ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume) (φ := montgomeryBump) tendsto_montgomeryBump_rOut
      (montgomeryKernel_continuous x t) u
  have hRadius : Tendsto montgomeryCutoffRadius atTop atTop := by
    unfold montgomeryCutoffRadius
    exact Filter.tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hdecay : Tendsto
      (fun n : ℕ => 2 * Real.exp (-montgomeryCutoffRadius n)) atTop (nhds 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hRadius
    have h' : Tendsto (fun n : ℕ => Real.exp (-montgomeryCutoffRadius n))
        atTop (nhds 0) := by
      simpa only [Function.comp_def] using h
    simpa only [mul_zero] using tendsto_const_nhds.mul h'
  have hdiff : Tendsto (fun n : ℕ =>
      ‖montgomeryCompactApprox x t n u - montgomerySmoothed x t n u‖) atTop
      (nhds 0) := by
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => montgomeryCompactApprox_sub_smoothed_norm_le x t u n) hdecay
  apply hsmoothed.congr_dist
  simpa only [dist_eq_norm, norm_sub_rev] using hdiff

theorem exp_neg_abs_log_sub_log_le_div (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.exp (-|Real.log y - Real.log x|) ≤ x / y := by
  calc
    Real.exp (-|Real.log y - Real.log x|) ≤
        Real.exp (Real.log x - Real.log y) := by
      apply Real.exp_le_exp.mpr
      rw [abs_sub_comm]
      exact neg_abs_le _
    _ = x / y := by rw [Real.exp_sub, Real.exp_log hx, Real.exp_log hy]

theorem exp_neg_abs_neg_log_sub_log_le_div (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Real.exp (-|-Real.log y - Real.log x|) ≤ x / y := by
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  calc
    Real.exp (-|-Real.log y - Real.log x|) =
        Real.exp (-Real.log y - Real.log x) := by
      rw [abs_of_nonpos (by linarith)]
      congr 1
      ring
    _ ≤ Real.exp (Real.log x - Real.log y) := by
      exact Real.exp_le_exp.mpr (by linarith)
    _ = x / y := by
      rw [Real.exp_sub, Real.exp_log (lt_of_lt_of_le zero_lt_one hx),
        Real.exp_log (lt_of_lt_of_le zero_lt_one hy)]

theorem norm_vonMangoldt_LSeries_term_three_halves (n : ℕ) (hn : n ≠ 0) :
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (((3 / 2 : ℝ) : ℂ)) n‖ =
      ArithmeticFunction.vonMangoldt n / (Real.sqrt n * n) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.norm_term_eq, ite_eq_right hn]
  simp only [Complex.ofReal_re, norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  congr 1
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hnpos,
    ← Real.sqrt_eq_rpow, Real.rpow_one]

/-- The prime sum for the compact approximations converges to the prime sum for Montgomery's
kernel.  Absolute convergence at exponent `3 / 2` supplies a single summable majorant. -/
theorem tendsto_montgomeryCompactApprox_prime_tsum (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    Tendsto
      (fun n : ℕ => ∑' m : ℕ,
        (((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
          (montgomeryCompactApprox x t n (Real.log m) +
            montgomeryCompactApprox x t n (-Real.log m))))
      atTop
      (nhds (∑' m : ℕ,
        (((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
          (montgomeryKernel x t (Real.log m) +
            montgomeryKernel x t (-Real.log m))))) := by
  let b : ℕ → ℝ := fun m =>
    6 * Real.exp 1 * x *
      ‖LSeries.term (fun j => (ArithmeticFunction.vonMangoldt j : ℂ))
        (((3 / 2 : ℝ) : ℂ)) m‖
  have hLSeries : LSeriesSummable
      (fun j => (ArithmeticFunction.vonMangoldt j : ℂ))
      (((3 / 2 : ℝ) : ℂ)) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hb : Summable b := by
    have hnorm : Summable (fun m : ℕ =>
        ‖LSeries.term (fun j => (ArithmeticFunction.vonMangoldt j : ℂ))
          (((3 / 2 : ℝ) : ℂ)) m‖) :=
      summable_norm_iff.mpr hLSeries
    simpa only [b] using Summable.mul_left (6 * Real.exp 1 * x) hnorm
  apply tendsto_tsum_of_dominated_convergence hb
  · intro m
    exact tendsto_const_nhds.mul
      ((tendsto_montgomeryCompactApprox x t (Real.log m)).add
        (tendsto_montgomeryCompactApprox x t (-Real.log m)))
  · filter_upwards with n
    intro m
    by_cases hm : m = 0
    · subst m
      simp [b]
    · have hmOne : 1 ≤ (m : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
      have hmPos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hmOne
      have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hx
      have hplus :
          ‖montgomeryCompactApprox x t n (Real.log m)‖ ≤
            3 * Real.exp 1 * (x / m) := by
        refine (montgomeryCompactApprox_norm_le x t (Real.log m) n).trans ?_
        exact mul_le_mul_of_nonneg_left
          (exp_neg_abs_log_sub_log_le_div x m hxPos hmPos)
          (by positivity)
      have hminus :
          ‖montgomeryCompactApprox x t n (-Real.log m)‖ ≤
            3 * Real.exp 1 * (x / m) := by
        refine (montgomeryCompactApprox_norm_le x t (-Real.log m) n).trans ?_
        exact mul_le_mul_of_nonneg_left
          (exp_neg_abs_neg_log_sub_log_le_div x m hx hmOne)
          (by positivity)
      dsimp only [b]
      rw [norm_vonMangoldt_LSeries_term_three_halves m hm]
      rw [norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.sqrt_nonneg _))]
      calc
        ArithmeticFunction.vonMangoldt m / Real.sqrt m *
            ‖montgomeryCompactApprox x t n (Real.log m) +
              montgomeryCompactApprox x t n (-Real.log m)‖ ≤
          ArithmeticFunction.vonMangoldt m / Real.sqrt m *
            (‖montgomeryCompactApprox x t n (Real.log m)‖ +
              ‖montgomeryCompactApprox x t n (-Real.log m)‖) := by
            exact mul_le_mul_of_nonneg_left (norm_add_le _ _)
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        _ ≤ ArithmeticFunction.vonMangoldt m / Real.sqrt m *
            (3 * Real.exp 1 * (x / m) + 3 * Real.exp 1 * (x / m)) := by
          gcongr
        _ = 6 * Real.exp 1 * x *
            (ArithmeticFunction.vonMangoldt m / (Real.sqrt m * m)) := by
          field_simp [ne_of_gt hmPos, ne_of_gt (Real.sqrt_pos.2 hmPos)]
          ring

/-- The Archimedean integrand for Montgomery's non-compact kernel is integrable. -/
theorem montgomeryKernel_archimedean_integrable (x t : ℝ) :
    Integrable (fun r : ℝ =>
      Zeta23.paperFT (montgomeryKernel x t) r * Zeta23.mu r) := by
  obtain ⟨K, hK, hinc⟩ := archimedeanDensity_increment_sqrt
  let w : ℝ → ℝ := fun u => (1 + |u|) ^ (1 / 2 : ℝ) / (1 + u ^ 2)
  let g : ℝ → ℝ := fun u => (2 * K) * w u
  have hw : Integrable w := by
    simpa only [w] using archimedeanIncrementWeight_integrable
  have hg : Integrable g := hw.const_mul (2 * K)
  let L : ℝ → ℂ := fun u =>
    2 * Complex.exp (Complex.I * (u : ℂ) * Real.log x) / (1 + (u : ℂ) ^ 2)
  have hL : Integrable L := by
    simpa only [L] using lorentzianOscillatory_integrable (Real.log x)
  have hLnorm (u : ℝ) : ‖L u‖ = 2 / (1 + u ^ 2) := by
    have hre : (Complex.I * (u : ℂ) * (Real.log x : ℂ)).re = 0 := by
      simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im]
      ring
    have hden : (1 : ℂ) + (u : ℂ) ^ 2 = ((1 + u ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    dsimp [L]
    rw [norm_div, norm_mul, Complex.norm_exp, hre, Real.exp_zero]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
      show ‖(1 : ℂ) + (u : ℂ) ^ 2‖ = 1 + u ^ 2 by
        rw [hden, norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < 1 + u ^ 2)]]
    norm_num
  have hmain : Integrable (fun u : ℝ => L u * (Zeta23.mu t : ℂ)) :=
    hL.mul_const _
  have hremContinuous : Continuous (fun u : ℝ =>
      L u * ((Zeta23.mu (t + u) - Zeta23.mu t : ℝ) : ℂ)) := by
    have hLc : Continuous L := by
      dsimp [L]
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro u
        have hden : (1 : ℂ) + (u : ℂ) ^ 2 = ((1 + u ^ 2 : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hden]
        exact ofReal_ne_zero.mpr (by positivity)
    have hmuContinuous : Continuous (fun u : ℝ =>
        Zeta23.mu (t + u) - Zeta23.mu t) :=
      (archimedeanDensity_smooth.continuous.comp (by fun_prop)).sub continuous_const
    exact hLc.mul (Complex.continuous_ofReal.comp hmuContinuous)
  have hremBound (u : ℝ) :
      ‖L u * ((Zeta23.mu (t + u) - Zeta23.mu t : ℝ) : ℂ)‖ ≤ g u := by
    rw [norm_mul, hLnorm, norm_real]
    calc
      2 / (1 + u ^ 2) * |Zeta23.mu (t + u) - Zeta23.mu t| ≤
          2 / (1 + u ^ 2) * (K * (1 + |u|) ^ (1 / 2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (hinc t u) (by positivity)
      _ = g u := by
        dsimp [g, w]
        ring
  have hrem : Integrable (fun u : ℝ =>
      L u * ((Zeta23.mu (t + u) - Zeta23.mu t : ℝ) : ℂ)) :=
    hg.mono' hremContinuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hremBound)
  have htotal : Integrable (fun u : ℝ => L u * Zeta23.mu (t + u)) := by
    apply (hmain.add hrem).congr
    filter_upwards with u
    simp only [Pi.add_apply]
    push_cast
    ring
  have htranslated : Integrable (fun u : ℝ =>
      Zeta23.paperFT (montgomeryKernel x t) ((u + t : ℝ) : ℂ) *
        Zeta23.mu (u + t)) := by
    apply htotal.congr
    filter_upwards with u
    rw [add_comm u t, montgomeryKernel_paperFT_realShift]
  simpa only [sub_add_cancel] using htranslated.comp_sub_right t

theorem montgomeryCutoffCorrectionRight_norm_le (t : ℝ) (n : ℕ) (z : ℂ)
    (hz : |z.im| ≤ (1 / 2 : ℝ)) :
    ‖montgomeryCutoffCoeffRight t n *
        Complex.exp (Complex.I * z * montgomeryCutoffRadius n)‖ ≤
      Real.exp (-montgomeryCutoffRadius n / 2) := by
  have hR := montgomeryCutoffRadius_nonneg n
  have hz' : -z.im ≤ (1 / 2 : ℝ) := by
    linarith [(abs_le.mp hz).1]
  have hexponent :
      -z.im * montgomeryCutoffRadius n ≤ montgomeryCutoffRadius n / 2 := by
    exact (mul_le_mul_of_nonneg_right hz' hR).trans_eq (by ring)
  rw [norm_mul, Complex.norm_exp]
  have hre :
      (Complex.I * z * (montgomeryCutoffRadius n : ℂ)).re =
        -z.im * montgomeryCutoffRadius n := by
    simp
  rw [hre]
  calc
    ‖montgomeryCutoffCoeffRight t n‖ *
        Real.exp (-z.im * montgomeryCutoffRadius n) ≤
      Real.exp (-montgomeryCutoffRadius n) *
        Real.exp (montgomeryCutoffRadius n / 2) := by
          exact mul_le_mul (montgomeryCutoffCoeffRight_norm_le t n)
            (Real.exp_le_exp.mpr hexponent) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (-montgomeryCutoffRadius n / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem montgomeryCutoffCorrectionLeft_norm_le (t : ℝ) (n : ℕ) (z : ℂ)
    (hz : |z.im| ≤ (1 / 2 : ℝ)) :
    ‖montgomeryCutoffCoeffLeft t n *
        Complex.exp (-Complex.I * z * montgomeryCutoffRadius n)‖ ≤
      Real.exp (-montgomeryCutoffRadius n / 2) := by
  have hR := montgomeryCutoffRadius_nonneg n
  have hz' : z.im ≤ (1 / 2 : ℝ) := (abs_le.mp hz).2
  have hexponent :
      z.im * montgomeryCutoffRadius n ≤ montgomeryCutoffRadius n / 2 := by
    exact (mul_le_mul_of_nonneg_right hz' hR).trans_eq (by ring)
  rw [norm_mul, Complex.norm_exp]
  have hre :
      (-Complex.I * z * (montgomeryCutoffRadius n : ℂ)).re =
        z.im * montgomeryCutoffRadius n := by
    simp
  rw [hre]
  calc
    ‖montgomeryCutoffCoeffLeft t n‖ *
        Real.exp (z.im * montgomeryCutoffRadius n) ≤
      Real.exp (-montgomeryCutoffRadius n) *
        Real.exp (montgomeryCutoffRadius n / 2) := by
          exact mul_le_mul (montgomeryCutoffCoeffLeft_norm_le t n)
            (Real.exp_le_exp.mpr hexponent) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (-montgomeryCutoffRadius n / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem tendsto_montgomeryCutoffRadius :
    Tendsto montgomeryCutoffRadius atTop atTop := by
  unfold montgomeryCutoffRadius
  exact Filter.tendsto_atTop_add_const_right atTop 1
    (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_montgomeryCutoffDecay :
    Tendsto (fun n : ℕ => Real.exp (-montgomeryCutoffRadius n / 2))
      atTop (nhds 0) := by
  have hhalf : Tendsto (fun n : ℕ => montgomeryCutoffRadius n * (1 / 2 : ℝ))
      atTop atTop :=
    tendsto_montgomeryCutoffRadius.atTop_mul_const (by norm_num)
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hhalf using 1
  funext n
  congr 1
  ring

theorem tendsto_montgomeryCutoffMultiplier (t : ℝ) (z : ℂ)
    (hz : |z.im| ≤ (1 / 2 : ℝ)) :
    Tendsto (fun n : ℕ => montgomeryCutoffMultiplier t n z) atTop (nhds 1) := by
  have hright : Tendsto
      (fun n : ℕ => montgomeryCutoffCoeffRight t n *
        Complex.exp (Complex.I * z * montgomeryCutoffRadius n))
      atTop (nhds 0) := by
    exact squeeze_zero_norm
      (fun n => montgomeryCutoffCorrectionRight_norm_le t n z hz)
      tendsto_montgomeryCutoffDecay
  have hleft : Tendsto
      (fun n : ℕ => montgomeryCutoffCoeffLeft t n *
        Complex.exp (-Complex.I * z * montgomeryCutoffRadius n))
      atTop (nhds 0) := by
    exact squeeze_zero_norm
      (fun n => montgomeryCutoffCorrectionLeft_norm_le t n z hz)
      tendsto_montgomeryCutoffDecay
  simpa only [montgomeryCutoffMultiplier, add_zero] using
    ((tendsto_const_nhds.add hright).add hleft)

theorem montgomeryCutoffMultiplier_norm_le (t : ℝ) (n : ℕ) (z : ℂ)
    (hz : |z.im| ≤ (1 / 2 : ℝ)) :
    ‖montgomeryCutoffMultiplier t n z‖ ≤ 3 := by
  have hdecay : Real.exp (-montgomeryCutoffRadius n / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hR := montgomeryCutoffRadius_nonneg n
    linarith
  unfold montgomeryCutoffMultiplier
  calc
    ‖1 + montgomeryCutoffCoeffRight t n *
          Complex.exp (Complex.I * z * montgomeryCutoffRadius n) +
        montgomeryCutoffCoeffLeft t n *
          Complex.exp (-Complex.I * z * montgomeryCutoffRadius n)‖ ≤
        ‖1 + montgomeryCutoffCoeffRight t n *
          Complex.exp (Complex.I * z * montgomeryCutoffRadius n)‖ +
          ‖montgomeryCutoffCoeffLeft t n *
            Complex.exp (-Complex.I * z * montgomeryCutoffRadius n)‖ :=
      norm_add_le _ _
    _ ≤
        ‖(1 : ℂ)‖ +
          ‖montgomeryCutoffCoeffRight t n *
            Complex.exp (Complex.I * z * montgomeryCutoffRadius n)‖ +
          ‖montgomeryCutoffCoeffLeft t n *
            Complex.exp (-Complex.I * z * montgomeryCutoffRadius n)‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ 1 + Real.exp (-montgomeryCutoffRadius n / 2) +
          Real.exp (-montgomeryCutoffRadius n / 2) := by
      exact add_le_add
        (add_le_add (by norm_num)
          (montgomeryCutoffCorrectionRight_norm_le t n z hz))
        (montgomeryCutoffCorrectionLeft_norm_le t n z hz)
    _ ≤ 3 := by linarith

theorem montgomeryMollifierPaperFT_norm_le (n : ℕ) (z : ℂ)
    (hz : |z.im| ≤ (1 / 2 : ℝ)) :
    ‖montgomeryMollifierPaperFT n z‖ ≤ Real.exp 1 := by
  have hmollIntegrable : Integrable (montgomeryMollifier n) := by
    unfold montgomeryMollifier
    exact (montgomeryBump n).continuous_normed.integrable_of_hasCompactSupport
      (montgomeryBump n).hasCompactSupport_normed
  have hmajorant : Integrable (fun u : ℝ => Real.exp 1 * montgomeryMollifier n u) :=
    hmollIntegrable.const_mul _
  have hpoint (u : ℝ) :
      ‖(montgomeryMollifier n u : ℂ) *
          Complex.exp (Complex.I * z * (u : ℂ))‖ ≤
        Real.exp 1 * montgomeryMollifier n u := by
    have hmollNonneg : 0 ≤ montgomeryMollifier n u :=
      (montgomeryBump n).nonneg_normed u
    by_cases hu : montgomeryMollifier n u = 0
    · simp [hu]
    · have husupport : u ∈ Function.support (montgomeryMollifier n) := hu
      unfold montgomeryMollifier at husupport
      rw [(montgomeryBump n).support_normed_eq] at husupport
      have huRadius : |u| < (montgomeryBump n).rOut := by
        simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using husupport
      have hradius : (montgomeryBump n).rOut ≤ 1 := by
        rw [montgomeryBump_rOut, div_le_iff₀ (by positivity)]
        norm_num
      have huOne : |u| ≤ 1 := huRadius.le.trans hradius
      have hexponent : -z.im * u ≤ 1 := by
        calc
          -z.im * u ≤ |-z.im * u| := le_abs_self _
          _ = |z.im| * |u| := by rw [abs_mul, abs_neg]
          _ ≤ (1 / 2 : ℝ) * 1 := by
            exact mul_le_mul hz huOne (abs_nonneg _) (by norm_num)
          _ ≤ 1 := by norm_num
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hmollNonneg,
        Complex.norm_exp]
      have hre : (Complex.I * z * (u : ℂ)).re = -z.im * u := by simp
      rw [hre]
      nlinarith [Real.exp_le_exp.mpr hexponent]
  unfold montgomeryMollifierPaperFT
  calc
    ‖∫ u : ℝ, (montgomeryMollifier n u : ℂ) *
        Complex.exp (Complex.I * z * (u : ℂ))‖ ≤
        ∫ u : ℝ, Real.exp 1 * montgomeryMollifier n u :=
      norm_integral_le_of_norm_le hmajorant (Filter.Eventually.of_forall hpoint)
    _ = Real.exp 1 * 1 := by
      rw [integral_const_mul]
      exact congrArg (fun v : ℝ => Real.exp 1 * v)
        (montgomeryBump n).integral_normed
    _ = Real.exp 1 := mul_one _

/-- The transforms of the compact approximations converge throughout the closed half-strip
needed by the zero and pole terms. -/
theorem tendsto_montgomeryCompactApprox_paperFT (x t : ℝ) (z : ℂ)
    (hz : |z.im| ≤ (1 / 2 : ℝ)) :
    Tendsto
      (fun n : ℕ => Zeta23.paperFT (montgomeryCompactApprox x t n) z)
      atTop (nhds (Zeta23.paperFT (montgomeryKernel x t) z)) := by
  have hz' : |z.im| < 1 := hz.trans_lt (by norm_num)
  simp_rw [montgomeryCompactApprox_paperFT_factor x t _ z hz']
  simpa using
    ((tendsto_montgomeryMollifierPaperFT z).mul tendsto_const_nhds).mul
      (tendsto_montgomeryCutoffMultiplier t z hz)

/-- Dominated convergence for the Archimedean terms of the compact approximations. -/
theorem tendsto_montgomeryCompactApprox_archimedean_integral (x t : ℝ) :
    Tendsto
      (fun n : ℕ => ∫ r : ℝ,
        Zeta23.paperFT (montgomeryCompactApprox x t n) r * Zeta23.mu r)
      atTop
      (nhds (∫ r : ℝ,
        Zeta23.paperFT (montgomeryKernel x t) r * Zeta23.mu r)) := by
  let b : ℝ → ℝ := fun r =>
    3 * Real.exp 1 *
      ‖Zeta23.paperFT (montgomeryKernel x t) r * Zeta23.mu r‖
  have hb : Integrable b := by
    simpa only [b] using
      (montgomeryKernel_archimedean_integrable x t).norm.const_mul (3 * Real.exp 1)
  apply MeasureTheory.tendsto_integral_of_dominated_convergence b
  · intro n
    have hft : Continuous (fun r : ℝ =>
        Zeta23.paperFT (montgomeryCompactApprox x t n) (r : ℂ)) :=
      (Zeta23.WeilEF.differentiable_paperFT
        (montgomeryCompactApprox_contDiff x t n).continuous
        (montgomeryCompactApprox_hasCompactSupport x t n)).continuous.comp
          Complex.continuous_ofReal
    exact (hft.mul (Complex.continuous_ofReal.comp
      archimedeanDensity_smooth.continuous)).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards with r
    have hrealStrip : |((r : ℂ)).im| < 1 := by simp
    rw [montgomeryCompactApprox_paperFT_factor x t n (r : ℂ) hrealStrip]
    dsimp only [b]
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    calc
      ‖montgomeryMollifierPaperFT n (r : ℂ)‖ *
            ‖Zeta23.paperFT (montgomeryKernel x t) (r : ℂ)‖ *
              ‖montgomeryCutoffMultiplier t n (r : ℂ)‖ *
                ‖(Zeta23.mu r : ℂ)‖ ≤
          Real.exp 1 * ‖Zeta23.paperFT (montgomeryKernel x t) (r : ℂ)‖ *
            3 * ‖(Zeta23.mu r : ℂ)‖ := by
        gcongr
        · exact montgomeryMollifierPaperFT_norm_le n (r : ℂ) (by simp)
        · exact montgomeryCutoffMultiplier_norm_le t n (r : ℂ) (by simp)
      _ = 3 * Real.exp 1 *
          (‖Zeta23.paperFT (montgomeryKernel x t) (r : ℂ)‖ *
            ‖(Zeta23.mu r : ℂ)‖) := by ring
  · filter_upwards with r
    exact (tendsto_montgomeryCompactApprox_paperFT x t (r : ℂ) (by simp)).mul
      tendsto_const_nhds

/-- Every term on the literature side of the explicit formula passes to Montgomery's
non-compact kernel. -/
theorem tendsto_montgomeryCompactApprox_literatureRHS (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    Tendsto
      (fun n : ℕ => Zeta23.EF.literatureRHS (montgomeryCompactApprox x t n))
      atTop (nhds (Zeta23.EF.literatureRHS (montgomeryKernel x t))) := by
  have hpoleRight := tendsto_montgomeryCompactApprox_paperFT x t
    (Complex.I / 2) (by norm_num)
  have hpoleLeft := tendsto_montgomeryCompactApprox_paperFT x t
    (-Complex.I / 2) (by norm_num)
  have hprime := tendsto_montgomeryCompactApprox_prime_tsum x hx t
  have harch := tendsto_montgomeryCompactApprox_archimedean_integral x t
  simpa only [Zeta23.EF.literatureRHS, Zeta23.EF.gamma_term] using
    ((hpoleRight.add hpoleLeft).sub hprime).add harch

theorem montgomeryCompactApprox_explicitFormula (x t : ℝ) (n : ℕ) :
    (∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
      ((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ) *
        Zeta23.paperFT (montgomeryCompactApprox x t n) (Zeta23.gammaOf rho)) =
      Zeta23.EF.literatureRHS (montgomeryCompactApprox x t n) :=
  (compactExplicitFormula (montgomeryCompactApprox x t n)
    (montgomeryCompactApprox_contDiff x t n)
    (montgomeryCompactApprox_hasCompactSupport x t n)).2

theorem tendsto_montgomeryCompactApprox_zero_tsum (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    Tendsto (fun n : ℕ =>
      ∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        ((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ) *
          Zeta23.paperFT (montgomeryCompactApprox x t n) (Zeta23.gammaOf rho))
      atTop (nhds (∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        ((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ) *
          Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho))) := by
  let b : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier → ℝ := fun rho =>
    3 * Real.exp 1 *
      ‖((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ) *
        Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho)‖
  have hb : Summable b := by
    simpa only [b] using Summable.mul_left (3 * Real.exp 1)
      (montgomeryKernel_zeroSeries_summable x hx t).norm
  apply tendsto_tsum_of_dominated_convergence hb
  · intro rho
    have hstrip := (Zeta23.zetaZeros Zeta23.zetaSeam).strip (rho : ℂ) rho.2
    have hgammaHalf : |(Zeta23.gammaOf (rho : ℂ)).im| ≤ (1 / 2 : ℝ) := by
      rw [Zeta23.WeilEF.gammaOf_im, abs_le]
      constructor <;> linarith [hstrip.1, hstrip.2]
    have hgammaOne : |(Zeta23.gammaOf (rho : ℂ)).im| < 1 :=
      hgammaHalf.trans_lt (by norm_num)
    have hft : Tendsto (fun n : ℕ =>
        Zeta23.paperFT (montgomeryCompactApprox x t n) (Zeta23.gammaOf rho))
        atTop (nhds (Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho))) := by
      simp_rw [montgomeryCompactApprox_paperFT_factor x t _
        (Zeta23.gammaOf rho) hgammaOne]
      simpa using ((tendsto_montgomeryMollifierPaperFT (Zeta23.gammaOf rho)).mul
        tendsto_const_nhds).mul
          (tendsto_montgomeryCutoffMultiplier t (Zeta23.gammaOf rho) hgammaHalf)
    exact tendsto_const_nhds.mul hft
  · filter_upwards with n
    intro rho
    have hstrip := (Zeta23.zetaZeros Zeta23.zetaSeam).strip (rho : ℂ) rho.2
    have hgammaHalf : |(Zeta23.gammaOf (rho : ℂ)).im| ≤ (1 / 2 : ℝ) := by
      rw [Zeta23.WeilEF.gammaOf_im, abs_le]
      constructor <;> linarith [hstrip.1, hstrip.2]
    have hgammaOne : |(Zeta23.gammaOf (rho : ℂ)).im| < 1 :=
      hgammaHalf.trans_lt (by norm_num)
    rw [montgomeryCompactApprox_paperFT_factor x t n
      (Zeta23.gammaOf rho) hgammaOne]
    dsimp [b]
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    calc
      ‖((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ)‖ *
          (‖montgomeryMollifierPaperFT n (Zeta23.gammaOf rho)‖ *
            ‖Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho)‖ *
              ‖montgomeryCutoffMultiplier t n (Zeta23.gammaOf rho)‖) ≤
        ‖((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ)‖ *
          (Real.exp 1 *
            ‖Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho)‖ * 3) := by
        gcongr
        · exact montgomeryMollifierPaperFT_norm_le n (Zeta23.gammaOf rho) hgammaHalf
        · exact montgomeryCutoffMultiplier_norm_le t n (Zeta23.gammaOf rho) hgammaHalf
      _ = 3 * Real.exp 1 *
          (‖((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ)‖ *
            ‖Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho)‖) := by ring_nf

/-- The compactly supported Weil formula extends to Montgomery's kernel by simultaneous
dominated convergence on its zero, prime, pole, and Archimedean terms. -/
theorem montgomeryKernel_explicitFormula (x : ℝ) (hx : 1 ≤ x) (t : ℝ) :
    Summable (fun rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
      ((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ) *
        Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho)) ∧
      (∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
          ((Zeta23.zetaZeros Zeta23.zetaSeam).mult rho : ℂ) *
            Zeta23.paperFT (montgomeryKernel x t) (Zeta23.gammaOf rho)) =
        Zeta23.EF.literatureRHS (montgomeryKernel x t) := by
  refine ⟨montgomeryKernel_zeroSeries_summable x hx t, ?_⟩
  exact tendsto_nhds_unique_of_eventuallyEq
    (tendsto_montgomeryCompactApprox_zero_tsum x hx t)
    (tendsto_montgomeryCompactApprox_literatureRHS x hx t)
    (Filter.Eventually.of_forall fun n => montgomeryCompactApprox_explicitFormula x t n)

end ZetaZeros.Unconditional.PairCorrelationProof
