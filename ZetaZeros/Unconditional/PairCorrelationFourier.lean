/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationLorentzian

/-!
# Fourier identities for pair correlation

This file proves the elementary Fourier identities for the Lorentzian kernel used in the
unconditional pair-correlation argument.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set

/-- Integrability in blueprint `lem_lorentz_ft`. -/
theorem twoSidedExponential_integrable (c : ℝ) (_hc : 0 < c) (z : ℂ)
    (hz : |z.im| < c) :
    Integrable (fun u : ℝ ↦
      Complex.exp (-(c : ℂ) * |u|) * Complex.exp (-Complex.I * z * u)) := by
  obtain ⟨hz_lower, hz_upper⟩ := abs_lt.mp hz
  have hleft : 0 < ((c : ℂ) - Complex.I * z).re := by
    simp only [sub_re, ofReal_re, mul_re, I_re, I_im]
    linarith
  have hright : ((-(c : ℂ) - Complex.I * z).re) < 0 := by
    simp only [sub_re, neg_re, ofReal_re, mul_re, I_re, I_im]
    linarith
  have intLeft : IntegrableOn
      (fun u : ℝ ↦ Complex.exp (((c : ℂ) - Complex.I * z) * u)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic hleft 0
  have intRight : IntegrableOn
      (fun u : ℝ ↦ Complex.exp ((-(c : ℂ) - Complex.I * z) * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hright 0
  have eqLeft : EqOn
      (fun u : ℝ ↦ Complex.exp (-(c : ℂ) * |u|) * Complex.exp (-Complex.I * z * u))
      (fun u : ℝ ↦ Complex.exp (((c : ℂ) - Complex.I * z) * u)) (Iic 0) := by
    intro u hu
    simp only [mem_Iic] at hu
    simp only [abs_of_nonpos hu, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have eqRight : EqOn
      (fun u : ℝ ↦ Complex.exp (-(c : ℂ) * |u|) * Complex.exp (-Complex.I * z * u))
      (fun u : ℝ ↦ Complex.exp ((-(c : ℂ) - Complex.I * z) * u)) (Ioi 0) := by
    intro u hu
    simp only [mem_Ioi] at hu
    simp only [abs_of_pos hu, ← Complex.exp_add]
    congr 1
    ring
  have := (intLeft.congr_fun eqLeft.symm measurableSet_Iic).union
    (intRight.congr_fun eqRight.symm measurableSet_Ioi)
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- Blueprint `lem_lorentz_ft`: the transform of a two-sided exponential. -/
theorem twoSidedExponential_integral (c : ℝ) (_hc : 0 < c) (z : ℂ)
    (hz : |z.im| < c) :
    ∫ u : ℝ, Complex.exp (-(c : ℂ) * |u|) * Complex.exp (-Complex.I * z * u) =
      2 * c / (c ^ 2 + z ^ 2) := by
  obtain ⟨hz_lower, hz_upper⟩ := abs_lt.mp hz
  have hleft : 0 < ((c : ℂ) - Complex.I * z).re := by
    simp only [sub_re, ofReal_re, mul_re, I_re, I_im]
    linarith
  have hright : ((-(c : ℂ) - Complex.I * z).re) < 0 := by
    simp only [sub_re, neg_re, ofReal_re, mul_re, I_re, I_im]
    linarith
  have intLeft : IntegrableOn
      (fun u : ℝ ↦ Complex.exp (((c : ℂ) - Complex.I * z) * u)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic hleft 0
  have intRight : IntegrableOn
      (fun u : ℝ ↦ Complex.exp ((-(c : ℂ) - Complex.I * z) * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hright 0
  have eqLeft : EqOn
      (fun u : ℝ ↦ Complex.exp (-(c : ℂ) * |u|) * Complex.exp (-Complex.I * z * u))
      (fun u : ℝ ↦ Complex.exp (((c : ℂ) - Complex.I * z) * u)) (Iic 0) := by
    intro u hu
    simp only [mem_Iic] at hu
    simp only [abs_of_nonpos hu, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have eqRight : EqOn
      (fun u : ℝ ↦ Complex.exp (-(c : ℂ) * |u|) * Complex.exp (-Complex.I * z * u))
      (fun u : ℝ ↦ Complex.exp ((-(c : ℂ) - Complex.I * z) * u)) (Ioi 0) := by
    intro u hu
    simp only [mem_Ioi] at hu
    simp only [abs_of_pos hu, ← Complex.exp_add]
    congr 1
    ring
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0)
      (intLeft.congr_fun eqLeft.symm measurableSet_Iic)
      (intRight.congr_fun eqRight.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Iic eqLeft,
    setIntegral_congr_fun measurableSet_Ioi eqRight,
    integral_exp_mul_complex_Iic hleft 0,
    integral_exp_mul_complex_Ioi hright 0]
  simp only [ofReal_zero, mul_zero, exp_zero]
  have hleft_ne : (c : ℂ) - Complex.I * z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [zero_re] at this
    linarith
  have hright_ne : -(c : ℂ) - Complex.I * z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [zero_re] at this
    linarith
  have hdenom : (c : ℂ) ^ 2 + z ^ 2 ≠ 0 := by
    rw [show (c : ℂ) ^ 2 + z ^ 2 =
      ((c : ℂ) - Complex.I * z) * ((c : ℂ) + Complex.I * z) by
        calc
          (c : ℂ) ^ 2 + z ^ 2 = (c : ℂ) ^ 2 - (Complex.I * z) ^ 2 := by
            rw [mul_pow, Complex.I_sq]
            ring
          _ = ((c : ℂ) - Complex.I * z) * ((c : ℂ) + Complex.I * z) := by ring]
    refine mul_ne_zero hleft_ne ?_
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, zero_re] at hre
    linarith
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A complex translate of the Lorentzian kernel is integrable as long as neither pole crosses
the real axis. -/
theorem shiftedLorentzian_integrable (a : ℂ) (ha : |a.im| < 1) :
    Integrable (fun t : ℝ ↦ 1 / (1 + ((t : ℂ) + a) ^ 2)) := by
  obtain ⟨ha_lower, ha_upper⟩ := abs_lt.mp ha
  have hc : 0 < 1 - a.im ^ 2 := by
    have hprod : 0 < (1 - a.im) * (1 + a.im) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hlower (t : ℝ) :
      (1 - a.im ^ 2) * (1 + (t + a.re) ^ 2) ≤
        ‖(1 : ℂ) + ((t : ℂ) + a) ^ 2‖ := by
    calc
      (1 - a.im ^ 2) * (1 + (t + a.re) ^ 2) ≤
          1 - a.im ^ 2 + (t + a.re) ^ 2 := by
        have hprod : 0 ≤ a.im ^ 2 * (t + a.re) ^ 2 :=
          mul_nonneg (sq_nonneg _) (sq_nonneg _)
        nlinarith
      _ = ((1 : ℂ) + ((t : ℂ) + a) ^ 2).re := by
        simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.one_re,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      _ ≤ ‖(1 : ℂ) + ((t : ℂ) + a) ^ 2‖ := Complex.re_le_norm _
  have hbase (t : ℝ) : 0 < 1 + (t + a.re) ^ 2 := by positivity
  have hdenom (t : ℝ) : (1 : ℂ) + ((t : ℂ) + a) ^ 2 ≠ 0 := by
    intro hzero
    have := hlower t
    rw [hzero, norm_zero] at this
    exact (not_le_of_gt (mul_pos hc (hbase t))) this
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ ↦ 1 / (1 + ((t : ℂ) + a) ^ 2)) := by
    apply Continuous.aestronglyMeasurable
    fun_prop (disch := aesop)
  have hmajorant : Integrable
      (fun t : ℝ ↦ (1 - a.im ^ 2)⁻¹ * (1 + (t + a.re) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_add_right a.re).const_mul _
  refine hmajorant.mono' hmeas ?_
  filter_upwards with t
  have hpos : 0 < (1 - a.im ^ 2) * (1 + (t + a.re) ^ 2) :=
    mul_pos hc (hbase t)
  calc
    ‖(1 : ℂ) / (1 + ((t : ℂ) + a) ^ 2)‖ =
        1 / ‖(1 : ℂ) + ((t : ℂ) + a) ^ 2‖ := by simp
    _ ≤ 1 / ((1 - a.im ^ 2) * (1 + (t + a.re) ^ 2)) :=
      one_div_le_one_div_of_le hpos (hlower t)
    _ = (1 - a.im ^ 2)⁻¹ * (1 + (t + a.re) ^ 2)⁻¹ := by
      rw [one_div, mul_inv_rev]
      ring

/-- The exponentially decaying function whose Fourier transform is a shifted Lorentzian. -/
def lorentzianFourierSource (a : ℂ) (u : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (Complex.exp (-(1 : ℂ) * |u|) *
    Complex.exp (-Complex.I * a * u))

theorem lorentzianFourierSource_continuous (a : ℂ) :
    Continuous (lorentzianFourierSource a) := by
  unfold lorentzianFourierSource
  fun_prop

theorem lorentzianFourierSource_integrable (a : ℂ) (ha : |a.im| < 1) :
    Integrable (lorentzianFourierSource a) := by
  apply (twoSidedExponential_integrable 1 zero_lt_one a ha).const_mul
    (1 / 2 : ℂ) |>.congr
  filter_upwards with u
  simp only [lorentzianFourierSource]
  congr 3

/-- The normalized Fourier transform of `lorentzianFourierSource`. -/
theorem fourier_lorentzianFourierSource (a : ℂ) (ha : |a.im| < 1) (ξ : ℝ) :
    FourierTransform.fourier (lorentzianFourierSource a) ξ =
      1 / (1 + (((2 * Real.pi * ξ : ℝ) : ℂ) + a) ^ 2) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hintegrand (u : ℝ) :
      Complex.exp (((-2 * Real.pi * u * ξ : ℝ) : ℂ) * Complex.I) •
          lorentzianFourierSource a u =
        (1 / 2 : ℂ) * (Complex.exp (-(1 : ℂ) * |u|) *
          Complex.exp (-Complex.I * (((2 * Real.pi * ξ : ℝ) : ℂ) + a) * u)) := by
    simp only [lorentzianFourierSource, smul_eq_mul]
    calc
      Complex.exp (((-2 * Real.pi * u * ξ : ℝ) : ℂ) * Complex.I) *
          ((1 / 2 : ℂ) * (Complex.exp (-(1 : ℂ) * |u|) *
            Complex.exp (-Complex.I * a * u))) =
          (1 / 2 : ℂ) * Complex.exp (-(1 : ℂ) * |u|) *
            (Complex.exp (((-2 * Real.pi * u * ξ : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-Complex.I * a * u)) := by ring
      _ = (1 / 2 : ℂ) * Complex.exp (-(1 : ℂ) * |u|) *
          Complex.exp (-Complex.I * (((2 * Real.pi * ξ : ℝ) : ℂ) + a) * u) := by
        rw [← Complex.exp_add]
        congr 3
        push_cast
        ring
      _ = (1 / 2 : ℂ) * (Complex.exp (-(1 : ℂ) * |u|) *
          Complex.exp (-Complex.I * (((2 * Real.pi * ξ : ℝ) : ℂ) + a) * u)) := by ring
  rw [integral_congr_ae (ae_of_all _ hintegrand), integral_const_mul]
  have htransform := twoSidedExponential_integral 1 zero_lt_one
    (((2 * Real.pi * ξ : ℝ) : ℂ) + a) (by simpa using ha)
  norm_num at htransform ⊢
  rw [htransform]
  ring

/-- Self-adjointness of the real Fourier transform, specialized to complex multiplication. -/
theorem integral_fourier_mul_eq (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ : ℝ, FourierTransform.fourier f ξ * g ξ) =
      ∫ x : ℝ, f x * FourierTransform.fourier g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := volume) (ν := volume)
    (L := innerₗ ℝ) (f := f) (g := g)
    Real.continuous_fourierChar (by fun_prop) hf hg
  have hflip (x : ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ).flip g x =
        FourierTransform.fourier g x := by
    rw [Real.vector_fourierIntegral_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with v
    congr 3
    simp only [LinearMap.flip_apply]
    simp
    ring
  simpa only [smul_eq_mul, FourierTransform.fourier, Real.instFourierTransform,
    hflip] using h

/-- Blueprint `lem_lorentz_conv`: convolution of two complex-shifted Lorentzian kernels. -/
theorem shiftedLorentzian_convolution (a b : ℂ) (ha : |a.im| < 1) (hb : |b.im| < 1) :
    ∫ t : ℝ,
      1 / ((1 + (t + a) ^ 2) * (1 + (t + b) ^ 2)) =
      2 * Real.pi / (4 + (a - b) ^ 2) := by
  have hfa := lorentzianFourierSource_integrable a ha
  have hfb := lorentzianFourierSource_integrable b hb
  have hFbi : Integrable (FourierTransform.fourier (lorentzianFourierSource b)) := by
    have hscaled := (shiftedLorentzian_integrable b hb).comp_mul_right'
      (show 2 * Real.pi ≠ 0 by positivity)
    apply hscaled.congr
    filter_upwards with ξ
    rw [fourier_lorentzianFourierSource b hb]
    congr 4
    push_cast
    ring
  have hdouble (x : ℝ) :
      FourierTransform.fourier
          (FourierTransform.fourier (lorentzianFourierSource b)) x =
        lorentzianFourierSource b (-x) := by
    calc
      FourierTransform.fourier
          (FourierTransform.fourier (lorentzianFourierSource b)) x =
          FourierTransformInv.fourierInv
            (FourierTransform.fourier (lorentzianFourierSource b)) (-x) := by
        rw [Real.fourierInv_eq_fourier_neg]
        simp
      _ = lorentzianFourierSource b (-x) :=
        hfb.fourierInv_fourier_eq hFbi
          (lorentzianFourierSource_continuous b).continuousAt
  have hparseval :
      (∫ ξ : ℝ, FourierTransform.fourier (lorentzianFourierSource a) ξ *
        FourierTransform.fourier (lorentzianFourierSource b) ξ) =
        ∫ x : ℝ, lorentzianFourierSource a x * lorentzianFourierSource b (-x) := by
    calc
      _ = ∫ x : ℝ, lorentzianFourierSource a x *
          FourierTransform.fourier
            (FourierTransform.fourier (lorentzianFourierSource b)) x :=
        integral_fourier_mul_eq _ _ hfa hFbi
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hdouble]
  have hz : |(a - b).im| < (2 : ℝ) := by
    rw [Complex.sub_im]
    calc
      |a.im - b.im| ≤ |a.im| + |b.im| := abs_sub _ _
      _ < 2 := by linarith
  have hsource :
      (∫ x : ℝ, lorentzianFourierSource a x * lorentzianFourierSource b (-x)) =
        1 / (4 + (a - b) ^ 2) := by
    have hpoint (x : ℝ) :
        lorentzianFourierSource a x * lorentzianFourierSource b (-x) =
          (1 / 4 : ℂ) * (Complex.exp (-(2 : ℂ) * |x|) *
            Complex.exp (-Complex.I * (a - b) * x)) := by
      simp only [lorentzianFourierSource, abs_neg]
      push_cast
      calc
        ((1 / 2 : ℂ) *
            (Complex.exp (-(1 : ℂ) * |x|) * Complex.exp (-Complex.I * a * x))) *
            ((1 / 2 : ℂ) *
              (Complex.exp (-(1 : ℂ) * |x|) * Complex.exp (-Complex.I * b * (-x)))) =
            (1 / 4 : ℂ) *
              ((Complex.exp (-(1 : ℂ) * |x|) * Complex.exp (-(1 : ℂ) * |x|)) *
                (Complex.exp (-Complex.I * a * x) *
                  Complex.exp (-Complex.I * b * (-x)))) := by ring
        _ = (1 / 4 : ℂ) * (Complex.exp (-(2 : ℂ) * |x|) *
            Complex.exp (-Complex.I * (a - b) * x)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 3 <;> ring
    rw [integral_congr_ae (ae_of_all _ hpoint), integral_const_mul]
    have htransform := twoSidedExponential_integral 2 (by norm_num) (a - b) hz
    norm_num at htransform ⊢
    rw [htransform]
    ring
  let q : ℝ → ℂ := fun t ↦
    1 / ((1 + ((t : ℂ) + a) ^ 2) * (1 + ((t : ℂ) + b) ^ 2))
  change (∫ t : ℝ, q t) = 2 * Real.pi / (4 + (a - b) ^ 2)
  have hfrequency :
      (∫ ξ : ℝ, q (ξ * (2 * Real.pi))) = 1 / (4 + (a - b) ^ 2) := by
    calc
      (∫ ξ : ℝ, q (ξ * (2 * Real.pi))) =
          ∫ ξ : ℝ,
            1 / (1 + (((2 * Real.pi * ξ : ℝ) : ℂ) + a) ^ 2) *
              (1 / (1 + (((2 * Real.pi * ξ : ℝ) : ℂ) + b) ^ 2)) := by
        apply integral_congr_ae
        filter_upwards with ξ
        simp only [q, one_div]
        have hcast : (((ξ * (2 * Real.pi) : ℝ) : ℂ)) =
            (((2 * Real.pi * ξ : ℝ) : ℂ)) := by
          push_cast
          ring
        rw [hcast, mul_inv_rev]
        ring
      _ = ∫ x : ℝ,
          lorentzianFourierSource a x * lorentzianFourierSource b (-x) := by
        calc
          _ = ∫ ξ : ℝ, FourierTransform.fourier (lorentzianFourierSource a) ξ *
              FourierTransform.fourier (lorentzianFourierSource b) ξ := by
            apply integral_congr_ae
            filter_upwards with ξ
            rw [fourier_lorentzianFourierSource a ha,
              fourier_lorentzianFourierSource b hb]
          _ = _ := hparseval
      _ = _ := hsource
  have hscale := MeasureTheory.Measure.integral_comp_mul_right q (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := by positivity
  calc
    (∫ t : ℝ, q t) = (2 * Real.pi : ℝ) • ∫ ξ : ℝ, q (ξ * (2 * Real.pi)) := by
      rw [hscale, abs_of_pos (inv_pos.mpr hpi), smul_smul,
        mul_inv_cancel₀ hpi.ne', one_smul]
    _ = 2 * Real.pi / (4 + (a - b) ^ 2) := by
      rw [hfrequency]
      rw [Complex.real_smul]
      push_cast
      ring

end ZetaZeros.Unconditional.PairCorrelationProof
