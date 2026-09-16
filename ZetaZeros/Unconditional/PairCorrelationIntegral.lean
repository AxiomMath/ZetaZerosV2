/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationError

/-!
# The integral step in Montgomery's pair-correlation argument

This file turns a uniform estimate for Montgomery's finite pair function into the test-function
asymptotic used by the unconditional pair-correlation theorem.  It also records the finite
sum/integral interchange that connects the Fourier-transform formulation to the finite pair
function.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set

/-- The normalizing factor in Montgomery's finite pair-function estimate. -/
noncomputable def pairNormalization (T : ℝ) : ℂ :=
  (((T / (2 * Real.pi)) * Real.log T : ℝ) : ℂ)

/-- The real main term in the uniform finite pair-function estimate. -/
noncomputable def finitePairModel (T a : ℝ) : ℝ :=
  T ^ (-2 * a) * Real.log T + a

/-- Reversing the real-power parameter negates the spectral exponent. -/
theorem pairPower_rpow_neg (T a : ℝ) (z : ℂ) (hT : 0 < T) :
    pairPower (T ^ (-a)) z = pairPower (T ^ a) (-z) := by
  rw [pairPower_rpow T (-a) z hT, pairPower_rpow T a (-z) hT]
  congr 1
  push_cast
  ring

/-- Montgomery's finite pair function is even in its logarithmic parameter. -/
theorem finitePairFunction_rpow_neg (T a : ℝ) (hT : 0 < T) :
    finitePairFunction (T ^ (-a)) T = finitePairFunction (T ^ a) T := by
  rw [finitePairFunction_eq_finset_sum, finitePairFunction_eq_finset_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rho' hrho'
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [pairPower_rpow_neg T a (rho - rho') hT]
  rw [show rho - rho' = -(rho' - rho) by ring, finitePairKernel_neg]
  rw [neg_neg]
  push_cast
  ring

/-- The finite-pair integrand is integrable for every admissibly supported integrable test
function. -/
theorem integrable_mul_finitePairFunction_rpow (f : ℝ → ℝ) (hf : Integrable f)
    (hsupp : ∀ a : ℝ, 1 < |a| → f a = 0) (T : ℝ) (hT : 0 < T) :
    Integrable (fun a : ℝ => (f a : ℂ) * finitePairFunction (T ^ a) T) := by
  rw [show (fun a : ℝ => (f a : ℂ) * finitePairFunction (T ^ a) T) =
      fun a : ℝ =>
        ∑ rho ∈ (Zeta23.zerosIn_finite 0 T).toFinset,
          ∑ rho' ∈ (Zeta23.zerosIn_finite 0 T).toFinset,
            ((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ) *
              ((f a : ℂ) * pairPower (T ^ a) (rho - rho')) *
                finitePairKernel (rho - rho') by
    funext a
    rw [finitePairFunction_eq_finset_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hrho
    apply Finset.sum_congr rfl
    intro rho' hrho'
    ring]
  apply integrable_finsetSum
  intro rho hrho
  apply integrable_finsetSum
  intro rho' hrho'
  exact ((integrable_mul_pairPower_rpow f hf hsupp T hT (rho - rho')).const_mul
    (((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ))).mul_const
      (finitePairKernel (rho - rho'))

/-- Integrating against the finite pair function is exactly the ordered zero-pair sum of the
individual pair-power integrals. -/
theorem integral_mul_finitePairFunction_rpow (f : ℝ → ℝ) (hf : Integrable f)
    (hsupp : ∀ a : ℝ, 1 < |a| → f a = 0) (T : ℝ) (hT : 0 < T) :
    (∫ a : ℝ, (f a : ℂ) * finitePairFunction (T ^ a) T) =
      ∑ᶠ rho ∈ Zeta23.zerosIn 0 T, ∑ᶠ rho' ∈ Zeta23.zerosIn 0 T,
        ((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ) *
          (∫ a : ℝ, (f a : ℂ) * pairPower (T ^ a) (rho - rho')) *
            finitePairKernel (rho - rho') := by
  rw [nested_finsum_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite 0 T)]
  rw [show (fun a : ℝ => (f a : ℂ) * finitePairFunction (T ^ a) T) =
      fun a : ℝ =>
        ∑ rho ∈ (Zeta23.zerosIn_finite 0 T).toFinset,
          ∑ rho' ∈ (Zeta23.zerosIn_finite 0 T).toFinset,
            ((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ) *
              ((f a : ℂ) * pairPower (T ^ a) (rho - rho')) *
                finitePairKernel (rho - rho') by
    funext a
    rw [finitePairFunction_eq_finset_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hrho
    apply Finset.sum_congr rfl
    intro rho' hrho'
    ring]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro rho hrho
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro rho' hrho'
      rw [show (fun a : ℝ =>
          ((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ) *
              ((f a : ℂ) * pairPower (T ^ a) (rho - rho')) *
                finitePairKernel (rho - rho')) =
          fun a : ℝ =>
            ((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ) *
              (((f a : ℂ) * pairPower (T ^ a) (rho - rho')) *
                finitePairKernel (rho - rho')) by
            funext a
            ring,
        integral_const_mul, integral_mul_const]
      ring
    · intro rho' hrho'
      exact ((integrable_mul_pairPower_rpow f hf hsupp T hT (rho - rho')).const_mul
        (((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ))).mul_const
          (finitePairKernel (rho - rho'))
  · intro rho hrho
    apply integrable_finsetSum
    intro rho' hrho'
    exact ((integrable_mul_pairPower_rpow f hf hsupp T hT (rho - rho')).const_mul
      (((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ))).mul_const
        (finitePairKernel (rho - rho'))

/-- The raw Fourier-transform pair sum, stated independently of the challenge module. -/
noncomputable def rawPairCorrelation (f : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∑ᶠ rho ∈ Zeta23.zerosIn 0 T, ∑ᶠ rho' ∈ Zeta23.zerosIn 0 T,
    ((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ) *
      (∫ a : ℝ, (f a : ℂ) *
        Complex.exp
          (-(2 * (Real.pi : ℂ)) * Complex.I *
            (Complex.I * (rho - rho') *
              ((Real.log T / (2 * Real.pi) : ℝ) : ℂ)) * (a : ℂ))) *
        finitePairKernel (rho - rho')

/-- Finite sum/integral interchange in the exact Fourier normalization of the challenge. -/
theorem rawPairCorrelation_eq_integral (f : ℝ → ℝ) (hf : Integrable f)
    (hsupp : ∀ a : ℝ, 1 < |a| → f a = 0) (T : ℝ) (hT : 0 < T) :
    rawPairCorrelation f T =
      ∫ a : ℝ, (f a : ℂ) * finitePairFunction (T ^ a) T := by
  rw [integral_mul_finitePairFunction_rpow f hf hsupp T hT]
  unfold rawPairCorrelation
  apply finsum_congr
  intro rho
  apply finsum_congr
  intro hrho
  apply finsum_congr
  intro rho'
  apply finsum_congr
  intro hrho'
  rw [fourierIntegral_rescaled_eq_pairPower f T (rho - rho') hT]

/-- An even integrable function supported on `[-1,1]` integrates over the line to twice its
integral on `[0,1]`. -/
theorem integral_eq_two_mul_intervalIntegral_of_even_of_supported
    (g : ℝ → ℂ) (hg : Integrable g) (heven : ∀ a, g (-a) = g a)
    (hsupp : ∀ a : ℝ, 1 < |a| → g a = 0) :
    (∫ a : ℝ, g a) = 2 * ∫ a : ℝ in 0..1, g a := by
  have houtside : ∀ a ∉ Icc (-1 : ℝ) 1, g a = 0 := by
    intro a ha
    apply hsupp
    simp only [mem_Icc, not_and_or, not_le] at ha
    rcases ha with ha | ha
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      exact ha
  have hwhole :
      (∫ a : ℝ, g a) = ∫ a : ℝ in (-1 : ℝ)..1, g a := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [← integral_Icc_eq_integral_Ioc]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero houtside).symm
  have hleft : (∫ a : ℝ in (-1 : ℝ)..0, g a) = ∫ a : ℝ in 0..1, g a := by
    have hneg : (∫ a : ℝ in 0..1, g (-a)) = ∫ a : ℝ in (-1)..0, g a := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg (a := 0) (b := 1) g)
    rw [← hneg]
    apply intervalIntegral.integral_congr
    intro a ha
    exact heven a
  rw [hwhole]
  calc
    (∫ a : ℝ in (-1 : ℝ)..1, g a) =
        (∫ a : ℝ in (-1 : ℝ)..0, g a) + ∫ a : ℝ in 0..1, g a :=
      (intervalIntegral.integral_add_adjacent_intervals
        hg.intervalIntegrable hg.intervalIntegrable).symm
    _ = 2 * ∫ a : ℝ in 0..1, g a := by rw [hleft]; ring

/-- On the positive half of the support, the finite-pair main term is the sum of the
approximate-identity kernel and the limiting linear density. -/
theorem finitePairModel_eq_exp (T a : ℝ) (hT : 0 < T) :
    finitePairModel T a =
      Real.exp (-(2 * Real.log T * a)) * Real.log T + a := by
  rw [finitePairModel, Real.rpow_def_of_pos hT]
  congr 2
  ring_nf

/-- The integral of the finite-pair main term separates into its endpoint and bulk pieces. -/
theorem integral_mul_finitePairModel (f : ℝ → ℝ) (hf : Integrable f)
    (T : ℝ) (hT : 0 < T) :
    (∫ a : ℝ in 0..1, f a * finitePairModel T a) =
      Real.log T * (∫ a : ℝ in 0..1,
        Real.exp (-(2 * Real.log T * a)) * f a) +
        ∫ a : ℝ in 0..1, a * f a := by
  have hexp : Continuous fun a : ℝ => Real.exp (-(2 * Real.log T * a)) := by fun_prop
  have hlinear : Continuous fun a : ℝ => a := continuous_id
  have hendpoint : IntervalIntegrable
      (fun a : ℝ => Real.exp (-(2 * Real.log T * a)) * f a) volume 0 1 :=
    by simpa [mul_comm] using
      hf.intervalIntegrable.mul_continuousOn hexp.continuousOn
  have hbulk : IntervalIntegrable (fun a : ℝ => a * f a) volume 0 1 :=
    by simpa [mul_comm] using
      hf.intervalIntegrable.mul_continuousOn hlinear.continuousOn
  rw [show (fun a : ℝ => f a * finitePairModel T a) =
      fun a : ℝ =>
        Real.log T * (Real.exp (-(2 * Real.log T * a)) * f a) + a * f a by
    funext a
    rw [finitePairModel_eq_exp T a hT]
    ring]
  rw [intervalIntegral.integral_add (hendpoint.const_mul _) hbulk,
    intervalIntegral.integral_const_mul]

end ZetaZeros.Unconditional.PairCorrelationProof
