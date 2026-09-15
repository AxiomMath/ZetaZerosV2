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

/-- The single analytic estimate needed by the integral step. -/
def FinitePairFunctionUniform : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
    ‖finitePairFunction (T ^ a) T / pairNormalization T -
        (finitePairModel T a : ℂ)‖ ≤
      K * (T ^ (-2 * a) + 1 / Real.sqrt (Real.log T))

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

/-- A uniform finite-pair estimate remains on the square-root logarithmic scale after
integration against an admissible test function. -/
theorem norm_integral_finitePairFunction_sub_model_le
    (f : ℝ → ℝ) (hf : Integrable f)
    (C : ℝ) (hC : ∀ x, |f x - f 0| ≤ C * |x|)
    (K : ℝ) (hK : 0 < K) (T : ℝ) (hT : 0 < T)
    (hlog : 1 ≤ Real.log T)
    (huniform : ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      ‖finitePairFunction (T ^ a) T / pairNormalization T -
          (finitePairModel T a : ℂ)‖ ≤
        K * (T ^ (-2 * a) + 1 / Real.sqrt (Real.log T))) :
    ‖∫ a : ℝ in 0..1, (f a : ℂ) *
        (finitePairFunction (T ^ a) T / pairNormalization T -
          (finitePairModel T a : ℂ))‖ ≤
      K * (|f 0| / 2 + C / 4 + ∫ a : ℝ in 0..1, |f a|) /
        Real.sqrt (Real.log T) := by
  have hexp : Continuous fun a : ℝ => Real.exp (-(2 * Real.log T * a)) := by fun_prop
  have hexpAbs : IntervalIntegrable
      (fun a : ℝ => Real.exp (-(2 * Real.log T * a)) * |f a|) volume 0 1 := by
    simpa [mul_comm] using
      hf.abs.intervalIntegrable.mul_continuousOn hexp.continuousOn
  have hconstAbs : IntervalIntegrable
      (fun a : ℝ => (1 / Real.sqrt (Real.log T)) * |f a|) volume 0 1 :=
    hf.abs.intervalIntegrable.const_mul _
  have hdom : IntervalIntegrable
      (fun a : ℝ => K * (Real.exp (-(2 * Real.log T * a)) * |f a| +
        (1 / Real.sqrt (Real.log T)) * |f a|)) volume 0 1 :=
    (hexpAbs.add hconstAbs).const_mul K
  have hpoint : ∀ a ∈ Ioc (0 : ℝ) 1,
      ‖(f a : ℂ) *
          (finitePairFunction (T ^ a) T / pairNormalization T -
            (finitePairModel T a : ℂ))‖ ≤
        K * (Real.exp (-(2 * Real.log T * a)) * |f a| +
          (1 / Real.sqrt (Real.log T)) * |f a|) := by
    intro a ha
    have hrpow : T ^ (-2 * a) = Real.exp (-(2 * Real.log T * a)) := by
      rw [Real.rpow_def_of_pos hT]
      congr 1
      ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |f a| * ‖finitePairFunction (T ^ a) T / pairNormalization T -
          (finitePairModel T a : ℂ)‖ ≤
          |f a| * (K * (T ^ (-2 * a) +
            1 / Real.sqrt (Real.log T))) :=
        mul_le_mul_of_nonneg_left (huniform a ha.1.le ha.2) (abs_nonneg _)
      _ = K * (Real.exp (-(2 * Real.log T * a)) * |f a| +
          (1 / Real.sqrt (Real.log T)) * |f a|) := by
        rw [hrpow]
        ring
  have hnorm :
      ‖∫ a : ℝ in 0..1, (f a : ℂ) *
          (finitePairFunction (T ^ a) T / pairNormalization T -
            (finitePairModel T a : ℂ))‖ ≤
        ∫ a : ℝ in 0..1, K *
          (Real.exp (-(2 * Real.log T * a)) * |f a| +
            (1 / Real.sqrt (Real.log T)) * |f a|) := by
    exact intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (by
        filter_upwards [] with a ha
        exact hpoint a ha)
      hdom
  have hweighted := integral_exp_neg_two_mul_abs_le f hf C hC
    (Real.log T) hlog
  have hinv := inv_le_inv_sqrt (Real.log T) hlog
  calc
    ‖∫ a : ℝ in 0..1, (f a : ℂ) *
        (finitePairFunction (T ^ a) T / pairNormalization T -
          (finitePairModel T a : ℂ))‖ ≤
        ∫ a : ℝ in 0..1, K *
          (Real.exp (-(2 * Real.log T * a)) * |f a| +
            (1 / Real.sqrt (Real.log T)) * |f a|) := hnorm
    _ = K * ((∫ a : ℝ in 0..1,
          Real.exp (-(2 * Real.log T * a)) * |f a|) +
        (1 / Real.sqrt (Real.log T)) *
          ∫ a : ℝ in 0..1, |f a|) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hexpAbs hconstAbs,
        intervalIntegral.integral_const_mul]
    _ ≤ K * (((|f 0| / 2 + C / 4) / Real.log T) +
        (1 / Real.sqrt (Real.log T)) *
          ∫ a : ℝ in 0..1, |f a|) := by
      gcongr
    _ ≤ K * (((|f 0| / 2 + C / 4) /
          Real.sqrt (Real.log T)) +
        (1 / Real.sqrt (Real.log T)) *
          ∫ a : ℝ in 0..1, |f a|) := by
      have hCnonneg : 0 ≤ C := by
        have h := hC 1
        norm_num only [abs_one, mul_one] at h
        exact (abs_nonneg _).trans h
      have hcoefficient : 0 ≤ |f 0| / 2 + C / 4 := by positivity
      have hterm : (|f 0| / 2 + C / 4) / Real.log T ≤
          (|f 0| / 2 + C / 4) / Real.sqrt (Real.log T) := by
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hinv hcoefficient
      exact mul_le_mul_of_nonneg_left (add_le_add hterm (le_refl _)) hK.le
    _ = K * (|f 0| / 2 + C / 4 + ∫ a : ℝ in 0..1, |f a|) /
        Real.sqrt (Real.log T) := by ring

/-- The uniform finite-pair estimate implies the pair-correlation asymptotic for every
admissible test function. -/
theorem rawPairCorrelation_asymptotic_of_uniform
    (huniform : FinitePairFunctionUniform) :
    ∀ f : ℝ → ℝ,
      (∀ x, f (-x) = f x) →
      Integrable f →
      (∀ x, 1 < |x| → f x = 0) →
      (∃ C, ∀ x, |f x - f 0| ≤ C * |x|) →
      ∃ C > 0, ∃ T₀, ∀ T ≥ T₀,
        ‖rawPairCorrelation f T / pairNormalization T -
            (((f 0 + 2 * ∫ a in (0 : ℝ)..1, a * f a) : ℝ) : ℂ)‖ ≤
          C / Real.sqrt (Real.log T) := by
  rcases huniform with ⟨K, hK, Tbase, huniform⟩
  intro f heven hf hsupp hLipschitz
  rcases hLipschitz with ⟨C, hC⟩
  have hCnonneg : 0 ≤ C := by
    have h := hC 1
    norm_num only [abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have habsIntegral : 0 ≤ ∫ a : ℝ in 0..1, |f a| :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => abs_nonneg _)
  let A : ℝ := C / 2 + |f 0|
  let B : ℝ := |f 0| / 2 + C / 4 + ∫ a : ℝ in 0..1, |f a|
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨1 + A + 2 * K * B, ?_, max Tbase (Real.exp 1), ?_⟩
  · have hKB : 0 ≤ 2 * K * B := by positivity
    linarith
  · intro T hTlarge
    have hTbase : Tbase ≤ T := le_trans (le_max_left _ _) hTlarge
    have hexpT : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hTlarge
    have hT : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hexpT
    have hlog : 1 ≤ Real.log T := (Real.le_log_iff_exp_le hT).2 hexpT
    have hsqrt : 0 < Real.sqrt (Real.log T) :=
      Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hlog)
    have hfiniteIntegrable :=
      integrable_mul_finitePairFunction_rpow f hf hsupp T hT
    have hfiniteEven : ∀ a : ℝ,
        (f (-a) : ℂ) * finitePairFunction (T ^ (-a)) T =
          (f a : ℂ) * finitePairFunction (T ^ a) T := by
      intro a
      rw [heven a, finitePairFunction_rpow_neg T a hT]
    have hfiniteSupport : ∀ a : ℝ, 1 < |a| →
        (f a : ℂ) * finitePairFunction (T ^ a) T = 0 := by
      intro a ha
      rw [hsupp a ha]
      simp
    have hraw : rawPairCorrelation f T =
        2 * ∫ a : ℝ in 0..1, (f a : ℂ) * finitePairFunction (T ^ a) T := by
      calc
        rawPairCorrelation f T =
            ∫ a : ℝ, (f a : ℂ) * finitePairFunction (T ^ a) T :=
          rawPairCorrelation_eq_integral f hf hsupp T hT
        _ = 2 * ∫ a : ℝ in 0..1,
            (f a : ℂ) * finitePairFunction (T ^ a) T :=
          integral_eq_two_mul_intervalIntegral_of_even_of_supported
            _ hfiniteIntegrable hfiniteEven hfiniteSupport
    have hrawNormalized : rawPairCorrelation f T / pairNormalization T =
        2 * ∫ a : ℝ in 0..1, (f a : ℂ) *
          (finitePairFunction (T ^ a) T / pairNormalization T) := by
      calc
        rawPairCorrelation f T / pairNormalization T =
            (2 * ∫ a : ℝ in 0..1,
              (f a : ℂ) * finitePairFunction (T ^ a) T) /
                pairNormalization T := by rw [hraw]
        _ = 2 * ((∫ a : ℝ in 0..1,
              (f a : ℂ) * finitePairFunction (T ^ a) T) /
                pairNormalization T) := by ring
        _ = 2 * ∫ a : ℝ in 0..1,
              ((f a : ℂ) * finitePairFunction (T ^ a) T) /
                pairNormalization T := by
          rw [intervalIntegral.integral_div]
        _ = 2 * ∫ a : ℝ in 0..1, (f a : ℂ) *
              (finitePairFunction (T ^ a) T / pairNormalization T) := by
          apply congrArg (fun z : ℂ => 2 * z)
          apply intervalIntegral.integral_congr
          intro a _
          ring
    have hquotientIntegrable : IntervalIntegrable
        (fun a : ℝ => (f a : ℂ) *
          (finitePairFunction (T ^ a) T / pairNormalization T)) volume 0 1 := by
      simpa [div_eq_mul_inv, mul_assoc] using
        (hfiniteIntegrable.div_const (pairNormalization T)).intervalIntegrable
    have hmodelContinuous : Continuous fun a : ℝ => (finitePairModel T a : ℂ) := by
      rw [show (fun a : ℝ => (finitePairModel T a : ℂ)) =
          fun a : ℝ =>
            ((Real.exp (-(2 * Real.log T * a)) * Real.log T + a : ℝ) : ℂ) by
        funext a
        rw [finitePairModel_eq_exp T a hT]]
      fun_prop
    have hmodelIntegrable : IntervalIntegrable
        (fun a : ℝ => (f a : ℂ) * (finitePairModel T a : ℂ)) volume 0 1 :=
      hf.ofReal.intervalIntegrable.mul_continuousOn hmodelContinuous.continuousOn
    have herrorIntegral :
        (∫ a : ℝ in 0..1, (f a : ℂ) *
            (finitePairFunction (T ^ a) T / pairNormalization T)) -
          (∫ a : ℝ in 0..1, (f a : ℂ) * (finitePairModel T a : ℂ)) =
        ∫ a : ℝ in 0..1, (f a : ℂ) *
          (finitePairFunction (T ^ a) T / pairNormalization T -
            (finitePairModel T a : ℂ)) := by
      calc
        (∫ a : ℝ in 0..1, (f a : ℂ) *
            (finitePairFunction (T ^ a) T / pairNormalization T)) -
          (∫ a : ℝ in 0..1, (f a : ℂ) * (finitePairModel T a : ℂ)) =
            ∫ a : ℝ in 0..1,
              ((f a : ℂ) *
                (finitePairFunction (T ^ a) T / pairNormalization T)) -
                  (f a : ℂ) * (finitePairModel T a : ℂ) :=
          (intervalIntegral.integral_sub hquotientIntegrable hmodelIntegrable).symm
        _ = ∫ a : ℝ in 0..1, (f a : ℂ) *
            (finitePairFunction (T ^ a) T / pairNormalization T -
              (finitePairModel T a : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro a _
          ring
    have hmodelIntegral :
        (∫ a : ℝ in 0..1, (f a : ℂ) * (finitePairModel T a : ℂ)) =
          ((Real.log T * (∫ a : ℝ in 0..1,
              Real.exp (-(2 * Real.log T * a)) * f a) +
            ∫ a : ℝ in 0..1, a * f a : ℝ) : ℂ) := by
      rw [show (fun a : ℝ => (f a : ℂ) * (finitePairModel T a : ℂ)) =
          fun a : ℝ => ((f a * finitePairModel T a : ℝ) : ℂ) by
        funext a
        push_cast
        rfl]
      rw [intervalIntegral.integral_ofReal,
        integral_mul_finitePairModel f hf T hT]
    have hendpointIdentity :
        ‖2 * (∫ a : ℝ in 0..1, (f a : ℂ) * (finitePairModel T a : ℂ)) -
            (((f 0 + 2 * ∫ a in (0 : ℝ)..1, a * f a) : ℝ) : ℂ)‖ =
          |2 * Real.log T * (∫ a : ℝ in 0..1,
              Real.exp (-(2 * Real.log T * a)) * f a) - f 0| := by
      rw [hmodelIntegral]
      rw [show
          (2 : ℂ) *
              ((Real.log T * (∫ a : ℝ in 0..1,
                    Real.exp (-(2 * Real.log T * a)) * f a) +
                ∫ a : ℝ in 0..1, a * f a : ℝ) : ℂ) -
              ((f 0 + 2 * ∫ a : ℝ in 0..1, a * f a : ℝ) : ℂ) =
            ((2 * Real.log T * (∫ a : ℝ in 0..1,
                Real.exp (-(2 * Real.log T * a)) * f a) - f 0 : ℝ) : ℂ) by
        push_cast
        ring]
      exact Complex.norm_real _
    have hendpoint :
        ‖2 * (∫ a : ℝ in 0..1, (f a : ℂ) * (finitePairModel T a : ℂ)) -
            (((f 0 + 2 * ∫ a in (0 : ℝ)..1, a * f a) : ℝ) : ℂ)‖ ≤
          A / Real.sqrt (Real.log T) := by
      rw [hendpointIdentity]
      calc
        |2 * Real.log T * (∫ a : ℝ in 0..1,
            Real.exp (-(2 * Real.log T * a)) * f a) - f 0| ≤
            (C / 2 + |f 0|) / Real.log T :=
          approximate_identity_bound f hf C hC (Real.log T) hlog
        _ ≤ A / Real.sqrt (Real.log T) := by
          have hinv := inv_le_inv_sqrt (Real.log T) hlog
          dsimp [A]
          simpa [A, div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left hinv hA
    have huniformAtT := huniform T hTbase
    have hintegrated := norm_integral_finitePairFunction_sub_model_le
      f hf C hC K hK T hT hlog huniformAtT
    have herror :
        ‖2 * ((∫ a : ℝ in 0..1, (f a : ℂ) *
              (finitePairFunction (T ^ a) T / pairNormalization T)) -
            (∫ a : ℝ in 0..1, (f a : ℂ) * (finitePairModel T a : ℂ)))‖ ≤
          2 * K * B / Real.sqrt (Real.log T) := by
      calc
        ‖2 * ((∫ a : ℝ in 0..1, (f a : ℂ) *
              (finitePairFunction (T ^ a) T / pairNormalization T)) -
            (∫ a : ℝ in 0..1, (f a : ℂ) * (finitePairModel T a : ℂ)))‖ =
            2 * ‖∫ a : ℝ in 0..1, (f a : ℂ) *
              (finitePairFunction (T ^ a) T / pairNormalization T -
                (finitePairModel T a : ℂ))‖ := by
          rw [herrorIntegral, norm_mul]
          norm_num
        _ ≤ 2 * (K * (|f 0| / 2 + C / 4 +
              ∫ a : ℝ in 0..1, |f a|) / Real.sqrt (Real.log T)) :=
          mul_le_mul_of_nonneg_left hintegrated (by norm_num)
        _ = 2 * K * B / Real.sqrt (Real.log T) := by
          dsimp [B]
          ring
    rw [hrawNormalized]
    calc
      ‖2 * (∫ a : ℝ in 0..1, (f a : ℂ) *
            (finitePairFunction (T ^ a) T / pairNormalization T)) -
          (((f 0 + 2 * ∫ a in (0 : ℝ)..1, a * f a) : ℝ) : ℂ)‖ =
          ‖2 * ((∫ a : ℝ in 0..1, (f a : ℂ) *
                (finitePairFunction (T ^ a) T / pairNormalization T)) -
              (∫ a : ℝ in 0..1, (f a : ℂ) * (finitePairModel T a : ℂ))) +
            (2 * (∫ a : ℝ in 0..1,
                (f a : ℂ) * (finitePairModel T a : ℂ)) -
              (((f 0 + 2 * ∫ a in (0 : ℝ)..1, a * f a) : ℝ) : ℂ))‖ := by
        congr 1
        ring
      _ ≤ ‖2 * ((∫ a : ℝ in 0..1, (f a : ℂ) *
              (finitePairFunction (T ^ a) T / pairNormalization T)) -
            (∫ a : ℝ in 0..1, (f a : ℂ) * (finitePairModel T a : ℂ)))‖ +
          ‖2 * (∫ a : ℝ in 0..1,
              (f a : ℂ) * (finitePairModel T a : ℂ)) -
            (((f 0 + 2 * ∫ a in (0 : ℝ)..1, a * f a) : ℝ) : ℂ)‖ :=
        norm_add_le _ _
      _ ≤ 2 * K * B / Real.sqrt (Real.log T) +
          A / Real.sqrt (Real.log T) := add_le_add herror hendpoint
      _ = (A + 2 * K * B) / Real.sqrt (Real.log T) := by ring
      _ ≤ (1 + A + 2 * K * B) / Real.sqrt (Real.log T) := by
        exact (div_le_div_iff_of_pos_right hsqrt).2 (by linarith)

end ZetaZeros.Unconditional.PairCorrelationProof
