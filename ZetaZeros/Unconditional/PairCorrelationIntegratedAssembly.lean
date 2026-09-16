/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationAssembly
import ZetaZeros.Unconditional.PairCorrelationMeanValue

/-!
# Integrated assembly for the endpoint pair-correlation estimate

Montgomery--Vaughan's mean-value remainder is not uniformly small at `x = T`, but its
integral against a test function is small enough.  This file records the corresponding
integrated contracts and proves, without a pointwise-uniform detour, that they imply the
exact test-function pair-correlation asymptotic.

Both contracts quantify over the test function and a displayed Lipschitz constant.  Their
constants are universal; all test-function dependence is carried by `integratedTestSize`.
In particular, the endpoint comparison remains a separate hypothesis and is not hidden in
the desired finite-pair conclusion.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set

/-- The explicit test-function size used by the integrated analytic contracts. -/
noncomputable def integratedTestSize (f : ℝ → ℝ) (C : ℝ) : ℝ :=
  |f 0| + C + ∫ a : ℝ in 0..1, |f a|

/-- Integrated full-zero mean-square input.  Unlike `FullZeroModelSecondMoment`, this asks
only for the weighted integral which is used downstream.  The universal constant `K` is
independent of `f` and of its displayed Lipschitz constant `C`. -/
def IntegratedFullZeroModelSecondMoment : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℝ,
    ∀ (f : ℝ → ℝ) (C : ℝ), Integrable f → 0 ≤ C →
      (∀ x : ℝ, |x| ≤ 1 → |f x - f 0| ≤ C * |x|) →
      ∀ T ≥ T₀,
        IntervalIntegrable
          (fun a : ℝ => (f a : ℂ) *
            (windowedFullZeroSecondMoment (T ^ a) T -
              ((2 * Real.pi : ℝ) : ℂ) * pairNormalization T *
                (finitePairModel T a : ℂ))) volume 0 1 ∧
        ‖∫ a : ℝ in 0..1, (f a : ℂ) *
            (windowedFullZeroSecondMoment (T ^ a) T -
              ((2 * Real.pi : ℝ) : ℂ) * pairNormalization T *
                (finitePairModel T a : ℂ))‖ ≤
          2 * Real.pi * ‖pairNormalization T‖ *
            (K * integratedTestSize f C / Real.sqrt (Real.log T))

/-- Integrated comparison between the finite zero window and the full-zero moment.  This is
the genuine closed-endpoint input; it is deliberately separate from the full-zero model
evaluation. -/
def IntegratedFullWindowEndpointComparison : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℝ,
    ∀ (f : ℝ → ℝ) (C : ℝ), Integrable f → 0 ≤ C →
      (∀ x : ℝ, |x| ≤ 1 → |f x - f 0| ≤ C * |x|) →
      ∀ T ≥ T₀,
        IntervalIntegrable
          (fun a : ℝ => (f a : ℂ) *
            (finiteWindowSecondMoment (T ^ a) T -
              windowedFullZeroSecondMoment (T ^ a) T)) volume 0 1 ∧
        ‖∫ a : ℝ in 0..1, (f a : ℂ) *
            (finiteWindowSecondMoment (T ^ a) T -
              windowedFullZeroSecondMoment (T ^ a) T)‖ ≤
          2 * Real.pi * ‖pairNormalization T‖ *
            (K * integratedTestSize f C / Real.sqrt (Real.log T))

/-- The integrated finite-pair estimate which is exactly sufficient for the final integral
step. -/
def IntegratedFinitePairFunctionEstimate : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℝ,
    ∀ (f : ℝ → ℝ) (C : ℝ), Integrable f → 0 ≤ C →
      (∀ x : ℝ, |x| ≤ 1 → |f x - f 0| ≤ C * |x|) →
      ∀ T ≥ T₀,
        ‖∫ a : ℝ in 0..1, (f a : ℂ) *
            (finitePairFunction (T ^ a) T / pairNormalization T -
              (finitePairModel T a : ℂ))‖ ≤
          K * integratedTestSize f C / Real.sqrt (Real.log T)

/-- Algebraic transfer from the two weighted second-moment errors to the weighted normalized
finite-pair error.  The two integrability hypotheses are explicit because they are exactly
what licenses addition of the two interval integrals. -/
theorem norm_integral_finitePairFunction_sub_model_le_of_integrated_secondMoment_bounds
    (f : ℝ → ℝ) (T E_main E_comparison : ℝ)
    (hN : pairNormalization T ≠ 0)
    (hmainIntegrable : IntervalIntegrable
      (fun a : ℝ => (f a : ℂ) *
        (windowedFullZeroSecondMoment (T ^ a) T -
          ((2 * Real.pi : ℝ) : ℂ) * pairNormalization T *
            (finitePairModel T a : ℂ))) volume 0 1)
    (hcomparisonIntegrable : IntervalIntegrable
      (fun a : ℝ => (f a : ℂ) *
        (finiteWindowSecondMoment (T ^ a) T -
          windowedFullZeroSecondMoment (T ^ a) T)) volume 0 1)
    (hmain :
      ‖∫ a : ℝ in 0..1, (f a : ℂ) *
          (windowedFullZeroSecondMoment (T ^ a) T -
            ((2 * Real.pi : ℝ) : ℂ) * pairNormalization T *
              (finitePairModel T a : ℂ))‖ ≤
        2 * Real.pi * ‖pairNormalization T‖ * E_main)
    (hcomparison :
      ‖∫ a : ℝ in 0..1, (f a : ℂ) *
          (finiteWindowSecondMoment (T ^ a) T -
            windowedFullZeroSecondMoment (T ^ a) T)‖ ≤
        2 * Real.pi * ‖pairNormalization T‖ * E_comparison) :
    ‖∫ a : ℝ in 0..1, (f a : ℂ) *
        (finitePairFunction (T ^ a) T / pairNormalization T -
          (finitePairModel T a : ℂ))‖ ≤ E_main + E_comparison := by
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ)
  have hcpos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hcne : c ≠ 0 := by
    change (((2 * Real.pi : ℝ) : ℂ) ≠ 0)
    exact_mod_cast ne_of_gt hcpos
  have hNnorm : 0 < ‖pairNormalization T‖ := norm_pos_iff.mpr hN
  have hdenpos : 0 < 2 * Real.pi * ‖pairNormalization T‖ :=
    mul_pos hcpos hNnorm
  have hcNnorm : ‖c * pairNormalization T‖ =
      2 * Real.pi * ‖pairNormalization T‖ := by
    norm_num [c, norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hpoint : ∀ a : ℝ,
      (f a : ℂ) *
          (finitePairFunction (T ^ a) T / pairNormalization T -
            (finitePairModel T a : ℂ)) =
        ((f a : ℂ) *
            (finiteWindowSecondMoment (T ^ a) T -
              windowedFullZeroSecondMoment (T ^ a) T) +
          (f a : ℂ) *
            (windowedFullZeroSecondMoment (T ^ a) T -
              c * pairNormalization T * (finitePairModel T a : ℂ))) /
            (c * pairNormalization T) := by
    intro a
    rw [finiteWindowSecondMoment_eq]
    field_simp [hcne, hN]
    dsimp [c]
    push_cast
    ring
  have hintegral :
      (∫ a : ℝ in 0..1, (f a : ℂ) *
          (finitePairFunction (T ^ a) T / pairNormalization T -
            (finitePairModel T a : ℂ))) =
        ((∫ a : ℝ in 0..1, (f a : ℂ) *
            (finiteWindowSecondMoment (T ^ a) T -
              windowedFullZeroSecondMoment (T ^ a) T)) +
          (∫ a : ℝ in 0..1, (f a : ℂ) *
            (windowedFullZeroSecondMoment (T ^ a) T -
              c * pairNormalization T * (finitePairModel T a : ℂ)))) /
            (c * pairNormalization T) := by
    calc
      (∫ a : ℝ in 0..1, (f a : ℂ) *
          (finitePairFunction (T ^ a) T / pairNormalization T -
            (finitePairModel T a : ℂ))) =
          ∫ a : ℝ in 0..1,
            (((f a : ℂ) *
                (finiteWindowSecondMoment (T ^ a) T -
                  windowedFullZeroSecondMoment (T ^ a) T) +
              (f a : ℂ) *
                (windowedFullZeroSecondMoment (T ^ a) T -
                  c * pairNormalization T * (finitePairModel T a : ℂ))) /
                (c * pairNormalization T)) := by
            apply intervalIntegral.integral_congr
            intro a _
            exact hpoint a
      _ = (∫ a : ℝ in 0..1,
            ((f a : ℂ) *
                (finiteWindowSecondMoment (T ^ a) T -
                  windowedFullZeroSecondMoment (T ^ a) T) +
              (f a : ℂ) *
                (windowedFullZeroSecondMoment (T ^ a) T -
                  c * pairNormalization T * (finitePairModel T a : ℂ)))) /
              (c * pairNormalization T) := by
            rw [intervalIntegral.integral_div]
      _ = ((∫ a : ℝ in 0..1, (f a : ℂ) *
              (finiteWindowSecondMoment (T ^ a) T -
                windowedFullZeroSecondMoment (T ^ a) T)) +
            (∫ a : ℝ in 0..1, (f a : ℂ) *
              (windowedFullZeroSecondMoment (T ^ a) T -
                c * pairNormalization T * (finitePairModel T a : ℂ)))) /
              (c * pairNormalization T) := by
            rw [intervalIntegral.integral_add hcomparisonIntegrable hmainIntegrable]
  rw [hintegral, norm_div, hcNnorm]
  apply (div_le_iff₀ hdenpos).2
  calc
    ‖(∫ a : ℝ in 0..1, (f a : ℂ) *
          (finiteWindowSecondMoment (T ^ a) T -
            windowedFullZeroSecondMoment (T ^ a) T)) +
        (∫ a : ℝ in 0..1, (f a : ℂ) *
          (windowedFullZeroSecondMoment (T ^ a) T -
            c * pairNormalization T * (finitePairModel T a : ℂ)))‖ ≤
        ‖∫ a : ℝ in 0..1, (f a : ℂ) *
          (finiteWindowSecondMoment (T ^ a) T -
            windowedFullZeroSecondMoment (T ^ a) T)‖ +
        ‖∫ a : ℝ in 0..1, (f a : ℂ) *
          (windowedFullZeroSecondMoment (T ^ a) T -
            c * pairNormalization T * (finitePairModel T a : ℂ))‖ := norm_add_le _ _
    _ ≤ 2 * Real.pi * ‖pairNormalization T‖ * E_comparison +
        2 * Real.pi * ‖pairNormalization T‖ * E_main :=
      add_le_add hcomparison hmain
    _ = (E_main + E_comparison) *
        (2 * Real.pi * ‖pairNormalization T‖) := by ring

/-- The two integrated second-moment contracts imply the exactly sufficient integrated
finite-pair estimate. -/
theorem integratedFinitePairFunctionEstimate_of_secondMomentContracts
    (hfull : IntegratedFullZeroModelSecondMoment)
    (hendpoint : IntegratedFullWindowEndpointComparison) :
    IntegratedFinitePairFunctionEstimate := by
  rcases hfull with ⟨Kmain, hKmain, Tmain, hmain⟩
  rcases hendpoint with ⟨Kcomparison, hKcomparison, Tcomparison, hcomparison⟩
  refine ⟨Kmain + Kcomparison, add_pos hKmain hKcomparison,
    max (max Tmain Tcomparison) (Real.exp 1), ?_⟩
  intro f C hf hC hLip T hT
  have hTmain : Tmain ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTcomparison : Tcomparison ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hexpT : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hexpT
  have hlogone : 1 ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 hexpT
  have hlogpos : 0 < Real.log T := lt_of_lt_of_le zero_lt_one hlogone
  have hN : pairNormalization T ≠ 0 := by
    unfold pairNormalization
    exact Complex.ofReal_ne_zero.mpr
      (mul_ne_zero
        (div_ne_zero (ne_of_gt hTpos)
          (mul_ne_zero (by norm_num) Real.pi_ne_zero))
        (ne_of_gt hlogpos))
  rcases hmain f C hf hC hLip T hTmain with ⟨hmainInt, hmainBound⟩
  rcases hcomparison f C hf hC hLip T hTcomparison with
    ⟨hcomparisonInt, hcomparisonBound⟩
  have hbound :=
    norm_integral_finitePairFunction_sub_model_le_of_integrated_secondMoment_bounds
      f T
      (Kmain * integratedTestSize f C / Real.sqrt (Real.log T))
      (Kcomparison * integratedTestSize f C / Real.sqrt (Real.log T))
      hN hmainInt hcomparisonInt hmainBound hcomparisonBound
  calc
    ‖∫ a : ℝ in 0..1, (f a : ℂ) *
        (finitePairFunction (T ^ a) T / pairNormalization T -
          (finitePairModel T a : ℂ))‖ ≤
        Kmain * integratedTestSize f C / Real.sqrt (Real.log T) +
          Kcomparison * integratedTestSize f C / Real.sqrt (Real.log T) := hbound
    _ = (Kmain + Kcomparison) * integratedTestSize f C /
        Real.sqrt (Real.log T) := by ring

/-- An integrated finite-pair estimate implies the exact raw pair-correlation asymptotic for
every even integrable test function supported on the closed interval `[-1,1]` and Lipschitz
at zero. -/
theorem rawPairCorrelation_asymptotic_of_integratedFinitePairFunctionEstimate
    (hintegrated : IntegratedFinitePairFunctionEstimate) :
    ∀ f : ℝ → ℝ,
      (∀ x, f (-x) = f x) →
      Integrable f →
      (∀ x, 1 < |x| → f x = 0) →
      (∃ C, ∀ x, |f x - f 0| ≤ C * |x|) →
      ∃ C > 0, ∃ T₀, ∀ T ≥ T₀,
        ‖rawPairCorrelation f T / pairNormalization T -
            (((f 0 + 2 * ∫ a in (0 : ℝ)..1, a * f a) : ℝ) : ℂ)‖ ≤
          C / Real.sqrt (Real.log T) := by
  rcases hintegrated with ⟨K, hK, Tbase, hintegrated⟩
  intro f heven hf hsupp hLipschitz
  rcases hLipschitz with ⟨C, hC⟩
  have hCnonneg : 0 ≤ C := by
    have h := hC 1
    norm_num only [abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hlocalLip : ∀ x : ℝ, |x| ≤ 1 → |f x - f 0| ≤ C * |x| :=
    fun x _ => hC x
  have habsIntegral : 0 ≤ ∫ a : ℝ in 0..1, |f a| :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => abs_nonneg _)
  let A : ℝ := C / 2 + |f 0|
  let B : ℝ := integratedTestSize f C
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B, integratedTestSize]
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
    have hintegratedAtT := hintegrated f C hf hCnonneg hlocalLip T hTbase
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
        _ ≤ 2 * (K * integratedTestSize f C /
              Real.sqrt (Real.log T)) :=
          mul_le_mul_of_nonneg_left hintegratedAtT (by norm_num)
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

/-- Complete integrated assembly from the two separated analytic contracts to the exact raw
pair-correlation asymptotic. -/
theorem rawPairCorrelation_asymptotic_of_integratedSecondMomentContracts
    (hfull : IntegratedFullZeroModelSecondMoment)
    (hendpoint : IntegratedFullWindowEndpointComparison) :
    ∀ f : ℝ → ℝ,
      (∀ x, f (-x) = f x) →
      Integrable f →
      (∀ x, 1 < |x| → f x = 0) →
      (∃ C, ∀ x, |f x - f 0| ≤ C * |x|) →
      ∃ C > 0, ∃ T₀, ∀ T ≥ T₀,
        ‖rawPairCorrelation f T / pairNormalization T -
            (((f 0 + 2 * ∫ a in (0 : ℝ)..1, a * f a) : ℝ) : ℂ)‖ ≤
          C / Real.sqrt (Real.log T) :=
  rawPairCorrelation_asymptotic_of_integratedFinitePairFunctionEstimate
    (integratedFinitePairFunctionEstimate_of_secondMomentContracts hfull hendpoint)

end ZetaZeros.Unconditional.PairCorrelationProof
