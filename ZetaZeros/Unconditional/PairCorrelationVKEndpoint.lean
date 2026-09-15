/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationAssembly

/-!
# The Vinogradov--Korobov input at the pair-correlation endpoint

The interior-support argument in the unconditional blueprint does not cover the endpoint
`x = T`.  The missing input is the direct comparison, uniform for `1 ≤ x ≤ T`, between
the second moment of the finite zero window and that of the full zero model.  In the
notation of Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh, their explicit-formula
argument first gives a Vinogradov--Korobov remainder, and then absorbs that remainder to
obtain an `O(T + x)` comparison.

This file formalizes the elementary absorption and the transfer of that comparison into
`FullWindowEndpointComparison`.  It deliberately does **not** assert that the analytic
BGST comparison has been formalized: `BGSTVinogradovKorobovMomentComparison` is an
explicit proposition accepted only as a hypothesis by the reduction theorem below.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex Filter MeasureTheory Set

/-- A coarse upper model for the exponentially decaying error produced by a
Vinogradov--Korobov zero-free region.  The exponent `1 / 4` is a convenient weakening of
the usual VK rate; it is still strong enough to absorb every fixed logarithmic power. -/
def vinogradovKorobovRemainder (c T : ℝ) : ℝ :=
  T * ((Real.log T) ^ (3 : ℝ) /
      Real.exp (c * (Real.log T) ^ (1 / 4 : ℝ))) +
    (Real.log T) ^ (3 : ℝ)

/-- The coarse VK remainder is at most `T` once `T` is sufficiently large. -/
theorem vinogradovKorobovRemainder_le_id (c : ℝ) (hc : 0 < c) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, vinogradovKorobovRemainder c T ≤ T := by
  have hscale : Tendsto (fun T : ℝ => (Real.log T) ^ (1 / 4 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      Real.tendsto_log_atTop
  have hdecay :=
    (isLittleO_rpow_exp_pos_mul_atTop (12 : ℝ) hc).comp_tendsto hscale
  have hdecayBound := hdecay.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog := isLittleO_log_rpow_rpow_atTop (3 : ℝ)
    (by norm_num : (0 : ℝ) < 1)
  have hlogBound := hlog.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have heventually : ∀ᶠ T : ℝ in atTop,
      vinogradovKorobovRemainder c T ≤ T := by
    filter_upwards [hdecayBound, hlogBound,
      eventually_ge_atTop (Real.exp 1)] with T hdecayT hlogT hT
    have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
    have hTone : (1 : ℝ) ≤ T :=
      (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hT
    have hlognonneg : 0 ≤ Real.log T := Real.log_nonneg hTone
    have hlogpow : 0 ≤ (Real.log T) ^ (3 : ℝ) :=
      Real.rpow_nonneg hlognonneg _
    have hpow :
        ((Real.log T) ^ (1 / 4 : ℝ)) ^ (12 : ℝ) =
          (Real.log T) ^ (3 : ℝ) := by
      rw [← Real.rpow_mul hlognonneg]
      norm_num
    simp only [Function.comp_apply] at hdecayT
    rw [hpow, Real.norm_eq_abs, abs_of_nonneg hlogpow,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hdecayT
    have hratio :
        (Real.log T) ^ (3 : ℝ) /
            Real.exp (c * (Real.log T) ^ (1 / 4 : ℝ)) ≤ 1 / 2 := by
      exact (div_le_iff₀ (Real.exp_pos _)).2 hdecayT
    rw [Real.norm_eq_abs, abs_of_nonneg hlogpow, Real.rpow_one,
      Real.norm_eq_abs, abs_of_pos hTpos] at hlogT
    unfold vinogradovKorobovRemainder
    calc
      T * ((Real.log T) ^ (3 : ℝ) /
            Real.exp (c * (Real.log T) ^ (1 / 4 : ℝ))) +
          (Real.log T) ^ (3 : ℝ) ≤
          T * (1 / 2) + (1 / 2) * T :=
        add_le_add (mul_le_mul_of_nonneg_left hratio hTpos.le) hlogT
      _ = T := by ring
  exact Filter.eventually_atTop.1 heventually

/-- The precise analytic input supplied by the BGST explicit-formula argument at the
closed endpoint.  It is recorded as a proposition, not proved in this file.

The point of retaining the VK remainder here, rather than postulating the already
absorbed result, is to expose exactly where a genuine principal-zeta VK zero-free theorem
or an equivalent integrated endpoint theorem must enter the formalization. -/
def BGSTVinogradovKorobovMomentComparison : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ,
    ∀ T ≥ T₀, ∀ x : ℝ, 1 ≤ x → x ≤ T →
      ‖finiteWindowSecondMoment x T -
          windowedFullZeroSecondMoment x T‖ ≤
        C * (vinogradovKorobovRemainder c T + x)

/-- The post-absorption form of the endpoint moment comparison. -/
def BGSTFullWindowMomentComparison : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ x : ℝ, 1 ≤ x → x ≤ T →
    ‖finiteWindowSecondMoment x T - windowedFullZeroSecondMoment x T‖ ≤
      C * (T + x)

/-- Absorb the explicit VK remainder into the `O(T + x)` endpoint comparison. -/
theorem bgstFullWindowMomentComparison_of_vinogradovKorobov
    (hBGST : BGSTVinogradovKorobovMomentComparison) :
    BGSTFullWindowMomentComparison := by
  rcases hBGST with ⟨c, hc, C, hC, T₀, hBGST⟩
  rcases vinogradovKorobovRemainder_le_id c hc with ⟨T₁, hrem⟩
  refine ⟨C, hC, max T₀ T₁, ?_⟩
  intro T hT x hxone hxT
  have hT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT₁ : T₁ ≤ T := le_trans (le_max_right _ _) hT
  calc
    ‖finiteWindowSecondMoment x T - windowedFullZeroSecondMoment x T‖ ≤
        C * (vinogradovKorobovRemainder c T + x) :=
      hBGST T hT₀ x hxone hxT
    _ ≤ C * (T + x) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact add_le_add (hrem T hT₁) le_rfl

/-- A uniform `O(T + x)` comparison yields the quantitative endpoint contract used by
the unconditional pair-correlation assembly. -/
theorem fullWindowEndpointComparison_of_bgstFullWindowMomentComparison
    (hBGST : BGSTFullWindowMomentComparison) :
    FullWindowEndpointComparison := by
  rcases hBGST with ⟨C, hC, T₀, hBGST⟩
  refine ⟨2 * C, mul_pos (by norm_num) hC, max T₀ (Real.exp 1), ?_⟩
  intro T hT a ha0 ha1
  have hT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hexpT : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTone : 1 ≤ T := by
    exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hexpT
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hlogone : 1 ≤ Real.log T :=
    (Real.le_log_iff_exp_le hTpos).2 hexpT
  have hlogpos : 0 < Real.log T := zero_lt_one.trans_le hlogone
  have hsqrtone : 1 ≤ Real.sqrt (Real.log T) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ Real.log T by positivity),
      Real.sqrt_nonneg (Real.log T)]
  have hxa : 1 ≤ T ^ a := Real.one_le_rpow hTone ha0
  have hxaT : T ^ a ≤ T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hTone ha1
  have hnorm :
      2 * Real.pi * ‖pairNormalization T‖ = T * Real.log T := by
    rw [pairNormalization, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos]
    · field_simp
    · positivity
  have hraw := hBGST T hT₀ (T ^ a) hxa hxaT
  calc
    ‖finiteWindowSecondMoment (T ^ a) T -
        windowedFullZeroSecondMoment (T ^ a) T‖ ≤ C * (T + T ^ a) := hraw
    _ ≤ C * (2 * T) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      linarith
    _ ≤ T * Real.log T * ((2 * C) *
          (1 / Real.sqrt (Real.log T))) := by
      rw [show T * Real.log T * ((2 * C) *
          (1 / Real.sqrt (Real.log T))) =
          C * (2 * T) * Real.sqrt (Real.log T) by
            field_simp
            nlinarith [Real.sq_sqrt hlogpos.le]]
      exact le_mul_of_one_le_right (by positivity) hsqrtone
    _ ≤ T * Real.log T * ((2 * C) *
          (T ^ (-2 * a) + 1 / Real.sqrt (Real.log T))) := by
      gcongr
      linarith [Real.rpow_nonneg hTpos.le (-2 * a)]
    _ = 2 * Real.pi * ‖pairNormalization T‖ *
          ((2 * C) *
            (T ^ (-2 * a) + 1 / Real.sqrt (Real.log T))) := by rw [hnorm]

/-- Conditional composition of the analytic BGST input with the two kernel-checked
reductions in this file. -/
theorem fullWindowEndpointComparison_of_bgstVinogradovKorobovMomentComparison
    (hBGST : BGSTVinogradovKorobovMomentComparison) :
    FullWindowEndpointComparison :=
  fullWindowEndpointComparison_of_bgstFullWindowMomentComparison
    (bgstFullWindowMomentComparison_of_vinogradovKorobov hBGST)

end ZetaZeros.Unconditional.PairCorrelationProof
