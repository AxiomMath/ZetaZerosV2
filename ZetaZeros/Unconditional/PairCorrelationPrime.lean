/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationPNT
import Zeta23.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The prime diagonal in pair correlation

This file isolates the arithmetic input in the BGST pair-correlation calculation.  The
coefficient `pairDirichletCoefficient n` is `Λ(n)² / n`, and `pairPrimeMeanSquare x` is
its multiplicatively smoothed mean square with kernel `min(n / x, x / n)²`.
-/

namespace ZetaZeros.Unconditional

open Filter Finset MeasureTheory
open scoped BigOperators Chebyshev Topology

/-- The Dirichlet coefficient on the diagonal of Montgomery's prime polynomial. -/
noncomputable def pairDirichletCoefficient (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n ^ 2 / n

/-- The cumulative diagonal coefficient up to the real cutoff `x`. -/
noncomputable def pairCoefficientSum (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, pairDirichletCoefficient n

/-- The multiplicative tent kernel occurring in the prime diagonal. -/
noncomputable def pairPrimeKernel (x : ℝ) (n : ℕ) : ℝ :=
  min ((n : ℝ) / x) (x / n) ^ 2

/-- The smoothed prime mean square
`∑ n, (Λ(n)² / n) min(n / x, x / n)²`. -/
noncomputable def pairPrimeMeanSquare (x : ℝ) : ℝ :=
  ∑' n : ℕ, pairDirichletCoefficient n * pairPrimeKernel x n

/-- The coefficient-weighted tent-kernel sum which controls the Hilbert error in
Montgomery's Dirichlet-polynomial mean-value theorem. -/
noncomputable def pairWeightedPrimeMeanSquare (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    ArithmeticFunction.vonMangoldt n ^ 2 * pairPrimeKernel x n

private noncomputable def pairAbelWeight (t : ℝ) : ℝ :=
  Real.log t / t

private theorem pairAbelWeight_hasDerivAt {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt pairAbelWeight ((1 - Real.log t) / t ^ 2) t := by
  unfold pairAbelWeight
  have hid : HasDerivAt (fun u : ℝ ↦ u) 1 t := hasDerivAt_id t
  convert (Real.hasDerivAt_log ht).div hid ht using 1
  all_goals try rfl
  · rw [inv_mul_cancel₀ ht, mul_one]

private theorem pairAbelWeight_deriv {t : ℝ} (ht : t ≠ 0) :
    deriv pairAbelWeight t = (1 - Real.log t) / t ^ 2 :=
  (pairAbelWeight_hasDerivAt ht).deriv

private theorem pairAbelSummation {x : ℝ} (_hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * Real.log n / n =
      pairAbelWeight x * Chebyshev.psi x -
        ∫ t in Set.Ioc 1 x, ((1 - Real.log t) / t ^ 2) * Chebyshev.psi t := by
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ pairAbelWeight t := by
    intro t ht
    exact (pairAbelWeight_hasDerivAt (by nlinarith [ht.1])).differentiableAt
  have hint : IntegrableOn (deriv pairAbelWeight) (Set.Icc (1 : ℝ) x) := by
    have hcont : ContinuousOn (fun t : ℝ ↦ (1 - Real.log t) / t ^ 2) (Set.Icc 1 x) := by
      intro t ht
      have ht0 : t ≠ 0 := by nlinarith [ht.1]
      exact ((continuousAt_const.sub (Real.continuousAt_log ht0)).div
        (continuousAt_id.pow 2) (pow_ne_zero 2 ht0)).continuousWithinAt
    refine (hcont.integrableOn_Icc).congr_fun ?_ measurableSet_Icc
    intro t ht
    rw [pairAbelWeight_deriv (by nlinarith [ht.1])]
  have habel := sum_mul_eq_sub_integral_mul₀
    (fun n ↦ ArithmeticFunction.vonMangoldt n) (by simp) x hdiff hint
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at habel
  calc
    ∑ n ∈ Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * Real.log n / n =
        ∑ n ∈ Icc 0 ⌊x⌋₊, pairAbelWeight n * ArithmeticFunction.vonMangoldt n := by
      rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊x⌋₊), Finset.sum_cons]
      · simp only [CharP.cast_eq_zero, ArithmeticFunction.map_zero, mul_zero, zero_add]
        apply Finset.sum_congr rfl
        intro n hn
        rw [pairAbelWeight]
        ring
    _ = pairAbelWeight x * Chebyshev.psi x -
        ∫ t in Set.Ioc 1 x, deriv pairAbelWeight t * Chebyshev.psi t := habel
    _ = pairAbelWeight x * Chebyshev.psi x -
        ∫ t in Set.Ioc 1 x, ((1 - Real.log t) / t ^ 2) * Chebyshev.psi t := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
      rw [pairAbelWeight_deriv (by nlinarith [ht.1])]

private theorem integral_inv_mul_log_pair {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t = Real.log x ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hx]
  have hftc : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (fun u : ℝ ↦ Real.log u ^ 2 / 2) (t⁻¹ * Real.log t) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by nlinarith [ht.1]
    have h := ((Real.hasDerivAt_log ht0).pow 2).div_const 2
    have heq :
        t⁻¹ * Real.log t =
          ((2 : ℕ) : ℝ) * Real.log t ^ (2 - 1) * t⁻¹ / 2 := by
      push_cast
      ring
    rw [heq]
    exact h
  have hint : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ * Real.log t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.mono fun t ht ↦ by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
    · exact fun t ht ↦
        (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint]
  simp [Real.log_one]

private theorem pairMainIntegral {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, ((1 - Real.log t) / t ^ 2) * t =
      Real.log x - Real.log x ^ 2 / 2 := by
  have hinv : ∫ t in Set.Ioc 1 x, t⁻¹ = Real.log x := by
    rw [← intervalIntegral.integral_of_le hx, integral_inv]
    · simp
    · rw [Set.uIcc_of_le hx]
      intro h
      nlinarith [h.1]
  rw [← integral_inv_mul_log_pair hx, ← hinv, ← MeasureTheory.integral_sub]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : t ≠ 0 := by nlinarith [ht.1]
    field_simp
  · exact (ContinuousOn.integrableOn_Icc
      (continuousOn_inv₀.mono fun t ht ↦ by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1])).mono_set Set.Ioc_subset_Icc_self
  · exact (ContinuousOn.integrableOn_Icc
      (ContinuousOn.mul
        (continuousOn_inv₀.mono fun t ht ↦ by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          nlinarith [ht.1])
        (fun t ht ↦
          (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt))).mono_set
      Set.Ioc_subset_Icc_self

private noncomputable def pairPNTError (x : ℝ) : ℝ :=
  Chebyshev.psi x - x

private noncomputable def pairPNTIntegrand (x : ℝ) : ℝ :=
  ((1 - Real.log x) / x ^ 2) * pairPNTError x

private theorem pairPNTError_isBigO :
    ∃ c > 0,
      pairPNTError =O[atTop]
        fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  rcases pairCorrelation_mediumPNT with ⟨c, hc, hPNT⟩
  refine ⟨c, hc, ?_⟩
  convert hPNT using 1
  funext x
  rfl

private theorem pairPNTLogMajorant_integrable {c : ℝ} (hc : 0 < c) :
    IntegrableOn
      (fun u : ℝ ↦ (1 - u) * Real.exp (-c * u ^ ((1 : ℝ) / 10)))
      (Set.Ioi 0) := by
  have hzero := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (0 : ℝ)) (p := (1 : ℝ) / 10) (b := c) (by norm_num) (by norm_num) hc
  have hone := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (1 : ℝ)) (p := (1 : ℝ) / 10) (b := c) (by norm_num) (by norm_num) hc
  refine (hzero.sub hone).congr_fun ?_ measurableSet_Ioi
  intro u hu
  simp only [Pi.sub_apply, Real.rpow_zero, Real.rpow_one]
  ring

private theorem pairPNTMajorant_integrable {c : ℝ} (hc : 0 < c) :
    IntegrableOn
      (fun x : ℝ ↦ x⁻¹ *
        ((1 - Real.log x) *
          Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))))
      (Set.Ioi 1) := by
  apply (integrableOn_comp_log_Ioi
    (fun u : ℝ ↦ (1 - u) * Real.exp (-c * u ^ ((1 : ℝ) / 10))) one_pos).2
  simpa only [Real.log_one] using pairPNTLogMajorant_integrable hc

private theorem pairPNTIntegrand_integrable {c : ℝ} (hc : 0 < c)
    (hPNT : pairPNTError =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :
    IntegrableOn pairPNTIntegrand (Set.Ici 1) := by
  have herrorLocallyIntegrable : LocallyIntegrable pairPNTError := by
    exact Chebyshev.psi_mono.locallyIntegrable.sub continuous_id.locallyIntegrable
  have hkernelContinuous : ContinuousOn
      (fun x : ℝ ↦ (1 - Real.log x) / x ^ 2) (Set.Ici 1) := by
    intro x hx
    have hx1 : 1 ≤ x := hx
    have hx0 : x ≠ 0 := by nlinarith
    exact ((continuousAt_const.sub (Real.continuousAt_log hx0)).div
      (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).continuousWithinAt
  have hlocallyIntegrable : LocallyIntegrableOn pairPNTIntegrand (Set.Ici 1) := by
    change LocallyIntegrableOn
      (fun x : ℝ ↦ ((1 - Real.log x) / x ^ 2) * pairPNTError x) (Set.Ici 1)
    exact (herrorLocallyIntegrable.locallyIntegrableOn (Set.Ici 1)).continuousOn_mul
      hkernelContinuous isLocallyClosed_Ici
  have hOraw : pairPNTIntegrand =O[atTop]
      fun x : ℝ ↦ ((1 - Real.log x) / x ^ 2) *
        (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
    refine ((Asymptotics.isBigO_refl
      (fun x : ℝ ↦ (1 - Real.log x) / x ^ 2) atTop).mul hPNT).congr' ?_ ?_
    · exact Eventually.of_forall fun _ ↦ rfl
    · exact Eventually.of_forall fun _ ↦ rfl
  have hO : pairPNTIntegrand =O[atTop]
      fun x : ℝ ↦ x⁻¹ *
        ((1 - Real.log x) *
          Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
    refine hOraw.congr' (Eventually.of_forall fun _ ↦ rfl) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hmajorantAtTop : IntegrableAtFilter
      (fun x : ℝ ↦ x⁻¹ *
        ((1 - Real.log x) *
          Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))) atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp
      (pairPNTMajorant_integrable hc)).1
  exact hlocallyIntegrable.integrableOn_of_isBigO_atTop hO hmajorantAtTop

private theorem pairPNTBoundary_tendsto_zero {c : ℝ} (hc : 0 < c)
    (hPNT : pairPNTError =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :
    Tendsto (fun x : ℝ ↦ pairAbelWeight x * pairPNTError x) atTop (𝓝 0) := by
  have hinner : Tendsto
      (fun x : ℝ ↦ (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)).comp
      Real.tendsto_log_atTop
  have hdecayRaw :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 : ℝ) c hc).comp hinner
  have hdecay : Tendsto
      (fun x : ℝ ↦ Real.log x *
        Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) atTop (𝓝 0) := by
    refine hdecayRaw.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [show (1 : ℝ) / 10 = ((10 : ℝ)⁻¹) by norm_num]
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul (Real.log_nonneg hx)]
    norm_num
  have hOraw : (fun x : ℝ ↦ pairAbelWeight x * pairPNTError x) =O[atTop]
      fun x : ℝ ↦ pairAbelWeight x *
        (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
    exact ((Asymptotics.isBigO_refl pairAbelWeight atTop).mul hPNT).congr'
      (Eventually.of_forall fun _ ↦ rfl) (Eventually.of_forall fun _ ↦ rfl)
  have hO : (fun x : ℝ ↦ pairAbelWeight x * pairPNTError x) =O[atTop]
      fun x : ℝ ↦ Real.log x *
        Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
    refine hOraw.congr' (Eventually.of_forall fun _ ↦ rfl) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [pairAbelWeight]
    field_simp
  exact hO.trans_tendsto hdecay

private theorem pairLogWeighted_error_identity
    (herror : IntegrableOn pairPNTIntegrand (Set.Ici 1)) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n * Real.log n / n) - Real.log x ^ 2 / 2 =
      pairAbelWeight x * pairPNTError x -
        ∫ t in Set.Ioc 1 x, pairPNTIntegrand t := by
  have hx0 : x ≠ 0 := by nlinarith
  have hmain : IntegrableOn
      (fun t : ℝ ↦ ((1 - Real.log t) / t ^ 2) * t) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro t ht
    have ht0 : t ≠ 0 := by nlinarith [ht.1]
    exact (((continuousAt_const.sub (Real.continuousAt_log ht0)).div
      (continuousAt_id.pow 2) (pow_ne_zero 2 ht0)).mul continuousAt_id).continuousWithinAt
  have herr : IntegrableOn pairPNTIntegrand (Set.Ioc 1 x) :=
    herror.mono_set fun t ht ↦ le_of_lt ht.1
  have hsplit :
      (∫ t in Set.Ioc 1 x, ((1 - Real.log t) / t ^ 2) * Chebyshev.psi t) =
        (∫ t in Set.Ioc 1 x, ((1 - Real.log t) / t ^ 2) * t) +
          ∫ t in Set.Ioc 1 x, pairPNTIntegrand t := by
    rw [← MeasureTheory.integral_add hmain herr]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    rw [pairPNTIntegrand, pairPNTError]
    ring
  rw [pairAbelSummation hx, hsplit, pairMainIntegral hx]
  rw [show Chebyshev.psi x = x + pairPNTError x by
    rw [pairPNTError]
    ring]
  rw [pairAbelWeight]
  field_simp
  ring

private theorem pairLogWeighted_bounded :
    ∃ C > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀,
      |(∑ n ∈ Ioc 0 ⌊x⌋₊,
          ArithmeticFunction.vonMangoldt n * Real.log n / n) -
        Real.log x ^ 2 / 2| ≤ C := by
  rcases pairPNTError_isBigO with ⟨c, hc, hPNT⟩
  have herror := pairPNTIntegrand_integrable hc hPNT
  have hboundary := pairPNTBoundary_tendsto_zero hc hPNT
  have hboundaryEventually : ∀ᶠ x : ℝ in atTop,
      |pairAbelWeight x * pairPNTError x| < 1 := by
    filter_upwards [hboundary.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)]
      with x hx
    simpa only [Real.dist_eq, sub_zero] using hx
  rcases (eventually_atTop.1 hboundaryEventually) with ⟨x₁, hx₁⟩
  let M : ℝ := ∫ t in Set.Ici 1, |pairPNTIntegrand t|
  have hM : 0 ≤ M := by
    exact integral_nonneg_of_ae (Eventually.of_forall fun _ ↦ abs_nonneg _)
  refine ⟨M + 1, by positivity, max 1 x₁, ?_⟩
  intro x hx
  have hxone : 1 ≤ x := le_trans (le_max_left 1 x₁) hx
  have hxx₁ : x₁ ≤ x := le_trans (le_max_right 1 x₁) hx
  have hboundaryOne : |pairAbelWeight x * pairPNTError x| ≤ 1 :=
    le_of_lt (hx₁ x hxx₁)
  have hnormIntegral :
      |∫ t in Set.Ioc 1 x, pairPNTIntegrand t| ≤ M := by
    calc
      |∫ t in Set.Ioc 1 x, pairPNTIntegrand t| =
          ‖∫ t in Set.Ioc 1 x, pairPNTIntegrand t‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ t in Set.Ioc 1 x, ‖pairPNTIntegrand t‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ t in Set.Ioc 1 x, |pairPNTIntegrand t| := by
        simp only [Real.norm_eq_abs]
      _ ≤ ∫ t in Set.Ici 1, |pairPNTIntegrand t| := by
        apply setIntegral_mono_set herror.abs
        · exact Eventually.of_forall fun _ ↦ abs_nonneg _
        · exact Eventually.of_forall fun t ht ↦ le_of_lt ht.1
      _ = M := rfl
  rw [pairLogWeighted_error_identity herror hxone]
  calc
    |pairAbelWeight x * pairPNTError x -
        ∫ t in Set.Ioc 1 x, pairPNTIntegrand t| ≤
        |pairAbelWeight x * pairPNTError x| +
          |∫ t in Set.Ioc 1 x, pairPNTIntegrand t| := abs_sub _ _
    _ ≤ 1 + M := add_le_add hboundaryOne hnormIntegral
    _ = M + 1 := add_comm 1 M

/-- The cumulative diagonal coefficient has the Mertens asymptotic
`∑_{n ≤ x} Λ(n)² / n = ½ log² x + O(1)`. -/
theorem pairCoefficientSum_bounded :
    ∃ C > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀,
      |pairCoefficientSum x - Real.log x ^ 2 / 2| ≤ C := by
  rcases pairLogWeighted_bounded with ⟨C, hC, x₀, hweighted⟩
  refine ⟨C + 1537, by positivity, x₀, ?_⟩
  intro x hx
  let D : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊,
    ArithmeticFunction.vonMangoldt n *
      (Real.log n - ArithmeticFunction.vonMangoldt n) / n
  have hD0 : 0 ≤ D := by
    exact Finset.sum_nonneg fun n _ ↦
      div_nonneg
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (sub_nonneg.mpr ArithmeticFunction.vonMangoldt_le_log))
        (Nat.cast_nonneg n)
  have hDle : D ≤ 1537 := Zeta23.Cheb.defect_bounded_explicit x
  have hdiff :
      (∑ n ∈ Ioc 0 ⌊x⌋₊,
          ArithmeticFunction.vonMangoldt n * Real.log n / n) -
        pairCoefficientSum x = D := by
    rw [pairCoefficientSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ by
      rw [pairDirichletCoefficient]
      ring
  have hrearrange :
      pairCoefficientSum x - Real.log x ^ 2 / 2 =
        ((∑ n ∈ Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt n * Real.log n / n) -
          Real.log x ^ 2 / 2) - D := by
    linarith
  rw [hrearrange]
  calc
    |((∑ n ∈ Ioc 0 ⌊x⌋₊,
          ArithmeticFunction.vonMangoldt n * Real.log n / n) -
        Real.log x ^ 2 / 2) - D| ≤
        |(∑ n ∈ Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt n * Real.log n / n) -
          Real.log x ^ 2 / 2| + |D| := abs_sub _ _
    _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt n * Real.log n / n) -
          Real.log x ^ 2 / 2| + D := by rw [abs_of_nonneg hD0]
    _ ≤ C + 1537 := add_le_add (hweighted x hx) hDle

/-- A version of `pairCoefficientSum_bounded` uniform down to the endpoint `x = 1`. -/
theorem pairCoefficientSum_bounded_global :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      |pairCoefficientSum x - Real.log x ^ 2 / 2| ≤ C := by
  rcases pairCoefficientSum_bounded with ⟨C, hC, x₀, hbound⟩
  let B : ℝ := max 2 x₀
  let K : ℝ := 2 * (Real.log 4 + 4) + 1537 / Real.log 2
  have hBtwo : 2 ≤ B := le_max_left 2 x₀
  have hBone : 1 ≤ B := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hBone
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨C + K * Real.log B + Real.log B ^ 2 / 2 + 1,
    by nlinarith [mul_nonneg hK hlogB, sq_nonneg (Real.log B)], ?_⟩
  intro x hxone
  by_cases hxx₀ : x₀ ≤ x
  · exact (hbound x hxx₀).trans (by
      nlinarith [mul_nonneg hK hlogB, sq_nonneg (Real.log B)])
  by_cases hxtwo : 2 ≤ x
  · have hxB : x ≤ B := le_trans (le_of_not_ge hxx₀) (le_max_right 2 x₀)
    have hlog : Real.log x ≤ Real.log B := Real.log_le_log (by positivity) hxB
    have hexplicit :
        |pairCoefficientSum x - Real.log x ^ 2 / 2| ≤ K * Real.log x := by
      simpa only [pairCoefficientSum, pairDirichletCoefficient, K] using
        Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit x hxtwo
    exact hexplicit.trans <| (mul_le_mul_of_nonneg_left hlog hK).trans (by
      nlinarith [sq_nonneg (Real.log B)])
  · have hxlt : x < 2 := lt_of_not_ge hxtwo
    have hfloor : ⌊x⌋₊ = 1 :=
      Nat.floor_eq_on_Ico 1 x ⟨by exact_mod_cast hxone, by norm_num; exact hxlt⟩
    have hsumzero : pairCoefficientSum x = 0 := by
      simp [pairCoefficientSum, hfloor, pairDirichletCoefficient]
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hxone
    have hxB : x ≤ B := by linarith
    have hlog : Real.log x ≤ Real.log B := Real.log_le_log (by positivity) hxB
    have hneg : (0 : ℝ) - Real.log x ^ 2 / 2 ≤ 0 := by
      nlinarith [sq_nonneg (Real.log x)]
    rw [hsumzero, abs_of_nonpos hneg]
    nlinarith [sq_nonneg (Real.log B - Real.log x)]

private theorem pairDirichletCoefficient_zero : pairDirichletCoefficient 0 = 0 := by
  simp [pairDirichletCoefficient]

private theorem pairDirichletCoefficient_nonneg (n : ℕ) :
    0 ≤ pairDirichletCoefficient n := by
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)

private theorem pairCoefficientSum_eq_Icc (x : ℝ) :
    pairCoefficientSum x = ∑ n ∈ Icc 0 ⌊x⌋₊, pairDirichletCoefficient n := by
  rw [pairCoefficientSum, Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊x⌋₊), Finset.sum_cons]
  · rw [pairDirichletCoefficient_zero, zero_add]

private theorem pairCoefficientSum_nonneg (x : ℝ) : 0 ≤ pairCoefficientSum x := by
  rw [pairCoefficientSum]
  exact Finset.sum_nonneg fun n _ ↦ pairDirichletCoefficient_nonneg n

private theorem pairCoefficientSum_monotone : Monotone pairCoefficientSum := by
  intro x y hxy
  rw [pairCoefficientSum, pairCoefficientSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor hxy)
  · intro n _ _
    exact pairDirichletCoefficient_nonneg n

private noncomputable def pairLowWeight (x t : ℝ) : ℝ :=
  t ^ 2 / x ^ 2

private noncomputable def pairHighWeight (x t : ℝ) : ℝ :=
  x ^ 2 / t ^ 2

private theorem pairLowWeight_hasDerivAt {x t : ℝ} :
    HasDerivAt (pairLowWeight x) (2 * t / x ^ 2) t := by
  unfold pairLowWeight
  have hid : HasDerivAt (fun u : ℝ ↦ u) 1 t := hasDerivAt_id t
  convert (hid.pow 2).div_const (x ^ 2) using 1
  all_goals try rfl
  norm_num

private theorem pairLowWeight_deriv {x t : ℝ} :
    deriv (pairLowWeight x) t = 2 * t / x ^ 2 :=
  pairLowWeight_hasDerivAt.deriv

private theorem pairHighWeight_hasDerivAt {x t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (pairHighWeight x) (-2 * x ^ 2 / t ^ 3) t := by
  unfold pairHighWeight
  have hc : HasDerivAt (fun _ : ℝ ↦ x ^ 2) 0 t := hasDerivAt_const t (x ^ 2)
  have hid : HasDerivAt (fun u : ℝ ↦ u) 1 t := hasDerivAt_id t
  convert hc.div (hid.pow 2) (pow_ne_zero 2 ht) using 1
  all_goals try rfl
  norm_num
  field_simp

private theorem pairHighWeight_deriv {x t : ℝ} (ht : t ≠ 0) :
    deriv (pairHighWeight x) t = -2 * x ^ 2 / t ^ 3 :=
  (pairHighWeight_hasDerivAt ht).deriv

private theorem pairCoefficientSum_locallyIntegrable :
    LocallyIntegrable pairCoefficientSum :=
  pairCoefficientSum_monotone.locallyIntegrable

private theorem pairCoefficientSum_le_chebyshev {x : ℝ} (hx : 1 ≤ x) :
    pairCoefficientSum x ≤ (Real.log 4 + 4) * x * Real.log x := by
  rw [pairCoefficientSum]
  calc
    ∑ n ∈ Ioc 0 ⌊x⌋₊, pairDirichletCoefficient n ≤
        ∑ n ∈ Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n ^ 2 := by
      refine Finset.sum_le_sum fun n hn ↦ ?_
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1))
      rw [pairDirichletCoefficient]
      have hsq : 0 ≤ ArithmeticFunction.vonMangoldt n ^ 2 := sq_nonneg _
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < n)).2 (by nlinarith)
    _ ≤ (Real.log 4 + 4) * x * Real.log x :=
      Zeta23.Cheb.sum_vonMangoldt_sq_le hx

private theorem pairLogDivSq_integrable :
    IntegrableOn (fun t : ℝ ↦ Real.log t / t ^ 2) (Set.Ioi 1) := by
  have hexp : IntegrableOn (fun u : ℝ ↦ u * Real.exp (-u)) (Set.Ioi 0) := by
    simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (1 : ℝ)) (p := (1 : ℝ)) (b := (1 : ℝ)) (by norm_num) (by norm_num)
          (by norm_num))
  have hcomp : IntegrableOn
      (fun t : ℝ ↦ t⁻¹ * (Real.log t * Real.exp (-Real.log t))) (Set.Ioi 1) := by
    exact (integrableOn_comp_log_Ioi (fun u : ℝ ↦ u * Real.exp (-u)) one_pos).2
      (by simpa only [Real.log_one] using hexp)
  refine hcomp.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  change t⁻¹ * (Real.log t * Real.exp (-Real.log t)) = Real.log t / t ^ 2
  rw [Real.exp_neg, Real.exp_log ht0]
  field_simp

private theorem pairHighBoundary_tendsto_zero {x : ℝ} (hx : 1 ≤ x) :
    Tendsto
      (fun n : ℕ ↦ pairHighWeight x n *
        ∑ k ∈ Icc 0 n, pairDirichletCoefficient k)
      atTop (𝓝 0) := by
  let K : ℝ := Real.log 4 + 4
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hmajor : Tendsto
      (fun n : ℕ ↦ K * x ^ 2 * (Real.log (n : ℝ) / n)) atTop (𝓝 0) := by
    have hlog : Tendsto
        (fun t : ℝ ↦ Real.log t / t) atTop (𝓝 0) := by
      simpa only [pow_one, one_mul, add_zero] using
        Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hlogNat : Tendsto
        (fun n : ℕ ↦ Real.log (n : ℝ) / n) atTop (𝓝 0) :=
      hlog.comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using (tendsto_const_nhds.mul hlogNat)
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact mul_nonneg (by
      exact div_nonneg (sq_nonneg x) (sq_nonneg (n : ℝ)))
      (Finset.sum_nonneg fun k _ ↦ pairDirichletCoefficient_nonneg k)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
    have hsum :
        (∑ k ∈ Icc 0 n, pairDirichletCoefficient k) =
          pairCoefficientSum (n : ℝ) := by
      rw [pairCoefficientSum_eq_Icc]
      norm_num
    rw [hsum]
    have hA := pairCoefficientSum_le_chebyshev hnR
    rw [pairHighWeight]
    have hweight : 0 ≤ x ^ 2 / (n : ℝ) ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    calc
      x ^ 2 / (n : ℝ) ^ 2 * pairCoefficientSum (n : ℝ) ≤
          x ^ 2 / (n : ℝ) ^ 2 * (K * n * Real.log n) :=
        mul_le_mul_of_nonneg_left (by simpa only [K] using hA) hweight
      _ = K * x ^ 2 * (Real.log (n : ℝ) / n) := by
        field_simp

private theorem pairHighAbelLimit {x : ℝ} (hx : 1 ≤ x) :
    Tendsto
      (fun n : ℕ ↦ ∑ k ∈ Icc 0 n,
        pairHighWeight x k * pairDirichletCoefficient k)
      atTop
      (𝓝 (∫ t in Set.Ioi 1,
        (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t)) := by
  have hdiff : ∀ t ∈ Set.Ici (1 : ℝ),
      DifferentiableAt ℝ (pairHighWeight x) t := by
    intro t ht
    exact (pairHighWeight_hasDerivAt
      (by nlinarith [show (1 : ℝ) ≤ t from ht])).differentiableAt
  have hcont : ContinuousOn
      (fun t : ℝ ↦ -2 * x ^ 2 / t ^ 3) (Set.Ici 1) := by
    intro t ht
    have ht0 : t ≠ 0 := by nlinarith [show (1 : ℝ) ≤ t from ht]
    exact continuousAt_const.div (continuousAt_id.pow 3)
      (pow_ne_zero 3 ht0) |>.continuousWithinAt
  have hlocal : LocallyIntegrableOn (deriv (pairHighWeight x)) (Set.Ici 1) := by
    apply (hcont.locallyIntegrableOn measurableSet_Ici).congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [pairHighWeight_deriv
      (by nlinarith [show (1 : ℝ) ≤ t from ht])]
  let K : ℝ := Real.log 4 + 4
  let g : ℝ → ℝ := fun t ↦ 2 * x ^ 2 * K * (Real.log t / t ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hgOn : IntegrableOn g (Set.Ioi 1) := by
    exact pairLogDivSq_integrable.const_mul (2 * x ^ 2 * K)
  have hg : IntegrableAtFilter g atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp hgOn).1
  have hO :
      (fun t : ℝ ↦ deriv (pairHighWeight x) t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, pairDirichletCoefficient k) =O[atTop] g := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hA0 := pairCoefficientSum_nonneg t
    have hA := pairCoefficientSum_le_chebyshev ht
    have hfactor : 0 ≤ 2 * x ^ 2 / t ^ 3 := by positivity
    have hneg : -2 * x ^ 2 / t ^ 3 ≤ 0 := by
      rw [show -2 * x ^ 2 / t ^ 3 = -(2 * x ^ 2 / t ^ 3) by ring]
      exact neg_nonpos.mpr hfactor
    have hprod :
        (-2 * x ^ 2 / t ^ 3) * pairCoefficientSum t ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg hneg hA0
    have hg0 : 0 ≤ g t := by
      dsimp [g]
      exact mul_nonneg (mul_nonneg (by positivity) hK)
        (div_nonneg (Real.log_nonneg ht) (sq_nonneg t))
    rw [pairHighWeight_deriv (ne_of_gt ht0), ← pairCoefficientSum_eq_Icc]
    simp only [one_mul, Real.norm_eq_abs, abs_of_nonpos hprod, abs_of_nonneg hg0]
    calc
      -((-2 * x ^ 2 / t ^ 3) * pairCoefficientSum t) =
          (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t := by ring
      _ ≤ (2 * x ^ 2 / t ^ 3) * (K * t * Real.log t) :=
        mul_le_mul_of_nonneg_left (by simpa only [K] using hA) hfactor
      _ = g t := by
        dsimp [g]
        field_simp
  have hlim := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    pairDirichletCoefficient pairDirichletCoefficient_zero hdiff hlocal
    (l := (0 : ℝ)) (pairHighBoundary_tendsto_zero hx) (g := g) hO hg
  have hintegral :
      (0 - ∫ t in Set.Ioi 1, deriv (pairHighWeight x) t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, pairDirichletCoefficient k) =
        ∫ t in Set.Ioi 1, (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t := by
    rw [zero_sub, ← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [pairHighWeight_deriv
      (by nlinarith [show (1 : ℝ) < t from ht]), pairCoefficientSum_eq_Icc]
    ring
  rw [hintegral] at hlim
  exact hlim

private theorem pairHigh_hasSum {x : ℝ} (hx : 1 ≤ x) :
    HasSum
      (fun n : ℕ ↦ pairHighWeight x n * pairDirichletCoefficient n)
      (∫ t in Set.Ioi 1,
        (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hfin : ∀ n : ℕ, Icc 0 n = range (n + 1) := by
      intro n
      ext k
      simp only [mem_Icc, mem_range]
      omega
    have hshift : Tendsto
        (fun n : ℕ ↦ ∑ k ∈ range (n + 1),
          pairHighWeight x k * pairDirichletCoefficient k)
        atTop
        (𝓝 (∫ t in Set.Ioi 1,
          (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t)) := by
      simpa only [hfin] using pairHighAbelLimit hx
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp hshift
  · intro n
    exact mul_nonneg (by
      rw [pairHighWeight]
      positivity) (pairDirichletCoefficient_nonneg n)

private theorem pairHigh_summable {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun n : ℕ ↦
      pairHighWeight x n * pairDirichletCoefficient n) :=
  (pairHigh_hasSum hx).summable

/-! The Hilbert-error mean-value theorem needs one additional power of the
Dirichlet index.  The following cutoff Abel sum proves the resulting
`Λ(n)²`-weighted tent-kernel bound without losing a logarithm. -/

private noncomputable def pairWeightedTailCoeff (x : ℝ) (n : ℕ) : ℝ :=
  if ⌊x⌋₊ < n then ArithmeticFunction.vonMangoldt n ^ 2 else 0

private noncomputable def pairWeightedTailSum (x t : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊t⌋₊, pairWeightedTailCoeff x n

private theorem pairWeightedTailCoeff_zero (x : ℝ) :
    pairWeightedTailCoeff x 0 = 0 := by
  simp [pairWeightedTailCoeff]

private theorem pairWeightedTailCoeff_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ pairWeightedTailCoeff x n := by
  simp only [pairWeightedTailCoeff]
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

private theorem pairWeightedTailSum_nonneg (x t : ℝ) :
    0 ≤ pairWeightedTailSum x t := by
  rw [pairWeightedTailSum]
  exact Finset.sum_nonneg fun n _ ↦ pairWeightedTailCoeff_nonneg x n

private theorem pairWeightedTailSum_monotone (x : ℝ) :
    Monotone (pairWeightedTailSum x) := by
  intro s t hst
  rw [pairWeightedTailSum, pairWeightedTailSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.Icc_subset_Icc_right (Nat.floor_le_floor hst)
  · intro n _ _
    exact pairWeightedTailCoeff_nonneg x n

private theorem pairWeightedTailSum_locallyIntegrable (x : ℝ) :
    LocallyIntegrable (pairWeightedTailSum x) :=
  (pairWeightedTailSum_monotone x).locallyIntegrable

private theorem pairWeightedTailSum_le_chebyshev
    {x t : ℝ} (ht : 1 ≤ t) :
    pairWeightedTailSum x t ≤
      (Real.log 4 + 4) * t * Real.log t := by
  rw [pairWeightedTailSum]
  calc
    ∑ n ∈ Icc 0 ⌊t⌋₊, pairWeightedTailCoeff x n ≤
        ∑ n ∈ Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n ^ 2 := by
      refine Finset.sum_le_sum fun n _ ↦ ?_
      simp only [pairWeightedTailCoeff]
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _
    _ = ∑ n ∈ Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n ^ 2 := by
      rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊t⌋₊), Finset.sum_cons]
      · simp
    _ ≤ (Real.log 4 + 4) * t * Real.log t :=
      Zeta23.Cheb.sum_vonMangoldt_sq_le ht

private theorem pairWeightedTailSum_eq_zero_of_le
    {x t : ℝ} (htx : t ≤ x) :
    pairWeightedTailSum x t = 0 := by
  rw [pairWeightedTailSum]
  apply Finset.sum_eq_zero
  intro n hn
  have hnle : n ≤ ⌊t⌋₊ := (Finset.mem_Icc.mp hn).2
  have hfloor : ⌊t⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor htx
  have hnot : ¬⌊x⌋₊ < n := by omega
  simp [pairWeightedTailCoeff, hnot]

private theorem pairLogDivSq_integral {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioi x, Real.log t / t ^ 2 =
      (Real.log x + 1) / x := by
  let F : ℝ → ℝ := fun t ↦ -((Real.log t + 1) / t)
  have hderiv : ∀ t ∈ Set.Ici x,
      HasDerivAt F (Real.log t / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := by
      nlinarith [show x ≤ t from ht, hx]
    dsimp only [F]
    refine ((((Real.hasDerivAt_log ht0).add_const 1).div
      (hasDerivAt_id t) ht0).neg).congr_deriv ?_
    simp only [id_eq]
    field_simp [ht0]
    ring
  have hint : IntegrableOn (fun t : ℝ ↦ Real.log t / t ^ 2) (Set.Ioi x) :=
    pairLogDivSq_integrable.mono_set fun t ht ↦ lt_of_le_of_lt hx ht
  have hlog : Tendsto (fun t : ℝ ↦ Real.log t / t) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Tendsto (fun t : ℝ ↦ 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hF : Tendsto F atTop (𝓝 0) := by
    convert (hlog.add hinv).neg using 1
    · funext t
      dsimp only [F]
      ring
    · simp
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hF]
  dsimp only [F]
  have hx0 : x ≠ 0 := by nlinarith
  field_simp [hx0]
  ring

private theorem pairWeightedTailBoundary_tendsto_zero
    {x : ℝ} (hx : 1 ≤ x) :
    Tendsto
      (fun n : ℕ ↦ pairHighWeight x n *
        ∑ k ∈ Icc 0 n, pairWeightedTailCoeff x k)
      atTop (𝓝 0) := by
  let K : ℝ := Real.log 4 + 4
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hmajor : Tendsto
      (fun n : ℕ ↦ K * x ^ 2 * (Real.log (n : ℝ) / n)) atTop (𝓝 0) := by
    have hlog : Tendsto
        (fun t : ℝ ↦ Real.log t / t) atTop (𝓝 0) := by
      simpa only [pow_one, one_mul, add_zero] using
        Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hlogNat : Tendsto
        (fun n : ℕ ↦ Real.log (n : ℝ) / n) atTop (𝓝 0) :=
      hlog.comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using (tendsto_const_nhds.mul hlogNat)
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact mul_nonneg
      (div_nonneg (sq_nonneg x) (sq_nonneg (n : ℝ)))
      (Finset.sum_nonneg fun k _ ↦ pairWeightedTailCoeff_nonneg x k)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
    have hsum :
        (∑ k ∈ Icc 0 n, pairWeightedTailCoeff x k) =
          pairWeightedTailSum x (n : ℝ) := by
      rw [pairWeightedTailSum]
      norm_num
    rw [hsum]
    have hA := pairWeightedTailSum_le_chebyshev (x := x) hnR
    rw [pairHighWeight]
    have hweight : 0 ≤ x ^ 2 / (n : ℝ) ^ 2 :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    calc
      x ^ 2 / (n : ℝ) ^ 2 * pairWeightedTailSum x n ≤
          x ^ 2 / (n : ℝ) ^ 2 * (K * n * Real.log n) :=
        mul_le_mul_of_nonneg_left (by simpa only [K] using hA) hweight
      _ = K * x ^ 2 * (Real.log (n : ℝ) / n) := by
        field_simp

private theorem pairWeightedTailAbelLimit {x : ℝ} (hx : 1 ≤ x) :
    Tendsto
      (fun n : ℕ ↦ ∑ k ∈ Icc 0 n,
        pairHighWeight x k * pairWeightedTailCoeff x k)
      atTop
      (𝓝 (∫ t in Set.Ioi 1,
        (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t)) := by
  have hdiff : ∀ t ∈ Set.Ici (1 : ℝ),
      DifferentiableAt ℝ (pairHighWeight x) t := by
    intro t ht
    exact (pairHighWeight_hasDerivAt
      (by nlinarith [show (1 : ℝ) ≤ t from ht])).differentiableAt
  have hcont : ContinuousOn
      (fun t : ℝ ↦ -2 * x ^ 2 / t ^ 3) (Set.Ici 1) := by
    intro t ht
    have ht0 : t ≠ 0 := by nlinarith [show (1 : ℝ) ≤ t from ht]
    exact continuousAt_const.div (continuousAt_id.pow 3)
      (pow_ne_zero 3 ht0) |>.continuousWithinAt
  have hlocal : LocallyIntegrableOn (deriv (pairHighWeight x)) (Set.Ici 1) := by
    apply (hcont.locallyIntegrableOn measurableSet_Ici).congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [pairHighWeight_deriv
      (by nlinarith [show (1 : ℝ) ≤ t from ht])]
  let K : ℝ := Real.log 4 + 4
  let g : ℝ → ℝ := fun t ↦ 2 * x ^ 2 * K * (Real.log t / t ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hgOn : IntegrableOn g (Set.Ioi 1) :=
    pairLogDivSq_integrable.const_mul (2 * x ^ 2 * K)
  have hg : IntegrableAtFilter g atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp hgOn).1
  have hO :
      (fun t : ℝ ↦ deriv (pairHighWeight x) t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, pairWeightedTailCoeff x k) =O[atTop] g := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hA0 := pairWeightedTailSum_nonneg x t
    have hA := pairWeightedTailSum_le_chebyshev (x := x) ht
    have hfactor : 0 ≤ 2 * x ^ 2 / t ^ 3 := by positivity
    have hneg : -2 * x ^ 2 / t ^ 3 ≤ 0 := by
      rw [show -2 * x ^ 2 / t ^ 3 = -(2 * x ^ 2 / t ^ 3) by ring]
      exact neg_nonpos.mpr hfactor
    have hprod :
        (-2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg hA0
    have hg0 : 0 ≤ g t := by
      dsimp [g]
      exact mul_nonneg (mul_nonneg (by positivity) hK)
        (div_nonneg (Real.log_nonneg ht) (sq_nonneg t))
    rw [pairHighWeight_deriv (ne_of_gt ht0)]
    change ‖(-2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t‖ ≤ 1 * ‖g t‖
    simp only [one_mul, Real.norm_eq_abs, abs_of_nonpos hprod, abs_of_nonneg hg0]
    calc
      -((-2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t) =
          (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t := by ring
      _ ≤ (2 * x ^ 2 / t ^ 3) * (K * t * Real.log t) :=
        mul_le_mul_of_nonneg_left (by simpa only [K] using hA) hfactor
      _ = g t := by
        dsimp [g]
        field_simp
  have hlim := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (pairWeightedTailCoeff x) (pairWeightedTailCoeff_zero x) hdiff hlocal
    (l := (0 : ℝ)) (pairWeightedTailBoundary_tendsto_zero hx) (g := g) hO hg
  have hintegral :
      (0 - ∫ t in Set.Ioi 1, deriv (pairHighWeight x) t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, pairWeightedTailCoeff x k) =
        ∫ t in Set.Ioi 1,
          (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t := by
    rw [zero_sub, ← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [pairHighWeight_deriv (by nlinarith [show (1 : ℝ) < t from ht])]
    change -((-2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t) =
      (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t
    ring
  rw [hintegral] at hlim
  exact hlim

private theorem pairWeightedTail_hasSum {x : ℝ} (hx : 1 ≤ x) :
    HasSum
      (fun n : ℕ ↦ pairHighWeight x n * pairWeightedTailCoeff x n)
      (∫ t in Set.Ioi 1,
        (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hfin : ∀ n : ℕ, Icc 0 n = range (n + 1) := by
      intro n
      ext k
      simp only [mem_Icc, mem_range]
      omega
    have hshift : Tendsto
        (fun n : ℕ ↦ ∑ k ∈ range (n + 1),
          pairHighWeight x k * pairWeightedTailCoeff x k)
        atTop
        (𝓝 (∫ t in Set.Ioi 1,
          (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t)) := by
      simpa only [hfin] using pairWeightedTailAbelLimit hx
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp hshift
  · intro n
    exact mul_nonneg (by rw [pairHighWeight]; positivity)
      (pairWeightedTailCoeff_nonneg x n)

private theorem pairWeightedTailIntegrand_integrable {x : ℝ} :
    IntegrableOn
      (fun t : ℝ ↦
        (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t)
      (Set.Ioi 1) := by
  have hkernel : ContinuousOn
      (fun t : ℝ ↦ 2 * x ^ 2 / t ^ 3) (Set.Ici 1) := by
    intro t ht
    have ht0 : t ≠ 0 := by nlinarith [show (1 : ℝ) ≤ t from ht]
    exact continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 ht0)
      |>.continuousWithinAt
  have hlocal : LocallyIntegrableOn
      (fun t : ℝ ↦
        (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t)
      (Set.Ici 1) :=
    ((pairWeightedTailSum_locallyIntegrable x).locallyIntegrableOn
      (Set.Ici 1)).continuousOn_mul hkernel isLocallyClosed_Ici
  let K : ℝ := Real.log 4 + 4
  let g : ℝ → ℝ := fun t ↦ 2 * x ^ 2 * K * (Real.log t / t ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hgOn : IntegrableOn g (Set.Ioi 1) :=
    pairLogDivSq_integrable.const_mul (2 * x ^ 2 * K)
  have hg : IntegrableAtFilter g atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp hgOn).1
  have hO :
      (fun t : ℝ ↦
        (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t) =O[atTop] g := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hA0 := pairWeightedTailSum_nonneg x t
    have hA := pairWeightedTailSum_le_chebyshev (x := x) ht
    have hfactor : 0 ≤ 2 * x ^ 2 / t ^ 3 := by positivity
    have hprod : 0 ≤
        (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t :=
      mul_nonneg hfactor hA0
    have hg0 : 0 ≤ g t := by
      dsimp [g]
      exact mul_nonneg (mul_nonneg (by positivity) hK)
        (div_nonneg (Real.log_nonneg ht) (sq_nonneg t))
    simp only [one_mul, Real.norm_eq_abs, abs_of_nonneg hprod, abs_of_nonneg hg0]
    calc
      (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t ≤
          (2 * x ^ 2 / t ^ 3) * (K * t * Real.log t) :=
        mul_le_mul_of_nonneg_left (by simpa only [K] using hA) hfactor
      _ = g t := by
        dsimp [g]
        field_simp
  exact (hlocal.integrableOn_of_isBigO_atTop hO hg).mono_set
    Set.Ioi_subset_Ici_self

private theorem pairPrimeTerm_nonneg {x : ℝ} (n : ℕ) :
    0 ≤ pairDirichletCoefficient n * pairPrimeKernel x n := by
  exact mul_nonneg (pairDirichletCoefficient_nonneg n) (sq_nonneg _)

private theorem pairPrimeKernel_le_high {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    pairPrimeKernel x n ≤ pairHighWeight x n := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have ha : 0 ≤ (n : ℝ) / x := div_nonneg (Nat.cast_nonneg n) (le_of_lt hx0)
  have hb : 0 ≤ x / (n : ℝ) := div_nonneg (le_of_lt hx0) (Nat.cast_nonneg n)
  have hm : 0 ≤ min ((n : ℝ) / x) (x / n) := le_min ha hb
  have hle : min ((n : ℝ) / x) (x / n) ≤ x / n := min_le_right _ _
  rw [pairPrimeKernel, pairHighWeight, ← div_pow]
  nlinarith

private theorem pairPrime_summable {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun n : ℕ ↦
      pairDirichletCoefficient n * pairPrimeKernel x n) := by
  apply Summable.of_nonneg_of_le
  · exact pairPrimeTerm_nonneg
  · intro n
    calc
      pairDirichletCoefficient n * pairPrimeKernel x n ≤
          pairDirichletCoefficient n * pairHighWeight x n :=
        mul_le_mul_of_nonneg_left (pairPrimeKernel_le_high hx n)
          (pairDirichletCoefficient_nonneg n)
      _ = pairHighWeight x n * pairDirichletCoefficient n := mul_comm _ _
  · exact pairHigh_summable hx

private theorem pairPrimeTerm_eq_low {x : ℝ} (hx : 1 ≤ x) {n : ℕ}
    (hn : n ∈ Icc 0 ⌊x⌋₊) :
    pairDirichletCoefficient n * pairPrimeKernel x n =
      pairLowWeight x n * pairDirichletCoefficient n := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hnx : (n : ℝ) ≤ x := by
    exact le_trans (by exact_mod_cast (mem_Icc.mp hn).2) (Nat.floor_le (le_of_lt hx0))
  have hmin : min ((n : ℝ) / x) (x / n) = (n : ℝ) / x := by
    by_cases hn0 : n = 0
    · subst n
      simp
    · rw [min_eq_left]
      have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      rw [div_le_div_iff₀ hx0 hnR]
      nlinarith
  rw [pairPrimeKernel, hmin, pairLowWeight, div_pow]
  ring

private theorem pairPrimeTerm_eq_high {x : ℝ} (hx : 1 ≤ x) {n : ℕ}
    (hn : n ∉ Icc 0 ⌊x⌋₊) :
    pairDirichletCoefficient n * pairPrimeKernel x n =
      pairHighWeight x n * pairDirichletCoefficient n := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hfloor : ⌊x⌋₊ < n := by
    simpa only [mem_Icc, Nat.zero_le, true_and, not_le] using hn
  have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hfloor
  have hn0 : 0 < (n : ℝ) := lt_trans hx0 hxn
  have hmin : min ((n : ℝ) / x) (x / n) = x / n := by
    rw [min_eq_right]
    rw [div_le_div_iff₀ hn0 hx0]
    nlinarith
  rw [pairPrimeKernel, hmin, pairHighWeight, div_pow]
  ring

private theorem pairPrimeKernel_eq_low {x : ℝ} (hx : 1 ≤ x) {n : ℕ}
    (hn : n ∈ Icc 0 ⌊x⌋₊) :
    pairPrimeKernel x n = pairLowWeight x n := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hnx : (n : ℝ) ≤ x := by
    exact le_trans (by exact_mod_cast (mem_Icc.mp hn).2) (Nat.floor_le (le_of_lt hx0))
  have hmin : min ((n : ℝ) / x) (x / n) = (n : ℝ) / x := by
    by_cases hn0 : n = 0
    · subst n
      simp
    · rw [min_eq_left]
      have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      rw [div_le_div_iff₀ hx0 hnR]
      nlinarith
  rw [pairPrimeKernel, hmin, pairLowWeight, div_pow]

private theorem pairPrimeKernel_eq_high {x : ℝ} (hx : 1 ≤ x) {n : ℕ}
    (hn : n ∉ Icc 0 ⌊x⌋₊) :
    pairPrimeKernel x n = pairHighWeight x n := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hfloor : ⌊x⌋₊ < n := by
    simpa only [mem_Icc, Nat.zero_le, true_and, not_le] using hn
  have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hfloor
  have hn0 : 0 < (n : ℝ) := lt_trans hx0 hxn
  have hmin : min ((n : ℝ) / x) (x / n) = x / n := by
    rw [min_eq_right]
    rw [div_le_div_iff₀ hn0 hx0]
    nlinarith
  rw [pairPrimeKernel, hmin, pairHighWeight, div_pow]

/-- The extra index-weighted prime diagonal required by the Hilbert error is
summable and is `O(x (1 + log x))`, uniformly for `x ≥ 1`. -/
theorem pairWeightedPrimeMeanSquare_bound :
    ∃ K > 0, ∀ x : ℝ, 1 ≤ x →
      Summable (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n ^ 2 * pairPrimeKernel x n) ∧
      pairWeightedPrimeMeanSquare x ≤ K * x * (1 + Real.log x) := by
  let K₀ : ℝ := Real.log 4 + 4
  have hK₀ : 0 < K₀ := by
    dsimp [K₀]
    positivity
  refine ⟨3 * K₀, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let s : Finset ℕ := Icc 0 ⌊x⌋₊
  let lowTerm : ℕ → ℝ := fun n ↦
    if n ∈ s then
      pairLowWeight x n * ArithmeticFunction.vonMangoldt n ^ 2
    else 0
  let highTerm : ℕ → ℝ := fun n ↦
    pairHighWeight x n * pairWeightedTailCoeff x n
  have hlowHasSum :
      HasSum lowTerm
        (∑ n ∈ s,
          pairLowWeight x n * ArithmeticFunction.vonMangoldt n ^ 2) := by
    have h := hasSum_sum_of_ne_finset_zero
      (L := SummationFilter.unconditional ℕ) (s := s) (f := lowTerm) (by
      intro n hn
      simp [lowTerm, hn])
    simpa [lowTerm] using h
  have hhighHasSum :
      HasSum highTerm
        (∫ t in Set.Ioi 1,
          (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t) := by
    simpa only [highTerm] using pairWeightedTail_hasSum hx
  have hdecomp : ∀ n : ℕ,
      ArithmeticFunction.vonMangoldt n ^ 2 * pairPrimeKernel x n =
        lowTerm n + highTerm n := by
    intro n
    by_cases hn : n ∈ s
    · have hnle : n ≤ ⌊x⌋₊ := by
        simpa only [s, mem_Icc, Nat.zero_le, true_and] using hn
      have htail : pairWeightedTailCoeff x n = 0 := by
        simp [pairWeightedTailCoeff, not_lt_of_ge hnle]
      rw [pairPrimeKernel_eq_low hx (by simpa only [s] using hn)]
      simp [lowTerm, highTerm, hn, htail, mul_comm]
    · have hfloor : ⌊x⌋₊ < n := by
        simpa only [s, mem_Icc, Nat.zero_le, true_and, not_le] using hn
      have htail : pairWeightedTailCoeff x n =
          ArithmeticFunction.vonMangoldt n ^ 2 := by
        simp [pairWeightedTailCoeff, hfloor]
      rw [pairPrimeKernel_eq_high hx (by simpa only [s] using hn)]
      simp [lowTerm, highTerm, hn, htail, mul_comm]
  have hsummable : Summable (fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n ^ 2 * pairPrimeKernel x n) := by
    have hadd : Summable (fun n ↦ lowTerm n + highTerm n) :=
      hlowHasSum.summable.add hhighHasSum.summable
    exact hadd.congr fun n ↦ (hdecomp n).symm
  refine ⟨hsummable, ?_⟩
  have htsum : pairWeightedPrimeMeanSquare x =
      (∑ n ∈ s,
        pairLowWeight x n * ArithmeticFunction.vonMangoldt n ^ 2) +
      ∫ t in Set.Ioi 1,
        (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t := by
    rw [pairWeightedPrimeMeanSquare]
    calc
      (∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n ^ 2 * pairPrimeKernel x n) =
          ∑' n : ℕ, (lowTerm n + highTerm n) := tsum_congr hdecomp
      _ = (∑ n ∈ s,
          pairLowWeight x n * ArithmeticFunction.vonMangoldt n ^ 2) +
          ∫ t in Set.Ioi 1,
            (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t := by
        exact (hlowHasSum.add hhighHasSum).tsum_eq
  have hlow :
      (∑ n ∈ s,
        pairLowWeight x n * ArithmeticFunction.vonMangoldt n ^ 2) ≤
        K₀ * x * Real.log x := by
    calc
      (∑ n ∈ s,
          pairLowWeight x n * ArithmeticFunction.vonMangoldt n ^ 2) ≤
          ∑ n ∈ s, ArithmeticFunction.vonMangoldt n ^ 2 := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        have hnx : (n : ℝ) ≤ x := by
          exact le_trans (by
            exact_mod_cast (mem_Icc.mp (by simpa only [s] using hn)).2)
            (Nat.floor_le (le_of_lt hx0))
        have hweight0 : 0 ≤ pairLowWeight x n := by
          rw [pairLowWeight]
          positivity
        have hweight1 : pairLowWeight x n ≤ 1 := by
          rw [pairLowWeight]
          rw [div_le_one (sq_pos_of_pos hx0)]
          exact (sq_le_sq₀ (Nat.cast_nonneg n) (le_of_lt hx0)).2 hnx
        calc
          pairLowWeight x n * ArithmeticFunction.vonMangoldt n ^ 2 ≤
              1 * ArithmeticFunction.vonMangoldt n ^ 2 :=
            mul_le_mul_of_nonneg_right hweight1 (sq_nonneg _)
          _ = ArithmeticFunction.vonMangoldt n ^ 2 := one_mul _
      _ = ∑ n ∈ Ioc 0 ⌊x⌋₊,
          ArithmeticFunction.vonMangoldt n ^ 2 := by
        dsimp only [s]
        rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊x⌋₊), Finset.sum_cons]
        · simp
      _ ≤ (Real.log 4 + 4) * x * Real.log x :=
        Zeta23.Cheb.sum_vonMangoldt_sq_le hx
      _ = K₀ * x * Real.log x := by rfl
  let tailIntegrand : ℝ → ℝ := fun t ↦
    (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t
  have htailFull : IntegrableOn tailIntegrand (Set.Ioi 1) := by
    simpa only [tailIntegrand] using pairWeightedTailIntegrand_integrable (x := x)
  have htailOn : IntegrableOn tailIntegrand (Set.Ioi x) :=
    htailFull.mono_set fun t ht ↦ lt_of_le_of_lt hx ht
  have htailZero : ∫ t in Set.Ioc 1 x, tailIntegrand t = 0 := by
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t = 0
    rw [pairWeightedTailSum_eq_zero_of_le ht.2, mul_zero]
  have htailRestrict :
      (∫ t in Set.Ioi 1, tailIntegrand t) =
        ∫ t in Set.Ioi x, tailIntegrand t := by
    have hsplit := intervalIntegral.integral_interval_add_Ioi htailFull htailOn
    rw [intervalIntegral.integral_of_le hx, htailZero, zero_add] at hsplit
    exact hsplit.symm
  have hlogTail : IntegrableOn
      (fun t : ℝ ↦ Real.log t / t ^ 2) (Set.Ioi x) :=
    pairLogDivSq_integrable.mono_set fun t ht ↦ lt_of_le_of_lt hx ht
  have hmajor : IntegrableOn
      (fun t : ℝ ↦ 2 * x ^ 2 * K₀ * (Real.log t / t ^ 2))
      (Set.Ioi x) := hlogTail.const_mul (2 * x ^ 2 * K₀)
  have htailBound :
      (∫ t in Set.Ioi 1, tailIntegrand t) ≤
        2 * K₀ * x * (Real.log x + 1) := by
    rw [htailRestrict]
    calc
      (∫ t in Set.Ioi x, tailIntegrand t) ≤
          ∫ t in Set.Ioi x,
            2 * x ^ 2 * K₀ * (Real.log t / t ^ 2) := by
        apply MeasureTheory.setIntegral_mono_on htailOn hmajor measurableSet_Ioi
        intro t ht
        have ht1 : 1 ≤ t := hx.trans (le_of_lt ht)
        have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
        have hfactor : 0 ≤ 2 * x ^ 2 / t ^ 3 := by positivity
        have hA := pairWeightedTailSum_le_chebyshev (x := x) ht1
        dsimp only [tailIntegrand]
        calc
          (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t ≤
              (2 * x ^ 2 / t ^ 3) * (K₀ * t * Real.log t) :=
            mul_le_mul_of_nonneg_left (by simpa only [K₀] using hA) hfactor
          _ = 2 * x ^ 2 * K₀ * (Real.log t / t ^ 2) := by
            field_simp
      _ = 2 * x ^ 2 * K₀ * ((Real.log x + 1) / x) := by
        rw [MeasureTheory.integral_const_mul, pairLogDivSq_integral hx]
      _ = 2 * K₀ * x * (Real.log x + 1) := by
        field_simp
  rw [htsum]
  calc
    (∑ n ∈ s,
        pairLowWeight x n * ArithmeticFunction.vonMangoldt n ^ 2) +
        ∫ t in Set.Ioi 1,
          (2 * x ^ 2 / t ^ 3) * pairWeightedTailSum x t ≤
        K₀ * x * Real.log x + 2 * K₀ * x * (Real.log x + 1) :=
      add_le_add hlow (by simpa only [tailIntegrand] using htailBound)
    _ ≤ (3 * K₀) * x * (1 + Real.log x) := by
      have hKx : 0 ≤ K₀ * x := mul_nonneg (le_of_lt hK₀) (le_of_lt hx0)
      nlinarith

private theorem pairHighIntegrand_integrable {x : ℝ} :
    IntegrableOn
      (fun t : ℝ ↦ (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t)
      (Set.Ioi 1) := by
  have hkernel : ContinuousOn
      (fun t : ℝ ↦ 2 * x ^ 2 / t ^ 3) (Set.Ici 1) := by
    intro t ht
    have ht0 : t ≠ 0 := by nlinarith [show (1 : ℝ) ≤ t from ht]
    exact continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 ht0)
      |>.continuousWithinAt
  have hlocal : LocallyIntegrableOn
      (fun t : ℝ ↦ (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t)
      (Set.Ici 1) :=
    (pairCoefficientSum_locallyIntegrable.locallyIntegrableOn
      (Set.Ici 1)).continuousOn_mul hkernel isLocallyClosed_Ici
  let K : ℝ := Real.log 4 + 4
  let g : ℝ → ℝ := fun t ↦ 2 * x ^ 2 * K * (Real.log t / t ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hgOn : IntegrableOn g (Set.Ioi 1) :=
    pairLogDivSq_integrable.const_mul (2 * x ^ 2 * K)
  have hg : IntegrableAtFilter g atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp hgOn).1
  have hO :
      (fun t : ℝ ↦ (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t) =O[atTop] g := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hA0 := pairCoefficientSum_nonneg t
    have hA := pairCoefficientSum_le_chebyshev ht
    have hfactor : 0 ≤ 2 * x ^ 2 / t ^ 3 := by positivity
    have hprod : 0 ≤ (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t :=
      mul_nonneg hfactor hA0
    have hg0 : 0 ≤ g t := by
      dsimp [g]
      exact mul_nonneg (mul_nonneg (by positivity) hK)
        (div_nonneg (Real.log_nonneg ht) (sq_nonneg t))
    simp only [one_mul, Real.norm_eq_abs, abs_of_nonneg hprod, abs_of_nonneg hg0]
    calc
      (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t ≤
          (2 * x ^ 2 / t ^ 3) * (K * t * Real.log t) :=
        mul_le_mul_of_nonneg_left (by simpa only [K] using hA) hfactor
      _ = g t := by
        dsimp [g]
        field_simp
  exact (hlocal.integrableOn_of_isBigO_atTop hO hg).mono_set Set.Ioi_subset_Ici_self

private theorem pairLowAbel {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 0 ⌊x⌋₊, pairLowWeight x n * pairDirichletCoefficient n =
      pairCoefficientSum x -
        ∫ t in Set.Ioc 1 x, (2 * t / x ^ 2) * pairCoefficientSum t := by
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) x,
      DifferentiableAt ℝ (pairLowWeight x) t := fun t _ ↦
    pairLowWeight_hasDerivAt.differentiableAt
  have hint : IntegrableOn (deriv (pairLowWeight x)) (Set.Icc (1 : ℝ) x) := by
    have hcont : Continuous fun t : ℝ ↦ 2 * t / x ^ 2 :=
      (continuous_const.mul continuous_id).div_const _
    refine hcont.continuousOn.integrableOn_Icc.congr_fun ?_ measurableSet_Icc
    intro t _
    rw [pairLowWeight_deriv]
  have habel := sum_mul_eq_sub_integral_mul₀ pairDirichletCoefficient
    pairDirichletCoefficient_zero x hdiff hint
  calc
    ∑ n ∈ Icc 0 ⌊x⌋₊, pairLowWeight x n * pairDirichletCoefficient n =
        pairLowWeight x x * pairCoefficientSum x -
          ∫ t in Set.Ioc 1 x, deriv (pairLowWeight x) t * pairCoefficientSum t := by
      simpa only [pairCoefficientSum_eq_Icc] using habel
    _ = pairCoefficientSum x -
        ∫ t in Set.Ioc 1 x, (2 * t / x ^ 2) * pairCoefficientSum t := by
      have hx0 : x ≠ 0 := by nlinarith
      rw [show pairLowWeight x x = 1 by
        rw [pairLowWeight, div_self (pow_ne_zero 2 hx0)], one_mul]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
      rw [pairLowWeight_deriv]

private theorem pairHighAbelFinite {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 0 ⌊x⌋₊, pairHighWeight x n * pairDirichletCoefficient n =
      pairCoefficientSum x +
        ∫ t in Set.Ioc 1 x, (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t := by
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) x,
      DifferentiableAt ℝ (pairHighWeight x) t := by
    intro t ht
    exact (pairHighWeight_hasDerivAt (by nlinarith [ht.1])).differentiableAt
  have hint : IntegrableOn (deriv (pairHighWeight x)) (Set.Icc (1 : ℝ) x) := by
    have hcont : ContinuousOn (fun t : ℝ ↦ -2 * x ^ 2 / t ^ 3) (Set.Icc 1 x) := by
      intro t ht
      have ht0 : t ≠ 0 := by nlinarith [ht.1]
      exact continuousAt_const.div (continuousAt_id.pow 3)
        (by simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 3 ht0) |>.continuousWithinAt
    refine hcont.integrableOn_Icc.congr_fun ?_ measurableSet_Icc
    intro t ht
    rw [pairHighWeight_deriv (by nlinarith [ht.1])]
  have habel := sum_mul_eq_sub_integral_mul₀ pairDirichletCoefficient
    pairDirichletCoefficient_zero x hdiff hint
  calc
    ∑ n ∈ Icc 0 ⌊x⌋₊, pairHighWeight x n * pairDirichletCoefficient n =
        pairHighWeight x x * pairCoefficientSum x -
          ∫ t in Set.Ioc 1 x, deriv (pairHighWeight x) t * pairCoefficientSum t := by
      simpa only [pairCoefficientSum_eq_Icc] using habel
    _ = pairCoefficientSum x +
        ∫ t in Set.Ioc 1 x, (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t := by
      have hx0 : x ≠ 0 := by nlinarith
      rw [show pairHighWeight x x = 1 by
        rw [pairHighWeight, div_self (pow_ne_zero 2 hx0)], one_mul]
      rw [← sub_neg_eq_add]
      congr 1
      rw [← MeasureTheory.integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
      rw [pairHighWeight_deriv (by nlinarith [ht.1])]
      ring

private theorem pairPrimeMeanSquare_integral_identity {x : ℝ} (hx : 1 ≤ x) :
    pairPrimeMeanSquare x =
      -(∫ t in Set.Ioc 1 x,
          (2 * t / x ^ 2) * pairCoefficientSum t) +
        ∫ t in Set.Ioi x,
          (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t := by
  let s : Finset ℕ := Icc 0 ⌊x⌋₊
  have hprimeSplit :=
    (pairPrime_summable hx).sum_add_tsum_subtype_compl s
  have hhighSplit :=
    (pairHigh_summable hx).sum_add_tsum_subtype_compl s
  have hfinitePrime :
      ∑ n ∈ s, pairDirichletCoefficient n * pairPrimeKernel x n =
        ∑ n ∈ s, pairLowWeight x n * pairDirichletCoefficient n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact pairPrimeTerm_eq_low hx hn
  have houtside :
      (∑' n : {n // n ∉ s},
          pairDirichletCoefficient n * pairPrimeKernel x n) =
        ∑' n : {n // n ∉ s},
          pairHighWeight x n * pairDirichletCoefficient n := by
    apply tsum_congr
    intro n
    exact pairPrimeTerm_eq_high hx n.property
  rw [hfinitePrime, houtside] at hprimeSplit
  have hseries :
      pairPrimeMeanSquare x =
        (∑ n ∈ s, pairLowWeight x n * pairDirichletCoefficient n) +
          ((∑' n : ℕ, pairHighWeight x n * pairDirichletCoefficient n) -
            ∑ n ∈ s, pairHighWeight x n * pairDirichletCoefficient n) := by
    rw [pairPrimeMeanSquare]
    linarith
  have hfull := pairHighIntegrand_integrable (x := x)
  have htail : IntegrableOn
      (fun t : ℝ ↦ (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t)
      (Set.Ioi x) := by
    exact hfull.mono_set fun t ht ↦ lt_of_le_of_lt hx ht
  have hintegralSplit :
      (∫ t in Set.Ioc 1 x,
          (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t) +
        (∫ t in Set.Ioi x,
          (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t) =
        ∫ t in Set.Ioi 1,
          (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t := by
    have h := intervalIntegral.integral_interval_add_Ioi hfull htail
    rw [intervalIntegral.integral_of_le hx] at h
    exact h
  rw [hseries, (pairHigh_hasSum hx).tsum_eq]
  dsimp only [s]
  rw [pairLowAbel hx, pairHighAbelFinite hx]
  linarith

private noncomputable def pairLowMainPrimitive (x t : ℝ) : ℝ :=
  (t ^ 2 * Real.log t ^ 2 / 2 - t ^ 2 * Real.log t / 2 + t ^ 2 / 4) / x ^ 2

private theorem pairLowMainPrimitive_hasDerivAt {x t : ℝ} (hx : x ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (pairLowMainPrimitive x)
      ((2 * t / x ^ 2) * (Real.log t ^ 2 / 2)) t := by
  have hid : HasDerivAt (fun u : ℝ ↦ u) 1 t := hasDerivAt_id t
  have hpow := hid.pow 2
  have hlog := Real.hasDerivAt_log ht
  have hlogpow := hlog.pow 2
  unfold pairLowMainPrimitive
  refine ((((hpow.mul hlogpow).div_const 2).sub
    ((hpow.mul hlog).div_const 2) |>.add (hpow.div_const 4)).div_const
      (x ^ 2)).congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, mul_one, Pi.pow_apply]
  field_simp [hx, ht]
  ring

private theorem pairLowMain_integrable {x : ℝ} :
    IntegrableOn
      (fun t : ℝ ↦ (2 * t / x ^ 2) * (Real.log t ^ 2 / 2))
      (Set.Icc 1 x) := by
  have hcont : ContinuousOn
      (fun t : ℝ ↦ (2 * t / x ^ 2) * (Real.log t ^ 2 / 2))
      (Set.Icc 1 x) := by
    intro t ht
    have ht0 : t ≠ 0 := by nlinarith [ht.1]
    exact (((continuousAt_const.mul continuousAt_id).div_const _).mul
      (((Real.continuousAt_log ht0).pow 2).div_const _)).continuousWithinAt
  exact hcont.integrableOn_Icc

private theorem pairLowMain_integral {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, (2 * t / x ^ 2) * (Real.log t ^ 2 / 2) =
      Real.log x ^ 2 / 2 - Real.log x / 2 + 1 / 4 - 1 / (4 * x ^ 2) := by
  have hx0 : x ≠ 0 := by nlinarith
  rw [← intervalIntegral.integral_of_le hx]
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (pairLowMainPrimitive x)
        ((2 * t / x ^ 2) * (Real.log t ^ 2 / 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact pairLowMainPrimitive_hasDerivAt hx0 (by nlinarith [ht.1])
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ (2 * t / x ^ 2) * (Real.log t ^ 2 / 2)) volume 1 x := by
    apply IntegrableOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    exact pairLowMain_integrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hint]
  unfold pairLowMainPrimitive
  rw [Real.log_one]
  field_simp
  ring

private noncomputable def pairHighMainPrimitive (x t : ℝ) : ℝ :=
  -(x ^ 2 *
    (Real.log t ^ 2 / 2 + Real.log t / 2 + 1 / 4)) / t ^ 2

private theorem pairHighMainPrimitive_hasDerivAt {x t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (pairHighMainPrimitive x)
      ((2 * x ^ 2 / t ^ 3) * (Real.log t ^ 2 / 2)) t := by
  have hid : HasDerivAt (fun u : ℝ ↦ u) 1 t := hasDerivAt_id t
  have hpow := hid.pow 2
  have hlog := Real.hasDerivAt_log ht
  have hlogpow := hlog.pow 2
  have hconst : HasDerivAt (fun _ : ℝ ↦ (1 : ℝ) / 4) 0 t :=
    hasDerivAt_const t (1 / 4)
  have hinner := ((hlogpow.div_const 2).add (hlog.div_const 2)).add hconst
  have houter := (hasDerivAt_const t (x ^ 2)).mul hinner |>.neg
  unfold pairHighMainPrimitive
  refine (houter.div hpow (pow_ne_zero 2 ht)).congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, mul_one, zero_mul,
    zero_add, add_zero, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.neg_apply,
    ]
  field_simp [ht]
  ring_nf

private theorem pairHighMain_integrable {x : ℝ} :
    IntegrableOn
      (fun t : ℝ ↦ (2 * x ^ 2 / t ^ 3) * (Real.log t ^ 2 / 2))
      (Set.Ioi 1) := by
  have hexp : IntegrableOn
      (fun u : ℝ ↦ u ^ 2 * Real.exp (-2 * u)) (Set.Ioi 0) := by
    simpa [Real.rpow_two, Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (2 : ℝ)) (p := (1 : ℝ)) (b := (2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  have hcomp : IntegrableOn
      (fun t : ℝ ↦ t⁻¹ *
        (x ^ 2 * (Real.log t ^ 2 * Real.exp (-2 * Real.log t))))
      (Set.Ioi 1) := by
    have hscaled : IntegrableOn
        (fun u : ℝ ↦ x ^ 2 * (u ^ 2 * Real.exp (-2 * u))) (Set.Ioi 0) :=
      hexp.const_mul (x ^ 2)
    exact (integrableOn_comp_log_Ioi
      (fun u : ℝ ↦ x ^ 2 * (u ^ 2 * Real.exp (-2 * u))) one_pos).2
      (by simpa only [Real.log_one] using hscaled)
  refine hcomp.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  change t⁻¹ * (x ^ 2 * (Real.log t ^ 2 * Real.exp (-2 * Real.log t))) =
    (2 * x ^ 2 / t ^ 3) * (Real.log t ^ 2 / 2)
  rw [show -2 * Real.log t = -(Real.log t + Real.log t) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_log ht0]
  field_simp

private theorem pairHighMainPrimitive_tendsto_zero (x : ℝ) :
    Tendsto (pairHighMainPrimitive x) atTop (𝓝 0) := by
  have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlogtwo : Tendsto (fun t : ℝ ↦ Real.log t ^ 2 / t) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hlogone : Tendsto (fun t : ℝ ↦ Real.log t / t) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlogtwoSq : Tendsto (fun t : ℝ ↦ Real.log t ^ 2 / t ^ 2) atTop (𝓝 0) := by
    convert hlogtwo.mul hinv using 1 <;>
      simp [div_eq_mul_inv, pow_two, mul_assoc]
  have hlogoneSq : Tendsto (fun t : ℝ ↦ Real.log t / t ^ 2) atTop (𝓝 0) := by
    convert hlogone.mul hinv using 1 <;>
      simp [div_eq_mul_inv, pow_two, mul_assoc]
  have hinvSq : Tendsto (fun t : ℝ ↦ 1 / t ^ 2) atTop (𝓝 0) := by
    convert hinv.mul hinv using 1 <;>
      simp [div_eq_mul_inv, pow_two]
  have hsum : Tendsto
      (fun t : ℝ ↦ Real.log t ^ 2 / t ^ 2 / 2 +
        Real.log t / t ^ 2 / 2 + (1 / t ^ 2) / 4)
      atTop (𝓝 0) := by
    simpa only [zero_div, zero_add] using
      ((hlogtwoSq.div_const 2).add (hlogoneSq.div_const 2)).add (hinvSq.div_const 4)
  have hconst : Tendsto (fun _ : ℝ ↦ x ^ 2) atTop (𝓝 (x ^ 2)) :=
    tendsto_const_nhds
  have hscaled : Tendsto
      (fun t : ℝ ↦ -(x ^ 2 *
        (Real.log t ^ 2 / t ^ 2 / 2 + Real.log t / t ^ 2 / 2 +
          (1 / t ^ 2) / 4))) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_zero] using (hconst.mul hsum).neg
  convert hscaled using 1
  funext t
  unfold pairHighMainPrimitive
  ring_nf

private theorem pairHighMain_integral {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioi x, (2 * x ^ 2 / t ^ 3) * (Real.log t ^ 2 / 2) =
      Real.log x ^ 2 / 2 + Real.log x / 2 + 1 / 4 := by
  have hderiv : ∀ t ∈ Set.Ici x,
      HasDerivAt (pairHighMainPrimitive x)
        ((2 * x ^ 2 / t ^ 3) * (Real.log t ^ 2 / 2)) t := by
    intro t ht
    exact pairHighMainPrimitive_hasDerivAt
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (hx.trans ht)))
  have hint := (pairHighMain_integrable (x := x)).mono_set
    (show Set.Ioi x ⊆ Set.Ioi (1 : ℝ) by intro t ht; exact lt_of_le_of_lt hx ht)
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint
    (pairHighMainPrimitive_tendsto_zero x)]
  unfold pairHighMainPrimitive
  have hx0 : x ≠ 0 := by nlinarith
  field_simp
  ring

private theorem pairLowKernel_integrable {x : ℝ} :
    IntegrableOn (fun t : ℝ ↦ 2 * t / x ^ 2) (Set.Icc 1 x) := by
  exact ((continuous_const.mul continuous_id).div_const _).continuousOn.integrableOn_Icc

private theorem pairLowKernel_integral {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, 2 * t / x ^ 2 = 1 - 1 / x ^ 2 := by
  have hx0 : x ≠ 0 := by nlinarith
  rw [← intervalIntegral.integral_of_le hx]
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (pairLowWeight x) (2 * t / x ^ 2) t :=
    fun t _ ↦ pairLowWeight_hasDerivAt
  have hint : IntervalIntegrable (fun t : ℝ ↦ 2 * t / x ^ 2) volume 1 x := by
    apply IntegrableOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    exact pairLowKernel_integrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hint]
  simp [pairLowWeight, hx0]

private theorem pairHighKernel_integrable {x : ℝ} :
    IntegrableOn (fun t : ℝ ↦ 2 * x ^ 2 / t ^ 3) (Set.Ioi 1) := by
  have hexp : IntegrableOn (fun u : ℝ ↦ Real.exp (-2 * u)) (Set.Ioi 0) := by
    simpa [Real.rpow_zero, Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (0 : ℝ)) (p := (1 : ℝ)) (b := (2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  have hcomp : IntegrableOn
      (fun t : ℝ ↦ t⁻¹ * Real.exp (-2 * Real.log t)) (Set.Ioi 1) := by
    exact (integrableOn_comp_log_Ioi
      (fun u : ℝ ↦ Real.exp (-2 * u)) one_pos).2
      (by simpa only [Real.log_one] using hexp)
  have hscaled : IntegrableOn
      (fun t : ℝ ↦ (2 * x ^ 2) * (t⁻¹ * Real.exp (-2 * Real.log t)))
      (Set.Ioi 1) := hcomp.const_mul (2 * x ^ 2)
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  change (2 * x ^ 2) * (t⁻¹ * Real.exp (-2 * Real.log t)) =
    2 * x ^ 2 / t ^ 3
  rw [show -2 * Real.log t = -(Real.log t + Real.log t) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_log ht0]
  field_simp

private theorem pairHighKernel_integral {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioi x, 2 * x ^ 2 / t ^ 3 = 1 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hderiv : ∀ t ∈ Set.Ici x,
      HasDerivAt (fun u : ℝ ↦ -pairHighWeight x u) (2 * x ^ 2 / t ^ 3) t := by
    intro t ht
    refine (pairHighWeight_hasDerivAt
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (hx.trans ht)))).neg.congr_deriv ?_
    ring
  have hint := (pairHighKernel_integrable (x := x)).mono_set
    (show Set.Ioi x ⊆ Set.Ioi (1 : ℝ) by intro t ht; exact lt_of_le_of_lt hx ht)
  have htend : Tendsto (fun t : ℝ ↦ -pairHighWeight x t) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ ↦ x ^ 2) atTop (𝓝 (x ^ 2)) :=
      tendsto_const_nhds
    have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    have h := (hconst.mul (hinv.pow 2)).neg
    simpa [pairHighWeight, div_eq_mul_inv] using h
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  simp [pairHighWeight, ne_of_gt hx0]

private noncomputable def pairCoefficientError (t : ℝ) : ℝ :=
  pairCoefficientSum t - Real.log t ^ 2 / 2

private theorem pairCoefficientError_measurable :
    Measurable pairCoefficientError := by
  unfold pairCoefficientError
  exact pairCoefficientSum_monotone.measurable.sub
    ((Real.measurable_log.pow_const 2).div_const 2)

/-- The smoothed prime diagonal differs from `log x` by a bounded amount,
uniformly for `x ≥ 1`. -/
theorem pairPrimeMeanSquare_bounded :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      |pairPrimeMeanSquare x - Real.log x| ≤ C := by
  rcases pairCoefficientSum_bounded_global with ⟨C, hC, herror⟩
  refine ⟨2 * C + 1 / 4, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlowKernel : IntegrableOn
      (fun t : ℝ ↦ 2 * t / x ^ 2) (Set.Ioc 1 x) :=
    (pairLowKernel_integrable (x := x)).mono_set Set.Ioc_subset_Icc_self
  have hhighKernel : IntegrableOn
      (fun t : ℝ ↦ 2 * x ^ 2 / t ^ 3) (Set.Ioi x) :=
    (pairHighKernel_integrable (x := x)).mono_set fun t ht ↦
      lt_of_le_of_lt hx ht
  have hlowMajorant : IntegrableOn
      (fun t : ℝ ↦ C * (2 * t / x ^ 2)) (Set.Ioc 1 x) :=
    hlowKernel.const_mul C
  have hhighMajorant : IntegrableOn
      (fun t : ℝ ↦ C * (2 * x ^ 2 / t ^ 3)) (Set.Ioi x) :=
    hhighKernel.const_mul C
  have hlowErrorMeasurable : AEStronglyMeasurable
      (fun t : ℝ ↦ (2 * t / x ^ 2) * pairCoefficientError t)
      (volume.restrict (Set.Ioc 1 x)) := by
    exact (((measurable_const.mul measurable_id).div_const _).mul
      pairCoefficientError_measurable).aestronglyMeasurable
  have hhighErrorMeasurable : AEStronglyMeasurable
      (fun t : ℝ ↦ (2 * x ^ 2 / t ^ 3) * pairCoefficientError t)
      (volume.restrict (Set.Ioi x)) := by
    exact ((measurable_const.div (measurable_id.pow_const 3)).mul
      pairCoefficientError_measurable).aestronglyMeasurable
  have hlowDomination : ∀ᵐ t ∂volume.restrict (Set.Ioc 1 x),
      ‖(2 * t / x ^ 2) * pairCoefficientError t‖ ≤
        C * (2 * t / x ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num) (le_of_lt ht.1)
    have hkernel : 0 ≤ 2 * t / x ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) ht0) (sq_nonneg x)
    have herr : |pairCoefficientError t| ≤ C := by
      simpa only [pairCoefficientError] using herror t (le_of_lt ht.1)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel]
    calc
      (2 * t / x ^ 2) * |pairCoefficientError t| ≤
          (2 * t / x ^ 2) * C :=
        mul_le_mul_of_nonneg_left herr hkernel
      _ = C * (2 * t / x ^ 2) := mul_comm _ _
  have hhighDomination : ∀ᵐ t ∂volume.restrict (Set.Ioi x),
      ‖(2 * x ^ 2 / t ^ 3) * pairCoefficientError t‖ ≤
        C * (2 * x ^ 2 / t ^ 3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hx0 ht
    have hkernel : 0 ≤ 2 * x ^ 2 / t ^ 3 :=
      div_nonneg (mul_nonneg (by norm_num) (sq_nonneg x))
        (pow_nonneg (le_of_lt ht0) 3)
    have herr : |pairCoefficientError t| ≤ C := by
      simpa only [pairCoefficientError] using
        herror t (hx.trans (le_of_lt ht))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel]
    calc
      (2 * x ^ 2 / t ^ 3) * |pairCoefficientError t| ≤
          (2 * x ^ 2 / t ^ 3) * C :=
        mul_le_mul_of_nonneg_left herr hkernel
      _ = C * (2 * x ^ 2 / t ^ 3) := mul_comm _ _
  have hlowError : IntegrableOn
      (fun t : ℝ ↦ (2 * t / x ^ 2) * pairCoefficientError t)
      (Set.Ioc 1 x) :=
    hlowMajorant.mono' hlowErrorMeasurable hlowDomination
  have hhighError : IntegrableOn
      (fun t : ℝ ↦ (2 * x ^ 2 / t ^ 3) * pairCoefficientError t)
      (Set.Ioi x) :=
    hhighMajorant.mono' hhighErrorMeasurable hhighDomination
  have hlowBound :
      |∫ t in Set.Ioc 1 x,
          (2 * t / x ^ 2) * pairCoefficientError t| ≤ C := by
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ t in Set.Ioc 1 x,
          (2 * t / x ^ 2) * pairCoefficientError t‖ ≤
          ∫ t in Set.Ioc 1 x, C * (2 * t / x ^ 2) := by
        apply MeasureTheory.norm_integral_le_of_norm_le hlowMajorant
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : 0 ≤ t := le_trans (by norm_num) (le_of_lt ht.1)
        have hkernel : 0 ≤ 2 * t / x ^ 2 :=
          div_nonneg (mul_nonneg (by norm_num) ht0) (sq_nonneg x)
        have herr : |pairCoefficientError t| ≤ C := by
          simpa only [pairCoefficientError] using herror t (le_of_lt ht.1)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel]
        calc
          (2 * t / x ^ 2) * |pairCoefficientError t| ≤
              (2 * t / x ^ 2) * C :=
            mul_le_mul_of_nonneg_left herr hkernel
          _ = C * (2 * t / x ^ 2) := mul_comm _ _
      _ = C * (1 - 1 / x ^ 2) := by
        rw [MeasureTheory.integral_const_mul, pairLowKernel_integral hx]
      _ ≤ C := by
        have hinv : 0 ≤ 1 / x ^ 2 := by positivity
        nlinarith
  have hhighBound :
      |∫ t in Set.Ioi x,
          (2 * x ^ 2 / t ^ 3) * pairCoefficientError t| ≤ C := by
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ t in Set.Ioi x,
          (2 * x ^ 2 / t ^ 3) * pairCoefficientError t‖ ≤
          ∫ t in Set.Ioi x, C * (2 * x ^ 2 / t ^ 3) := by
        apply MeasureTheory.norm_integral_le_of_norm_le hhighMajorant
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans hx0 ht
        have hkernel : 0 ≤ 2 * x ^ 2 / t ^ 3 :=
          div_nonneg (mul_nonneg (by norm_num) (sq_nonneg x))
            (pow_nonneg (le_of_lt ht0) 3)
        have herr : |pairCoefficientError t| ≤ C := by
          simpa only [pairCoefficientError] using
            herror t (hx.trans (le_of_lt ht))
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel]
        calc
          (2 * x ^ 2 / t ^ 3) * |pairCoefficientError t| ≤
              (2 * x ^ 2 / t ^ 3) * C :=
            mul_le_mul_of_nonneg_left herr hkernel
          _ = C * (2 * x ^ 2 / t ^ 3) := mul_comm _ _
      _ = C := by
        rw [MeasureTheory.integral_const_mul, pairHighKernel_integral hx, mul_one]
  have hlowSplit :
      (∫ t in Set.Ioc 1 x, (2 * t / x ^ 2) * pairCoefficientSum t) =
        (∫ t in Set.Ioc 1 x,
          (2 * t / x ^ 2) * (Real.log t ^ 2 / 2)) +
        ∫ t in Set.Ioc 1 x,
          (2 * t / x ^ 2) * pairCoefficientError t := by
    rw [← MeasureTheory.integral_add
      ((pairLowMain_integrable (x := x)).mono_set Set.Ioc_subset_Icc_self)
      hlowError]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    rw [pairCoefficientError]
    ring
  have hhighSplit :
      (∫ t in Set.Ioi x, (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t) =
        (∫ t in Set.Ioi x,
          (2 * x ^ 2 / t ^ 3) * (Real.log t ^ 2 / 2)) +
        ∫ t in Set.Ioi x,
          (2 * x ^ 2 / t ^ 3) * pairCoefficientError t := by
    calc
      (∫ t in Set.Ioi x, (2 * x ^ 2 / t ^ 3) * pairCoefficientSum t) =
          ∫ t in Set.Ioi x,
            ((2 * x ^ 2 / t ^ 3) * (Real.log t ^ 2 / 2) +
              (2 * x ^ 2 / t ^ 3) * pairCoefficientError t) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
        rw [pairCoefficientError]
        ring
      _ = (∫ t in Set.Ioi x,
            (2 * x ^ 2 / t ^ 3) * (Real.log t ^ 2 / 2)) +
          ∫ t in Set.Ioi x,
            (2 * x ^ 2 / t ^ 3) * pairCoefficientError t := by
        exact MeasureTheory.integral_add
          ((pairHighMain_integrable (x := x)).mono_set fun t ht ↦
            lt_of_le_of_lt hx ht)
          hhighError
  have hidentity :
      pairPrimeMeanSquare x - Real.log x =
        -(∫ t in Set.Ioc 1 x,
            (2 * t / x ^ 2) * pairCoefficientError t) +
          (∫ t in Set.Ioi x,
            (2 * x ^ 2 / t ^ 3) * pairCoefficientError t) +
          1 / (4 * x ^ 2) := by
    rw [pairPrimeMeanSquare_integral_identity hx, hlowSplit, hhighSplit,
      pairLowMain_integral hx, pairHighMain_integral hx]
    ring
  have hcorrection : |1 / (4 * x ^ 2)| ≤ (1 : ℝ) / 4 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / (4 * x ^ 2))]
    rw [div_le_iff₀ (by positivity : 0 < (4 : ℝ) * x ^ 2)]
    nlinarith [sq_nonneg (x - 1)]
  rw [hidentity]
  calc
    |-(∫ t in Set.Ioc 1 x,
          (2 * t / x ^ 2) * pairCoefficientError t) +
        (∫ t in Set.Ioi x,
          (2 * x ^ 2 / t ^ 3) * pairCoefficientError t) +
        1 / (4 * x ^ 2)| ≤
        |-(∫ t in Set.Ioc 1 x,
          (2 * t / x ^ 2) * pairCoefficientError t)| +
        |∫ t in Set.Ioi x,
          (2 * x ^ 2 / t ^ 3) * pairCoefficientError t| +
        |1 / (4 * x ^ 2)| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C + C + 1 / 4 := by
      rw [abs_neg]
      exact add_le_add (add_le_add hlowBound hhighBound) hcorrection
    _ = 2 * C + 1 / 4 := by ring

end ZetaZeros.Unconditional
