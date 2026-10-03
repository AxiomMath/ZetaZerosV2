/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import ZetaZeros.Meta.Attr

/-!
# Elementary estimates for the pair-correlation formula

Calculus and real-analysis estimates used in the proof of the pair-correlation formula.

## Main results

* `ZetaZeros.inv_natCast_add_one_le_abs_log_sub_log`: distinct positive integers `m ≠ n` have
  `|log n - log m| ≥ 1 / (n + 1)`.
* `ZetaZeros.abs_le_of_abs_sub_le_mul_abs`: a function Lipschitz at `0` is bounded near `0`.
* `ZetaZeros.exists_integral_rpow_neg_mul_abs_le`: an exponential weight against an `L¹`
  function, `∫_0^1 T^{-cα} |g α| dα = O(1 / log T)` uniformly in `c ≥ 1`.
* `ZetaZeros.exists_abs_integral_rpow_neg_two_mul_sub_le`: the main-term integral,
  `2 log T ∫_0^1 T^{-2α} g α dα = g 0 + O(log log T / log T)`.
* `ZetaZeros.exists_abs_integral_log_sq_sub_le`: the mean square of the logarithm,
  `∫_0^T log (|t| + 2) ^ 2 dt = T (log T) ^ 2 + O(T log T)`.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory Filter intervalIntegral

/-- The elementary lower bound `(b - a) / b ≤ log b - log a` for positive reals: the inequality
`1 - x⁻¹ ≤ log x` evaluated at `x = b / a`. -/
private lemma sub_div_le_log_sub_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b - a) / b ≤ Real.log b - Real.log a :=
  calc (b - a) / b = 1 - a / b := by field_simp
    _ = 1 - (b / a)⁻¹ := by rw [inv_div]
    _ ≤ Real.log (b / a) := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
    _ = Real.log b - Real.log a := Real.log_div hb.ne' ha.ne'

/-- Distinct positive integers have logarithms separated by at least `1 / (n + 1)`.

The two nearest values of `m` are `n - 1` and `n + 1`, and the worse of the two gaps is
`log (n + 1) - log n ≥ 1 / (n + 1)`. -/
@[zz_tag "lem_log_gap"]
theorem inv_natCast_add_one_le_abs_log_sub_log {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m ≠ n) : ((n : ℝ) + 1)⁻¹ ≤ |Real.log n - Real.log m| := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    have hlog : Real.log m ≤ Real.log n := Real.log_le_log hm0 (by linarith)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log n - Real.log m)]
    have h1 : ((n : ℝ) - m) / n ≤ Real.log n - Real.log m := sub_div_le_log_sub_log hm0 hn0
    have h2 : ((n : ℝ) + 1)⁻¹ ≤ ((n : ℝ) - m) / n := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hn0]
      nlinarith
    linarith
  · have hnm' : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    have hlog : Real.log n ≤ Real.log m := Real.log_le_log hn0 (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log m - Real.log n)]
    have h1 : ((m : ℝ) - n) / m ≤ Real.log m - Real.log n := sub_div_le_log_sub_log hn0 hm0
    have h2 : ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) - n) / m := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hm0]
      nlinarith
    linarith

/-- A function whose distance from `g 0` is at most `K * |α|` throughout `|α| < δ` is bounded by
`|g 0| + K * δ` there: Lipschitz at a point implies locally bounded. -/
@[zz_tag "lem_lip_bounded_near_zero"]
theorem abs_le_of_abs_sub_le_mul_abs {g : ℝ → ℝ} {K δ α : ℝ} (hK : 0 < K)
    (h : ∀ β : ℝ, |β| < δ → |g β - g 0| ≤ K * |β|) (hα : |α| < δ) :
    |g α| ≤ |g 0| + K * δ := by
  have h1 : |g α| ≤ |g 0| + |g α - g 0| :=
    calc |g α| = |g 0 + (g α - g 0)| := by rw [show g 0 + (g α - g 0) = g α by ring]
      _ ≤ |g 0| + |g α - g 0| := abs_add_le _ _
  have h2 := h α hα
  have h3 : K * |α| ≤ K * δ := mul_le_mul_of_nonneg_left hα.le hK.le
  linarith

/-- For `k ≥ 0` and an integrable `g`, the exponentially damped function
`α ↦ exp (-(k * α)) * |g α|` is interval integrable on any interval with nonnegative
endpoints, the damping factor being bounded by `1` there. -/
private lemma expWeightIntervalIntegrable {g : ℝ → ℝ} (hg : Integrable g) {k a b : ℝ}
    (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun α => Real.exp (-(k * α)) * |g α|) volume a b := by
  rw [intervalIntegrable_iff]
  have hmeas : AEStronglyMeasurable (fun α : ℝ => Real.exp (-(k * α)))
      (volume.restrict (Set.uIoc a b)) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  refine MeasureTheory.Integrable.bdd_mul (c := 1)
    (hg.abs.mono_measure Measure.restrict_le_self) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with α hα
  have h0 : 0 ≤ α := le_trans (le_inf ha hb) hα.1.le
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith)

/-- The elementary bound `∫_0^b exp (-(k α)) dα ≤ 1 / k`, valid for every `k > 0`, since the
exact value of the integral is `(1 - exp (-(k b))) / k`. -/
private lemma expWeightIntegralExpLe {k b : ℝ} (hk : 0 < k) :
    (∫ α in (0:ℝ)..b, Real.exp (-(k * α))) ≤ 1 / k := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hne : (-k) ≠ 0 := neg_ne_zero.2 hk0
  have hfun : ∀ α : ℝ, Real.exp (-(k * α)) = Real.exp (-k * α) := by
    intro α; congr 1; ring
  simp only [hfun]
  rw [intervalIntegral.integral_comp_mul_left (fun u => Real.exp u) hne, integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  have h5 : 0 < Real.exp (-k * b) := Real.exp_pos _
  have h6 : (-k)⁻¹ * (Real.exp (-k * b) - 1) = 1 / k - Real.exp (-k * b) / k := by
    field_simp
    ring
  rw [h6]
  have h7 : 0 ≤ Real.exp (-k * b) / k := div_nonneg h5.le hk.le
  linarith

/-- If `g` is integrable on `ℝ` and bounded by `M` almost everywhere on a neighbourhood
`|α| < δ` of the origin, then the exponentially weighted integrals
`∫_0^1 T^{-cα} |g α| dα` are `O(1 / log T)` uniformly in `c ≥ 1`, with a constant
depending only on `M`, `δ` and `‖g‖_{L^1}`. -/
@[zz_tag "lem_exp_weight_L1"]
theorem exists_integral_rpow_neg_mul_abs_le {g : ℝ → ℝ} {M δ : ℝ}
    (hg : MeasureTheory.Integrable g) (hM : 0 < M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hbdd : ∀ᵐ α : ℝ, |α| < δ → |g α| ≤ M) :
    ∃ C > 0, ∀ T : ℝ, 3 ≤ T → ∀ c : ℝ, 1 ≤ c →
      (∫ α in (0:ℝ)..1, T ^ (-(c * α)) * |g α|) ≤ C / Real.log T := by
  have hI0 : 0 ≤ ∫ α, |g α| := integral_nonneg fun α => abs_nonneg _
  obtain ⟨η, hη0, hηδ, hη1⟩ : ∃ η : ℝ, 0 < η ∧ η < δ ∧ η ≤ 1 :=
    ⟨δ / 2, by linarith, by linarith, by linarith⟩
  refine ⟨M + (∫ α, |g α|) / η, add_pos_of_pos_of_nonneg hM (div_nonneg hI0 hη0.le), ?_⟩
  intro T hT c hc
  have hT0 : (0:ℝ) < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hc0 : (0:ℝ) < c := by linarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = c * Real.log T := ⟨_, rfl⟩
  have hk : 0 < k := by rw [hkdef]; exact mul_pos hc0 hL
  have hrw : ∀ α : ℝ, T ^ (-(c * α)) = Real.exp (-(k * α)) := by
    intro α
    rw [Real.rpow_def_of_pos hT0, hkdef]
    congr 1
    ring
  simp only [hrw]
  have hInt : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun α => Real.exp (-(k * α)) * |g α|) volume a b :=
    fun a b ha hb => expWeightIntervalIntegrable hg hk.le ha hb
  have hsplit : (∫ α in (0:ℝ)..1, Real.exp (-(k * α)) * |g α|) =
      (∫ α in (0:ℝ)..η, Real.exp (-(k * α)) * |g α|) +
        (∫ α in η..1, Real.exp (-(k * α)) * |g α|) :=
    (integral_add_adjacent_intervals (hInt 0 η le_rfl hη0.le)
      (hInt η 1 hη0.le zero_le_one)).symm
  have hb1 : (∫ α in (0:ℝ)..η, Real.exp (-(k * α)) * |g α|) ≤ M / Real.log T := by
    have step1 : (∫ α in (0:ℝ)..η, Real.exp (-(k * α)) * |g α|)
        ≤ ∫ α in (0:ℝ)..η, M * Real.exp (-(k * α)) := by
      refine integral_mono_ae_restrict hη0.le (hInt 0 η le_rfl hη0.le)
        (Continuous.intervalIntegrable (by fun_prop) 0 η) ?_
      filter_upwards [ae_restrict_of_ae hbdd, ae_restrict_mem measurableSet_Icc] with α hα hmem
      have h0 : 0 ≤ α := hmem.1
      have hlt : |α| < δ := by
        rw [abs_of_nonneg h0]; exact lt_of_le_of_lt hmem.2 hηδ
      have hgM : |g α| ≤ M := hα hlt
      calc Real.exp (-(k * α)) * |g α| ≤ Real.exp (-(k * α)) * M :=
            mul_le_mul_of_nonneg_left hgM (Real.exp_pos _).le
        _ = M * Real.exp (-(k * α)) := by ring
    have step2 : (∫ α in (0:ℝ)..η, M * Real.exp (-(k * α))) ≤ M / Real.log T := by
      rw [intervalIntegral.integral_const_mul]
      have hEx : (∫ α in (0:ℝ)..η, Real.exp (-(k * α))) ≤ 1 / k :=
        expWeightIntegralExpLe hk
      have hstep : M * (∫ α in (0:ℝ)..η, Real.exp (-(k * α))) ≤ M * (1 / k) :=
        mul_le_mul_of_nonneg_left hEx hM.le
      have hfin : M * (1 / k) ≤ M / Real.log T := by
        rw [mul_one_div, div_le_div_iff₀ hk hL, hkdef]
        nlinarith [mul_nonneg (mul_nonneg hM.le hL.le) (sub_nonneg.2 hc)]
      linarith
    linarith
  have hb2 : (∫ α in η..1, Real.exp (-(k * α)) * |g α|)
      ≤ ((∫ α, |g α|) / η) / Real.log T := by
    have step1 : (∫ α in η..1, Real.exp (-(k * α)) * |g α|)
        ≤ ∫ α in η..1, Real.exp (-(k * η)) * |g α| := by
      refine integral_mono_on hη1 (hInt η 1 hη0.le zero_le_one)
        (hg.abs.intervalIntegrable.const_mul _) ?_
      intro α hmem
      have hle : -(k * α) ≤ -(k * η) := by nlinarith [hmem.1]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hle) (abs_nonneg _)
    have step2 : (∫ α in η..1, Real.exp (-(k * η)) * |g α|)
        = Real.exp (-(k * η)) * ∫ α in η..1, |g α| :=
      intervalIntegral.integral_const_mul _ _
    have step3 : (∫ α in η..1, |g α|) ≤ ∫ α, |g α| := by
      rw [intervalIntegral.integral_of_le hη1]
      exact setIntegral_le_integral hg.abs (Filter.Eventually.of_forall fun α => abs_nonneg _)
    have step4 : Real.exp (-(k * η)) ≤ 1 / (η * Real.log T) := by
      have hx : 0 < η * Real.log T := mul_pos hη0 hL
      have h1 : η * Real.log T ≤ Real.exp (k * η) := by
        have h2 : η * Real.log T ≤ k * η := by rw [hkdef]; nlinarith
        have h3 := Real.add_one_le_exp (k * η)
        linarith
      have h4 : Real.exp (-(k * η)) = 1 / Real.exp (k * η) := by
        rw [Real.exp_neg, one_div]
      rw [h4]
      exact one_div_le_one_div_of_le hx h1
    have step5 : Real.exp (-(k * η)) * (∫ α in η..1, |g α|)
        ≤ Real.exp (-(k * η)) * ∫ α, |g α| :=
      mul_le_mul_of_nonneg_left step3 (Real.exp_pos _).le
    have step6 : Real.exp (-(k * η)) * (∫ α, |g α|)
        ≤ (1 / (η * Real.log T)) * ∫ α, |g α| :=
      mul_le_mul_of_nonneg_right step4 hI0
    have step7 : (1 / (η * Real.log T)) * (∫ α, |g α|)
        = ((∫ α, |g α|) / η) / Real.log T := by
      field_simp
    rw [step2] at step1
    linarith
  rw [hsplit]
  have hsum : M / Real.log T + ((∫ α, |g α|) / η) / Real.log T
      = (M + (∫ α, |g α|) / η) / Real.log T := by ring
  linarith

/-- The exact value of the elementary integral `∫_0^x T^{-2α} dα = (1 - T^{-2x}) / (2 log T)`,
valid for every `T > 1`. -/
private lemma integral_rpow_neg_two_mul (T x : ℝ) (hT : 1 < T) :
    ∫ α in (0:ℝ)..x, T ^ (-(2 * α)) = (1 - T ^ (-(2 * x))) / (2 * Real.log T) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hc : -(2 * Real.log T) ≠ 0 := by intro h; nlinarith [h]
  have key : ∀ α : ℝ, T ^ (-(2 * α)) = Real.exp (-(2 * Real.log T) * α) := by
    intro α
    rw [Real.rpow_def_of_pos hT0]
    ring_nf
  simp only [key]
  rw [intervalIntegral.integral_comp_mul_left Real.exp hc, integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

/-- If `g` is integrable and `T ≥ 1`, then `α ↦ T^{-2α} * g α` is interval integrable between any
two nonnegative endpoints, the weight being bounded by `1` there. -/
private lemma intervalIntegrable_rpow_mul {g : ℝ → ℝ} (hg : MeasureTheory.Integrable g)
    {T : ℝ} (hT : 1 ≤ T) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun α => T ^ (-(2 * α)) * g α) volume a b := by
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun α : ℝ => T ^ (-(2 * α)))
      (volume.restrict (Set.uIcc a b)) := by
    apply Continuous.aestronglyMeasurable
    have hkey : (fun α : ℝ => T ^ (-(2 * α))) = fun α : ℝ => Real.exp (Real.log T * (-(2 * α))) :=
      funext fun α => Real.rpow_def_of_pos hT0 _
    rw [hkey]
    fun_prop
  refine (hg.integrableOn (s := Set.uIcc a b)).bdd_mul (c := 1) hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIcc] with α hα
  have h0 : 0 ≤ α := le_trans (le_inf ha hb) hα.1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hT0.le _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hT (by linarith)

/-- For every `δ > 0` there is a threshold `T₀ ≥ 3` beyond which `log log T ≥ 1` and
`log log T / log T < δ`. -/
private lemma exists_threshold_log_log {δ : ℝ} (hδ0 : 0 < δ) :
    ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      1 ≤ Real.log (Real.log T) ∧ Real.log (Real.log T) / Real.log T < δ := by
  have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (nhds 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun T : ℝ => Real.log (Real.log T) / Real.log T) atTop (nhds 0) :=
    h1.comp Real.tendsto_log_atTop
  have e1 : ∀ᶠ T : ℝ in atTop, Real.log (Real.log T) / Real.log T < δ :=
    h2.eventually_lt_const hδ0
  have e2 : ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log (Real.log T) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  obtain ⟨T₁, hT₁⟩ := ((e1.and e2).and (eventually_ge_atTop (3:ℝ))).exists_forall_of_atTop
  refine ⟨max 3 T₁, le_max_left _ _, fun T hT => ?_⟩
  obtain ⟨⟨hd, hlog⟩, -⟩ := hT₁ T (le_trans (le_max_right _ _) hT)
  exact ⟨hlog, hd⟩

/-- Let `1 < L`, `1 ≤ log L`, `A = log L / L > 0`, `K > 0` and `G ≥ 0`. If `2 L W = 1 - L⁻²`,
`I = g0 W + P + Q`, `|P| ≤ K A W` and `|Q| ≤ L⁻² G`, then `|2 L I - g0| ≤ (|g0| + K + 2 G) A`. -/
private lemma abs_sub_le_of_split {g0 K A L W P Q I G : ℝ}
    (hL1 : 1 < L) (hA0 : 0 < A) (hK : 0 < K) (hG0 : 0 ≤ G)
    (hlogL : 1 ≤ Real.log L) (hAdef : A = Real.log L / L)
    (hW : 2 * L * W = 1 - (L ^ 2)⁻¹) (hI : I = g0 * W + P + Q)
    (hPb : |P| ≤ K * A * W) (hQb : |Q| ≤ (L ^ 2)⁻¹ * G) :
    |2 * L * I - g0| ≤ (|g0| + K + 2 * G) * A := by
  have hL0 : (0:ℝ) < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hEinv : (0:ℝ) ≤ (L ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg L)
  have hLinv : 0 < L⁻¹ := inv_pos.mpr hL0
  have hLc : L * L⁻¹ = 1 := mul_inv_cancel₀ hLne
  have hinvL : L⁻¹ ≤ A := by rw [hAdef, div_eq_mul_inv]; nlinarith
  have h4 : L⁻¹ ≤ 1 := by nlinarith
  have hinvA : (L ^ 2)⁻¹ ≤ A := by
    have h1 : (L ^ 2)⁻¹ = L⁻¹ * L⁻¹ := by rw [sq, mul_inv]
    rw [h1]; nlinarith
  have h2L : 2 * L * (L ^ 2)⁻¹ ≤ 2 * A := by
    have h1 : L * (L ^ 2)⁻¹ = L⁻¹ := by
      rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hLne, one_mul]
    linarith
  have b1 : |g0| * (L ^ 2)⁻¹ ≤ |g0| * A := mul_le_mul_of_nonneg_left hinvA (abs_nonneg _)
  have b2 : 2 * L * |P| ≤ K * A := by
    have h1 : 2 * L * |P| ≤ 2 * L * (K * A * W) := mul_le_mul_of_nonneg_left hPb (by linarith)
    have h2 : 2 * L * (K * A * W) = K * A * (1 - (L ^ 2)⁻¹) := by
      have h : 2 * L * (K * A * W) = K * A * (2 * L * W) := by ring
      rw [h, hW]
    linarith [mul_nonneg (mul_nonneg hK.le hA0.le) hEinv]
  have b3 : 2 * L * |Q| ≤ 2 * A * G := by
    have h1 : 2 * L * |Q| ≤ 2 * L * ((L ^ 2)⁻¹ * G) :=
      mul_le_mul_of_nonneg_left hQb (by linarith)
    have h3 : 2 * L * (L ^ 2)⁻¹ * G ≤ 2 * A * G := mul_le_mul_of_nonneg_right h2L hG0
    linarith
  have hfin : |2 * L * I - g0| ≤ |g0| * (L ^ 2)⁻¹ + 2 * L * |P| + 2 * L * |Q| := by
    have heq : 2 * L * I - g0 = -(g0 * (L ^ 2)⁻¹) + 2 * L * P + 2 * L * Q := by
      rw [hI]; linear_combination g0 * hW
    rw [heq]
    have t1 := abs_add_le (-(g0 * (L ^ 2)⁻¹) + 2 * L * P) (2 * L * Q)
    have t2 := abs_add_le (-(g0 * (L ^ 2)⁻¹)) (2 * L * P)
    have t3 : |(-(g0 * (L ^ 2)⁻¹))| = |g0| * (L ^ 2)⁻¹ := by
      rw [abs_neg, abs_mul, abs_of_nonneg hEinv]
    have t4 : |2 * L * P| = 2 * L * |P| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * L)]
    have t5 : |2 * L * Q| = 2 * L * |Q| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * L)]
    linarith
  linarith

/-- **Main-term integral estimate.**  Let `g : ℝ → ℝ` be integrable and Lipschitz at the origin
in the weak sense that `|g α - g 0| ≤ K * |α|` whenever `|α| < δ`, where `K > 0` and
`0 < δ ≤ 1`.  Then `2 * log T * ∫_0^1 T^{-2α} * g α dα` approximates `g 0` with the explicit
rate `log log T / log T`: there are `T₀ ≥ 3` and `C > 0` such that for every `T ≥ T₀`,
`|2 * log T * ∫_0^1 T^{-2α} * g α dα - g 0| ≤ C * (log log T / log T)`. -/
@[zz_tag "lem_main_term_integral"]
theorem exists_abs_integral_rpow_neg_two_mul_sub_le {g : ℝ → ℝ} {K δ : ℝ}
    (hg : MeasureTheory.Integrable g) (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hlip : ∀ α : ℝ, |α| < δ → |g α - g 0| ≤ K * |α|) :
    ∃ T₀ ≥ 3, ∃ C > 0, ∀ T : ℝ, T₀ ≤ T →
      |2 * Real.log T * (∫ α in (0:ℝ)..1, T ^ (-(2 * α)) * g α) - g 0|
        ≤ C * (Real.log (Real.log T) / Real.log T) := by
  obtain ⟨T₀, hT₀3, hT₀⟩ := exists_threshold_log_log hδ0
  have hG0 : 0 ≤ ∫ α, |g α| := integral_nonneg fun α => abs_nonneg _
  refine ⟨T₀, hT₀3, |g 0| + K + 2 * ∫ α, |g α|, by linarith [abs_nonneg (g 0)], fun T hT => ?_⟩
  have hT3 : (3:ℝ) ≤ T := le_trans hT₀3 hT
  have hT1 : (1:ℝ) < T := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hL0 : 0 < Real.log T := Real.log_pos hT1
  have hLne : Real.log T ≠ 0 := ne_of_gt hL0
  obtain ⟨hlogL, hAd⟩ := hT₀ T hT
  have hL1 : 1 < Real.log T := by
    rcases le_or_gt (Real.log T) 1 with hc | hc
    · have := Real.log_nonpos hL0.le hc
      linarith
    · exact hc
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Real.log (Real.log T) / Real.log T := ⟨_, rfl⟩
  rw [← hAdef] at hAd ⊢
  have hA0 : 0 < A := by rw [hAdef]; exact div_pos (by linarith) hL0
  have hA1 : A < 1 := lt_of_lt_of_le hAd hδ1
  have hEinv : (0:ℝ) ≤ (Real.log T ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hEq : T ^ (-(2 * A)) = (Real.log T ^ 2)⁻¹ := by
    rw [Real.rpow_def_of_pos hT0]
    have h : Real.log T * (-(2 * A)) = -Real.log (Real.log T) + -Real.log (Real.log T) := by
      rw [hAdef]; field_simp; ring
    rw [h]
    simp only [Real.exp_add, Real.exp_neg, Real.exp_log hL0]
    ring
  have hwcont : Continuous (fun α : ℝ => T ^ (-(2 * α))) := by
    have h : (fun α : ℝ => T ^ (-(2 * α))) = fun α : ℝ => Real.exp (Real.log T * (-(2 * α))) :=
      funext fun α => Real.rpow_def_of_pos hT0 _
    rw [h]; fun_prop
  have hi0A : IntervalIntegrable (fun α => T ^ (-(2 * α)) * g α) volume 0 A :=
    intervalIntegrable_rpow_mul hg hT1.le le_rfl hA0.le
  have hiA1 : IntervalIntegrable (fun α => T ^ (-(2 * α)) * g α) volume A 1 :=
    intervalIntegrable_rpow_mul hg hT1.le hA0.le zero_le_one
  have hiC : IntervalIntegrable (fun α : ℝ => g 0 * T ^ (-(2 * α))) volume 0 A :=
    (hwcont.intervalIntegrable 0 A).const_mul (g 0)
  have hW : 2 * Real.log T * (∫ α in (0:ℝ)..A, T ^ (-(2 * α))) = 1 - (Real.log T ^ 2)⁻¹ := by
    rw [integral_rpow_neg_two_mul T A hT1, hEq]
    field_simp
  have hPsplit : (∫ α in (0:ℝ)..A, T ^ (-(2 * α)) * (g α - g 0))
      = (∫ α in (0:ℝ)..A, T ^ (-(2 * α)) * g α)
        - g 0 * ∫ α in (0:ℝ)..A, T ^ (-(2 * α)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi0A hiC]
    exact intervalIntegral.integral_congr fun α _ => by ring
  have hI : (∫ α in (0:ℝ)..1, T ^ (-(2 * α)) * g α)
      = g 0 * (∫ α in (0:ℝ)..A, T ^ (-(2 * α)))
          + (∫ α in (0:ℝ)..A, T ^ (-(2 * α)) * (g α - g 0))
        + ∫ α in A..1, T ^ (-(2 * α)) * g α := by
    rw [hPsplit, ← intervalIntegral.integral_add_adjacent_intervals hi0A hiA1]
    ring
  have hptwP : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0:ℝ) A →
      ‖T ^ (-(2 * t)) * (g t - g 0)‖ ≤ K * A * T ^ (-(2 * t)) := by
    filter_upwards with t ht
    have ht0 : 0 < t := ht.1
    have htA : t ≤ A := ht.2
    have hta : |t| = t := abs_of_pos ht0
    have h1 : |g t - g 0| ≤ K * A := by
      have h2 := hlip t (by rw [hta]; linarith)
      rw [hta] at h2
      nlinarith
    have hw0 : (0:ℝ) ≤ T ^ (-(2 * t)) := Real.rpow_nonneg hT0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    nlinarith [mul_le_mul_of_nonneg_left h1 hw0]
  have hPb := intervalIntegral.norm_integral_le_of_norm_le hA0.le hptwP
    ((hwcont.intervalIntegrable 0 A).const_mul (K * A))
  rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at hPb
  have hptwQ : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc A 1 →
      ‖T ^ (-(2 * t)) * g t‖ ≤ (Real.log T ^ 2)⁻¹ * |g t| := by
    filter_upwards with t ht
    have hAt : A ≤ t := ht.1.le
    have hwle : T ^ (-(2 * t)) ≤ (Real.log T ^ 2)⁻¹ := by
      rw [← hEq]
      exact Real.rpow_le_rpow_of_exponent_le hT1.le (by linarith)
    have hw0 : (0:ℝ) ≤ T ^ (-(2 * t)) := Real.rpow_nonneg hT0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right hwle (abs_nonneg _)
  have hQb := intervalIntegral.norm_integral_le_of_norm_le hA1.le hptwQ
    ((hg.abs.intervalIntegrable).const_mul (Real.log T ^ 2)⁻¹)
  rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at hQb
  have hGb : (∫ α in A..1, |g α|) ≤ ∫ α, |g α| := by
    rw [intervalIntegral.integral_of_le hA1.le]
    exact MeasureTheory.setIntegral_le_integral hg.abs
      (Filter.Eventually.of_forall fun α => abs_nonneg _)
  have hQb2 : |∫ α in A..1, T ^ (-(2 * α)) * g α| ≤ (Real.log T ^ 2)⁻¹ * ∫ α, |g α| :=
    hQb.trans (mul_le_mul_of_nonneg_left hGb hEinv)
  exact abs_sub_le_of_split hL1 hA0 hK hG0 hlogL hAdef hW hI hPb hQb2

/-- The function `t ↦ (t + 2) * (log (t + 2) ^ 2 - 2 * log (t + 2) + 2)` is an antiderivative
of `t ↦ log (t + 2) ^ 2` at every point `t` with `t + 2 ≠ 0`. -/
private lemma hasDerivAt_log_sq_antideriv {t : ℝ} (ht : t + 2 ≠ 0) :
    HasDerivAt (fun x : ℝ => (x + 2) * (Real.log (x + 2) ^ 2 - 2 * Real.log (x + 2) + 2))
      (Real.log (t + 2) ^ 2) t := by
  have hid : HasDerivAt (fun x : ℝ => x + 2) 1 t := (hasDerivAt_id t).add_const 2
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x + 2)) (1 / (t + 2)) t := hid.log ht
  have hinner : HasDerivAt (fun x : ℝ => Real.log (x + 2) ^ 2 - 2 * Real.log (x + 2) + 2)
      (2 * Real.log (t + 2) ^ 1 * (1 / (t + 2)) - 2 * (1 / (t + 2))) t :=
    ((hlog.pow 2).sub (hlog.const_mul 2)).add_const 2
  have h : HasDerivAt (fun x : ℝ => (x + 2) * (Real.log (x + 2) ^ 2 - 2 * Real.log (x + 2) + 2))
      (1 * (Real.log (t + 2) ^ 2 - 2 * Real.log (t + 2) + 2)
        + (t + 2) * (2 * Real.log (t + 2) ^ 1 * (1 / (t + 2)) - 2 * (1 / (t + 2)))) t :=
    hid.mul hinner
  have key : 1 * (Real.log (t + 2) ^ 2 - 2 * Real.log (t + 2) + 2)
      + (t + 2) * (2 * Real.log (t + 2) ^ 1 * (1 / (t + 2)) - 2 * (1 / (t + 2)))
      = Real.log (t + 2) ^ 2 := by
    field_simp
    ring
  rw [key] at h
  exact h

/-- The map `t ↦ log (t + 2) ^ 2` is continuous on any set of nonnegative reals. -/
private lemma continuousOn_log_sq {s : Set ℝ} (hs : ∀ t ∈ s, (0 : ℝ) ≤ t) :
    ContinuousOn (fun t : ℝ => Real.log (t + 2) ^ 2) s := by
  refine ContinuousOn.pow (ContinuousOn.log (by fun_prop) ?_) 2
  intro t htm
  have := hs t htm
  linarith

/-- There is an absolute constant `C > 0` such that for all `T ≥ 3` the integral of
`log (|t| + 2) ^ 2` over `[0, T]` differs from `T * log T ^ 2` by at most `C * T * log T`. -/
@[zz_tag "lem_log_mean_square"]
theorem exists_abs_integral_log_sq_sub_le :
    ∃ C > 0, ∀ T : ℝ, 3 ≤ T →
      |(∫ t in (0:ℝ)..T, Real.log (|t| + 2) ^ 2) - T * Real.log T ^ 2| ≤ C * T * Real.log T := by
  refine ⟨100, by norm_num, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have huIcc : Set.uIcc (0 : ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hT0.le
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) T, (0 : ℝ) ≤ t := by
    intro t ht
    rw [huIcc] at ht
    exact ht.1
  have hcongr : (∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2)
      = ∫ t in (0 : ℝ)..T, Real.log (t + 2) ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [abs_of_nonneg (hmem t ht)]
  have hint : (∫ t in (0 : ℝ)..T, Real.log (t + 2) ^ 2)
      = (T + 2) * (Real.log (T + 2) ^ 2 - 2 * Real.log (T + 2) + 2)
        - 2 * (Real.log 2 ^ 2 - 2 * Real.log 2 + 2) := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun x : ℝ => (x + 2) * (Real.log (x + 2) ^ 2 - 2 * Real.log (x + 2) + 2))
          (Real.log (t + 2) ^ 2) t := by
      intro t ht
      have := hmem t ht
      exact hasDerivAt_log_sq_antideriv (by linarith)
    have hintble :
        IntervalIntegrable (fun t : ℝ => Real.log (t + 2) ^ 2) MeasureTheory.volume 0 T :=
      (continuousOn_log_sq hmem).intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintble]
    norm_num
  rw [hcongr, hint]
  set L := Real.log T with hL
  set a := Real.log (T + 2) with ha
  have hL1 : 1 ≤ L := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    have : Real.log 3 ≤ L := Real.log_le_log (by norm_num) hT
    linarith
  have hLa : L ≤ a := Real.log_le_log hT0 (by linarith)
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have ha2L : a ≤ 2 * L := by
    have h1 : T + 2 ≤ T ^ 2 := by nlinarith
    have h2 : a ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hTdiff : T * (a - L) ≤ 2 := by
    have hpos : (0 : ℝ) < (T + 2) / T := by positivity
    have h1 : Real.log ((T + 2) / T) ≤ (T + 2) / T - 1 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by linarith) (ne_of_gt hT0)] at h1
    have h2 : (T + 2) / T - 1 = 2 / T := by
      field_simp
      ring
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hT0.le
    rw [mul_div_cancel₀ _ (ne_of_gt hT0)] at h3
    rw [← hL, ← ha] at h3
    linarith
  have hLT : L ≤ T := by
    have h := Real.log_le_sub_one_of_pos hT0
    rw [← hL] at h
    linarith
  have hlog2a : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2b : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hsq : L ^ 2 ≤ a ^ 2 := by nlinarith
  have hcubic0 : (0 : ℝ) ≤ T * a ^ 2 - T * L ^ 2 := by nlinarith
  have hcubic : T * a ^ 2 - T * L ^ 2 ≤ 6 * L := by
    have hfac : T * a ^ 2 - T * L ^ 2 = T * (a - L) * (a + L) := by ring
    have h1 : (0 : ℝ) ≤ a + L := by linarith
    have h2 : T * (a - L) * (a + L) ≤ 2 * (a + L) := mul_le_mul_of_nonneg_right hTdiff h1
    rw [hfac]
    linarith
  have hLsq : L ^ 2 ≤ T * L := by nlinarith
  have hTa : T * a ≤ 2 * (T * L) := by nlinarith
  have hTa0 : (0 : ℝ) ≤ T * a := mul_nonneg hT0.le ha0
  have hTL : (1 : ℝ) ≤ T * L := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [hcubic, hcubic0, hLsq, hTa, hTa0, ha0, hTL, hlog2a, hlog2b,
    sq_nonneg (Real.log 2), ha2L, hLa, hL1, hLT, hT0]

end ZetaZeros
