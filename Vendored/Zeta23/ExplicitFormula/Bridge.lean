/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ExplicitFormula/Bridge.lean

The two "all integrals absolutely convergent" side-facts of App. A [app:EF]:
  * `integrable_fourier_of_contDiff_two` : k ∈ C_c²(ℝ) ⇒ 𝓕 k ∈ L¹(ℝ)   (from [eq:hfbound], Zeta23/Poisson/PaperFT.lean);
  * `integrable_paperFT_mul_mu`          : k ∈ C_c²(ℝ) ⇒ h_k · μ ∈ L¹(ℝ)  (from [eq:hfbound] + H-Γ [eq:mufacts]);
and the clean bridge
  * `explicitFormulaPaper_of_lit` : EF_lit Z → GammaFacts → ExplicitFormulaPaper Z,
i.e. the literature-form explicit formula [eq:EFstd] (plus the Stirling facts for μ that PaperInputs already
carries) implies the paper's [prop:EF]/[eq:EF] exactly as Hypotheses.lean states it.
-/
import Zeta23.ExplicitFormula
import Zeta23.Hypotheses
import Zeta23.Poisson.PaperFT
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23
namespace EF

/-- A compactly supported function on ℝ is supported in some `[−Λ, Λ]`. -/
theorem exists_abs_le_of_hasCompactSupport {k : ℝ → ℂ} (hkc : HasCompactSupport k) :
    ∃ Λ : ℝ, ∀ u, k u ≠ 0 → |u| ≤ Λ := by
  obtain ⟨R, hR⟩ := hkc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun u hu => ?_⟩
  have := hR (subset_tsupport _ (Function.mem_support.mpr hu))
  simpa [Real.norm_eq_abs] using this

/-- [eq:hfbound] on the real line, both orders, in terms of Mathlib's `𝓕`:
`‖𝓕 k w‖ (1 + w²) ≤ ‖k‖₁ + ‖k''‖₁/(4π²)`. -/
theorem norm_fourier_mul_one_add_sq_le {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) {Λ : ℝ}
    (hΛ : ∀ u, k u ≠ 0 → |u| ≤ Λ) (w : ℝ) :
    ‖𝓕 k w‖ * (1 + w ^ 2)
      ≤ (∫ u, ‖k u‖) + (∫ u, ‖deriv (deriv k) u‖) / (4 * π ^ 2) := by
  have hkc : HasCompactSupport k := Zeta23.hasCompactSupport_of_support_subset_abs hΛ
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  have hdict : 𝓕 k w = paperFT k ((-(2 * π * w) : ℝ) : ℂ) := by
    rw [paperFT_ofReal_eq_fourier]; field_simp
  have h1 := Zeta23.norm_paperFT_le hki hΛ ((-(2 * π * w) : ℝ) : ℂ)
  have h2 := Zeta23.norm_paperFT_mul_sq_le hk hΛ ((-(2 * π * w) : ℝ) : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at h1 h2
  rw [hdict]
  have h2' : ‖paperFT k ((-(2 * π * w) : ℝ) : ℂ)‖ * w ^ 2
      ≤ (∫ u, ‖deriv (deriv k) u‖) / (4 * π ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖paperFT k ((-(2 * π * w) : ℝ) : ℂ)‖ * w ^ 2 * (4 * π ^ 2)
        = ‖paperFT k ((-(2 * π * w) : ℝ) : ℂ)‖ * (-(2 * π * w)) ^ 2 := by ring
      _ ≤ ∫ u, ‖deriv (deriv k) u‖ := h2
  calc ‖paperFT k ((-(2 * π * w) : ℝ) : ℂ)‖ * (1 + w ^ 2)
      = ‖paperFT k ((-(2 * π * w) : ℝ) : ℂ)‖ + ‖paperFT k ((-(2 * π * w) : ℝ) : ℂ)‖ * w ^ 2 := by ring
    _ ≤ _ := add_le_add h1 h2'

theorem continuous_fourier_of_integrable {k : ℝ → ℂ} (hki : Integrable k) : Continuous (𝓕 k) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_inner) hki

/-- `k ∈ C_c²(ℝ)` ⇒ `𝓕 k` integrable (App. A: "h(r) ≪_k (1+|r|)^{-2}"). -/
theorem integrable_fourier_of_contDiff_two {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) : Integrable (𝓕 k) := by
  obtain ⟨Λ, hΛ⟩ := exists_abs_le_of_hasCompactSupport hkc
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  set K : ℝ := (∫ u, ‖k u‖) + (∫ u, ‖deriv (deriv k) u‖) / (4 * π ^ 2)
  refine ((integrable_inv_one_add_sq.const_mul K).mono'
    (continuous_fourier_of_integrable hki).aestronglyMeasurable (Eventually.of_forall fun w => ?_))
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact norm_fourier_mul_one_add_sq_le hk hΛ w

/-- From H-Γ: `|μ(τ)| ≤ K₂ (1+|τ|)^{1/2}` for all τ (continuity on [−1,1]; Stirling [eq:mufacts]
`μ(τ) = (1/2π)log(|τ|/2π) + O(τ^{-2})` and `log x ≤ 2x^{1/2}` for |τ| ≥ 1). -/
theorem abs_mu_le_of_gammaFacts (hΓ : GammaFacts) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ τ : ℝ, |mu τ| ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := hΓ.stirling
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΓ.smooth.continuous.continuousOn (s := Icc (-1 : ℝ) 1))
  have hπ : 0 < 1 / (2 * π) := by positivity
  have hL0 : 0 ≤ (1 / (2 * π)) * |Real.log (2 * π)| := mul_nonneg hπ.le (abs_nonneg _)
  set K₂ : ℝ := max M 0 + |C| + (1 / (2 * π)) * |Real.log (2 * π)| + 1 / π with hK₂
  have hK₂nn : 0 ≤ K₂ := by
    have : 0 ≤ max M 0 := le_max_right _ _
    have : 0 ≤ 1 / π := by positivity
    positivity
  refine ⟨K₂, hK₂nn, fun τ => ?_⟩
  have hb1 : 1 ≤ (1 + |τ|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
  rcases le_or_gt |τ| 1 with hτ | hτ
  · -- |τ| ≤ 1: continuity bound
    have := hM τ (abs_le.mp hτ)
    rw [Real.norm_eq_abs] at this
    calc |mu τ| ≤ max M 0 := this.trans (le_max_left _ _)
      _ ≤ K₂ * 1 := by
        rw [mul_one, hK₂]
        have : 0 ≤ 1 / π := by positivity
        linarith [abs_nonneg C]
      _ ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := by gcongr
  · -- |τ| ≥ 1: Stirling
    have hτ1 : 1 ≤ |τ| := hτ.le
    have hst := hC τ hτ1
    have hsq : 1 ≤ τ ^ 2 := by rw [← sq_abs]; nlinarith
    have hCτ : C / τ ^ 2 ≤ |C| := by
      calc C / τ ^ 2 ≤ |C| / τ ^ 2 := by gcongr; exact le_abs_self C
        _ ≤ |C| := div_le_self (abs_nonneg C) hsq
    have hlog : |Real.log (|τ| / (2 * π))| ≤ Real.log |τ| + |Real.log (2 * π)| := by
      rw [Real.log_div (by positivity) (by positivity)]
      calc abs (Real.log |τ| - Real.log (2 * π))
          ≤ abs (Real.log |τ|) + |Real.log (2 * π)| := abs_sub _ _
        _ = Real.log |τ| + |Real.log (2 * π)| := by rw [abs_of_nonneg (Real.log_nonneg hτ1)]
    have hlog2 : Real.log |τ| ≤ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div (abs_nonneg τ) (by norm_num : (0 : ℝ) < 1 / 2)
      have hmono : |τ| ^ (1 / 2 : ℝ) ≤ (1 + |τ|) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg τ) (by linarith) (by norm_num)
      calc Real.log |τ| ≤ |τ| ^ (1 / 2 : ℝ) / (1 / 2) := this
        _ = 2 * |τ| ^ (1 / 2 : ℝ) := by ring
        _ ≤ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by gcongr
    have hmu : |mu τ| ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + |Real.log (2 * π)|) := by
      have htri : |mu τ| ≤ |mu τ - 1 / (2 * π) * Real.log (|τ| / (2 * π))|
          + |1 / (2 * π) * Real.log (|τ| / (2 * π))| := by
        have := abs_add_le (mu τ - 1 / (2 * π) * Real.log (|τ| / (2 * π)))
          (1 / (2 * π) * Real.log (|τ| / (2 * π)))
        rwa [sub_add_cancel] at this
      calc |mu τ| ≤ C / τ ^ 2 + |1 / (2 * π) * Real.log (|τ| / (2 * π))| := by linarith
        _ ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + |Real.log (2 * π)|) := by
          rw [abs_mul, abs_of_pos hπ]
          gcongr
    set b := (1 + |τ|) ^ (1 / 2 : ℝ) with hb
    calc |mu τ| ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + |Real.log (2 * π)|) := hmu
      _ ≤ |C| + (1 / (2 * π)) * (2 * b + |Real.log (2 * π)|) := by gcongr
      _ = (|C| + (1 / (2 * π)) * |Real.log (2 * π)|) * 1 + (1 / π) * b := by ring
      _ ≤ (|C| + (1 / (2 * π)) * |Real.log (2 * π)|) * b + (1 / π) * b := by gcongr
      _ = (|C| + (1 / (2 * π)) * |Real.log (2 * π)| + 1 / π) * b := by ring
      _ ≤ K₂ * b := by
        gcongr; rw [hK₂]; linarith [le_max_right M 0]

end EF
end Zeta23
