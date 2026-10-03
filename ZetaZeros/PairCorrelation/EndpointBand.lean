/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.PairCorrelation.FromLandau
public import ZetaZeros.PairCorrelation.NonNegative

/-!
# Discarding the endpoint band by sign

`ZetaZeros.IsPairTestFunction` requires a test function to vanish on a neighbourhood of `±1`. This
file proves a one-sided form of the pair-correlation formula for weights `g` that are only required
to dominate an admissible `h` pointwise: since `F_T ≥ 0`
(`ZetaZeros.zero_le_normalizedPairCorrelation_re`) and `g - h ≥ 0`, the contribution of the band
near `±1` is non-negative and may be dropped. The conclusion is the lower bound
`pairMainTerm h - C / √log T ≤ (pairCorrelationSum g T / ((T / 2π) log T)).re`.

No upper bound holds in this generality: `g` may be arbitrarily large on the band
`1 - ε ≤ |α| ≤ 1` where `h` vanishes, and the pair-correlation sum of `g` grows with it.

## Main results

* `ZetaZeros.pairMainTerm_sub_le_pairCorrelationSum_div_re`: the lower bound above, for an
  integrable compactly supported `g ≥ h` with `F_T g` and `F_T h` integrable.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory

/-- An admissible test function vanishes off `[-1, 1]`: the margin clause gives an `ε > 0` with
`h` zero on `1 - ε ≤ |α|`, and `1 < |α|` implies `1 - ε < |α|`. -/
private theorem IsPairTestFunction.eq_zero_of_one_lt_abs {h : ℝ → ℝ} (hh : IsPairTestFunction h)
    {α : ℝ} (hα : 1 < |α|) : h α = 0 := by
  obtain ⟨-, -, ⟨ε, hε0, -, hzero⟩, -⟩ := hh
  exact hzero α (by linarith)

/-- **The pair-correlation lower bound for a weight that is only non-negative near `±1`.**
Let `h` be admissible and let `g ≥ h` be integrable and vanish off `[-R, R]`, with `F_T g` and
`F_T h` integrable for every `T`. Then for all sufficiently large `T`,
`pairMainTerm h - C / √log T ≤ re (pairCorrelationSum g T / ((T / 2π) log T))`. In particular `g`
need not vanish near `±1`. -/
theorem pairMainTerm_sub_le_pairCorrelationSum_div_re
    {g h : ℝ → ℝ} {R : ℝ} (hg : Integrable g) (hgsupp : ∀ α : ℝ, R < |α| → g α = 0)
    (hh : IsPairTestFunction h) (hle : ∀ α : ℝ, h α ≤ g α)
    (hIg : ∀ T : ℝ, Integrable fun α : ℝ => normalizedPairCorrelation T α * (g α : ℂ))
    (hIh : ∀ T : ℝ, Integrable fun α : ℝ => normalizedPairCorrelation T α * (h α : ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      pairMainTerm h - C / Real.sqrt (Real.log T)
        ≤ (pairCorrelationSum g T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ)).re := by
  have hhint : Integrable h := hh.2.1
  obtain ⟨C, hC, T₀, hbound⟩ := pairCorrelationFormula h hh
  refine ⟨C, hC, max T₀ 3, le_max_right _ _, fun T hT => ?_⟩
  have hT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT3 : (3 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT1 : (1 : ℝ) < T := by linarith
  have hQ : (0 : ℝ) < T / (2 * Real.pi) * Real.log T := by
    have hlog : 0 < Real.log T := Real.log_pos hT1
    have : (0 : ℝ) < T := by linarith
    positivity
  have hQne : ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hQ)
  have hgrep := pairCorrelationSum_eq_ofReal_integral hg hgsupp hT3
  have hhrep := pairCorrelationSum_eq_ofReal_integral hhint
    (fun α hα => hh.eq_zero_of_one_lt_abs hα) hT3
  have hgdiv : pairCorrelationSum g T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ)
      = ∫ α : ℝ, normalizedPairCorrelation T α * (g α : ℂ) := by
    rw [hgrep, mul_comm, mul_div_assoc, div_self hQne, mul_one]
  have hhdiv : pairCorrelationSum h T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ)
      = ∫ α : ℝ, normalizedPairCorrelation T α * (h α : ℂ) := by
    rw [hhrep, mul_comm, mul_div_assoc, div_self hQne, mul_one]
  have hmono : (∫ α : ℝ, normalizedPairCorrelation T α * (h α : ℂ)).re
      ≤ (∫ α : ℝ, normalizedPairCorrelation T α * (g α : ℂ)).re := by
    simp only [← RCLike.re_to_complex]
    rw [← integral_re (hIh T), ← integral_re (hIg T)]
    refine integral_mono ((hIh T).re) ((hIg T).re) fun α => ?_
    simp only [RCLike.re_to_complex]
    have hnn := zero_le_normalizedPairCorrelation_mul_re hT1 α (sub_nonneg.2 (hle α))
    have hsplit : normalizedPairCorrelation T α * ((g α - h α : ℝ) : ℂ)
        = normalizedPairCorrelation T α * (g α : ℂ)
          - normalizedPairCorrelation T α * (h α : ℂ) := by
      push_cast
      ring
    rw [hsplit, Complex.sub_re, sub_nonneg] at hnn
    exact hnn
  have hre : pairMainTerm h - C / Real.sqrt (Real.log T)
      ≤ (pairCorrelationSum h T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ)).re := by
    have hb := hbound T hT₀
    have hle' : |(pairCorrelationSum h T /
        ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ)).re - pairMainTerm h| ≤
        C / Real.sqrt (Real.log T) := by
      refine le_trans ?_ hb
      have : (pairCorrelationSum h T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ)
          - ((pairMainTerm h : ℝ) : ℂ)).re
          = (pairCorrelationSum h T /
              ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ)).re - pairMainTerm h := by
        rw [Complex.sub_re, Complex.ofReal_re]
      rw [← this]
      exact Complex.abs_re_le_norm _
    have := abs_le.1 hle'
    linarith [this.1]
  rw [hgdiv]
  rw [hhdiv] at hre
  linarith

end ZetaZeros
