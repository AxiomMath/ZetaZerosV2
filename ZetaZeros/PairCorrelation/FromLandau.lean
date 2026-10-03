/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.PairCorrelation.MeanSquare
public import ZetaZeros.Landau.Contour
public import ZetaZeros.Landau.Symmetrisation
public import ZetaZeros.PairCorrelation.Formula

/-!
# The pair-correlation formula

This file proves the unconditional pair-correlation formula `ZetaZeros.PairCorrelation`, together
with the intermediate results on which it rests, from Landau's explicit formula
`ZetaZeros.landauTruncatedLimit`.

The chain of implications is:

* `ZetaZeros.landauSymmetrisedFormula_of_truncatedLimit` turns the limit of symmetric partial sums
  in Landau's formula into `ZetaZeros.LandauSymmetrisedFormula`, an absolutely convergent identity.
  The unpaired family of terms is not summable, so the symmetrisation is necessary.
* `ZetaZeros.exists_abs_zeroSideMeanSquare_sub_sub_le` evaluates the mean square of the sum over
  zeros, with a five-term error whose fifth term is `(T/x)^{1/2} log²T`.
* `ZetaZeros.pairCorrelation_of_margin` deduces the asymptotic of `F_T` and the pair-correlation
  formula for every `ZetaZeros.IsPairTestFunction`.

## Main results

* `ZetaZeros.pairCorrelationFormula`: the unconditional pair-correlation formula
  `ZetaZeros.PairCorrelation`.
* `ZetaZeros.landauSymmetrisedFormula`: the symmetrised Landau formula.
* `ZetaZeros.montgomeryExplicit`: Montgomery's explicit-formula bound for `x > 1` not a prime
  power.
* `ZetaZeros.explicitAllX`: the same bound for every `x ≥ 1`.
* `ZetaZeros.lEvaluation`: the evaluation of the mean square `L (x, T)`.
* `ZetaZeros.fAsymptotic`: the asymptotic of `F_T (α)` on `0 ≤ α ≤ 1 - ε`.
* `ZetaZeros.pairCorrelationSumAsymptotic`: the pair-correlation formula for a single test
  function, with its hypotheses stated individually.
-/

@[expose] public section

namespace ZetaZeros

/-- **The unconditional pair-correlation formula.** For every admissible test function `f`, the
pair-correlation sum of `f` divided by `(T / 2π) log T` differs from `pairMainTerm f` by
`O (1 / √log T)`. -/
@[zz_tag "lem_bgst"]
theorem pairCorrelationFormula : PairCorrelation :=
  pairCorrelation_of_margin
    (exists_abs_zeroSideMeanSquare_sub_sub_le
      (landauSymmetrisedFormula_of_truncatedLimit landauTruncatedLimit))

/-! ### The intermediate results -/

/-- The symmetrised Landau formula. -/
@[zz_tag "lem_landau_combined"]
theorem landauSymmetrisedFormula : LandauSymmetrisedFormula :=
  landauSymmetrisedFormula_of_truncatedLimit landauTruncatedLimit

/-- **Montgomery's explicit formula.** For `x > 1` not a prime power and every real `t`,
`ℓ (x, t) + D (x, t) = log (|t| + 2) / x + O (1 / x + √x / (1 + t²))`. -/
@[zz_tag "lem_montgomery_explicit"]
theorem montgomeryExplicit :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → NotPrimePowerReal x → ∀ t : ℝ,
      ‖zeroSide x t + weightedPrimeSum x t - ((Real.log (|t| + 2) / x : ℝ) : ℂ)‖
        ≤ C * (1 / x + Real.sqrt x / (1 + t ^ 2)) :=
  exists_norm_zeroSide_add_weightedPrimeSum_sub_div_le
    landauSymmetrisedFormula

/-- **Montgomery's explicit formula for every `x ≥ 1`.** For `x ≥ 1`, prime powers included, and
every real `t`, `ℓ (x, t) + D (x, t) = log (|t| + 2) / x + O (1 / x + √x / (1 + t²))`. -/
@[zz_tag "lem_explicit_all_x"]
theorem explicitAllX :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ t : ℝ,
      ‖zeroSide x t + weightedPrimeSum x t - ((Real.log (|t| + 2) / x : ℝ) : ℂ)‖
        ≤ C * (1 / x + Real.sqrt x / (1 + t ^ 2)) :=
  exists_norm_zeroSide_add_weightedPrimeSum_sub_div_le_of_one_le
    landauSymmetrisedFormula

/-- **The evaluation of the mean square.** For `1 ≤ x ≤ T` and `T ≥ 3`, the difference
`L (x, T) - T log x - T log²T / x²` is bounded by a constant times
`T + x log²T + T log T / x² + T (log T)^{3/2} / x + (T/x)^{1/2} log²T`. -/
@[zz_tag "lem_L_evaluation"]
theorem lEvaluation :
    ∃ C > 0, ∀ x T : ℝ, 1 ≤ x → x ≤ T → 3 ≤ T →
      |zeroSideMeanSquare x T - T * Real.log x - T * Real.log T ^ 2 / x ^ 2|
        ≤ C * (T + x * Real.log T ^ 2 + T * Real.log T / x ^ 2
            + T * Real.sqrt (Real.log T) ^ 3 / x
            + Real.sqrt (T / x) * Real.log T ^ 2) :=
  exists_abs_zeroSideMeanSquare_sub_sub_le landauSymmetrisedFormula

/-- **The asymptotic of the normalised pair-correlation function.** For `T ≥ 3`, `0 < ε < 1` and
`0 ≤ α ≤ 1 - ε`, the difference `F_T (α) - T^{-2α} log T - α` is bounded in modulus by a constant
times `T^{-2α} + 1 / log T + T^{-α} √log T + T^{α - 1} log²T + T^{-(α + 1)/2} log T`. -/
@[zz_tag "lem_F_asymptotic"]
theorem fAsymptotic :
    ∃ C > 0, ∀ T : ℝ, 3 ≤ T → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 - ε →
      ‖normalizedPairCorrelation T α - ((T ^ (-(2 * α)) * Real.log T + α : ℝ) : ℂ)‖
        ≤ C * (T ^ (-(2 * α)) + 1 / Real.log T + T ^ (-α) * Real.sqrt (Real.log T)
            + T ^ (α - 1) * Real.log T ^ 2
            + T ^ (-((α + 1) / 2)) * Real.log T) :=
  exists_abs_normalizedPairCorrelation_sub_le
    (exists_abs_zeroSideMeanSquare_sub_sub_le landauSymmetrisedFormula)

/-- **The pair-correlation formula for a single test function.** Let `g` be integrable and even,
with `|g α - g 0| ≤ K |α|` for `|α| < δ`, and vanishing on `1 - ε ≤ |α|` for some `0 < ε < 1`.
Then for all sufficiently large `T`, the pair-correlation sum of `g` divided by `(T / 2π) log T`
differs from `pairMainTerm g` by `O (1 / √log T)`. -/
theorem pairCorrelationSumAsymptotic {g : ℝ → ℝ} {K δ ε : ℝ} (hg : MeasureTheory.Integrable g)
    (heven : ∀ α : ℝ, g (-α) = g α) (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hlip : ∀ α : ℝ, |α| < δ → |g α - g 0| ≤ K * |α|)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hsupp : ∀ α : ℝ, 1 - ε ≤ |α| → g α = 0) :
    ∃ T₀ ≥ 3, ∃ C > 0, ∀ T : ℝ, T₀ ≤ T →
      ‖pairCorrelationSum g T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ) -
          ((pairMainTerm g : ℝ) : ℂ)‖ ≤ C / Real.sqrt (Real.log T) :=
  exists_norm_pairCorrelationSum_div_sub_le lEvaluation hg heven hK hδ0 hδ1 hlip hε0 hε1 hsupp

end ZetaZeros
