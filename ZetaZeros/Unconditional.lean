/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math, Anthropic PBC
-/
import ZetaZeros.Main
import ZetaZeros.Zeta.RiemannVonMangoldt
import ZetaZeros.Unconditional.PairCorrelationFinal

/-!
# Unconditional zeta-zero bounds

This module discharges the two classical analytic inputs used by `ZetaZeros.Main`: the
Riemann--von Mangoldt zero-counting asymptotic and the unconditional pair-correlation theorem.
It then exposes assumption-free versions of all headline bounds.
-/

noncomputable section

namespace ZetaZeros.Unconditional

/-- The Riemann--von Mangoldt input used by the zeta-zero bounds. -/
theorem riemannVonMangoldt : RiemannVonMangoldt := by
  simpa only [RiemannVonMangoldt, zeroCount, nontrivialZeros,
    zeroMultiplicity, analyticOrderNatAt, Zeta23.Ncount, Zeta23.zerosIn,
    Zeta23.IsNontrivialZero, Zeta23.zeroMult, and_assoc] using
    RvM.ncount_asymptotic

/-- The unconditional pair-correlation input used by the zeta-zero bounds. -/
theorem pairCorrelation : PairCorrelation := by
  intro test htest
  rcases htest with ⟨heven, hintegrable, hsupported, hlipschitz⟩
  simpa only [PairCorrelation, pairCorrelationSum, pairMainTerm, fourierC, rescaledDiff,
    pairWeight, nontrivialZeros, zeroMultiplicity, analyticOrderNatAt,
    Zeta23.zerosIn, Zeta23.IsNontrivialZero, Zeta23.zeroMult,
    PairCorrelationProof.rawPairCorrelation, PairCorrelationProof.pairNormalization,
    PairCorrelationProof.finitePairKernel, and_assoc] using
    PairCorrelationProof.rawPairCorrelation_asymptotic
      test heven hintegrable hsupported hlipschitz

/-- Assumption-free version of `ZetaZeros.simple_proportion_lower`. -/
theorem simple_proportion_lower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - epsilon <
        (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  ZetaZeros.simple_proportion_lower riemannVonMangoldt pairCorrelation epsilon hepsilon

/-- Assumption-free version of `ZetaZeros.distinct_proportion_lower`. -/
theorem distinct_proportion_lower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - epsilon <
        (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
  ZetaZeros.distinct_proportion_lower riemannVonMangoldt pairCorrelation epsilon hepsilon

/-- Assumption-free version of `ZetaZeros.average_proportion_lower`. -/
theorem average_proportion_lower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - epsilon <
        ((simpleZeroCount T : ℝ) + (onLineCount T : ℝ)) / (2 * (zeroCount T : ℝ)) :=
  ZetaZeros.average_proportion_lower riemannVonMangoldt pairCorrelation epsilon hepsilon

/-- Assumption-free version of `ZetaZeros.simpleOrOnLine_proportion_lower`. -/
theorem simpleOrOnLine_proportion_lower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2)) /
            (3 + 2 * Real.sqrt 2) - epsilon <
        (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  ZetaZeros.simpleOrOnLine_proportion_lower
    riemannVonMangoldt pairCorrelation epsilon hepsilon

/-- More than `67.25%` of the non-trivial zeros are eventually simple and on the critical line. -/
theorem simple_proportion_d4 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.6725 < (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  ZetaZeros.simple_proportion_d4 riemannVonMangoldt pairCorrelation

/-- More than `83.625%` of the non-trivial zeros are eventually distinct. -/
theorem distinct_proportion_d5 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.83625 < (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
  ZetaZeros.distinct_proportion_d5 riemannVonMangoldt pairCorrelation

/-- The average of the simple-zero and on-line proportions eventually exceeds `83.625%`. -/
theorem average_proportion_d5 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      0.83625 < ((simpleZeroCount T : ℝ) + (onLineCount T : ℝ)) /
        (2 * (zeroCount T : ℝ)) :=
  ZetaZeros.average_proportion_d5 riemannVonMangoldt pairCorrelation

/-- More than `88.76%` of the non-trivial zeros are eventually simple or on the critical line. -/
theorem simpleOrOnLine_proportion_d4 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      0.8876 < (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  ZetaZeros.simpleOrOnLine_proportion_d4 riemannVonMangoldt pairCorrelation

end ZetaZeros.Unconditional
