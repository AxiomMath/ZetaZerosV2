/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace ZetaZeros.Challenge

/-- **`prop_simple_real_lower`** (2.3). The number of real points of multiplicity one is at
least `2 ∑_{z ∈ 𝒵} 1 - ∑_{z, s ∈ 𝒵} K (z - s) ^ 2`. -/
theorem prop_simple_real_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty) :
    2 * (∑ z ∈ Z, (m z : ℝ))
        - (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ ((simpleRealPart Z m).card : ℝ) :=
  card_simpleRealPart_lower h hZ hZne

/-- **`prop_distinct_lower`** (2.4). The number of distinct points is at least
`(3/2) ∑_{z ∈ 𝒵} 1 - (1/2) ∑_{z, s ∈ 𝒵} K (z - s) ^ 2`. -/
theorem prop_distinct_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty) :
    (3 / 2 : ℝ) * (∑ z ∈ Z, (m z : ℝ))
        - (1 / 2 : ℝ) *
          (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ (Z.card : ℝ) :=
  card_lower h hZ hZne

/-- **`prop_simple_plus_real_lower`** (2.5). The number of simple points plus the number of real
points counted with multiplicity is at least `3 ∑_{z ∈ 𝒵} 1 - ∑_{z, s ∈ 𝒵} K (z - s) ^ 2`. -/
theorem prop_simple_plus_real_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty) :
    3 * (∑ z ∈ Z, (m z : ℝ))
        - (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ ((simplePart Z m).card : ℝ) + ∑ z ∈ allRealPart Z, (m z : ℝ) :=
  card_simplePart_add_realMass_lower h hZ hZne

/-- **`prop_simple_or_real_lower`** (2.6). If the second moment is at most `A ∑_{z ∈ 𝒵} 1` for
some `1 ≤ A < 2`, then the points that are simple or real (or both), counted with multiplicity,
number at least `(5 + 2√2 - 2A) / (3 + 2√2) ∑_{z ∈ 𝒵} 1`. -/
theorem prop_simple_or_real_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ} {A : ℝ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty)
    (hA₁ : 1 ≤ A) (hA₂ : A < 2)
    (hbound : (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ A * ∑ z ∈ Z, (m z : ℝ)) :
    (5 + 2 * Real.sqrt 2 - 2 * A) / (3 + 2 * Real.sqrt 2) * (∑ z ∈ Z, (m z : ℝ))
      ≤ ∑ z ∈ simpleOrRealPart Z m, (m z : ℝ) :=
  simpleOrRealMass_lower h hZ hZne hA₁ hA₂ hbound

/-- **`thm_simple`.** Beyond a height depending on `ε`, the proportion of non-trivial zeros
that are simple and lie on the critical line exceeds `C₀ - ε = 0.6725007037… - ε`. -/
theorem thm_simple (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - ε <
        (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  simple_proportion_lower hRvM hPC ε hε

/-- **`thm_distinct`.** Beyond a height depending on `ε`, the proportion of non-trivial zeros
that are distinct exceeds `C₁ - ε = 0.8362503518… - ε`. -/
theorem thm_distinct (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
  distinct_proportion_lower hRvM hPC ε hε

/-- **`thm_average`.** Beyond a height depending on `ε`, the average of the proportion of simple
zeros and the proportion of zeros on the critical line exceeds `C₁ - ε = 0.8362503518… - ε`. -/
theorem thm_average (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        ((simpleZeroCount T : ℝ) + (onLineCount T : ℝ)) / (2 * (zeroCount T : ℝ)) :=
  average_proportion_lower hRvM hPC ε hε

/-- **`thm_simple_or_critical`.** Beyond a height depending on `ε`, the proportion of non-trivial
zeros that are simple or lie on the critical line (or both) exceeds
`C₂ - ε = 0.8876200082… - ε`. -/
theorem thm_simple_or_critical (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
            / (3 + 2 * Real.sqrt 2) - ε <
        (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  simpleOrOnLine_proportion_lower hRvM hPC ε hε

/-- **`thm_simple_numeric`.** Beyond some height, more than `67.25%` of the non-trivial zeros of
the Riemann zeta function are simple and lie on the critical line. -/
theorem thm_simple_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.6725 < (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  simple_proportion_d4 hRvM hPC

/-- **`thm_distinct_numeric`.** Beyond some height, more than `83.625%` of the non-trivial zeros
of the Riemann zeta function are distinct. -/
theorem thm_distinct_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.83625 < (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
  distinct_proportion_d5 hRvM hPC

/-- **`thm_average_numeric`.** Beyond some height, the average of the proportion of simple zeros
and the proportion of zeros on the critical line exceeds `83.625%`. -/
theorem thm_average_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      0.83625 < ((simpleZeroCount T : ℝ) + (onLineCount T : ℝ)) / (2 * (zeroCount T : ℝ)) :=
  average_proportion_d5 hRvM hPC

/-- **`thm_simple_or_critical_numeric`.** Beyond some height, more than `88.76%` of the
non-trivial zeros of the Riemann zeta function are simple or lie on the critical line (or
both). -/
theorem thm_simple_or_critical_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.8876 < (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  simpleOrOnLine_proportion_d4 hRvM hPC

end ZetaZeros.Challenge
