/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Simple zeros, critical zeros and distinct zeros of the Riemann zeta function

Given two classical analytic inputs, four unconditional proportions of the non-trivial zeros:

* more than `67.25%` are simple **and** lie on the critical line;
* more than `83.625%` are distinct;
* more than `88.76%` are simple **or** lie on the critical line (or both);
* the average of the proportion of simple zeros and of critical zeros is at least `83.625%`.

Y. Lamzouri, *A new proof that more than `2/3` of the zeros of the Riemann zeta function are
simple and on the critical line*, **Theorem 1.1**.
-/

@[expose] public section

namespace ZetaZeros

/-! ## Counting the zeros

The multiplicity conventions follow the source and are **not** uniform, so read each definition:
`zeroCount`, `onLineCount` and `simpleOrOnLineCount` count with multiplicity, while
`simpleOnLineCount`, `simpleZeroCount` and `distinctZeroCount` are set cardinalities.
-/

/-- The non-trivial zeros of the Riemann zeta function with imaginary part in `(0, T]`: the
zeros lying in the critical strip `0 < re s < 1`, as a set, so without multiplicity.

The source widens the strip to `0 ≤ re s ≤ 1` in a footnote; the two agree, since zeta has no
zeros with `re s ∈ {0, 1}`, so the open strip is kept. -/
def nontrivialZeros (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- The multiplicity of `ρ` as a zero of the Riemann zeta function, i.e. its order of
vanishing there. -/
noncomputable def zeroMultiplicity (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- The number of non-trivial zeros with imaginary part in `(0, T]`, counted with multiplicity.
This is `N T` in the source. -/
noncomputable def zeroCount (T : ℝ) : ℕ := ∑ᶠ ρ ∈ nontrivialZeros T, zeroMultiplicity ρ

/-- The number of non-trivial zeros with imaginary part in `(0, T]` that are simple and lie on
the critical line `re s = 1/2`. This is `N₀ˢ T` in the source. -/
noncomputable def simpleOnLineCount (T : ℝ) : ℕ :=
  {ρ ∈ nontrivialZeros T | ρ.re = 1 / 2 ∧ zeroMultiplicity ρ = 1}.ncard

/-- The number of distinct non-trivial zeros with imaginary part in `(0, T]`. This is `N_d T`
in the source. -/
noncomputable def distinctZeroCount (T : ℝ) : ℕ := (nontrivialZeros T).ncard

/-- The number of non-trivial zeros with imaginary part in `(0, T]` lying on the critical line,
counted **with multiplicity**. This is `N₀ T` in the source. -/
noncomputable def onLineCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros T | ρ.re = 1 / 2}, zeroMultiplicity ρ

/-- The number of simple non-trivial zeros with imaginary part in `(0, T]`. This is `N_s T` in
the source; each such zero has multiplicity one, so this is a set cardinality. -/
noncomputable def simpleZeroCount (T : ℝ) : ℕ :=
  {ρ ∈ nontrivialZeros T | zeroMultiplicity ρ = 1}.ncard

/-- The number of non-trivial zeros with imaginary part in `(0, T]` that are simple or lie on
the critical line (or both), counted **with multiplicity**. This is `N_{s∪0} T` in the source. -/
noncomputable def simpleOrOnLineCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros T | zeroMultiplicity ρ = 1 ∨ ρ.re = 1 / 2}, zeroMultiplicity ρ

/-- The Fourier transform of a compactly supported real function, at a complex argument. -/
noncomputable def fourierC (f : ℝ → ℝ) (ξ : ℂ) : ℂ :=
  ∫ u : ℝ, (f u : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ξ * (u : ℂ))

/-! ## The key proposition

The Hilbert-space inequalities at the heart of the proof. They speak only of a finite
conjugation-invariant multiset of complex numbers and a test function; no zeta function appears.
The multiset is presented by its finite support `Z` with a multiplicity function `m`, so that
`∑_{z ∈ 𝒵} 1` is `∑ z ∈ Z, (m z : ℝ)` and `∑_{z, s ∈ 𝒵} K (z - s) ^ 2` is
`∑ z ∈ Z, ∑ s ∈ Z, (m z * m s) * testKernel eta (z - s) ^ 2`. That sum is real -- `η` real and
even make `K` even with `conj (K ξ) = K (conj ξ)`, so pairing `(z, s)` with `(conj z, conj s)`
conjugates each term -- so the statements below take its real part, discarding nothing.

Y. Lamzouri, *op. cit.*, **Proposition 2.1**, equations (2.3), (2.4), (2.5) and (2.6).
-/

/-- `eta` is `lam`-admissible: square-integrable, real-valued, even, supported in
`(-lam, lam)`, and normalised so that its square has Fourier transform `1` at `0`. -/
structure IsAdmissible (lam : ℝ) (eta : ℝ → ℝ) : Prop where
  /-- `eta` is square-integrable. -/
  memLp : MeasureTheory.MemLp eta 2 MeasureTheory.volume
  /-- `eta` is even. -/
  even : ∀ x, eta (-x) = eta x
  /-- `eta` vanishes off `(-lam, lam)`. -/
  support : ∀ x, lam ≤ |x| → eta x = 0
  /-- `eta` is normalised: its square has Fourier transform `1` at `0`. -/
  fourier_sq_zero : fourierC (eta ^ 2) 0 = 1

/-- The kernel of a test function: the Fourier transform of `η²`, not the square of the Fourier
transform of `η`. -/
noncomputable def testKernel (eta : ℝ → ℝ) : ℂ → ℂ := fourierC (eta ^ 2)

/-- The support `Z` with multiplicities `m` is conjugation-invariant: every multiplicity is at
least one, and conjugation permutes `Z` preserving multiplicity. -/
structure IsConjInvariant (Z : Finset ℂ) (m : ℂ → ℕ) : Prop where
  /-- Every point of the support has multiplicity at least one. -/
  one_le : ∀ z ∈ Z, 1 ≤ m z
  /-- Conjugation maps the support to itself. -/
  conj_mem : ∀ z ∈ Z, (starRingEnd ℂ) z ∈ Z
  /-- Conjugation preserves multiplicity. -/
  mult_conj : ∀ z ∈ Z, m ((starRingEnd ℂ) z) = m z

/-- The simple real part of the support: real points of multiplicity one. -/
noncomputable def simpleRealPart (Z : Finset ℂ) (m : ℂ → ℕ) : Finset ℂ :=
  Z.filter fun x => x.im = 0 ∧ m x = 1

/-- The simple part of the support: points of multiplicity one, real or not. -/
noncomputable def simplePart (Z : Finset ℂ) (m : ℂ → ℕ) : Finset ℂ :=
  Z.filter fun z => m z = 1

/-- The real part of the support: the elements of `Z` that are real.

Named `allRealPart`, not `realPart`, because Mathlib's root-namespace `realPart` -- the real part
of an element of a star algebra -- is in scope here and unrelated. It is the union of
`simpleRealPart` and `multipleRealPart`. -/
noncomputable def allRealPart (Z : Finset ℂ) : Finset ℂ :=
  Z.filter fun z => z.im = 0

/-- The part of the support that is simple or real (or both). -/
noncomputable def simpleOrRealPart (Z : Finset ℂ) (m : ℂ → ℕ) : Finset ℂ :=
  Z.filter fun z => m z = 1 ∨ z.im = 0

namespace Challenge

/-- **`prop_simple_real_lower`** (2.3). The number of real points of multiplicity one is at
least `2 ∑_{z ∈ 𝒵} 1 - ∑_{z, s ∈ 𝒵} K (z - s) ^ 2`. -/
theorem prop_simple_real_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty) :
    2 * (∑ z ∈ Z, (m z : ℝ))
        - (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ ((simpleRealPart Z m).card : ℝ) :=
  sorry

/-- **`prop_distinct_lower`** (2.4). The number of distinct points is at least
`(3/2) ∑_{z ∈ 𝒵} 1 - (1/2) ∑_{z, s ∈ 𝒵} K (z - s) ^ 2`. -/
theorem prop_distinct_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty) :
    (3 / 2 : ℝ) * (∑ z ∈ Z, (m z : ℝ))
        - (1 / 2 : ℝ) *
          (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ (Z.card : ℝ) :=
  sorry

/-- **`prop_simple_plus_real_lower`** (2.5). The number of simple points plus the
number of real points counted with multiplicity is at least
`3 ∑_{z ∈ 𝒵} 1 - ∑_{z, s ∈ 𝒵} K (z - s) ^ 2`.

Note the asymmetry, which is the source's: the simple points are counted as a set (each has
multiplicity one anyway), the real points with multiplicity. -/
theorem prop_simple_plus_real_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty) :
    3 * (∑ z ∈ Z, (m z : ℝ))
        - (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ ((simplePart Z m).card : ℝ) + ∑ z ∈ allRealPart Z, (m z : ℝ) :=
  sorry

/-- **`prop_simple_or_real_lower`** (2.6). If the second moment is at most
`A ∑_{z ∈ 𝒵} 1` for some `1 ≤ A < 2`, then the points that are simple or real (or both),
counted with multiplicity, number at least `(5 + 2√2 - 2A) / (3 + 2√2) ∑_{z ∈ 𝒵} 1`.

The hypothesis `1 ≤ A` is not a restriction: (2.3) forces the second moment to be at least
`∑_{z ∈ 𝒵} 1`, since the left-hand side there is at most that. -/
theorem prop_simple_or_real_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ} {A : ℝ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty)
    (hA₁ : 1 ≤ A) (hA₂ : A < 2)
    (hbound : (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ A * ∑ z ∈ Z, (m z : ℝ)) :
    (5 + 2 * Real.sqrt 2 - 2 * A) / (3 + 2 * Real.sqrt 2) * (∑ z ∈ Z, (m z : ℝ))
      ≤ ∑ z ∈ simpleOrRealPart Z m, (m z : ℝ) :=
  sorry

end Challenge

/-! ## The two external inputs, as hypotheses

* **Riemann--von Mangoldt**: E. C. Titchmarsh, *The theory of the Riemann zeta-function*,
  Theorem 9.4.
* **Unconditional pair correlation**: S. A. C. Baluyot, D. A. Goldston, A. I. Suriajaya and
  C. L. Turnage-Butterbaugh, *An unconditional Montgomery theorem for pair correlation of zeros
  of the Riemann zeta-function*, Acta Arith. **214** (2024), 357--376, **Lemma 5**.

These two are the only assumptions.
-/

/-- The weight `4 / (4 - z²)` carried by the unconditional pair-correlation formula. -/
noncomputable def pairWeight (z : ℂ) : ℂ := 4 / (4 - z ^ 2)

/-- The rescaled difference `i(ρ - ρ') log T / (2π)` of two zeros. -/
noncomputable def rescaledDiff (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  Complex.I * (ρ - ρ') * ((Real.log T / (2 * Real.pi) : ℝ) : ℂ)

/-- The weighted sum of `fourierC f` over ordered pairs of non-trivial zeros with imaginary part
in `(0, T]`, each zero counted with multiplicity. -/
noncomputable def pairCorrelationSum (f : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ nontrivialZeros T, ∑ᶠ ρ' ∈ nontrivialZeros T,
    ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
      fourierC f (rescaledDiff T ρ ρ') * pairWeight (ρ - ρ')

/-- The main term `f 0 + 2 ∫₀¹ α f α` of the pair-correlation formula. -/
noncomputable def pairMainTerm (f : ℝ → ℝ) : ℝ := f 0 + 2 * ∫ α in (0:ℝ)..1, α * f α

/-- A test function admissible for the pair-correlation formula: even, integrable, supported in
`[-1, 1]`, and satisfying `|f x - f 0| ≤ C * |x|` for all `x`, not merely near `0`. -/
def IsPairTestFunction (f : ℝ → ℝ) : Prop :=
  (∀ x, f (-x) = f x) ∧ MeasureTheory.Integrable f ∧ (∀ x, 1 < |x| → f x = 0) ∧
    ∃ C : ℝ, ∀ x, |f x - f 0| ≤ C * |x|

/-- **The Riemann--von Mangoldt formula.** The number of non-trivial zeros up to height `T`,
counted with multiplicity, is asymptotic to `(T / 2π) log T`. -/
def RiemannVonMangoldt : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    |(zeroCount T : ℝ) / (T / (2 * Real.pi) * Real.log T) - 1| < ε

/-- **The unconditional pair correlation formula.** For every admissible test function the
weighted pair-correlation sum is `(T / 2π) log T` times its main term, with an error
`O(1 / √log T)`. -/
def PairCorrelation : Prop :=
  ∀ f : ℝ → ℝ, IsPairTestFunction f →
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ‖pairCorrelationSum f T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ) -
          ((pairMainTerm f : ℝ) : ℂ)‖ ≤ C / Real.sqrt (Real.log T)

/-! ## The main results

The four proportions. The constants are spelled out in closed form; numerically

* `C₀ = 3/2 - (1/√2) cot(1/√2)             = 0.6725007037…`
* `C₁ = 5/4 - (1/(2√2)) cot(1/√2)          = 0.8362503518…`
* `C₂ = (4 + 2√2 - √2 cot(1/√2)) / (3 + 2√2) = 0.8876200082…`

where `C₀ = 2 - C_MT`, `C₁ = 3/2 - C_MT/2` and `C₂ = (5 + 2√2 - 2 C_MT) / (3 + 2√2)` for the
Montgomery--Taylor constant `C_MT = 1/2 + (1/√2) cot(1/√2)`.
-/

namespace Challenge

/-- **`thm_simple`.** Beyond a height depending on `ε`, the proportion of non-trivial zeros
that are simple and lie on the critical line exceeds `C₀ - ε = 0.6725007037… - ε`. -/
theorem thm_simple (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - ε <
        (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  sorry

/-- **`thm_distinct`.** Beyond a height depending on `ε`, the proportion of non-trivial zeros
that are distinct exceeds `C₁ - ε = 0.8362503518… - ε`. -/
theorem thm_distinct (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
  sorry

/-- **`thm_average`.** Beyond a height depending on `ε`, the average of the
proportion of simple zeros and the proportion of zeros on the critical line exceeds
`C₁ - ε = 0.8362503518… - ε`.

In particular `max (N₀ T) (N_s T) ≥ (C₁ + o(1)) N T`: the argument does not say which of the two
is the larger, only that the larger one is at least `83.625%`. -/
theorem thm_average (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        ((simpleZeroCount T : ℝ) + (onLineCount T : ℝ)) / (2 * (zeroCount T : ℝ)) :=
  sorry

/-- **`thm_simple_or_critical`.** Beyond a height depending on `ε`, the proportion of
non-trivial zeros that are simple or lie on the critical line (or both) exceeds
`C₂ - ε = 0.8876200082… - ε`. -/
theorem thm_simple_or_critical (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
            / (3 + 2 * Real.sqrt 2) - ε <
        (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  sorry

/-! ### Numeric forms

The decimal thresholds the source quotes in prose. All four are reachable from the single
numerical input `C_MT < 1.3275`.

The `88.76%` threshold is quoted to four places on purpose: `C₂ = 0.887620008…` clears `0.88762`
by under `10⁻⁸`, so the five-place form would need `C_MT` to eight places rather than four.
-/

/-- **`thm_simple_numeric`.** Beyond some height, more than `67.25%` of the non-trivial zeros of
the Riemann zeta function are simple and lie on the critical line. -/
theorem thm_simple_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.6725 < (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  sorry

/-- **`thm_distinct_numeric`.** Beyond some height, more than `83.625%` of the non-trivial zeros
of the Riemann zeta function are distinct. -/
theorem thm_distinct_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.83625 < (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
  sorry

/-- **`thm_average_numeric`.** Beyond some height, the average of the proportion of simple zeros
and the proportion of zeros on the critical line exceeds `83.625%`. -/
theorem thm_average_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      0.83625 < ((simpleZeroCount T : ℝ) + (onLineCount T : ℝ)) / (2 * (zeroCount T : ℝ)) :=
  sorry

/-- **`thm_simple_or_critical_numeric`.** Beyond some height, more than `88.76%` of the
non-trivial zeros of the Riemann zeta function are simple or lie on the critical line (or
both). -/
theorem thm_simple_or_critical_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.8876 < (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  sorry

end Challenge

end ZetaZeros
