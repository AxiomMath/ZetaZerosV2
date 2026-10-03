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

/-!
# The vocabulary of the main results

The counts of the zeros of the Riemann zeta function and the Hilbert-space objects of the key
proposition, exactly as `Challenge/Basic.lean` states them.
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

end ZetaZeros
