/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Meta.Attr
public import ZetaZeros.ZeroCount.MainTerm
public import ZetaZeros.Zeta.Defs

/-!
# The Riemann--von Mangoldt formula and the pair-correlation formula

Statements, as `Prop`s, of two classical results about the non-trivial zeros of `riemannZeta`:
the Riemann--von Mangoldt formula (Titchmarsh, *The Theory of the Riemann Zeta-Function*,
Theorem 9.4) and the unconditional pair-correlation formula
(Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh 2024, Lemma 5). Both are proved in this
library: `RiemannVonMangoldt` by `ZetaZeros.riemannVonMangoldt` and `PairCorrelation` by
`ZetaZeros.pairCorrelationFormula`.

## Main definitions

* `IsPairTestFunction`: even, integrable test functions vanishing on a neighbourhood of `±1` and
  Lipschitz at the origin.
* `RiemannVonMangoldt`: `N(T) = M(T) + O(log T)` for `4 ≤ T`.
* `PairCorrelation`: the asymptotic of the weighted pair-correlation sum for every admissible test
  function, with error `O(1 / √log T)`.
-/

@[expose] public section

namespace ZetaZeros

/-- A test function admissible in the pair-correlation formula: `f` is even, integrable, vanishes
on `1 - ε ≤ |x|` for some `0 < ε < 1`, and satisfies `|f x - f 0| ≤ C |x|` for some `C`. -/
def IsPairTestFunction (f : ℝ → ℝ) : Prop :=
  (∀ x, f (-x) = f x) ∧ MeasureTheory.Integrable f ∧
    (∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x, 1 - ε ≤ |x| → f x = 0) ∧
    ∃ C : ℝ, ∀ x, |f x - f 0| ≤ C * |x|

/-- **Riemann--von Mangoldt formula** (Titchmarsh, *The Theory of the Riemann Zeta-Function*,
Theorem 9.4): there is `C` such that for all `T ≥ 4` the zero count `N (T)` differs from the main
term `M (T) = (T / 2π) log (T / 2π) - T / 2π` by at most `C log T`. This is proved as
`ZetaZeros.riemannVonMangoldt`. -/
def RiemannVonMangoldt : Prop :=
  ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T → |(zeroCount T : ℝ) - mainTerm T| ≤ C * Real.log T

/-- **Unconditional pair correlation** (Lemma 5 of
Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh, *An unconditional Montgomery theorem for pair
correlation of zeros of the Riemann zeta-function*, Acta Arith. 214 (2024), 357--376). For every
admissible test function `f` there are `C > 0` and `T₀` such that for `T ≥ T₀` the pair-correlation
sum of `f`, divided by `(T / 2π) log T`, differs from `pairMainTerm f` by at most `C / √log T`.
This is proved as `ZetaZeros.pairCorrelationFormula`. -/
def PairCorrelation : Prop :=
  ∀ f : ℝ → ℝ, IsPairTestFunction f →
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ‖pairCorrelationSum f T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ) -
          ((pairMainTerm f : ℝ) : ℂ)‖ ≤ C / Real.sqrt (Real.log T)

end ZetaZeros
