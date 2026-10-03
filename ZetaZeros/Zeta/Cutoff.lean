/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import ZetaZeros.Zeta.Defs

/-!
# Cutoffs exist

For `0 < delta < 1/4` there is a `delta`-cutoff: a smooth even function valued in `[0,1]`,
identically one on `|x| ≤ 1/2 - delta`, with compact support in `(-1/2, 1/2)`. It is Mathlib's
`ContDiffBump` centred at the origin with inner radius `1/2 - delta` and outer radius
`1/2 - delta/2`, so `IsCutoff.margin` holds with `tau = delta/2`.

## Main results

* `exists_isCutoff`: `delta`-cutoffs exist for `0 < delta < 1/4`.
-/

@[expose] public section

namespace ZetaZeros

open Metric

/-- **Cutoffs exist.** For `0 < delta < 1/4` there is a `delta`-cutoff. -/
@[zz_tag "lem_cutoff_exists"]
theorem exists_isCutoff {delta : ℝ} (h0 : 0 < delta) (h4 : delta < 1 / 4) :
    ∃ psi : ℝ → ℝ, IsCutoff delta psi := by
  have hrIn : (0 : ℝ) < 1 / 2 - delta := by linarith
  have hlt : (1 : ℝ) / 2 - delta < 1 / 2 - delta / 2 := by linarith
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2 - delta, 1 / 2 - delta / 2, hrIn, hlt⟩
  refine ⟨fun x => f x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact f.contDiff
  · intro x hx
    refine f.zero_of_le_dist ?_
    simp only [f, Real.dist_eq, sub_zero]
    linarith
  · intro x
    exact f.neg x
  · intro x
    exact f.nonneg
  · intro x
    exact f.le_one
  · intro x hx
    refine f.one_of_mem_closedBall ?_
    simpa [f, mem_closedBall, Real.dist_eq] using hx
  · refine ⟨delta / 2, by linarith, fun x hx => ?_⟩
    refine f.zero_of_le_dist ?_
    simpa [f, Real.dist_eq] using hx

end ZetaZeros
