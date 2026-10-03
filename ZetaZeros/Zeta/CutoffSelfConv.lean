/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import ZetaZeros.Zeta.Basic

/-!
# The self-convolution vanishes near the endpoints

A `delta`-cutoff `psi` lies in `C_c^∞((-1/2, 1/2))`: it vanishes not merely off the open interval
but on a neighbourhood of each of its endpoints, so its support is contained in
`[-1/2 + tau, 1/2 - tau]` for some `tau > 0`. The test function `f_psi` vanishes wherever `psi`
does, and the support of a convolution is contained in the sum of the supports, so
`Q_psi = f_psi ⋆ f_psi` vanishes on `1 - 2 tau ≤ |x|`.

Halving that margin makes `Q_psi` vanish identically on a whole neighbourhood of every point `x`
with `1 - tau ≤ |x|`, and a function vanishing near `x` has all its derivatives zero at `x`; so
`Q_psi''` vanishes near the endpoints as well.

## Main results

* `exists_cutoffSelfConv_eq_zero_of_one_sub_le_abs`: for some `eps > 0`, `Q_psi` vanishes at every
  `x` with `1 - eps ≤ |x|`.
* `exists_iteratedDeriv_two_cutoffSelfConv_eq_zero_of_one_sub_le_abs`: the same for `Q_psi''`.
-/

@[expose] public section

namespace ZetaZeros

open Filter MeasureTheory

variable {delta : ℝ} {psi : ℝ → ℝ}

/-- A function vanishing on a neighbourhood of `x` has every iterated derivative zero at `x`. -/
private theorem iteratedDeriv_eq_zero_of_eventuallyEq_zero {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) {f : 𝕜 → F} {x : 𝕜}
    (hf : f =ᶠ[nhds x] 0) : iteratedDeriv n f x = 0 := by
  rw [hf.iteratedDeriv_eq n]
  simp

/-- The support of a convolution lies in the sum of the supports: if `f` vanishes on `a ≤ |y|` and
`g` vanishes on `b ≤ |y|`, then `∫ f t * g (x - t)` vanishes as soon as `a + b ≤ |x|`. -/
private theorem integral_mul_sub_eq_zero_of_add_le_abs {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ y : ℝ, a ≤ |y| → f y = 0) (hg : ∀ y : ℝ, b ≤ |y| → g y = 0)
    {x : ℝ} (hx : a + b ≤ |x|) : ∫ t : ℝ, f t * g (x - t) = 0 := by
  have key : ∀ t : ℝ, f t * g (x - t) = 0 := fun t => by
    rcases le_or_gt a |t| with ht | ht
    · rw [hf t ht, zero_mul]
    · have habs := abs_sub_abs_le_abs_sub x t
      rw [hg _ (by linarith), mul_zero]
  simp [key]

/-- **`Q_psi` vanishes near the endpoints `±1`.** -/
@[zz_tag "lem_Q_psi_margin"]
theorem exists_cutoffSelfConv_eq_zero_of_one_sub_le_abs (h : IsCutoff delta psi) :
    ∃ eps > 0, ∀ x : ℝ, 1 - eps ≤ |x| → cutoffSelfConv psi x = 0 := by
  obtain ⟨tau, htau, hpsi⟩ := h.margin
  have hzero : ∀ y : ℝ, 1 / 2 - tau ≤ |y| → cutoffTestSq psi y = 0 := fun y hy => by
    simp [cutoffTestSq, Pi.pow_apply, cutoffTest, hpsi y hy]
  refine ⟨2 * tau, by linarith, fun x hx => ?_⟩
  rw [cutoffSelfConv]
  exact integral_mul_sub_eq_zero_of_add_le_abs hzero hzero (by linarith)

/-- **`Q_psi''` vanishes near the endpoints `±1`.** -/
@[zz_tag "lem_Q_psi_deriv_margin"]
theorem exists_iteratedDeriv_two_cutoffSelfConv_eq_zero_of_one_sub_le_abs
    (h : IsCutoff delta psi) :
    ∃ eps > 0, ∀ x : ℝ, 1 - eps ≤ |x| → iteratedDeriv 2 (cutoffSelfConv psi) x = 0 := by
  obtain ⟨eps, heps, hQ⟩ := exists_cutoffSelfConv_eq_zero_of_one_sub_le_abs h
  refine ⟨eps / 2, by linarith, fun x hx => iteratedDeriv_eq_zero_of_eventuallyEq_zero 2 ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (by linarith : (0 : ℝ) < eps / 2)] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have habs := abs_sub_abs_le_abs_sub x y
  have hxy : |x - y| < eps / 2 := by rwa [abs_sub_comm]
  simpa using hQ y (by linarith)

end ZetaZeros
