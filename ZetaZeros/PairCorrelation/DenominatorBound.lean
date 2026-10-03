/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.Norm
public import ZetaZeros.Meta.Attr

/-!
# A lower bound for the denominator of the sum over zeros

The sum over zeros `ℓ(x, t)` and the pair kernel `κ_{ρ,ρ'}(t)` of the unconditional
pair-correlation formula both carry the factor `1 - (ρ - (1/2 + it))²` in a denominator. This file
bounds that factor away from `0`, uniformly in `t` and in the zero `ρ`, with a bound that grows
quadratically in the distance from `t` to the ordinate of `ρ`: writing `ρ = 1/2 + δ + iγ`, the
factor is `1 - δ² + (γ - t)² - 2iδ(γ - t)`, whose real part is `1 - δ² + (γ - t)²`, and `|δ| < 1/2`
throughout the critical strip. Only the real part is used, so the estimate is a statement about a
half-plane rather than about the location of the zeros; the same bound applies to the conjugate
factor `1 - (conj ρ' - (1/2 - it))²`, which is the conjugate of the factor for `ρ'`.

## Main results

* `ZetaZeros.one_sub_re_sq_add_im_sq_le_norm_one_sub_sq`: the hypothesis-free core, that
  `‖1 - z ²‖ ≥ 1 - (re z)² + (im z)²` for every complex `z`.
* `ZetaZeros.three_quarters_add_sq_le_norm_one_sub_sq`: the bound
  `‖1 - (ρ - (1/2 + it))²‖ ≥ 3/4 + (t - im ρ)²` for `ρ` in the open critical strip.
-/

@[expose] public section

namespace ZetaZeros

open Complex

/-- The modulus of `1 - z ^ 2` is at least `1 - (re z) ^ 2 + (im z) ^ 2`, that quantity being its
real part. No hypothesis on `z` is needed; the interest of the bound is that it is positive as soon
as `|re z| ≤ 1`, and grows with `|im z|`. -/
theorem one_sub_re_sq_add_im_sq_le_norm_one_sub_sq (z : ℂ) :
    1 - z.re ^ 2 + z.im ^ 2 ≤ ‖1 - z ^ 2‖ := by
  refine le_trans (le_of_eq ?_) (Complex.re_le_norm _)
  simp [pow_two, Complex.mul_re]
  ring

/-- **The denominator is bounded below.** For a point `ρ` of the open critical strip and a real
`t`, the factor `1 - (ρ - (1/2 + it))²` appearing in the denominators of the sum over zeros and of
the pair kernel has modulus at least `3/4 + (t - im ρ)²`. -/
@[zz_tag "lem_denom_lower"]
theorem three_quarters_add_sq_le_norm_one_sub_sq {ρ : ℂ} (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) (t : ℝ) :
    3 / 4 + (t - ρ.im) ^ 2 ≤ ‖1 - (ρ - (1 / 2 + t * I)) ^ 2‖ := by
  refine le_trans ?_ (one_sub_re_sq_add_im_sq_le_norm_one_sub_sq _)
  have hre : (ρ - (1 / 2 + t * I)).re = ρ.re - 1 / 2 := by simp
  have him : (ρ - (1 / 2 + t * I)).im = ρ.im - t := by simp
  rw [hre, him]
  nlinarith [mul_pos h₀ (sub_pos.mpr h₁)]

end ZetaZeros
