/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import ZetaZeros.Zeta.Defs

/-!
# All the non-trivial zeros

The set `𝒩*` of all non-trivial zeros of the Riemann zeta function -- the zeros of the open
critical strip, with no restriction on the height -- and the fact that only finitely many of them
are real.

`allZeros` is `nontrivialZeros` with the two conditions `0 < im ρ` and `im ρ ≤ T` dropped.

## Main definitions

* `ZetaZeros.allZeros`: the set `𝒩*`.

## Main results

* `ZetaZeros.allZeros_im_eq_zero_finite`: only finitely many elements of `𝒩*` are real.
-/

@[expose] public section

namespace ZetaZeros

/-- The non-trivial zeros of the Riemann zeta function at every height: the zeros lying in the
critical strip `0 < re s < 1`, as a set, so without multiplicity. This is `𝒩*`, and it is
`nontrivialZeros` with the restriction on the imaginary part removed. -/
@[zz_tag "def_all_zeros"]
def allZeros : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- A non-trivial zero up to a height is a non-trivial zero: the height enters `nontrivialZeros`
only through conditions on the imaginary part, which `allZeros` drops. -/
theorem nontrivialZeros_subset_allZeros (T : ℝ) : nontrivialZeros T ⊆ allZeros :=
  fun _ hρ => ⟨hρ.1, hρ.2.1, hρ.2.2.1⟩

/-- **Finitely many zeros on the real axis.** A real element of `𝒩*` lies strictly between `0` and
`1`, hence in the closed unit ball, and a compact set contains only finitely many zeros of `ζ`. -/
@[zz_tag "lem_zeros_real_finite"]
theorem allZeros_im_eq_zero_finite : {ρ ∈ allZeros | ρ.im = 0}.Finite := by
  refine ((isCompact_closedBall (0 : ℂ) 1).inter_riemannZetaZeros_finite).subset fun ρ hρ => ?_
  obtain ⟨⟨hζ, h₀, h₁⟩, him⟩ := hρ
  refine ⟨?_, mem_riemannZetaZeros.mpr hζ⟩
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    _ ≤ 1 := by rw [him, abs_zero, add_zero, abs_of_pos h₀]; linarith

end ZetaZeros
