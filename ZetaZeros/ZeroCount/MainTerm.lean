/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import ZetaZeros.ZeroCount.GoodHeight
public import ZetaZeros.Zeta.Finite

/-!
# The main term of the zero-counting formula, and good heights

The main term `M(T) = (T / 2π) log (T / 2π) - T / 2π` of the Riemann--von Mangoldt formula, its
slow variation, and the existence of good heights in every unit interval. The derivative of `M` is
`log (u / 2π) / 2π`, which is at most `log T` in absolute value for `4 ≤ u ≤ 2T`; good heights
exist because only finitely many zeros lie below a given height.

## Main definitions

* `ZetaZeros.mainTerm`: the main term `M(T) = (T / 2π) log (T / 2π) - T / 2π`.

## Main results

* `ZetaZeros.exists_abs_mainTerm_sub_le`: the main term varies by at most `C log T` across an
  interval of length at most `1` above the height `4`.
* `ZetaZeros.exists_isGoodHeight`: every interval `(a, a + 1]` with `a ≥ 0` contains a good
  height.
-/

@[expose] public section

namespace ZetaZeros

/-! ### The main term -/

/-- The **main term** of the zero-counting formula, `M(T) = (T / 2π) log (T / 2π) - T / 2π`. -/
@[zz_tag "def_main_term"]
noncomputable def mainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi)

/-- The derivative of the main term is `M'(u) = log (u / 2π) / 2π` for `u ≠ 0`. -/
private lemma hasDerivAt_mainTerm {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt mainTerm (Real.log (u / (2 * Real.pi)) / (2 * Real.pi)) u := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hπ2 : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) u :=
    (hasDerivAt_id u).div_const (2 * Real.pi)
  have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)))
      (1 / (2 * Real.pi) / (u / (2 * Real.pi))) u := h1.log (div_ne_zero hu hπ2)
  have h3 := (h1.mul h2).sub h1
  have hval : 1 / (2 * Real.pi) * Real.log (u / (2 * Real.pi))
      + u / (2 * Real.pi) * (1 / (2 * Real.pi) / (u / (2 * Real.pi))) - 1 / (2 * Real.pi)
      = Real.log (u / (2 * Real.pi)) / (2 * Real.pi) := by
    field_simp
    ring
  have hfun : mainTerm = fun x : ℝ =>
      x / (2 * Real.pi) * Real.log (x / (2 * Real.pi)) - x / (2 * Real.pi) := rfl
  rw [hfun, ← hval]
  exact h3

/-- For `4 ≤ T` and `4 ≤ u ≤ 2T` one has `|log (u / 2π)| ≤ log T`. -/
private lemma abs_log_div_two_pi_le {T u : ℝ} (hT : 4 ≤ T) (hu : 4 ≤ u) (hu' : u ≤ 2 * T) :
    |Real.log (u / (2 * Real.pi))| ≤ Real.log T := by
  have hπ0 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have hT0 : (0 : ℝ) < T := by linarith
  have hune : u / (2 * Real.pi) ≠ 0 := div_ne_zero (by linarith) (ne_of_gt hπ0)
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h0 : 0 ≤ Real.log T + Real.log (u / (2 * Real.pi)) := by
      rw [← Real.log_mul (ne_of_gt hT0) hune]
      refine Real.log_nonneg ?_
      rw [mul_div_assoc', le_div_iff₀ hπ0]
      nlinarith
    linarith
  · refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hπ0]
    nlinarith

/-- **The main term varies slowly.** There is a constant `C` with `|M(T') - M(T)| ≤ C log T`
whenever `4 ≤ T ≤ T' ≤ T + 1`. -/
@[zz_tag "lem_main_term_lipschitz"]
theorem exists_abs_mainTerm_sub_le :
    ∃ C : ℝ, ∀ T T' : ℝ, 4 ≤ T → T ≤ T' → T' ≤ T + 1 →
      |mainTerm T' - mainTerm T| ≤ C * Real.log T := by
  refine ⟨1, fun T T' hT hTT' hT'' => ?_⟩
  have hπ0 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hderiv : ∀ u ∈ Set.Icc T T',
      HasDerivWithinAt mainTerm (Real.log (u / (2 * Real.pi)) / (2 * Real.pi))
        (Set.Icc T T') u := fun u hu =>
    (hasDerivAt_mainTerm (ne_of_gt (by linarith [hu.1]))).hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Icc T T',
      ‖Real.log (u / (2 * Real.pi)) / (2 * Real.pi)‖ ≤ Real.log T / (2 * Real.pi) := by
    intro u hu
    have habs : |Real.log (u / (2 * Real.pi))| ≤ Real.log T :=
      abs_log_div_two_pi_le hT (by linarith [hu.1]) (by linarith [hu.2])
    calc ‖Real.log (u / (2 * Real.pi)) / (2 * Real.pi)‖
        = |Real.log (u / (2 * Real.pi))| / (2 * Real.pi) := by
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hπ0]
      _ ≤ Real.log T / (2 * Real.pi) := by gcongr
  have key := (convex_Icc T T').norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (Set.left_mem_Icc.mpr hTT') (Set.right_mem_Icc.mpr hTT')
  have hlen : ‖T' - T‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  rw [Real.norm_eq_abs] at key
  calc |mainTerm T' - mainTerm T| ≤ Real.log T / (2 * Real.pi) * ‖T' - T‖ := key
    _ ≤ Real.log T / (2 * Real.pi) * 1 := mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = Real.log T / (2 * Real.pi) := mul_one _
    _ ≤ Real.log T := div_le_self hlog (by linarith)
    _ = 1 * Real.log T := (one_mul _).symm

/-! ### Good heights are plentiful -/

/-- **Good heights are plentiful.** Every interval `(a, a + 1]` with `a ≥ 0` contains a good
height. -/
@[zz_tag "lem_good_height_exists"]
theorem exists_isGoodHeight {a : ℝ} (ha : 0 ≤ a) :
    ∃ T : ℝ, IsGoodHeight T ∧ a < T ∧ T ≤ a + 1 := by
  have hfin : ((fun ρ : ℂ => ρ.im) '' nontrivialZeros (a + 1)).Finite :=
    (nontrivialZeros_finite (a + 1)).image _
  have hinf : (Set.Ioc a (a + 1)).Infinite := Set.Ioc_infinite (by linarith)
  obtain ⟨T, ⟨hT1, hT2⟩, hT3⟩ := (hinf.sdiff hfin).nonempty
  refine ⟨T, ?_, hT1, hT2⟩
  intro ρ hζ h0 h1 him
  exact hT3 ⟨ρ, ⟨hζ, h0, h1, by rw [him]; linarith, by rw [him]; exact hT2⟩, him⟩

end ZetaZeros
