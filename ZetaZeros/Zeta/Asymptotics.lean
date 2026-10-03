/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Zeta.Inputs

/-!
# Elementary asymptotic consequences of Riemann--von Mangoldt

From `N(T) = M(T) + O(log T)`, the zero count satisfies `N(T) / ((T / 2π) log T) → 1`, and is
eventually positive.

## Main results

* `RiemannVonMangoldt.tendsto`: `N(T) / ((T / 2π) log T) → 1`.
* `RiemannVonMangoldt.zeroCount_pos_eventually`: `N(T) > 0` for all sufficiently large `T`.
-/

@[expose] public section

namespace ZetaZeros

open Filter Topology

/-- The main scale in the Riemann--von Mangoldt and pair-correlation formulae. -/
noncomputable def zeroScale (T : ℝ) : ℝ := T / (2 * Real.pi) * Real.log T

/-- The Riemann--von Mangoldt scale is positive at all sufficiently large heights. -/
theorem zeroScale_pos_eventually : ∀ᶠ T in atTop, 0 < zeroScale T := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  exact mul_pos (div_pos hT0 (mul_pos (by norm_num) Real.pi_pos)) hlog

/-- The main term, normalised by the scale, tends to one: `M (T) / ((T / 2π) log T) → 1`. -/
theorem tendsto_mainTerm_div_zeroScale :
    Tendsto (fun T : ℝ => mainTerm T / zeroScale T) atTop (nhds 1) := by
  have hev : ∀ᶠ T : ℝ in atTop,
      mainTerm T / zeroScale T = 1 - (Real.log (2 * Real.pi) + 1) / Real.log T := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ne_atTop (0 : ℝ)] with T hT1 _
    have hT0 : (0 : ℝ) < T := by linarith
    have hlog : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT1)
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [mainTerm, zeroScale, Real.log_div hT0.ne' hpi.ne']
    field_simp
    ring
  have hq : Tendsto
      (fun T : ℝ => (Real.log (2 * Real.pi) + 1) / Real.log T) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hlim : Tendsto
      (fun T : ℝ => 1 - (Real.log (2 * Real.pi) + 1) / Real.log T) atTop (nhds 1) := by
    have := tendsto_const_nhds.sub hq (f := fun _ : ℝ => (1 : ℝ))
    simpa using this
  exact Tendsto.congr' (hev.mono fun T h => h.symm) hlim

/-- Under the Riemann--von Mangoldt formula, the zero count normalised by `(T / 2π) log T` tends
to one. -/
theorem RiemannVonMangoldt.tendsto (hRvM : RiemannVonMangoldt) :
    Tendsto (fun T : ℝ => (zeroCount T : ℝ) / zeroScale T) atTop (nhds 1) := by
  obtain ⟨C, hC⟩ := hRvM
  set D : ℝ := 2 * Real.pi * max C 0 with hD
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖((zeroCount T : ℝ) - mainTerm T) / zeroScale T‖ ≤ D / T := by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with T hT
    have hT0 : (0 : ℝ) < T := by linarith
    have hlog : (1 : ℝ) ≤ Real.log T := by
      have he : Real.exp 1 < 4 := by
        have := Real.exp_one_lt_d9
        linarith
      exact le_of_lt ((Real.lt_log_iff_exp_lt hT0).2 (lt_of_lt_of_le he hT))
    have hlog0 : (0 : ℝ) < Real.log T := by linarith
    have hQ : (0 : ℝ) < zeroScale T := by
      rw [zeroScale]; positivity
    have hnum : |(zeroCount T : ℝ) - mainTerm T| ≤ max C 0 * Real.log T :=
      le_trans (hC T hT) (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0.le)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hQ]
    calc |(zeroCount T : ℝ) - mainTerm T| / zeroScale T
        ≤ max C 0 * Real.log T / zeroScale T := by gcongr
      _ = D / T := by
          rw [zeroScale, hD]
          field_simp
  have hzero : Tendsto (fun T : ℝ => D / T) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have herr : Tendsto
      (fun T : ℝ => ((zeroCount T : ℝ) - mainTerm T) / zeroScale T) atTop (nhds 0) :=
    squeeze_zero_norm' hbound hzero
  have hsum := tendsto_mainTerm_div_zeroScale.add herr
  rw [add_zero] at hsum
  refine Tendsto.congr' (Eventually.of_forall fun T => ?_) hsum
  ring

/-- Under the Riemann--von Mangoldt formula, the zero count is eventually positive. -/
theorem RiemannVonMangoldt.zeroCount_pos_eventually (hRvM : RiemannVonMangoldt) :
    ∀ᶠ T in atTop, 0 < (zeroCount T : ℝ) := by
  have hhalf : ∀ᶠ T : ℝ in atTop, (1 : ℝ) / 2 < (zeroCount T : ℝ) / zeroScale T := by
    have := (tendsto_order.1 hRvM.tendsto).1 (1 / 2) (by norm_num)
    exact this
  filter_upwards [hhalf, zeroScale_pos_eventually] with T hratio hscale
  have hpos : 0 < (zeroCount T : ℝ) / zeroScale T := by linarith
  rcases (div_pos_iff.mp hpos) with h | h
  · exact h.1
  · exact (not_lt_of_ge (le_of_lt hscale) h.2).elim

end ZetaZeros
