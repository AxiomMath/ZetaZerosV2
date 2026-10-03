/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Main
public import ZetaZeros.Numeric.SimpleOrOnLine
public import ZetaZeros.Zeta.TransferBounds

/-!
# The average proportion and the simple-or-on-line proportion

For every `ε > 0`, beyond some height, the average of the proportion of simple zeros and the
proportion of zeros on the critical line exceeds `5/4 - (1/(2√2)) cot(1/√2) - ε`, and the
proportion of zeros that are simple or on the critical line exceeds
`(4 + 2√2 - √2 cot(1/√2)) / (3 + 2√2) - ε`.

## Main results

* `average_proportion_lower`: the lower bound for
  `(simpleZeroCount T + onLineCount T) / (2 zeroCount T)`.
* `simpleOrOnLine_proportion_lower`: the lower bound for `simpleOrOnLineCount T / zeroCount T`.
-/

@[expose] public section

namespace ZetaZeros

open Filter Topology

/-- From `3N - S ≤ A` and `S/N → C`, the average proportion is eventually above `3/2 - C/2 - ε`. -/
private theorem eventually_average_proportion
    (N A S : ℝ → ℝ) (C ε : ℝ) (hε : 0 < ε)
    (hNpos : ∀ᶠ T in atTop, 0 < N T)
    (hS : Tendsto (fun T => S T / N T) atTop (nhds C))
    (hbound : ∀ᶠ T in atTop, 3 * N T - S T ≤ A T) :
    ∀ᶠ T in atTop, 3 / 2 - C / 2 - ε < A T / (2 * N T) := by
  have hlt : ∀ᶠ T in atTop, S T / N T < C + ε :=
    (tendsto_order.1 hS).2 _ (by linarith)
  filter_upwards [hNpos, hlt, hbound] with T hNT hST hAT
  rw [lt_div_iff₀ (by linarith)]
  have hSN : S T < (C + ε) * N T := (div_lt_iff₀ hNT).mp hST
  nlinarith

/-- Once `S/N → C`, the sum is eventually below any strictly larger multiple of `N`. -/
private theorem eventually_le_mul_of_tendsto_ratio
    (N S : ℝ → ℝ) (C d : ℝ) (hd : 0 < d)
    (hNpos : ∀ᶠ T in atTop, 0 < N T)
    (hS : Tendsto (fun T => S T / N T) atTop (nhds C)) :
    ∀ᶠ T in atTop, S T ≤ (C + d) * N T := by
  have hlt : ∀ᶠ T in atTop, S T / N T < C + d := (tendsto_order.1 hS).2 _ (by linarith)
  filter_upwards [hNpos, hlt] with T hNT hST
  exact le_of_lt ((div_lt_iff₀ hNT).mp hST)

/-- **The average of the two proportions.** For every `ε > 0`, beyond some height,
`(simpleZeroCount T + onLineCount T) / (2 zeroCount T)` exceeds
`5/4 - (1/(2√2)) cot(1/√2) - ε`. -/
@[zz_tag "thm_average"]
theorem average_proportion_lower
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        ((simpleZeroCount T : ℝ) + (onLineCount T : ℝ)) / (2 * (zeroCount T : ℝ)) := by
  obtain ⟨eta, C, heta, hC, hsum⟩ := kernelConstruction (ε / 2) (by positivity)
  have hNscale := riemannVonMangoldt.tendsto
  have hscale : ∀ᶠ T : ℝ in atTop, zeroScale T ≠ 0 :=
    zeroScale_pos_eventually.mono fun _ h => ne_of_gt h
  have hratio : Tendsto
      (fun T => (unweightedKernelSum eta T).re / (zeroCount T : ℝ)) atTop (nhds C) :=
    tendsto_ratio_of_tendsto_div_scale _ _ _ _ hNscale hsum hscale
  have hNpos := riemannVonMangoldt.zeroCount_pos_eventually
  have hbound : ∀ᶠ T : ℝ in atTop,
      3 * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re
        ≤ (simpleZeroCount T : ℝ) + (onLineCount T : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hNpos] with T hT hNT
    exact simpleZeroCount_add_onLineCount_lower hT
      (nontrivialZeros_nonempty_of_zeroCount_pos hNT) heta
  have hprop := eventually_average_proportion
    (fun T => (zeroCount T : ℝ))
    (fun T => (simpleZeroCount T : ℝ) + (onLineCount T : ℝ))
    (fun T => (unweightedKernelSum eta T).re) C (ε / 2) (by positivity)
    hNpos hratio hbound
  have hconst : 5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε
      < 3 / 2 - C / 2 - ε / 2 := by
    rw [show 5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2)
        = 3 / 2 - montgomeryTaylorConst / 2 by rw [montgomeryTaylorConst]; ring]
    rw [abs_lt] at hC
    linarith
  exact eventually_atTop.1 (hprop.mono fun T hT => hconst.trans hT)

/-- `simpleOrOnLine_proportion_lower` for `0 < ε ≤ 1/8`. -/
private theorem simpleOrOnLine_proportion_lower_small
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1 / 8) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
            / (3 + 2 * Real.sqrt 2) - ε <
        (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) := by
  obtain ⟨eta, C, heta, hC, hsum⟩ := kernelConstruction (ε / 2) (by positivity)
  rw [abs_lt] at hC
  have hlo := montgomeryTaylorConst_gt
  have hhi := montgomeryTaylorConst_lt
  set Ac : ℝ := C + ε / 2 with hAc
  have hA1 : 1 ≤ Ac := by rw [hAc]; linarith
  have hA2 : Ac < 2 := by rw [hAc]; linarith
  have hNscale := riemannVonMangoldt.tendsto
  have hscale : ∀ᶠ T : ℝ in atTop, zeroScale T ≠ 0 :=
    zeroScale_pos_eventually.mono fun _ h => ne_of_gt h
  have hratio : Tendsto
      (fun T => (unweightedKernelSum eta T).re / (zeroCount T : ℝ)) atTop (nhds C) :=
    tendsto_ratio_of_tendsto_div_scale _ _ _ _ hNscale hsum hscale
  have hNpos := riemannVonMangoldt.zeroCount_pos_eventually
  have hle := eventually_le_mul_of_tendsto_ratio
    (fun T => (zeroCount T : ℝ)) (fun T => (unweightedKernelSum eta T).re)
    C (ε / 2) (by positivity) hNpos hratio
  have hfinal : ∀ᶠ T : ℝ in atTop,
      (5 + 2 * Real.sqrt 2 - 2 * Ac) / (3 + 2 * Real.sqrt 2) * (zeroCount T : ℝ)
        ≤ (simpleOrOnLineCount T : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hNpos, hle] with T hT hNT hbnd
    exact simpleOrOnLineCount_lower hT (nontrivialZeros_nonempty_of_zeroCount_pos hNT)
      heta hA1 hA2 hbnd
  have hden : (0 : ℝ) < 3 + 2 * Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2]
  have hgap : (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
        / (3 + 2 * Real.sqrt 2) - ε
      < (5 + 2 * Real.sqrt 2 - 2 * Ac) / (3 + 2 * Real.sqrt 2) := by
    have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hnum : 2 * Ac - 2 * montgomeryTaylorConst < ε * (3 + 2 * Real.sqrt 2) := by
      rw [hAc]; nlinarith [mul_nonneg hε.le hs]
    have hdiv : (2 * Ac - 2 * montgomeryTaylorConst) / (3 + 2 * Real.sqrt 2) < ε :=
      (div_lt_iff₀ hden).mpr hnum
    have heq : (5 + 2 * Real.sqrt 2 - 2 * montgomeryTaylorConst) / (3 + 2 * Real.sqrt 2)
        - (5 + 2 * Real.sqrt 2 - 2 * Ac) / (3 + 2 * Real.sqrt 2)
        = (2 * Ac - 2 * montgomeryTaylorConst) / (3 + 2 * Real.sqrt 2) := by
      rw [div_sub_div_same]; ring_nf
    rw [show (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
        / (3 + 2 * Real.sqrt 2)
        = (5 + 2 * Real.sqrt 2 - 2 * montgomeryTaylorConst) / (3 + 2 * Real.sqrt 2) from
      simpleOrOnLineProportion_eq]
    linarith
  refine eventually_atTop.1 ?_
  filter_upwards [hNpos, hfinal] with T hNT hT
  rw [lt_div_iff₀ hNT]
  calc ((4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
          / (3 + 2 * Real.sqrt 2) - ε) * (zeroCount T : ℝ)
      < (5 + 2 * Real.sqrt 2 - 2 * Ac) / (3 + 2 * Real.sqrt 2) * (zeroCount T : ℝ) := by
        exact mul_lt_mul_of_pos_right hgap hNT
    _ ≤ (simpleOrOnLineCount T : ℝ) := hT

/-- **Zeros that are simple or on the critical line.** For every `ε > 0`, beyond some height,
`simpleOrOnLineCount T / zeroCount T` exceeds `(4 + 2√2 - √2 cot(1/√2)) / (3 + 2√2) - ε`. -/
@[zz_tag "thm_simple_or_critical"]
theorem simpleOrOnLine_proportion_lower
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
            / (3 + 2 * Real.sqrt 2) - ε <
        (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) := by
  rcases le_or_gt ε (1 / 8) with h | h
  · exact simpleOrOnLine_proportion_lower_small ε hε h
  · obtain ⟨T₀, hT₀⟩ :=
      simpleOrOnLine_proportion_lower_small (1 / 8) (by norm_num) le_rfl
    exact ⟨T₀, fun T hT => by linarith [hT₀ T hT]⟩

end ZetaZeros
