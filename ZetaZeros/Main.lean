/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Numeric.MontgomeryTaylor
public import ZetaZeros.Numeric.SimpleOrOnLine
public import ZetaZeros.Zeta.Proportion
public import ZetaZeros.Zeta.Transfer
public import ZetaZeros.Zeta.TransferBounds

/-!
# Proportion bounds for the zeros of the Riemann zeta function

Granted the Riemann--von Mangoldt formula and the unconditional pair correlation estimate, the
finite-set bounds transferred to the zeta zeros combine with the kernel construction to give four
lower bounds, each valid beyond some height, for the proportion of non-trivial zeros that are

* simple and on the critical line (`simple_proportion_lower`);
* distinct (`distinct_proportion_lower`);
* simple or on the critical line, averaged with the proportion on the critical line
  (`average_proportion_lower`);
* simple or on the critical line (`simpleOrOnLine_proportion_lower`).

Each is stated up to an arbitrary `ε` below a closed-form constant in `cot(1/√2)`. The four decimal
corollaries record what those constants clear: `67.25%`, `83.625%`, `83.625%` and `88.76%`.
-/

@[expose] public section

namespace ZetaZeros

open Filter Topology

private lemma nontrivialZeros_nonempty_of_zeroCount_pos {T : ℝ}
    (h : 0 < (zeroCount T : ℝ)) : (nontrivialZeros T).Nonempty := by
  by_contra hne
  have hz : nontrivialZeros T = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  rw [zeroCount, hz] at h
  simp at h

/-- From `3N - S ≤ A` and `S/N → C`, the average proportion is eventually above `3/2 - C/2 - ε`. -/
theorem eventually_average_proportion
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
theorem eventually_le_mul_of_tendsto_ratio
    (N S : ℝ → ℝ) (C d : ℝ) (hd : 0 < d)
    (hNpos : ∀ᶠ T in atTop, 0 < N T)
    (hS : Tendsto (fun T => S T / N T) atTop (nhds C)) :
    ∀ᶠ T in atTop, S T ≤ (C + d) * N T := by
  have hlt : ∀ᶠ T in atTop, S T / N T < C + d := (tendsto_order.1 hS).2 _ (by linarith)
  filter_upwards [hNpos, hlt] with T hNT hST
  exact le_of_lt ((div_lt_iff₀ hNT).mp hST)

@[zz_tag "thm_simple"]
theorem simple_proportion_lower (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - ε <
        (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) := by
  obtain ⟨eta, C, heta, hC, hsum⟩ := kernelConstruction hPC (ε / 2) (by positivity)
  have hNscale := hRvM.tendsto
  have hscale : ∀ᶠ T : ℝ in atTop, zeroScale T ≠ 0 :=
    zeroScale_pos_eventually.mono fun _ h => ne_of_gt h
  have hratio : Tendsto
      (fun T => (unweightedKernelSum eta T).re / (zeroCount T : ℝ))
      atTop (nhds C) :=
    tendsto_ratio_of_tendsto_div_scale _ _ _ _ hNscale hsum hscale
  have hNpos := hRvM.zeroCount_pos_eventually
  have hbound : ∀ᶠ T : ℝ in atTop,
      2 * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re ≤
        (simpleOnLineCount T : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hNpos] with T hT hNT
    exact simpleOnLineCount_lower hT (nontrivialZeros_nonempty_of_zeroCount_pos hNT) heta
  have hprop := eventually_simple_proportion
    (fun T => (zeroCount T : ℝ)) (fun T => (simpleOnLineCount T : ℝ))
    (fun T => (unweightedKernelSum eta T).re) C (ε / 2) (by positivity)
    hNpos hratio hbound
  have hconst :
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - ε <
        2 - C - ε / 2 := by
    rw [show 3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) =
      2 - montgomeryTaylorConst by
        rw [montgomeryTaylorConst]
        ring]
    rw [abs_lt] at hC
    linarith
  have hfinal : ∀ᶠ T : ℝ in atTop,
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - ε <
        (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
    hprop.mono fun T hT => hconst.trans hT
  exact eventually_atTop.1 hfinal

@[zz_tag "thm_distinct"]
theorem distinct_proportion_lower (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) := by
  obtain ⟨eta, C, heta, hC, hsum⟩ := kernelConstruction hPC (ε / 2) (by positivity)
  have hNscale := hRvM.tendsto
  have hscale : ∀ᶠ T : ℝ in atTop, zeroScale T ≠ 0 :=
    zeroScale_pos_eventually.mono fun _ h => ne_of_gt h
  have hratio : Tendsto
      (fun T => (unweightedKernelSum eta T).re / (zeroCount T : ℝ))
      atTop (nhds C) :=
    tendsto_ratio_of_tendsto_div_scale _ _ _ _ hNscale hsum hscale
  have hNpos := hRvM.zeroCount_pos_eventually
  have hbound : ∀ᶠ T : ℝ in atTop,
      (3 / 2 : ℝ) * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re / 2 ≤
        (distinctZeroCount T : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hNpos] with T hT hNT
    exact distinctZeroCount_lower hT (nontrivialZeros_nonempty_of_zeroCount_pos hNT) heta
  have hprop := eventually_distinct_proportion
    (fun T => (zeroCount T : ℝ)) (fun T => (distinctZeroCount T : ℝ))
    (fun T => (unweightedKernelSum eta T).re) C (ε / 2) (by positivity)
    hNpos hratio hbound
  have hconst :
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        3 / 2 - C / 2 - ε / 2 := by
    rw [show 5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) =
      3 / 2 - montgomeryTaylorConst / 2 by
        rw [montgomeryTaylorConst]
        ring]
    rw [abs_lt] at hC
    linarith
  have hfinal : ∀ᶠ T : ℝ in atTop,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
    hprop.mono fun T hT => hconst.trans hT
  exact eventually_atTop.1 hfinal

/-- **The average of the two proportions.** -/
@[zz_tag "thm_average"]
theorem average_proportion_lower (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        ((simpleZeroCount T : ℝ) + (onLineCount T : ℝ)) / (2 * (zeroCount T : ℝ)) := by
  obtain ⟨eta, C, heta, hC, hsum⟩ := kernelConstruction hPC (ε / 2) (by positivity)
  have hNscale := hRvM.tendsto
  have hscale : ∀ᶠ T : ℝ in atTop, zeroScale T ≠ 0 :=
    zeroScale_pos_eventually.mono fun _ h => ne_of_gt h
  have hratio : Tendsto
      (fun T => (unweightedKernelSum eta T).re / (zeroCount T : ℝ)) atTop (nhds C) :=
    tendsto_ratio_of_tendsto_div_scale _ _ _ _ hNscale hsum hscale
  have hNpos := hRvM.zeroCount_pos_eventually
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

/-- The small-`ε` case of `simpleOrOnLine_proportion_lower`. The side condition on the constant `A`
is `1 ≤ A < 2`; taking `A = C + ε/2` gives `1 ≤ A` from `1.25 < C_MT` together with `ε/2 < 1/8`,
and `A < 2` from `C_MT < 1.3275`. The general case follows by monotonicity in `ε`. -/
private theorem simpleOrOnLine_proportion_lower_small
    (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1 / 8) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
            / (3 + 2 * Real.sqrt 2) - ε <
        (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) := by
  obtain ⟨eta, C, heta, hC, hsum⟩ := kernelConstruction hPC (ε / 2) (by positivity)
  rw [abs_lt] at hC
  have hlo := montgomeryTaylorConst_gt
  have hhi := montgomeryTaylorConst_lt
  set Ac : ℝ := C + ε / 2 with hAc
  have hA1 : 1 ≤ Ac := by rw [hAc]; linarith
  have hA2 : Ac < 2 := by rw [hAc]; linarith
  have hNscale := hRvM.tendsto
  have hscale : ∀ᶠ T : ℝ in atTop, zeroScale T ≠ 0 :=
    zeroScale_pos_eventually.mono fun _ h => ne_of_gt h
  have hratio : Tendsto
      (fun T => (unweightedKernelSum eta T).re / (zeroCount T : ℝ)) atTop (nhds C) :=
    tendsto_ratio_of_tendsto_div_scale _ _ _ _ hNscale hsum hscale
  have hNpos := hRvM.zeroCount_pos_eventually
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

/-- **Zeros that are simple or on the critical line.** -/
@[zz_tag "thm_simple_or_critical"]
theorem simpleOrOnLine_proportion_lower (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
            / (3 + 2 * Real.sqrt 2) - ε <
        (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) := by
  rcases le_or_gt ε (1 / 8) with h | h
  · exact simpleOrOnLine_proportion_lower_small hRvM hPC ε hε h
  · obtain ⟨T₀, hT₀⟩ :=
      simpleOrOnLine_proportion_lower_small hRvM hPC (1 / 8) (by norm_num) le_rfl
    exact ⟨T₀, fun T hT => by linarith [hT₀ T hT]⟩

/-- Beyond some height, more than `67.25%` of the non-trivial zeros of the Riemann zeta function
are simple and lie on the critical line. -/
@[zz_tag "thm_simple_numeric"]
theorem simple_proportion_d4 (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.6725 < (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) := by
  have hconst : (0.6725 : ℝ) <
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) := by
    rw [show 3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) =
      2 - montgomeryTaylorConst by
        rw [montgomeryTaylorConst]
        ring]
    linarith [montgomeryTaylorConst_lt]
  obtain ⟨T₀, hT₀⟩ := simple_proportion_lower hRvM hPC
    (3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - 0.6725)
    (sub_pos.mpr hconst)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- Beyond some height, more than `83.625%` of the non-trivial zeros of the Riemann zeta function
are distinct. -/
@[zz_tag "thm_distinct_numeric"]
theorem distinct_proportion_d5 (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.83625 < (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) := by
  have hconst : (0.83625 : ℝ) <
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) := by
    rw [show 5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) =
      3 / 2 - montgomeryTaylorConst / 2 by
        rw [montgomeryTaylorConst]
        ring]
    linarith [montgomeryTaylorConst_lt]
  obtain ⟨T₀, hT₀⟩ := distinct_proportion_lower hRvM hPC
    (5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - 0.83625)
    (sub_pos.mpr hconst)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- **More than `83.625%` on average.** -/
@[zz_tag "thm_average_numeric"]
theorem average_proportion_d5 (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      0.83625 < ((simpleZeroCount T : ℝ) + (onLineCount T : ℝ)) / (2 * (zeroCount T : ℝ)) := by
  have hconst : (0.83625 : ℝ)
      < 5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) := by
    rw [show 5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2)
        = 3 / 2 - montgomeryTaylorConst / 2 by rw [montgomeryTaylorConst]; ring]
    linarith [montgomeryTaylorConst_lt]
  obtain ⟨T₀, hT₀⟩ := average_proportion_lower hRvM hPC
    (5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - 0.83625)
    (sub_pos.mpr hconst)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- **More than `88.76%` simple or on the critical line.** Four decimal places and not five: see
`simpleOrOnLineProportion_gt`. -/
@[zz_tag "thm_simple_or_critical_numeric"]
theorem simpleOrOnLine_proportion_d4 (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.8876 < (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) := by
  have hconst : (0.8876 : ℝ)
      < (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
          / (3 + 2 * Real.sqrt 2) := simpleOrOnLineProportion_gt
  obtain ⟨T₀, hT₀⟩ := simpleOrOnLine_proportion_lower hRvM hPC
    ((4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
      / (3 + 2 * Real.sqrt 2) - 0.8876) (sub_pos.mpr hconst)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

end ZetaZeros
