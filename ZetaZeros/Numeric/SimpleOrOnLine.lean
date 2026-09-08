/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import ZetaZeros.Numeric.MontgomeryTaylor

/-!
# The proportion of zeros that are simple or on the critical line

The constant `C₂ = (4 + 2√2 - √2 cot(1/√2)) / (3 + 2√2)`, its closed form in terms of the
Montgomery--Taylor constant, and the elementary bounds that place it above `0.8876`.
-/

@[expose] public section

namespace ZetaZeros

/-- The proportion of zeros shown simple or on the critical line,
`(4 + 2√2 - √2 cot(1/√2)) / (3 + 2√2) = 0.8876200082…`. -/
@[zz_tag "def_C2"]
noncomputable def simpleOrOnLineProportion : ℝ :=
  (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2)) / (3 + 2 * Real.sqrt 2)

/-- `√2 > 1.4142`, which is what the numeric bound on `C₂` needs: the margin there is
`0.2248 * √2 > 0.3178`, and `0.2248 * 1.4142 = 0.31791216`. -/
@[zz_tag "lem_sqrt2_lower"]
theorem sqrt_two_gt : (1.4142 : ℝ) < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- **Four terms bound `cos(1/√2)` from below** (`lem_cos_lower`). The partial sum is
`0.760243055…`, and `range (2 * 2)` ends at an odd index, so the bracketing gives a lower bound. -/
@[zz_tag "lem_cos_lower"]
theorem cos_inv_sqrt_two_gt : 0.76 < Real.cos (1 / Real.sqrt 2) := by
  have h := Antitone.alternating_series_le_tendsto
    hasSum_cosTerm.tendsto_sum_nat cosTerm_antitone 2
  have hsum : (0.76 : ℝ) < ∑ i ∈ Finset.range (2 * 2), (-1 : ℝ) ^ i * cosTerm i := by
    norm_num [Finset.sum_range_succ, cosTerm, Nat.factorial]
  linarith

/-- **The sine is dominated by its argument.** This is Mathlib's `Real.sin_lt`. -/
@[zz_tag "lem_sin_lt_self"]
theorem sin_lt_self {x : ℝ} (hx : 0 < x) : Real.sin x < x := Real.sin_lt hx

/-- `√2 sin(1/√2) < 1`, because `sin x < x` for positive `x`. -/
theorem sqrt_two_mul_sin_inv_sqrt_two_lt_one :
    Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) < 1 := by
  have hpos : (0:ℝ) < Real.sqrt 2 := by positivity
  have h := sin_lt_self (show (0:ℝ) < 1 / Real.sqrt 2 by positivity)
  have hid : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by
    field_simp
  calc Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)
      < Real.sqrt 2 * (1 / Real.sqrt 2) := mul_lt_mul_of_pos_left h hpos
    _ = 1 := hid

/-- `(1/√2) cot(1/√2) > 0.75`: the numerator exceeds `0.76` and the denominator is below `1`. -/
theorem inv_sqrt_two_mul_cot_gt : 0.75 < (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) := by
  have hs : 0 < Real.sin (1 / Real.sqrt 2) := sin_inv_sqrt_two_pos
  have hden : 0 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) := by positivity
  have hcot : (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2)
      = Real.cos (1 / Real.sqrt 2) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)) := by
    rw [Real.cot_eq_cos_div_sin]
    field_simp
  rw [hcot, lt_div_iff₀ hden]
  linarith [cos_inv_sqrt_two_gt, sqrt_two_mul_sin_inv_sqrt_two_lt_one]

/-- **`C_MT > 1.25`** (`lem_cmt_lower`). This is what makes the side condition `1 ≤ A < 2`
manufacturable: with `A = C + ε/2` and `ε < 1/4`, `C > C_MT - ε/2 > 1`. -/
@[zz_tag "lem_cmt_lower"]
theorem montgomeryTaylorConst_gt : 1.25 < montgomeryTaylorConst := by
  have := inv_sqrt_two_mul_cot_gt
  rw [montgomeryTaylorConst]
  linarith

/-- **`C₂ = (5 + 2√2 - 2 C_MT) / (3 + 2√2)`** (`lem_C2_eq`). The whole content is `2/√2 = √2`,
supplied here by rewriting `1/√2` as `√2/2` on both sides. -/
@[zz_tag "lem_C2_eq"]
theorem simpleOrOnLineProportion_eq :
    simpleOrOnLineProportion
      = (5 + 2 * Real.sqrt 2 - 2 * montgomeryTaylorConst) / (3 + 2 * Real.sqrt 2) := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hhalf : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff hs (by norm_num : (2:ℝ) ≠ 0)]
    linarith [h2]
  rw [simpleOrOnLineProportion, montgomeryTaylorConst, hhalf]
  ring

/-- **`C₂ > 0.8876`** (`lem_C2_lower`). Four decimal places, not five: `C_MT < 1.3275` gives only
`C₂ > 0.887619766…`, which clears `0.8876` and does **not** clear `0.88762`. The margin is
`0.2248 * √2 > 0.3178`, and `0.2248 * 1.4142 = 0.31791216`. -/
@[zz_tag "lem_C2_lower"]
theorem simpleOrOnLineProportion_gt : 0.8876 < simpleOrOnLineProportion := by
  have hs : (1.4142 : ℝ) < Real.sqrt 2 := sqrt_two_gt
  have hcmt : montgomeryTaylorConst < 1.3275 := montgomeryTaylorConst_lt
  have hden : (0 : ℝ) < 3 + 2 * Real.sqrt 2 := by positivity
  rw [simpleOrOnLineProportion_eq, lt_div_iff₀ hden]
  linarith

end ZetaZeros
