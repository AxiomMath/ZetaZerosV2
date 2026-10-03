/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Proportions
public import ZetaZeros.ZeroCount.RiemannVonMangoldt

/-!
# Decimal forms of the average and simple-or-on-line proportion bounds

## Main results

* `average_proportion_d5`: beyond some height, the average of the proportion of simple zeros and
  the proportion of zeros on the critical line (counted with multiplicity) exceeds `0.83625`.
* `simpleOrOnLine_proportion_d4`: beyond some height, more than `88.76%` of the zeros, counted with
  multiplicity, are simple or on the critical line.
-/

@[expose] public section

namespace ZetaZeros

/-- **More than `83.625%` on average.** Beyond some height,
`(simpleZeroCount T + onLineCount T) / (2 zeroCount T) > 0.83625`. -/
@[zz_tag "thm_average_numeric"]
theorem average_proportion_d5 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      0.83625 < ((simpleZeroCount T : ℝ) + (onLineCount T : ℝ)) / (2 * (zeroCount T : ℝ)) := by
  have hconst : (0.83625 : ℝ)
      < 5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) := by
    rw [show 5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2)
        = 3 / 2 - montgomeryTaylorConst / 2 by rw [montgomeryTaylorConst]; ring]
    linarith [montgomeryTaylorConst_lt]
  obtain ⟨T₀, hT₀⟩ := average_proportion_lower
    (5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - 0.83625)
    (sub_pos.mpr hconst)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- **More than `88.76%` simple or on the critical line.** Beyond some height,
`simpleOrOnLineCount T / zeroCount T > 0.8876`. -/
@[zz_tag "thm_simple_or_critical_numeric"]
theorem simpleOrOnLine_proportion_d4 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.8876 < (simpleOrOnLineCount T : ℝ) / (zeroCount T : ℝ) := by
  have hconst : (0.8876 : ℝ)
      < (4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
          / (3 + 2 * Real.sqrt 2) := simpleOrOnLineProportion_gt
  obtain ⟨T₀, hT₀⟩ := simpleOrOnLine_proportion_lower
    ((4 + 2 * Real.sqrt 2 - Real.sqrt 2 * Real.cot (1 / Real.sqrt 2))
      / (3 + 2 * Real.sqrt 2) - 0.8876) (sub_pos.mpr hconst)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

end ZetaZeros
