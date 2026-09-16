/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationEndpoint

/-!
# Elementary error bounds for pair correlation

This file records the two real-variable estimates used to put the integrated endpoint error
in the `1 / sqrt (log T)` scale of the unconditional pair-correlation statement.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open MeasureTheory

/-- Above one, reciprocal decay is stronger than reciprocal-square-root decay. -/
theorem inv_le_inv_sqrt (L : ℝ) (hL : 1 ≤ L) :
    1 / L ≤ 1 / Real.sqrt L := by
  have hsqrtPos : 0 < Real.sqrt L := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hL)
  apply one_div_le_one_div_of_le hsqrtPos
  exact Real.sqrt_le_self_iff.2 (Or.inr hL)

end ZetaZeros.Unconditional.PairCorrelationProof
