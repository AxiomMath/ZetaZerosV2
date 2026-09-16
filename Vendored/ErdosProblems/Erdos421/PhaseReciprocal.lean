import ErdosProblems.Erdos421.LargeValues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Reciprocal phase bounds for the first-derivative exponential-sum test -/

namespace Erdos421

open Complex MeasureTheory

noncomputable def phaseReciprocal (x : ℝ) : ℂ := (oscillatoryPhase 1 x - 1)⁻¹

theorem integral_four_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 4 / x ^ 2) = 4 / a - 4 / b := by
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    exact ha.not_ge h.1
  have h := integral_zpow (a := a) (b := b) (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hzero⟩)
  have hf : (fun x : ℝ ↦ 4 / x ^ 2) = fun x ↦ 4 * x ^ (-2 : ℤ) := by
    ext x
    simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv]
  rw [hf, intervalIntegral.integral_const_mul, h]
  norm_num [div_eq_mul_inv]
  ring

end Erdos421
