import ErdosProblems.Erdos421.DifferenceConstants
import ErdosProblems.Erdos421.ZetaHeightParameters
import ErdosProblems.Erdos421.ZetaTailScale
import ErdosProblems.Erdos421.ZetaHeightWeight

/-! # Constants in the zeta strip estimate, uniformly in the difference order -/

namespace Erdos421

theorem one_sub_two_rpow_neg_half_lower {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    d / 8 ≤ 1 - (2 : ℝ) ^ (-d / 2) := by
  have hlog : 1 / 2 ≤ Real.log 2 := by
    have h := log_difference_lower (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  let x : ℝ := d * Real.log 2 / 2
  have hx : 0 < x := by dsimp only [x]; positivity
  have hx1 : x ≤ 1 := by dsimp only [x]; nlinarith
  have hdx : d / 8 ≤ x / 2 := by dsimp only [x]; nlinarith
  have he : (2 : ℝ) ^ (-d / 2) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp only [x]
    ring
  have hexp : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hq : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) hexp
  have hfrac : x / 2 ≤ x / (1 + x) :=
    div_le_div_of_nonneg_left hx.le (by linarith) (by linarith)
  have hid : x / (1 + x) = 1 - 1 / (1 + x) := by field_simp; ring
  rw [he]
  rw [hid] at hfrac
  linarith

end Erdos421
