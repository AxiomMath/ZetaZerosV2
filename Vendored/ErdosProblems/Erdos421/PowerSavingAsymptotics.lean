import ErdosProblems.Erdos421.LogPowerNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Explicit exponents and logarithmic decay of the power saving -/

namespace Erdos421

open Filter Topology

noncomputable def logarithmicSavingExponent (R K : ℕ) : ℝ :=
  ((K : ℝ) * ((2 ^ R : ℕ) : ℝ))⁻¹

noncomputable def logarithmicSavingConstant (R : ℕ) : ℝ :=
  (2 * logarithmicDifferenceConstant R) ^ (((2 ^ R : ℕ) : ℝ)⁻¹)

theorem logarithmicPowerSaving_eq {M : ℕ} (hM : 0 < M) (R K : ℕ) :
    logarithmicPowerSaving M R K = logarithmicSavingConstant R /
      (M : ℝ) ^ (logarithmicSavingExponent R K) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hc := logarithmicDifferenceConstant_pos R
  unfold logarithmicPowerSaving logarithmicSavingConstant logarithmicSavingExponent
  rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hMp.le]
  congr 2
  rw [mul_inv]

end Erdos421
