import ErdosProblems.Erdos421.LogarithmicSecondDerivative

/-! # Small- and large-frequency bounds for logarithmic sums -/

namespace Erdos421

theorem logarithmicSum_norm_le (M N : ℕ) (τ : ℝ) : ‖logarithmicSum M N τ‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖oscillatoryPhase (Real.log (M + n : ℕ)) τ‖ := norm_sum_le _ _
    _ = _ := by simp

theorem oscillatoryPhase_neg_time (ω t : ℝ) :
    oscillatoryPhase ω (-t) = starRingEnd ℂ (oscillatoryPhase ω t) := by
  simp only [oscillatoryPhase, Complex.ofReal_neg, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal]
  congr 1
  ring

theorem logarithmicSum_neg (M N : ℕ) (τ : ℝ) :
    logarithmicSum M N (-τ) = starRingEnd ℂ (logarithmicSum M N τ) := by
  simp only [logarithmicSum, oscillatoryPhase_neg_time, map_sum]

end Erdos421
