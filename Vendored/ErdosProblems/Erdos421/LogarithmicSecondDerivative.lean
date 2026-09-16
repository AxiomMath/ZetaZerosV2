import ErdosProblems.Erdos421.LogarithmicSums
import ErdosProblems.Erdos421.PhasePartition

/-! # A second-derivative bound for logarithmic exponential sums -/

namespace Erdos421

theorem logarithmicSum_eq_phase_sum (M N : ℕ) (τ : ℝ) :
    logarithmicSum M N τ =
      ∑ n ∈ Finset.range N, oscillatoryPhase 1 (τ * Real.log (M + n : ℕ)) := by
  apply Finset.sum_congr rfl
  intro n _
  unfold oscillatoryPhase
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_one, mul_one]
  ring

end Erdos421
