import ErdosProblems.Erdos421.FirstDerivativeSum

/-! # A small-frequency bound for logarithmic exponential sums -/

namespace Erdos421

noncomputable def logarithmicSum (M N : ℕ) (τ : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, oscillatoryPhase (Real.log (M + n : ℕ)) τ

end Erdos421
