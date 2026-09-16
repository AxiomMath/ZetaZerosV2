import ErdosProblems.Erdos421.MeanSquare
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # The elementary separated large-value bound for Dirichlet polynomials -/

namespace Erdos421

open Complex MeasureTheory

theorem oscillatoryPhase_hasDerivAt (ω t : ℝ) :
    HasDerivAt (oscillatoryPhase ω)
      ((Complex.I * (ω : ℂ)) * oscillatoryPhase ω t) t := by
  unfold oscillatoryPhase
  have h := ((Complex.hasDerivAt_exp (Complex.I * (ω : ℂ) * (t : ℂ))).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul (Complex.I * (ω : ℂ)))).comp_ofReal
  simpa only [Function.comp_apply, mul_one, mul_comm] using! h

end Erdos421
