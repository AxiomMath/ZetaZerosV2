import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Oscillatory kernels for Dirichlet-polynomial mean values

These elementary integral estimates begin the analytic infrastructure for
the long-gap argument. They do not assert Li's almost-all interval theorem.
-/

namespace Erdos421

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable def oscillatoryPhase (ω t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))

@[simp] theorem norm_oscillatoryPhase (ω t : ℝ) : ‖oscillatoryPhase ω t‖ = 1 := by
  simp [oscillatoryPhase, Complex.norm_exp]

theorem oscillatoryPhase_mul_conj (ω ν t : ℝ) :
    oscillatoryPhase ω t * conj (oscillatoryPhase ν t) = oscillatoryPhase (ω - ν) t := by
  unfold oscillatoryPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

/-- The elementary logarithmic lower bound for two distinct positive terms. -/
theorem log_difference_lower {m n : ℝ} (hm : 0 < m) (hmn : m < n) :
    (n - m) / n ≤ Real.log n - Real.log m := by
  have hn : 0 < n := hm.trans hmn
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hn hm)
  rw [Real.log_div hn.ne' hm.ne', inv_div] at h
  have heq : 1 - m / n = (n - m) / n := by field_simp
  rwa [heq] at h

end Erdos421
