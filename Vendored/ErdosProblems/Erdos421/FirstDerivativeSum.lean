import ErdosProblems.Erdos421.PhaseReciprocalPi

/-! # A first-derivative exponential-sum bound for small monotone increments -/

namespace Erdos421

theorem sum_difference_mul (w a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (w (n + 1) - w n) * a n) =
      w N * a N - w 0 * a 0 - ∑ n ∈ Finset.range N, w (n + 1) * (a (n + 1) - a n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

def phaseIncrement (f : ℕ → ℝ) (n : ℕ) : ℝ := f (n + 1) - f n

theorem phase_increment_step (f : ℕ → ℝ) (n : ℕ) :
    oscillatoryPhase 1 (f (n + 1)) =
      oscillatoryPhase 1 (f n) * oscillatoryPhase 1 (phaseIncrement f n) := by
  unfold oscillatoryPhase phaseIncrement
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end Erdos421
