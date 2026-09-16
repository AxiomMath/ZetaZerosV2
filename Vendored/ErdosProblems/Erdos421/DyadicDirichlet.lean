import ErdosProblems.Erdos421.MeanSquare
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import ErdosProblems.Erdos421.LogarithmicBounds
import ErdosProblems.Erdos421.HilbertLargeValues
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Dyadic decompositions of finite Dirichlet polynomials -/

namespace Erdos421

theorem sum_dyadic_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R) (K : ℕ) :
    (∑ j ∈ Finset.range K, ∑ n ∈ Finset.range (2 ^ j), f (2 ^ j + n)) =
      ∑ n ∈ Finset.Ico 1 (2 ^ K), f n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have hsplit := Finset.sum_Ico_consecutive f
      (show 1 ≤ 2 ^ K from one_le_pow₀ (by norm_num)) (show 2 ^ K ≤ 2 ^ (K + 1) by
        rw [pow_succ]
        omega)
    rw [← hsplit, Finset.sum_Ico_eq_sum_range f (2 ^ K) (2 ^ (K + 1))]
    have hlen : 2 ^ (K + 1) - 2 ^ K = 2 ^ K := by rw [pow_succ]; omega
    rw [hlen]

end Erdos421
