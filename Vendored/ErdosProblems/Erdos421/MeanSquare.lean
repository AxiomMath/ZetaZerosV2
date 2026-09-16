import ErdosProblems.Erdos421.DirichletMeanValue
import Mathlib.Data.Nat.Dist
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # An elementary mean-square bound with a logarithmic loss -/

namespace Erdos421

open Complex MeasureTheory
open scoped ComplexConjugate

theorem symmetric_weighted_sum_le (S : Finset ℕ) (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    {R : ℝ} (hw : ∀ m n, 0 ≤ w m n) (hsym : ∀ m n, w m n = w n m)
    (hrow : ∀ m ∈ S, (∑ n ∈ S, w m n) ≤ R) :
    (∑ m ∈ S, ∑ n ∈ S, 2 * x m * x n * w m n) ≤ 2 * R * (∑ m ∈ S, x m ^ 2) := by
  have hsplit : (∑ m ∈ S, ∑ n ∈ S, (x m ^ 2 + x n ^ 2) * w m n) =
      2 * (∑ m ∈ S, x m ^ 2 * (∑ n ∈ S, w m n)) := by
    simp_rw [add_mul, Finset.sum_add_distrib]
    have hfirst : (∑ m ∈ S, ∑ n ∈ S, x m ^ 2 * w m n) =
        ∑ m ∈ S, x m ^ 2 * (∑ n ∈ S, w m n) := by simp only [Finset.mul_sum]
    have hsecond : (∑ m ∈ S, ∑ n ∈ S, x n ^ 2 * w m n) =
        ∑ m ∈ S, x m ^ 2 * (∑ n ∈ S, w m n) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      simp_rw [hsym _ n, ← Finset.mul_sum]
    rw [hfirst, hsecond]
    ring
  calc
    _ ≤ ∑ m ∈ S, ∑ n ∈ S, (x m ^ 2 + x n ^ 2) * w m n := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (x m - x n)]) (hw m n)
    _ = 2 * (∑ m ∈ S, x m ^ 2 * (∑ n ∈ S, w m n)) := hsplit
    _ ≤ 2 * (∑ m ∈ S, x m ^ 2 * R) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun m hm ↦ mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _))
    _ = 2 * R * (∑ m ∈ S, x m ^ 2) := by rw [← Finset.sum_mul]; ring

end Erdos421
