import ErdosProblems.Erdos421.PrimePowerTuples

/-! # Reducing triangular polynomial systems to power sums -/

namespace Erdos421

open Polynomial

section CommRing

variable {R : Type*} [CommRing R] {m n : ℕ}

theorem sum_eval_eq_sum_coeff_power (x : Fin m → R) (P : R[X]) {k : ℕ}
    (hP : P.natDegree ≤ k) :
    (∑ i : Fin m, P.eval (x i)) =
      ∑ j ∈ Finset.range (k + 1), P.coeff j * ∑ i : Fin m, x i ^ j := by
  simp_rw [Polynomial.eval_eq_sum_range' (p := P) (Nat.lt_succ_of_le hP)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end CommRing

end Erdos421
