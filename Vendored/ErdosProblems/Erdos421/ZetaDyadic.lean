import ErdosProblems.Erdos421.ZetaBlocks
import ErdosProblems.Erdos421.PowerSavingAsymptotics
import ErdosProblems.Erdos421.DyadicDirichlet

/-! # Dyadic bounds for zeta polynomials near the line Re(s) = 1 -/

namespace Erdos421

theorem zetaBlock_trivial_norm_bound {M : ℕ} (hM : 0 < M) (N : ℕ)
    (s : ℂ) (hs : 0 ≤ s.re) :
    ‖zetaBlock M N s‖ ≤ (M : ℝ) ^ (-s.re) * N := by
  exact zetaBlock_norm_le_of_prefix_bounds hM N s hs (Nat.cast_nonneg N)
    (fun n hn ↦ (logarithmicSum_norm_le M n _).trans (by exact_mod_cast hn))

theorem zetaBlock_trivial_norm_bound_of_length_le {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (s : ℂ) (hs : 0 ≤ s.re) :
    ‖zetaBlock M N s‖ ≤ (M : ℝ) ^ (1 - s.re) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ ≤ (M : ℝ) ^ (-s.re) * N := zetaBlock_trivial_norm_bound hM N s hs
    _ ≤ (M : ℝ) ^ (-s.re) * M :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hN) (by positivity)
    _ = _ := by rw [sub_eq_add_neg, Real.rpow_add hMp, Real.rpow_one]; ring

theorem zetaBlock_one_dyadic (L : ℕ) (s : ℂ) :
    zetaBlock 1 (2 ^ L - 1) s = ∑ j ∈ Finset.range L, zetaBlock (2 ^ j) (2 ^ j) s := by
  have he := sum_dyadic_blocks (fun n : ℕ ↦ (n : ℂ) ^ (-s)) L
  rw [Finset.sum_Ico_eq_sum_range] at he
  simpa only [zetaBlock, Nat.add_comm 1] using he.symm

theorem zetaBlock_one_dyadic_trivial_bound (L : ℕ) (s : ℂ) (hs : 0 ≤ s.re)
    (hs1 : s.re ≤ 1) :
    ‖zetaBlock 1 (2 ^ L - 1) s‖ ≤ L * ((2 ^ L : ℕ) : ℝ) ^ (1 - s.re) := by
  rw [zetaBlock_one_dyadic]
  calc
    _ ≤ ∑ j ∈ Finset.range L, ‖zetaBlock (2 ^ j) (2 ^ j) s‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range L, ((2 ^ L : ℕ) : ℝ) ^ (1 - s.re) := by
      apply Finset.sum_le_sum
      intro j hj
      apply (zetaBlock_trivial_norm_bound_of_length_le (by positivity) le_rfl s hs).trans
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (sub_nonneg.mpr hs1)
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) (Finset.mem_range.mp hj).le
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Erdos421
