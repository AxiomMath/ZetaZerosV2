import ErdosProblems.Erdos421.PrimeAvoidance
import Mathlib.NumberTheory.Bertrand

/-! # Finite prime pools from Bertrand's postulate

The interval expands by a degree-dependent constant. No asymptotic
prime-counting theorem is needed to construct these pools.
-/

namespace Erdos421

theorem exists_prime_pool (M r : ℕ) (hM : 0 < M) :
    ∃ S : Finset ℕ, S.card = r ∧ ∀ p ∈ S, p.Prime ∧ M < p ∧ p ≤ 2 ^ r * M := by
  classical
  have hex (i : Fin r) : ∃ p : ℕ, p.Prime ∧ 2 ^ (i : ℕ) * M < p ∧
      p ≤ 2 * (2 ^ (i : ℕ) * M) :=
    Nat.exists_prime_lt_and_le_two_mul _ (Nat.mul_pos (pow_pos (by decide) _) hM).ne'
  choose P hP hlo hhi using hex
  have hmono : StrictMono P := by
    intro i j hij
    calc
      P i ≤ 2 * (2 ^ (i : ℕ) * M) := hhi i
      _ = 2 ^ ((i : ℕ) + 1) * M := by rw [pow_succ]; ring
      _ ≤ 2 ^ (j : ℕ) * M :=
        Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hij))
      _ < P j := hlo j
  refine ⟨Finset.univ.image P, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨hP i, ?_, ?_⟩
    · apply lt_of_le_of_lt _ (hlo i)
      exact Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
    · calc
        P i ≤ 2 * (2 ^ (i : ℕ) * M) := hhi i
        _ = 2 ^ ((i : ℕ) + 1) * M := by rw [pow_succ]; ring
        _ ≤ 2 ^ r * M :=
          Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt i.isLt))

theorem root_scale_prime_pool_bound {n N M : ℕ}
    (hn : 0 < n) (hM : 1 < M) (hN : N ≤ M ^ n) :
    N ^ (2 * (n * (n - 1))) < M ^ (2 * n ^ 3) := by
  have he : n * (2 * (n * (n - 1))) < 2 * n ^ 3 := by
    have hid : n * (2 * (n * (n - 1))) + 2 * n ^ 2 = 2 * n ^ 3 := by
      calc
        _ = 2 * n * n * (n - 1 + 1) := by ring
        _ = 2 * n ^ 3 := by rw [Nat.sub_add_cancel hn]; ring
    have hp : 0 < 2 * n ^ 2 := Nat.mul_pos (by decide) (pow_pos hn _)
    omega
  calc
    _ ≤ (M ^ n) ^ (2 * (n * (n - 1))) := Nat.pow_le_pow_left hN _
    _ = M ^ (n * (2 * (n * (n - 1)))) := (pow_mul _ _ _).symm
    _ < M ^ (2 * n ^ 3) := pow_lt_pow_right₀ hM he

end Erdos421
