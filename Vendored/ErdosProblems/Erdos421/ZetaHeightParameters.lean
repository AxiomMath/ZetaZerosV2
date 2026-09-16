import ErdosProblems.Erdos421.ZetaDyadic
import ErdosProblems.Erdos421.ZetaTruncation

/-! # Explicit dyadic parameter choices for the zeta strip estimate -/

namespace Erdos421

theorem dyadic_rpow_le_dyadic {L W : ℕ} {a : ℝ} (h : (L : ℝ) * a ≤ W) :
    (((2 ^ L : ℕ) : ℝ)) ^ a ≤ ((2 ^ W : ℕ) : ℝ) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num),
    Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem zeta_height_scale_pole_weight {u : ℕ} (hu : 0 < u) (R : ℕ)
    {a : ℝ} (ha : a ≤ 1 / 4) :
    (((2 ^ (2 * ((R + 1) * (u + 1))) : ℕ) : ℝ)) ^ a ≤
      ((2 ^ ((R + 1) * u) : ℕ) : ℝ) := by
  apply dyadic_rpow_le_dyadic
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have h₁ := mul_le_mul_of_nonneg_left ha
    (show (0 : ℝ) ≤ (2 * ((R + 1) * (u + 1)) : ℕ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (show (u : ℝ) + 1 ≤ 2 * u by linarith)
    (show 0 ≤ ((R : ℝ) + 1) by positivity)
  push_cast at h₁ ⊢
  nlinarith

end Erdos421
