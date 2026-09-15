/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationSharpComparison
import ZetaZeros.Unconditional.PairCorrelationLocalCount

/-!
# Quantitative tails for the Lorentzian zero sum

This file supplies the high-ordinate tail estimate used to compare the full zero side of
Montgomery's explicit formula with a finite zero window.  The elementary analytic input is a
telescoping bound for `1 / (u * sqrt u)`; it implies the required `log Z / Z` decay without
invoking an improper integral.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex Finset

/-- A square-root telescoping step. -/
lemma inv_mul_sqrt_step {a : ℝ} (ha : 0 < a) :
    1 / ((a + 1) * Real.sqrt (a + 1)) ≤
      2 * (1 / Real.sqrt a - 1 / Real.sqrt (a + 1)) := by
  have ha1 : 0 < a + 1 := by linarith
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsa1 : 0 < Real.sqrt (a + 1) := Real.sqrt_pos.2 ha1
  have hsle : Real.sqrt a ≤ Real.sqrt (a + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  rw [div_le_iff₀ (mul_pos ha1 hsa1)]
  field_simp [ne_of_gt hsa, ne_of_gt hsa1]
  nlinarith [Real.sq_sqrt ha.le, Real.sq_sqrt ha1.le,
    mul_le_mul_of_nonneg_left hsle (Real.sqrt_nonneg a)]

/-- Partial sums of the translated `u⁻³ᐟ²` majorant telescope against `u⁻¹ᐟ²`. -/
lemma sum_inv_mul_sqrt_le_telescope {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range (n + 1), 1 / ((D + i) * Real.sqrt (D + i)) ≤
      1 / (D * Real.sqrt D) +
        2 * (1 / Real.sqrt D - 1 / Real.sqrt (D + n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ]
      have hstep := inv_mul_sqrt_step (a := D + n) (by positivity)
      have heq : D + ((n + 1 : ℕ) : ℝ) = D + n + 1 := by
        push_cast
        ring
      rw [heq]
      calc
        (∑ i ∈ range (n + 1), 1 / ((D + i) * Real.sqrt (D + i))) +
              1 / ((D + n + 1) * Real.sqrt (D + n + 1)) ≤
            (1 / (D * Real.sqrt D) +
                2 * (1 / Real.sqrt D - 1 / Real.sqrt (D + n))) +
              2 * (1 / Real.sqrt (D + n) - 1 / Real.sqrt (D + n + 1)) :=
          add_le_add ih hstep
        _ = 1 / (D * Real.sqrt D) +
              2 * (1 / Real.sqrt D - 1 / Real.sqrt (D + n + 1)) := by ring

/-- Uniform finite-sum bound for the translated `u⁻³ᐟ²` majorant. -/
lemma sum_inv_mul_sqrt_le {D : ℝ} (hD : 1 ≤ D) (n : ℕ) :
    ∑ i ∈ range n, 1 / ((D + i) * Real.sqrt (D + i)) ≤
      3 / Real.sqrt D := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  cases n with
  | zero =>
      simp only [range_zero, one_div, mul_inv_rev, sum_empty, ge_iff_le]
      positivity
  | succ n =>
      refine (sum_inv_mul_sqrt_le_telescope hDpos n).trans ?_
      have hsqrt : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
      have hlast : 0 ≤ 1 / Real.sqrt (D + n) := by positivity
      have hfirst : 1 / (D * Real.sqrt D) ≤ 1 / Real.sqrt D := by
        rw [div_le_div_iff₀ (mul_pos hDpos hsqrt) hsqrt]
        nlinarith [Real.sq_sqrt hDpos.le]
      have hdiff :
          1 / Real.sqrt D - 1 / Real.sqrt (D + n) ≤ 1 / Real.sqrt D :=
        sub_le_self _ hlast
      calc
        1 / (D * Real.sqrt D) +
              2 * (1 / Real.sqrt D - 1 / Real.sqrt (D + n)) ≤
            1 / Real.sqrt D + 2 * (1 / Real.sqrt D) :=
          add_le_add hfirst (mul_le_mul_of_nonneg_left hdiff (by norm_num))
        _ = 3 / Real.sqrt D := by ring

/-- Above a base point whose logarithm is at least one, logarithmic growth is absorbed by a
square-root ratio. -/
lemma log_le_three_mul_log_mul_sqrt_ratio {D y : ℝ}
    (hD : Real.exp 1 ≤ D) (hy : D ≤ y) :
    Real.log y ≤ 3 * Real.log D * Real.sqrt (y / D) := by
  have hDpos : 0 < D := (Real.exp_pos 1).trans_le hD
  have hypos : 0 < y := hDpos.trans_le hy
  have hratio : 1 ≤ y / D := (le_div_iff₀ hDpos).2 (by simpa using hy)
  have hratiopos : 0 < y / D := zero_lt_one.trans_le hratio
  have hsqrt_sq := Real.sq_sqrt hratiopos.le
  have hsqrt_nonneg := Real.sqrt_nonneg (y / D)
  have hsqrt_one : 1 ≤ Real.sqrt (y / D) := by nlinarith
  have hlogD : 1 ≤ Real.log D := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hD
  have hlogratio : Real.log (y / D) ≤ 2 * Real.sqrt (y / D) := by
    have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hratiopos)
    rw [Real.log_sqrt hratiopos.le] at hlog
    linarith
  have hfirst : Real.log D ≤ Real.log D * Real.sqrt (y / D) := by
    nlinarith [mul_nonneg (show 0 ≤ Real.log D by linarith)
      (show 0 ≤ Real.sqrt (y / D) - 1 by linarith)]
  have hsecond : 2 * Real.sqrt (y / D) ≤
      2 * Real.log D * Real.sqrt (y / D) := by
    nlinarith [mul_nonneg (show 0 ≤ Real.log D - 1 by linarith) hsqrt_nonneg]
  rw [show y = D * (y / D) by field_simp]
  rw [Real.log_mul hDpos.ne' hratiopos.ne']
  rw [show D * (y / D) / D = y / D by field_simp]
  nlinarith

end ZetaZeros.Unconditional.PairCorrelationProof
