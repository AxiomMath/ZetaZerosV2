/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Landau.Symmetrisation

/-!
# The symmetric partial sums move slowly

For `x > 1`, the symmetric partial sums `∑_{ρ ∈ heightWindow U} landauZeroTerm x s ρ` of the zero
side of Landau's explicit formula change by `O(log U / U)` as `U` increases by at most `1`. The
estimate combines the bound `O(m_ρ / U)` for a single term at a zero with `|im ρ| > U` and the
bound `O(log U)` for the total multiplicity of the zeros with `U < |im ρ| ≤ U + 1`, the latter
obtained from the Poisson-weight sums `ZetaZeros.exists_summable_poissonWeight_tsum_le` at
`±(U + 1)`.

## Main results

* `ZetaZeros.exists_norm_sum_heightWindow_sub_le`: the symmetric partial sums move by
  `O(log U / U)` across one unit interval of heights.
-/

@[expose] public section

namespace ZetaZeros

open Filter

/-- The Poisson weight of a zero at height `t`, as in
`ZetaZeros.exists_summable_poissonWeight_tsum_le`. -/
private noncomputable def pWeight (t : ℝ) (ρ : allZeros) : ℝ :=
  (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)

private lemma pWeight_nonneg (t : ℝ) (ρ : allZeros) : 0 ≤ pWeight t ρ := by
  unfold pWeight
  have : (0 : ℝ) < 1 + (t - (ρ : ℂ).im) ^ 2 := by positivity
  positivity

/-- **The multiplicity of a zero of the annulus is dominated by the two Poisson weights at
`±(U+1)`.** For `U < |im ρ| ≤ U + 1`, `m_ρ` is at most twice the sum of the Poisson weights
of `ρ` at `U + 1` and at `-(U + 1)`. -/
private lemma multiplicity_le_pWeight_add {U : ℝ} {ρ : allZeros}
    (hlo : U < |(ρ : ℂ).im|) (hhi : |(ρ : ℂ).im| ≤ U + 1) :
    (zeroMultiplicity (ρ : ℂ) : ℝ) ≤ 2 * pWeight (U + 1) ρ + 2 * pWeight (-(U + 1)) ρ := by
  have hm : (0 : ℝ) ≤ (zeroMultiplicity (ρ : ℂ) : ℝ) := Nat.cast_nonneg _
  have hside : |(U + 1) - (ρ : ℂ).im| ≤ 1 ∨ |(-(U + 1)) - (ρ : ℂ).im| ≤ 1 := by
    rcases abs_cases ((ρ : ℂ).im) with ⟨he, hs⟩ | ⟨he, hs⟩
    · left
      rw [he] at hlo hhi
      rw [abs_le]
      constructor <;> linarith
    · right
      rw [he] at hlo hhi
      rw [abs_le]
      constructor <;> linarith
  have hkey : ∀ t : ℝ, |t - (ρ : ℂ).im| ≤ 1 →
      (zeroMultiplicity (ρ : ℂ) : ℝ) ≤ 2 * pWeight t ρ := by
    intro t ht
    have hsq : (t - (ρ : ℂ).im) ^ 2 ≤ 1 := by
      have h := abs_le.1 ht
      nlinarith [h.1, h.2]
    have hden : (0 : ℝ) < 1 + (t - (ρ : ℂ).im) ^ 2 := by positivity
    have hrw : 2 * pWeight t ρ
        = 2 * (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) := by
      rw [pWeight]; ring
    rw [hrw, le_div_iff₀ hden]
    nlinarith
  rcases hside with h | h
  · have := hkey _ h
    have := pWeight_nonneg (-(U + 1)) ρ
    linarith
  · have := hkey _ h
    have := pWeight_nonneg (U + 1) ρ
    linarith

/-- **The zeros of a unit annulus carry total multiplicity `O(log U)`.** -/
private lemma sum_multiplicity_annulus_le :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 0 ≤ U → ∀ F : Finset allZeros,
      (∀ ρ ∈ F, U < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ U + 1) →
        ∑ ρ ∈ F, (zeroMultiplicity (ρ : ℂ) : ℝ) ≤ 4 * C * Real.log (U + 4) := by
  obtain ⟨C, hC0, hC⟩ := exists_summable_poissonWeight_tsum_le
  refine ⟨C, hC0, fun U hU F hF => ?_⟩
  obtain ⟨hsumP, hleP⟩ := hC (U + 1)
  obtain ⟨hsumM, hleM⟩ := hC (-(U + 1))
  have hsP : Summable (pWeight (U + 1)) := hsumP
  have hsM : Summable (pWeight (-(U + 1))) := hsumM
  have habs : |U + 1| + 3 = U + 4 := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ U + 1)]; ring
  have habs' : |(-(U + 1))| + 3 = U + 4 := by
    rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ U + 1)]; ring
  have hleP' : ∑' ρ : allZeros, pWeight (U + 1) ρ ≤ C * Real.log (U + 4) := by
    have hEq : ∑' ρ : allZeros, pWeight (U + 1) ρ
        = ∑' ρ : allZeros,
            (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + ((U + 1) - (ρ : ℂ).im) ^ 2) := rfl
    rw [hEq, ← habs]
    exact hleP
  have hleM' : ∑' ρ : allZeros, pWeight (-(U + 1)) ρ ≤ C * Real.log (U + 4) := by
    have hEq : ∑' ρ : allZeros, pWeight (-(U + 1)) ρ
        = ∑' ρ : allZeros,
            (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + ((-(U + 1)) - (ρ : ℂ).im) ^ 2) := rfl
    rw [hEq, ← habs']
    exact hleM
  calc ∑ ρ ∈ F, (zeroMultiplicity (ρ : ℂ) : ℝ)
      ≤ ∑ ρ ∈ F, (2 * pWeight (U + 1) ρ + 2 * pWeight (-(U + 1)) ρ) :=
        Finset.sum_le_sum fun ρ hρ =>
          multiplicity_le_pWeight_add (hF ρ hρ).1 (hF ρ hρ).2
    _ = 2 * (∑ ρ ∈ F, pWeight (U + 1) ρ) + 2 * ∑ ρ ∈ F, pWeight (-(U + 1)) ρ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (∑' ρ : allZeros, pWeight (U + 1) ρ)
          + 2 * ∑' ρ : allZeros, pWeight (-(U + 1)) ρ := by
        have hP : ∑ ρ ∈ F, pWeight (U + 1) ρ ≤ ∑' ρ : allZeros, pWeight (U + 1) ρ := by
          rw [← Finset.tsum_subtype]
          exact Summable.tsum_subtype_le _ _ (pWeight_nonneg (U + 1)) hsP
        have hM : ∑ ρ ∈ F, pWeight (-(U + 1)) ρ
            ≤ ∑' ρ : allZeros, pWeight (-(U + 1)) ρ := by
          rw [← Finset.tsum_subtype]
          exact Summable.tsum_subtype_le _ _ (pWeight_nonneg (-(U + 1))) hsM
        linarith
    _ ≤ 2 * (C * Real.log (U + 4)) + 2 * (C * Real.log (U + 4)) := by
        linarith [hleP', hleM']
    _ = 4 * C * Real.log (U + 4) := by ring

/-- **A single term of the Landau sum, at a zero above height `U`, is `O(m_ρ / U)`.** -/
private lemma norm_landauZeroTerm_le {x : ℝ} (hx : 1 < x) {s : ℂ} {U : ℝ}
    (hU : 2 * |s.im| + 2 ≤ U) {ρ : allZeros} (hρ : U < |(ρ : ℂ).im|) :
    ‖landauZeroTerm x s ρ‖
      ≤ (zeroMultiplicity (ρ : ℂ) : ℝ) * x ^ (1 - s.re) * (2 / U) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hUpos : (0 : ℝ) < U := by
    have := abs_nonneg s.im; linarith
  have hm : (0 : ℝ) ≤ (zeroMultiplicity (ρ : ℂ) : ℝ) := Nat.cast_nonneg _
  have hden : U / 2 ≤ ‖s - (ρ : ℂ)‖ := by
    have h1 : |s.im - (ρ : ℂ).im| ≤ ‖s - (ρ : ℂ)‖ := by
      have : (s - (ρ : ℂ)).im = s.im - (ρ : ℂ).im := by simp
      rw [← this]
      exact Complex.abs_im_le_norm _
    have h2 : |(ρ : ℂ).im| - |s.im| ≤ |s.im - (ρ : ℂ).im| := by
      have := abs_sub_abs_le_abs_sub ((ρ : ℂ).im) s.im
      rwa [abs_sub_comm] at this
    have habs := abs_nonneg s.im
    linarith
  have hdpos : (0 : ℝ) < ‖s - (ρ : ℂ)‖ := lt_of_lt_of_le (by linarith) hden
  have hnum : ‖(x : ℂ) ^ ((ρ : ℂ) - s)‖ ≤ x ^ (1 - s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    refine Real.rpow_le_rpow_of_exponent_le hx.le ?_
    have := ρ.2.2.2
    simp only [Complex.sub_re]
    linarith
  have hUhalf : (0 : ℝ) < U / 2 := by linarith
  have hquot : ‖(x : ℂ) ^ ((ρ : ℂ) - s)‖ / ‖s - (ρ : ℂ)‖ ≤ x ^ (1 - s.re) / (U / 2) := by
    rw [div_le_div_iff₀ hdpos hUhalf]
    nlinarith [norm_nonneg ((x : ℂ) ^ ((ρ : ℂ) - s)), Real.rpow_nonneg hx0.le (1 - s.re),
      hnum, hden]
  rw [landauZeroTerm, norm_mul, norm_div, Complex.norm_natCast]
  calc (zeroMultiplicity (ρ : ℂ) : ℝ) * (‖(x : ℂ) ^ ((ρ : ℂ) - s)‖ / ‖s - (ρ : ℂ)‖)
      ≤ (zeroMultiplicity (ρ : ℂ) : ℝ) * (x ^ (1 - s.re) / (U / 2)) :=
        mul_le_mul_of_nonneg_left hquot hm
    _ = (zeroMultiplicity (ρ : ℂ) : ℝ) * x ^ (1 - s.re) * (2 / U) := by
        field_simp

/-- **The symmetric partial sums move by `O(log U / U)` across one unit interval.** -/
theorem exists_norm_sum_heightWindow_sub_le {x : ℝ} (hx : 1 < x) (s : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U U' : ℝ, 2 * |s.im| + 2 ≤ U → U ≤ U' → U' ≤ U + 1 →
      ‖(∑ ρ ∈ heightWindow U', landauZeroTerm x s ρ)
          - ∑ ρ ∈ heightWindow U, landauZeroTerm x s ρ‖
        ≤ C * Real.log (U + 4) / U := by
  obtain ⟨C, hC0, hC⟩ := sum_multiplicity_annulus_le
  have hx0 : (0 : ℝ) < x := by linarith
  refine ⟨8 * C * x ^ (1 - s.re), by positivity, fun U U' hU hUU' hU'1 => ?_⟩
  have hUpos : (0 : ℝ) < U := by have := abs_nonneg s.im; linarith
  have hU0 : (0 : ℝ) ≤ U := hUpos.le
  have hsub : heightWindow U ⊆ heightWindow U' := fun ρ hρ => by
    rw [mem_heightWindow] at hρ ⊢
    linarith
  rw [← Finset.sum_sdiff_eq_sub hsub]
  have hmem : ∀ ρ ∈ heightWindow U' \ heightWindow U,
      U < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ U + 1 := by
    intro ρ hρ
    rw [Finset.mem_sdiff, mem_heightWindow, mem_heightWindow] at hρ
    exact ⟨not_le.1 hρ.2, le_trans hρ.1 hU'1⟩
  calc ‖∑ ρ ∈ heightWindow U' \ heightWindow U, landauZeroTerm x s ρ‖
      ≤ ∑ ρ ∈ heightWindow U' \ heightWindow U, ‖landauZeroTerm x s ρ‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ heightWindow U' \ heightWindow U,
          (zeroMultiplicity (ρ : ℂ) : ℝ) * x ^ (1 - s.re) * (2 / U) :=
        Finset.sum_le_sum fun ρ hρ => norm_landauZeroTerm_le hx hU (hmem ρ hρ).1
    _ = (x ^ (1 - s.re) * (2 / U))
          * ∑ ρ ∈ heightWindow U' \ heightWindow U, (zeroMultiplicity (ρ : ℂ) : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ρ _ => by ring
    _ ≤ (x ^ (1 - s.re) * (2 / U)) * (4 * C * Real.log (U + 4)) := by
        refine mul_le_mul_of_nonneg_left (hC U hU0 _ hmem) (by positivity)
    _ = 8 * C * x ^ (1 - s.re) * Real.log (U + 4) / U := by ring

end ZetaZeros
