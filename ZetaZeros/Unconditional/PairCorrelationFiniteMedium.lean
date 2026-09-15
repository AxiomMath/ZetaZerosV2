/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationHighTail

/-!
# Finite-height complementary zeros at the closed pair-correlation endpoint

The complementary zero sum below an arbitrary cutoff `Z ≥ T` consists of ordinates in
`[-Z, 0]` and `(T, Z]`. Unit-window zero counts and the Lorentzian decay from the two
endpoints give an integrable boundary majorant for this entire finite-height part.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex Finset MeasureTheory Set

/-- An arbitrary finite sub-sum of the reciprocal-square tail is bounded by the standard
telescoping majorant. -/
lemma sum_inv_pow_two_finset_le (F : Finset ℕ) {D : ℝ} (hD : 0 < D) :
    ∑ i ∈ F, ((D + i) ^ 2)⁻¹ ≤ (D ^ 2)⁻¹ + D⁻¹ := by
  classical
  set N : ℕ := F.sup id + 1
  have hsub : F ⊆ Finset.range N := by
    intro i hi
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  calc
    ∑ i ∈ F, ((D + i) ^ 2)⁻¹ ≤
        ∑ i ∈ Finset.range N, ((D + i) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ (D ^ 2)⁻¹ + D⁻¹ := Zeta23.Tail.sum_inv_pow_two_le hD N

/-- If every unit shell has mass at most `M`, its Lorentzian-weighted mass beyond distance
`d` is at most `4M/(1+d)`. -/
lemma shell_lorentzian_sum_le
    {ι : Type*} (s : Finset ι) (m : ι → ℕ) (key : ι → ℕ) (q : ι → ℝ)
    {M d : ℝ} (hM : 0 ≤ M) (hd : 0 ≤ d)
    (hweight : ∀ ρ ∈ s,
      1 / (1 + (q ρ) ^ 2) ≤ 2 / ((1 + d + key ρ) ^ 2))
    (hcount : ∀ j : ℕ,
      ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) ≤ M) :
    ∑ ρ ∈ s, (m ρ : ℝ) / (1 + (q ρ) ^ 2) ≤ 4 * M / (1 + d) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := key) (t := s.image key)
    (fun ρ hρ => Finset.mem_image_of_mem key hρ)]
  have hfiber : ∀ j ∈ s.image key,
      ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) / (1 + (q ρ) ^ 2) ≤
        (2 / ((1 + d + j) ^ 2)) * M := by
    intro j _
    calc
      ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) / (1 + (q ρ) ^ 2) ≤
          ∑ ρ ∈ s with key ρ = j,
            (2 / ((1 + d + j) ^ 2)) * (m ρ : ℝ) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        simp only [Finset.mem_filter] at hρ
        have hw := hweight ρ hρ.1
        rw [hρ.2] at hw
        calc
          (m ρ : ℝ) / (1 + (q ρ) ^ 2) =
              (m ρ : ℝ) * (1 / (1 + (q ρ) ^ 2)) := by ring
          _ ≤ (m ρ : ℝ) * (2 / ((1 + d + j) ^ 2)) :=
            mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
          _ = (2 / ((1 + d + j) ^ 2)) * (m ρ : ℝ) := by ring
      _ = (2 / ((1 + d + j) ^ 2)) *
            ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ (2 / ((1 + d + j) ^ 2)) * M := by
        exact mul_le_mul_of_nonneg_left (hcount j) (by positivity)
  calc
    ∑ j ∈ s.image key,
        ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) / (1 + (q ρ) ^ 2) ≤
        ∑ j ∈ s.image key, (2 / ((1 + d + j) ^ 2)) * M :=
      Finset.sum_le_sum hfiber
    _ = 2 * M * ∑ j ∈ s.image key, (((1 + d) + j) ^ 2)⁻¹ := by
      simp only [div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 2 * M * (((1 + d) ^ 2)⁻¹ + (1 + d)⁻¹) := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_inv_pow_two_finset_le (s.image key) (by linarith)
      · positivity
    _ ≤ 4 * M / (1 + d) := by
      have hdpos : 0 < 1 + d := by linarith
      have hinvSq : ((1 + d) ^ 2)⁻¹ ≤ (1 + d)⁻¹ := by
        apply inv_anti₀ (by positivity)
        nlinarith
      calc
        2 * M * (((1 + d) ^ 2)⁻¹ + (1 + d)⁻¹) ≤
            2 * M * (2 * (1 + d)⁻¹) := by
          gcongr
          linarith
        _ = 4 * M / (1 + d) := by ring

/-- The zeros immediately above the integration window are controlled by their distance
from the upper endpoint. -/
lemma upper_medium_shifted_lorentzian_sum_le_of_localCount {ι : Type*}
    {γ : ι → ℝ} {m : ι → ℕ} {A T Z t : ℝ}
    (hLC : Zeta23.Tail.LocalCount γ m A)
    (hT : 0 ≤ T) (hTZ : T ≤ Z) (_ht0 : 0 ≤ t) (htT : t ≤ T)
    (s : Finset ι) (hupper : ∀ ρ ∈ s, T < γ ρ)
    (hheight : ∀ ρ ∈ s, γ ρ ≤ Z) :
    ∑ ρ ∈ s, (m ρ : ℝ) / (1 + (t - γ ρ) ^ 2) ≤
      4 * (A * Real.log (Z + 4)) / (1 + (T - t)) := by
  classical
  have hA : 0 ≤ A := le_trans (by norm_num) hLC.one_le
  have hZ : 0 ≤ Z := hT.trans hTZ
  let key : ι → ℕ := fun ρ => ⌈γ ρ - T⌉₊ - 1
  apply shell_lorentzian_sum_le s m key (fun ρ => t - γ ρ)
    (mul_nonneg hA (Real.log_nonneg (by linarith))) (by linarith)
  · intro ρ hρ
    have hceil1 : 1 ≤ ⌈γ ρ - T⌉₊ :=
      Nat.one_le_ceil_iff.mpr (by linarith [hupper ρ hρ])
    have hc : ⌈γ ρ - T⌉₊ = key ρ + 1 := by
      dsimp only [key]
      omega
    have hinter := (Nat.ceil_eq_iff (Nat.succ_ne_zero (key ρ))).mp hc
    push_cast at hinter
    have hnear : T - t + (key ρ : ℝ) ≤ γ ρ - t := by linarith
    have hleft : 0 ≤ T - t + (key ρ : ℝ) := by positivity
    have hright : 0 ≤ γ ρ - t := by linarith [hupper ρ hρ]
    have hsq : (T - t + (key ρ : ℝ)) ^ 2 ≤ (γ ρ - t) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnear) (add_nonneg hright hleft)]
    rw [div_le_div_iff₀ (by positivity : 0 < 1 + (t - γ ρ) ^ 2)
      (sq_pos_of_pos (by positivity : 0 < 1 + (T - t) + (key ρ : ℝ)))]
    nlinarith [sq_nonneg (T - t + (key ρ : ℝ) - 1)]
  · intro j
    let f : Finset ι := s.filter (fun ρ => key ρ = j)
    by_cases hf : f.Nonempty
    · obtain ⟨ρ₀, hρ₀⟩ := hf
      have hρ₀' := (Finset.mem_filter.mp hρ₀)
      have hceil1 : 1 ≤ ⌈γ ρ₀ - T⌉₊ :=
        Nat.one_le_ceil_iff.mpr (by linarith [hupper ρ₀ hρ₀'.1])
      have hc : ⌈γ ρ₀ - T⌉₊ = j + 1 := by
        dsimp only [key] at hρ₀'
        omega
      have hinter₀ := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
      push_cast at hinter₀
      have hlog : Real.log (|T + (j : ℝ)| + 3) ≤ Real.log (Z + 4) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ T + (j : ℝ))]
        exact Real.log_le_log (by positivity) (by linarith [hheight ρ₀ hρ₀'.1])
      have hw := hLC.window (T + j) f (by
        intro ρ hρ
        have hρ' := Finset.mem_filter.mp hρ
        have hceil1' : 1 ≤ ⌈γ ρ - T⌉₊ :=
          Nat.one_le_ceil_iff.mpr (by linarith [hupper ρ hρ'.1])
        have hc' : ⌈γ ρ - T⌉₊ = j + 1 := by
          dsimp only [key, f] at hρ'
          omega
        have hinter := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc'
        push_cast at hinter
        constructor <;> linarith)
      change ∑ ρ ∈ f, (m ρ : ℝ) ≤ A * Real.log (Z + 4)
      exact hw.trans (mul_le_mul_of_nonneg_left hlog hA)
    · have hfempty : f = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
      change ∑ ρ ∈ f, (m ρ : ℝ) ≤ A * Real.log (Z + 4)
      rw [hfempty]
      simp only [sum_empty]
      exact mul_nonneg hA (Real.log_nonneg (by linarith))

/-- The zeros below ordinate zero are controlled by their distance from the lower endpoint
of the integration window.  The natural-floor shells coincide exactly with the half-open
windows in `LocalCount`. -/
lemma lower_medium_shifted_lorentzian_sum_le_of_localCount {ι : Type*}
    {γ : ι → ℝ} {m : ι → ℕ} {A Z t : ℝ}
    (hLC : Zeta23.Tail.LocalCount γ m A)
    (hZ : 0 ≤ Z) (ht0 : 0 ≤ t)
    (s : Finset ι) (hlower : ∀ ρ ∈ s, γ ρ ≤ 0)
    (hheight : ∀ ρ ∈ s, -Z ≤ γ ρ) :
    ∑ ρ ∈ s, (m ρ : ℝ) / (1 + (t - γ ρ) ^ 2) ≤
      4 * (A * Real.log (Z + 4)) / (1 + t) := by
  classical
  have hA : 0 ≤ A := le_trans (by norm_num) hLC.one_le
  let key : ι → ℕ := fun ρ => ⌊-γ ρ⌋₊
  apply shell_lorentzian_sum_le s m key (fun ρ => t - γ ρ)
    (mul_nonneg hA (Real.log_nonneg (by linarith))) ht0
  · intro ρ hρ
    have hnonneg : 0 ≤ -γ ρ := neg_nonneg.mpr (hlower ρ hρ)
    have hinter := (Nat.floor_eq_iff hnonneg).mp (rfl : key ρ = key ρ)
    have hnear : t + (key ρ : ℝ) ≤ t - γ ρ := by
      dsimp only [key] at hinter
      linarith
    have hleft : 0 ≤ t + (key ρ : ℝ) := by positivity
    have hright : 0 ≤ t - γ ρ := by linarith [hlower ρ hρ]
    have hsq : (t + (key ρ : ℝ)) ^ 2 ≤ (t - γ ρ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnear) (add_nonneg hright hleft)]
    rw [div_le_div_iff₀ (by positivity : 0 < 1 + (t - γ ρ) ^ 2)
      (sq_pos_of_pos (by positivity : 0 < 1 + t + (key ρ : ℝ)))]
    nlinarith [sq_nonneg (t + (key ρ : ℝ) - 1)]
  · intro j
    let f : Finset ι := s.filter (fun ρ => key ρ = j)
    by_cases hf : f.Nonempty
    · obtain ⟨ρ₀, hρ₀⟩ := hf
      have hρ₀' := Finset.mem_filter.mp hρ₀
      have hnonneg₀ : 0 ≤ -γ ρ₀ := neg_nonneg.mpr (hlower ρ₀ hρ₀'.1)
      have hinter₀ := (Nat.floor_eq_iff hnonneg₀).mp hρ₀'.2
      have hlog : Real.log (|-(j : ℝ) - 1| + 3) ≤ Real.log (Z + 4) := by
        have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
        rw [abs_of_nonpos (by linarith : -(j : ℝ) - 1 ≤ 0)]
        exact Real.log_le_log (by linarith) (by linarith [hheight ρ₀ hρ₀'.1])
      have hw := hLC.window (-(j : ℝ) - 1) f (by
        intro ρ hρ
        have hρ' := Finset.mem_filter.mp hρ
        have hnonneg : 0 ≤ -γ ρ := neg_nonneg.mpr (hlower ρ hρ'.1)
        have hinter := (Nat.floor_eq_iff hnonneg).mp hρ'.2
        constructor <;> linarith)
      change ∑ ρ ∈ f, (m ρ : ℝ) ≤ A * Real.log (Z + 4)
      exact hw.trans (mul_le_mul_of_nonneg_left hlog hA)
    · have hfempty : f = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
      change ∑ ρ ∈ f, (m ρ : ℝ) ≤ A * Real.log (Z + 4)
      rw [hfempty]
      simp only [sum_empty]
      exact mul_nonneg hA (Real.log_nonneg (by linarith))

theorem complementary_medium_shifted_lorentzian_sum_le_of_localCount {Index : Type*}
    {ordinate : Index → ℝ} {multiplicity : Index → ℕ} {countConst height cutoff time : ℝ}
    (hcount : Zeta23.Tail.LocalCount ordinate multiplicity countConst)
    (hheight : 0 ≤ height) (hcutoff : height ≤ cutoff)
    (htimeLower : 0 ≤ time) (htimeUpper : time ≤ height)
    (zeros : Finset Index)
    (houtside : ∀ zero ∈ zeros, ordinate zero ≤ 0 ∨ height < ordinate zero)
    (hbounded : ∀ zero ∈ zeros, |ordinate zero| ≤ cutoff) :
    ∑ zero ∈ zeros, (multiplicity zero : ℝ) / (1 + (time - ordinate zero) ^ 2) ≤
      4 * (countConst * Real.log (cutoff + 4)) *
        ((1 + time)⁻¹ + (1 + (height - time))⁻¹) := by
  classical
  have hlower := lower_medium_shifted_lorentzian_sum_le_of_localCount
    hcount (hheight.trans hcutoff) htimeLower
    (zeros.filter fun zero ↦ ordinate zero ≤ 0)
    (fun zero hzero ↦ (Finset.mem_filter.mp hzero).2)
    (fun zero hzero ↦ (abs_le.mp (hbounded zero (Finset.mem_filter.mp hzero).1)).1)
  have hupper := upper_medium_shifted_lorentzian_sum_le_of_localCount
    hcount hheight hcutoff htimeLower htimeUpper
    (zeros.filter fun zero ↦ ¬ ordinate zero ≤ 0)
    (fun zero hzero ↦
      (houtside zero (Finset.mem_filter.mp hzero).1).resolve_left
        (Finset.mem_filter.mp hzero).2)
    (fun zero hzero ↦ (abs_le.mp (hbounded zero (Finset.mem_filter.mp hzero).1)).2)
  calc
    ∑ zero ∈ zeros, (multiplicity zero : ℝ) / (1 + (time - ordinate zero) ^ 2) =
        (∑ zero ∈ zeros with ordinate zero ≤ 0,
          (multiplicity zero : ℝ) / (1 + (time - ordinate zero) ^ 2)) +
        ∑ zero ∈ zeros with ¬ ordinate zero ≤ 0,
          (multiplicity zero : ℝ) / (1 + (time - ordinate zero) ^ 2) :=
      (Finset.sum_filter_add_sum_filter_not zeros _ _).symm
    _ ≤ 4 * (countConst * Real.log (cutoff + 4)) / (1 + time) +
        4 * (countConst * Real.log (cutoff + 4)) / (1 + (height - time)) :=
      add_le_add hlower hupper
    _ = _ := by ring

end ZetaZeros.Unconditional.PairCorrelationProof
