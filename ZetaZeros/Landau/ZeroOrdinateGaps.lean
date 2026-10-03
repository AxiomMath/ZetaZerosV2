/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Hilbert.AlphaExpansion
public import ZetaZeros.Landau.ZeroSums

/-!
# A height in every unit interval far from every zero ordinate

In every interval `[U₀, U₀ + 1]` with `U₀ ≥ 3` there is a height `U` whose distance to `|im ρ|`
is at least `C / log U₀` for every non-trivial zero `ρ` of `ζ`, with `C > 0` absolute. Since at
most `M = O(log U₀)` ordinates lie in the window, by
`ZetaZeros.exists_finsum_zeroMultiplicity_window_le`, cutting `[U₀, U₀ + 1]` into `2M + 1` equal
closed pieces leaves one piece meeting none of them.

## Main results

* `ZetaZeros.exists_height_far_from_zeros`: the height exists, at the rate `C / log U₀`.
-/

@[expose] public section

namespace ZetaZeros

open Complex

/-! ### Two elementary facts about `log` at heights `≥ 3` -/

/-- `log U₀ > 1` for `U₀ ≥ 3`, since `3 > e`. -/
private lemma one_lt_log_of_three_le {U₀ : ℝ} (hU₀ : 3 ≤ U₀) : 1 < Real.log U₀ := by
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
  exact hlog3.trans_le (Real.log_le_log (by norm_num) hU₀)

/-- `log (U₀ + 3) ≤ 2 log U₀` for `U₀ ≥ 3`. -/
private lemma log_add_three_le {U₀ : ℝ} (hU₀ : 3 ≤ U₀) :
    Real.log (U₀ + 3) ≤ 2 * Real.log U₀ := by
  have hsq : U₀ + 3 ≤ U₀ ^ 2 := by nlinarith
  calc Real.log (U₀ + 3) ≤ Real.log (U₀ ^ 2) := Real.log_le_log (by linarith) hsq
    _ = 2 * Real.log U₀ := by rw [Real.log_pow]; norm_num

/-! ### The pigeonhole -/

/-- **Pigeonhole for a mesh of midpoints.** If a finite set `S ⊆ ℝ` has fewer than `N` elements
and `δ` is the half-mesh, i.e. `2 N δ = 1`, then one of the `N` midpoints
`a + (2 i + 1) δ` of the equal subdivision of `[a, a + 1]` is at distance at least `δ` from every
element of `S`. -/
private lemma exists_far_from_finset {S : Finset ℝ} (a δ : ℝ) (hδ : 0 < δ) {N : ℕ}
    (hN : S.card < N) (hδN : 2 * (N : ℝ) * δ = 1) :
    ∃ x : ℝ, a + δ ≤ x ∧ x ≤ a + 1 - δ ∧ ∀ s ∈ S, δ ≤ |x - s| := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ i : ℕ, g i = a + (2 * (i : ℝ) + 1) * δ :=
    ⟨fun i => a + (2 * (i : ℝ) + 1) * δ, fun _ => rfl⟩
  have hex : ∃ i ∈ Finset.range N, ∀ s ∈ S, δ ≤ |g i - s| := by
    by_contra hcon
    push Not at hcon
    have hch : ∀ i : ℕ, ∃ s : ℝ, i ∈ Finset.range N → s ∈ S ∧ |g i - s| < δ := by
      intro i
      by_cases hi : i ∈ Finset.range N
      · obtain ⟨s, hsS, hs⟩ := hcon i hi
        exact ⟨s, fun _ => ⟨hsS, hs⟩⟩
      · exact ⟨0, fun hc => absurd hc hi⟩
    choose f hf using hch
    obtain ⟨i, hi, j, hj, hij, hfij⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range N) (t := S)
        (by simpa using hN) (fun i hi => (hf i hi).1)
    have hone : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
      rcases lt_or_gt_of_ne hij with h | h
      · have hle : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have hle : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]
        linarith
    have h1 : |g i - f j| < δ := by rw [← hfij]; exact (hf i hi).2
    have h2 : |f j - g j| < δ := by rw [abs_sub_comm]; exact (hf j hj).2
    have hup : |g i - g j| < 2 * δ := by
      calc |g i - g j| ≤ |g i - f j| + |f j - g j| := abs_sub_le _ _ _
        _ < δ + δ := add_lt_add h1 h2
        _ = 2 * δ := by ring
    have hlow : 2 * δ ≤ |g i - g j| := by
      have hgd : g i - g j = 2 * ((i : ℝ) - (j : ℝ)) * δ := by rw [hg, hg]; ring
      rw [hgd, abs_mul, abs_mul, abs_of_pos hδ, show |(2 : ℝ)| = 2 by norm_num]
      nlinarith [hone, hδ]
    linarith
  obtain ⟨i, hi, hfar⟩ := hex
  refine ⟨g i, ?_, ?_, hfar⟩
  · have hmono : (1 : ℝ) * δ ≤ (2 * (i : ℝ) + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg' (α := ℝ) i]) hδ.le
    rw [hg]
    linarith
  · have hiN : (i : ℝ) + 1 ≤ (N : ℝ) := by
      have h : i + 1 ≤ N := Finset.mem_range.1 hi
      exact_mod_cast h
    have hmono : (2 * (i : ℝ) + 1) * δ ≤ (2 * (N : ℝ) - 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have hexp : (2 * (N : ℝ) - 1) * δ = 1 - δ := by
      rw [show (2 * (N : ℝ) - 1) * δ = 2 * (N : ℝ) * δ - δ by ring, hδN]
    rw [hg]
    linarith

/-! ### The height avoiding every zero ordinate -/

/-- **A height far from every zero ordinate.** There is an absolute constant `C > 0` such that
every interval `[U₀, U₀ + 1]` with `U₀ ≥ 3` contains a height `U` with
`|U - |im ρ|| ≥ C / log U₀` for every non-trivial zero `ρ` of `ζ`. -/
theorem exists_height_far_from_zeros :
    ∃ C : ℝ, 0 < C ∧ ∀ U₀ : ℝ, 3 ≤ U₀ → ∃ U : ℝ, U₀ ≤ U ∧ U ≤ U₀ + 1 ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        C / Real.log U₀ ≤ |(U - |ρ.im|)| := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_finsum_zeroMultiplicity_window_le
  refine ⟨1 / (8 * C + 2), by positivity, fun U₀ hU₀ => ?_⟩
  have hU₀pos : (0 : ℝ) < U₀ := by linarith
  have hlog1 : 1 < Real.log U₀ := one_lt_log_of_three_le hU₀
  have hVsub : {ρ ∈ allZeros | |ρ.im - U₀| ≤ 1} ⊆ nontrivialZeros (U₀ + 1) := by
    rintro ρ ⟨⟨hζ, h0, h1⟩, hw⟩
    rw [abs_le] at hw
    exact ⟨hζ, h0, h1, by linarith [hw.1], by linarith [hw.2]⟩
  have hVfin : {ρ ∈ allZeros | |ρ.im - U₀| ≤ 1}.Finite :=
    (nontrivialZeros_finite _).subset hVsub
  have hWsub : {ρ ∈ allZeros | U₀ ≤ ρ.im ∧ ρ.im ≤ U₀ + 1} ⊆ nontrivialZeros (U₀ + 1) := by
    rintro ρ ⟨⟨hζ, h0, h1⟩, hlo, hhi⟩
    exact ⟨hζ, h0, h1, by linarith, hhi⟩
  have hWfin : {ρ ∈ allZeros | U₀ ≤ ρ.im ∧ ρ.im ≤ U₀ + 1}.Finite :=
    (nontrivialZeros_finite _).subset hWsub
  set S : Finset ℝ := hWfin.toFinset.image (fun ρ => ρ.im) with hSdef
  have hMreal : (S.card : ℝ) ≤ 2 * C * Real.log U₀ := by
    have hc1 : S.card ≤ hWfin.toFinset.card := by rw [hSdef]; exact Finset.card_image_le
    have hc2 : hWfin.toFinset.card ≤ ∑ ρ ∈ hWfin.toFinset, zeroMultiplicity ρ := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun ρ hρ =>
        one_le_zeroMultiplicity (hWsub (hWfin.mem_toFinset.1 hρ))
    have hc3 : ∑ ρ ∈ hWfin.toFinset, zeroMultiplicity ρ
        ≤ ∑ ρ ∈ hVfin.toFinset, zeroMultiplicity ρ := by
      refine Finset.sum_le_sum_of_subset fun ρ hρ => ?_
      rw [Set.Finite.mem_toFinset] at hρ ⊢
      obtain ⟨hA, hlo, hhi⟩ := hρ
      refine ⟨hA, ?_⟩
      rw [abs_le]
      constructor <;> linarith
    have h := hC U₀
    rw [abs_of_pos hU₀pos, finsum_mem_eq_finite_toFinset_sum _ hVfin] at h
    have hcast : (S.card : ℝ) ≤ ((∑ ρ ∈ hVfin.toFinset, zeroMultiplicity ρ : ℕ) : ℝ) :=
      Nat.cast_le.2 (hc1.trans (hc2.trans hc3))
    nlinarith [mul_le_mul_of_nonneg_left (log_add_three_le hU₀) hC0.le]
  set δ : ℝ := 1 / (2 * (2 * (S.card : ℝ) + 1)) with hδdef
  have hden : (0 : ℝ) < 2 * (2 * (S.card : ℝ) + 1) := by positivity
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδN : 2 * ((2 * S.card + 1 : ℕ) : ℝ) * δ = 1 := by
    rw [hδdef, show ((2 * S.card + 1 : ℕ) : ℝ) = 2 * (S.card : ℝ) + 1 by push_cast; ring,
      mul_one_div, div_self (by linarith)]
  obtain ⟨U, hU1, hU2, hUfar⟩ :=
    exists_far_from_finset (S := S) U₀ δ hδpos (N := 2 * S.card + 1) (by omega) hδN
  refine ⟨U, by linarith, by linarith, fun ρ hζ h0 h1 => ?_⟩
  have hrate : 1 / (8 * C + 2) / Real.log U₀ ≤ δ := by
    rw [hδdef, div_div, div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) hden]
    nlinarith [hMreal, hlog1]
  refine hrate.trans ?_
  by_cases hlo : |ρ.im| < U₀
  · rw [abs_of_nonneg (by linarith)]
    linarith
  by_cases hhi : U₀ + 1 < |ρ.im|
  · rw [abs_of_nonpos (by linarith)]
    linarith
  push Not at hlo hhi
  refine hUfar _ ?_
  rw [hSdef, Finset.mem_image]
  rcases lt_trichotomy ρ.im 0 with him | him | him
  · refine ⟨(starRingEnd ℂ) ρ, ?_, by simp [abs_of_neg him]⟩
    rw [Set.Finite.mem_toFinset]
    have hconj : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by rw [riemannZeta_conj, hζ, map_zero]
    refine ⟨⟨hconj, by simpa using h0, by simpa using h1⟩, ?_, ?_⟩
    · simpa using hlo.trans_eq (abs_of_neg him)
    · simpa using (abs_of_neg him).symm.trans_le hhi
  · exact absurd hlo (by rw [him, abs_zero]; linarith)
  · refine ⟨ρ, ?_, (abs_of_pos him).symm⟩
    rw [Set.Finite.mem_toFinset, abs_of_pos him] at *
    exact ⟨⟨hζ, h0, h1⟩, hlo, hhi⟩

end ZetaZeros
