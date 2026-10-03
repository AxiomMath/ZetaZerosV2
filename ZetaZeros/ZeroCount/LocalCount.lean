/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import ZetaZeros.Analytic.ZetaBounds
public import ZetaZeros.Zeta.Finite
public import ZetaZeros.Zeta.OrderConj

/-!
# The local count

`N(t + 1) - N(t) ≤ C log(|t| + 3)`, where `N(T)` is the number of non-trivial zeros of the Riemann
zeta function with imaginary part in `(0, T]` counted with multiplicity: a window of unit height
carries only logarithmically many zeros.

A zero of the window with real part at least `1/2` lies within `8/5` of `2 + i(t + 1/2)`, and the
reflection `ρ ↦ 1 - conj ρ` carries the zeros with `re ρ < 1/2` to zeros with `re ρ > 1/2`,
preserving the imaginary part and the multiplicity. Jensen's inequality, applied to `ζ` on the
discs of radii `8/5 < 7/4` about `2 + iτ`, bounds the zeros in such a disc.

## Main results

* `ZetaZeros.zeroCount_mono`: `N` is monotone.
* `ZetaZeros.norm_sub_le_of_half_le_re_of_lt_im`: the right half of a window lies in the closed
  disc of centre `2 + i(t + 1/2)` and radius `8/5`.
* `ZetaZeros.finsum_zeroMultiplicity_re_lt_half_le`: the multiplicity carried by the left half of a
  window is at most the multiplicity carried by its right half.
* `ZetaZeros.exists_finsum_zeroMultiplicity_disc_le`: the zeros of `ζ` in the closed disc of centre
  `2 + iτ` and radius `8/5` are finite in number and carry multiplicity `O(log (τ + 3))`.
* `ZetaZeros.exists_zeroCount_sub_le`: the local count `N(t + 1) - N(t) = O(log (|t| + 3))`.
-/

@[expose] public section

namespace ZetaZeros

open Complex Metric MeromorphicOn

/-! ### Monotonicity -/

/-- The set `nontrivialZeros T` is monotone in `T`. -/
private theorem nontrivialZeros_mono : Monotone nontrivialZeros := fun _ _ hT _ hρ =>
  ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.1, hρ.2.2.2.2.trans hT⟩

/-- **The zero count is monotone.** If `T₁ ≤ T₂` then `N T₁ ≤ N T₂`. -/
@[zz_tag "lem_N_mono"]
theorem zeroCount_mono : Monotone zeroCount := by
  intro T₁ T₂ hT
  rw [zeroCount, zeroCount, finsum_mem_eq_finite_toFinset_sum _ (nontrivialZeros_finite T₁),
    finsum_mem_eq_finite_toFinset_sum _ (nontrivialZeros_finite T₂)]
  exact Finset.sum_le_sum_of_subset
    (Set.Finite.toFinset_subset_toFinset.mpr (nontrivialZeros_mono hT))

/-! ### The right half of a window lies in a disc -/

/-- **The right half of a window lies in the disc.** A point with `1/2 ≤ re ρ < 1` and
`t < im ρ ≤ t + 1` is within `8/5` of `2 + i(t + 1/2)`. -/
@[zz_tag "lem_window_in_disc"]
theorem norm_sub_le_of_half_le_re_of_lt_im {t : ℝ} {ρ : ℂ} (hre₀ : 1 / 2 ≤ ρ.re) (hre₁ : ρ.re < 1)
    (him₀ : t < ρ.im) (him₁ : ρ.im ≤ t + 1) :
    ‖ρ - (2 + ((t + 1 / 2 : ℝ) : ℂ) * I)‖ ≤ 8 / 5 := by
  have hsq : ‖ρ - (2 + ((t + 1 / 2 : ℝ) : ℂ) * I)‖ ^ 2 ≤ (8 / 5) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  nlinarith [norm_nonneg (ρ - (2 + ((t + 1 / 2 : ℝ) : ℂ) * I))]

/-! ### Reflecting the left half of a window -/

/-- The reflection `ρ ↦ 1 - conj ρ` preserves the multiplicity of a point of the open critical
strip `0 < re ρ < 1`. -/
lemma zeroMultiplicity_one_sub_conj {ρ : ℂ} (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) :
    zeroMultiplicity (1 - (starRingEnd ℂ) ρ) = zeroMultiplicity ρ := by
  have hre : ((starRingEnd ℂ) ρ).re = ρ.re := Complex.conj_re ρ
  have hne : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at h₁
    exact absurd h₁ (lt_irrefl 1)
  rw [zeroMultiplicity_one_sub (hre ▸ h₀) (hre ▸ h₁), zeroMultiplicity_conj hne]

/-- The reflection `ρ ↦ 1 - conj ρ` carries a zero of the left half of a window to a zero of its
right half. -/
private lemma one_sub_conj_mem {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ ρ.re < 1 / 2}) :
    1 - (starRingEnd ℂ) ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ 1 / 2 < ρ.re} := by
  obtain ⟨⟨hζ, h₀, h₁, hi₀, hi₁⟩, hti, hhalf⟩ := hρ
  have hre : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by simp
  have him : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by simp
  have hne : (starRingEnd ℂ) ρ ≠ 1 := by
    intro h
    have : ((starRingEnd ℂ) ρ).re = (1 : ℂ).re := by rw [h]
    rw [Complex.conj_re, Complex.one_re] at this
    linarith
  have hnat : ∀ n : ℕ, (starRingEnd ℂ) ρ ≠ -(n : ℂ) := by
    intro n h
    have : ((starRingEnd ℂ) ρ).re = (-(n : ℂ)).re := by rw [h]
    rw [Complex.conj_re] at this
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hζconj : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
    rw [riemannZeta_conj, hζ, map_zero]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [riemannZeta_one_sub hnat hne, hζconj, mul_zero]
  · rw [hre]; linarith
  · rw [hre]; linarith
  · rw [him]; exact hi₀
  · rw [him]; exact hi₁
  · rw [him]; exact hti
  · rw [hre]; linarith

/-- **Reflecting the left half of a window.** The multiplicity carried by the zeros of a window
`t < im ρ ≤ t + 1` lying to the left of the critical line is at most the multiplicity carried by
those lying to its right. -/
@[zz_tag "lem_window_reflection"]
theorem finsum_zeroMultiplicity_re_lt_half_le (t : ℝ) :
    ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ ρ.re < 1 / 2}, zeroMultiplicity ρ ≤
      ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ 1 / 2 < ρ.re}, zeroMultiplicity ρ := by
  classical
  have hA : {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ ρ.re < 1 / 2}.Finite :=
    (nontrivialZeros_finite _).subset fun _ hρ => hρ.1
  have hB : {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ 1 / 2 < ρ.re}.Finite :=
    (nontrivialZeros_finite _).subset fun _ hρ => hρ.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hB]
  have hinj : ∀ x ∈ hA.toFinset, ∀ y ∈ hA.toFinset,
      1 - (starRingEnd ℂ) x = 1 - (starRingEnd ℂ) y → x = y := by
    intro x _ y _ h
    have h' : (starRingEnd ℂ) x = (starRingEnd ℂ) y := by linear_combination -h
    simpa using congrArg (starRingEnd ℂ) h'
  calc ∑ ρ ∈ hA.toFinset, zeroMultiplicity ρ
      = ∑ ρ ∈ hA.toFinset, zeroMultiplicity (1 - (starRingEnd ℂ) ρ) := by
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        obtain ⟨⟨-, h₀, h₁, -, -⟩, -, -⟩ := hA.mem_toFinset.mp hρ
        exact (zeroMultiplicity_one_sub_conj h₀ h₁).symm
    _ = ∑ z ∈ hA.toFinset.image fun ρ => 1 - (starRingEnd ℂ) ρ, zeroMultiplicity z :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ z ∈ hB.toFinset, zeroMultiplicity z := by
        refine Finset.sum_le_sum_of_subset fun z hz => ?_
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
        exact hB.mem_toFinset.mpr (one_sub_conj_mem (hA.mem_toFinset.mp hρ))

/-! ### The zeros in a disc centred to the right -/

/-- `ζ` is analytic on a neighbourhood of the closed disc of centre `2 + iτ` and radius `r ≤ 7/4`
once `τ ≥ 5`. -/
private lemma analyticOnNhd_zeta_disc {τ r : ℝ} (hτ : 5 ≤ τ) (hr₀ : 0 ≤ r) (hr : r ≤ 7 / 4) :
    AnalyticOnNhd ℂ riemannZeta (closedBall ((2 : ℂ) + (τ : ℂ) * I) |r|) := by
  refine analyticOn_riemannZeta.mono fun z hz => ?_
  simp only [mem_closedBall, dist_eq_norm, abs_of_nonneg hr₀] at hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  subst h
  have h1 : |((1 : ℂ) - (2 + (τ : ℂ) * I)).im| ≤ ‖(1 : ℂ) - (2 + (τ : ℂ) * I)‖ :=
    Complex.abs_im_le_norm _
  simp only [Complex.sub_im, Complex.one_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.im_ofNat] at h1
  rw [abs_of_nonpos (by linarith)] at h1
  linarith

/-- At the centre `2 + iτ` the zeta function has norm at least `1/4`. -/
private lemma one_quarter_le_norm_zeta_centre (τ : ℝ) :
    (1 : ℝ) / 4 ≤ ‖riemannZeta ((2 : ℂ) + (τ : ℂ) * I)‖ :=
  le_trans (one_quarter_le_riemannZeta_re (s := (2 : ℂ) + (τ : ℂ) * I) (by simp))
    (Complex.re_le_norm _)

/-- On the circle of centre `2 + iτ` and radius `7/4` one has `‖ζ z‖ ≤ 26 (τ + 3)` for `τ ≥ 5`. -/
private lemma norm_zeta_le_on_sphere {τ : ℝ} (hτ : 5 ≤ τ) {z : ℂ}
    (hz : z ∈ sphere ((2 : ℂ) + (τ : ℂ) * I) |(7 / 4 : ℝ)|) :
    ‖riemannZeta z‖ ≤ 26 * (τ + 3) := by
  simp only [mem_sphere_iff_norm, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4)] at hz
  have hre : |(z - ((2 : ℂ) + (τ : ℂ) * I)).re| ≤ 7 / 4 := by
    rw [← hz]; exact Complex.abs_re_le_norm _
  have him : |(z - ((2 : ℂ) + (τ : ℂ) * I)).im| ≤ 7 / 4 := by
    rw [← hz]; exact Complex.abs_im_le_norm _
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat] at hre him
  rw [abs_le] at hre him
  have hi : 2 ≤ |z.im| := by
    rw [abs_of_nonneg (by linarith [him.1])]; linarith [him.1]
  have hb := norm_riemannZeta_le_thirteen_mul_abs_im (s := z)
    (by linarith [hre.1]) (by linarith [hre.2]) hi
  rw [abs_of_nonneg (by linarith [him.1])] at hb
  linarith [him.2]

/-- The zeros of `ζ` in the closed disc of centre `2 + iτ` and radius `8/5` are finite in number.
-/
private lemma discZeros_finite (τ : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ ‖ρ - ((2 : ℂ) + (τ : ℂ) * I)‖ ≤ 8 / 5}.Finite := by
  have hc := isCompact_closedBall ((2 : ℂ) + (τ : ℂ) * I) (8 / 5)
  refine hc.inter_riemannZetaZeros_finite.subset fun ρ hρ => ⟨?_, mem_riemannZetaZeros.mpr hρ.1⟩
  simpa [mem_closedBall, dist_eq_norm] using hρ.2

/-- For `τ ≥ 5` one has `1 ≤ log (τ + 3)`. -/
private lemma one_le_log_add_three {τ : ℝ} (hτ : 5 ≤ τ) : (1 : ℝ) ≤ Real.log (τ + 3) := by
  have hmono : Real.log 8 ≤ Real.log (τ + 3) := Real.log_le_log (by norm_num) (by linarith)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  nlinarith [Real.log_two_gt_d9]

/-- **The zeros of `ζ` in a disc centred to the right.** There is a constant `C` such that for
every `τ ≥ 5` the zeros of `ζ` in the closed disc of centre `2 + iτ` and radius `8/5` are finite in
number and their multiplicities sum to at most `C log (τ + 3)`. -/
@[zz_tag "lem_zeta_disc_count"]
theorem exists_finsum_zeroMultiplicity_disc_le :
    ∃ C : ℝ, ∀ τ : ℝ, 5 ≤ τ →
      {ρ : ℂ | riemannZeta ρ = 0 ∧ ‖ρ - ((2 : ℂ) + (τ : ℂ) * I)‖ ≤ 8 / 5}.Finite ∧
        ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ ‖ρ - ((2 : ℂ) + (τ : ℂ) * I)‖ ≤ 8 / 5},
            zeroMultiplicity ρ : ℕ) : ℝ) ≤ C * Real.log (τ + 3) := by
  classical
  set L : ℝ := Real.log (7 / 4 / (8 / 5))
  have hLpos : 0 < L := Real.log_pos (by norm_num)
  refine ⟨(1 + Real.log 104) / L, fun τ hτ => ⟨discZeros_finite τ, ?_⟩⟩
  set a : ℂ := (2 : ℂ) + (τ : ℂ) * I
  set S : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ ‖ρ - a‖ ≤ 8 / 5}
  have hS : S.Finite := discZeros_finite τ
  have habs : |(8 / 5 : ℝ)| = 8 / 5 := abs_of_nonneg (by norm_num)
  have hB : AnalyticOnNhd ℂ riemannZeta (closedBall a |(8 / 5 : ℝ)|) :=
    analyticOnNhd_zeta_disc hτ (by norm_num) (by norm_num)
  have hBR : AnalyticOnNhd ℂ riemannZeta (closedBall a |(7 / 4 : ℝ)|) :=
    analyticOnNhd_zeta_disc hτ (by norm_num) le_rfl
  have hcentre : (1 : ℝ) / 4 ≤ ‖riemannZeta a‖ := one_quarter_le_norm_zeta_centre τ
  have hne : riemannZeta a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcentre
    linarith
  have jensen : ((∑ᶠ u, divisor riemannZeta (closedBall a |(8 / 5 : ℝ)|) u : ℤ) : ℝ) ≤
      Real.log (26 * (τ + 3) / ‖riemannZeta a‖) / L :=
    hBR.sum_divisor_le (by rw [habs]; norm_num)
      (by rw [habs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4)]; norm_num)
      (by nlinarith) hne fun z hz => norm_zeta_le_on_sphere hτ hz
  have hsub : S ⊆ closedBall a |(8 / 5 : ℝ)| := by
    intro ρ hρ
    simp only [mem_closedBall, dist_eq_norm, habs]
    exact hρ.2
  have hval : ∀ z ∈ closedBall a |(8 / 5 : ℝ)|,
      divisor riemannZeta (closedBall a |(8 / 5 : ℝ)|) z = (zeroMultiplicity z : ℤ) := by
    intro z hz
    rw [hB.divisor_apply hz, zeroMultiplicity, analyticOrderNatAt]
    cases h : analyticOrderAt riemannZeta z with
    | top => simp
    | coe n => simp
  have hsupp : Function.support
      (fun u => divisor riemannZeta (closedBall a |(8 / 5 : ℝ)|) u) ⊆ hS.toFinset := by
    intro u hu
    simp only [Function.mem_support, ne_eq] at hu
    by_cases hmem : u ∈ closedBall a |(8 / 5 : ℝ)|
    · rw [hval u hmem] at hu
      have hz0 : zeroMultiplicity u ≠ 0 := by exact_mod_cast hu
      have hord : analyticOrderAt riemannZeta u ≠ 0 := by
        intro h
        rw [zeroMultiplicity, analyticOrderNatAt, h] at hz0
        simp at hz0
      have hζ : riemannZeta u = 0 := by
        by_contra hnz
        exact hord (analyticOrderAt_eq_zero.2 (Or.inr hnz))
      simp only [mem_closedBall, dist_eq_norm, habs] at hmem
      exact hS.mem_toFinset.2 ⟨hζ, hmem⟩
    · have h0 := (divisor riemannZeta (closedBall a |(8 / 5 : ℝ)|)).apply_eq_zero_of_notMem hmem
      exact absurd h0 hu
  have hbridge : ((∑ᶠ ρ ∈ S, zeroMultiplicity ρ : ℕ) : ℤ)
      = ∑ᶠ u, divisor riemannZeta (closedBall a |(8 / 5 : ℝ)|) u := by
    rw [finsum_eq_sum_of_support_subset _ hsupp, finsum_mem_eq_finite_toFinset_sum _ hS,
      Nat.cast_sum]
    exact Finset.sum_congr rfl fun z hz => (hval z (hsub (hS.mem_toFinset.1 hz))).symm
  have hlog1 : Real.log (26 * (τ + 3) / ‖riemannZeta a‖) ≤ Real.log (104 * (τ + 3)) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hlog2 : Real.log (104 * (τ + 3)) = Real.log 104 + Real.log (τ + 3) :=
    Real.log_mul (by norm_num) (by positivity)
  have hlogτ : (1 : ℝ) ≤ Real.log (τ + 3) := one_le_log_add_three hτ
  have h104 : (0 : ℝ) ≤ Real.log 104 := Real.log_nonneg (by norm_num)
  have hfinal : Real.log (26 * (τ + 3) / ‖riemannZeta a‖) / L
      ≤ (1 + Real.log 104) / L * Real.log (τ + 3) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hLpos]
    nlinarith
  calc ((∑ᶠ ρ ∈ S, zeroMultiplicity ρ : ℕ) : ℝ)
      = ((∑ᶠ u, divisor riemannZeta (closedBall a |(8 / 5 : ℝ)|) u : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) hbridge
    _ ≤ Real.log (26 * (τ + 3) / ‖riemannZeta a‖) / L := jensen
    _ ≤ (1 + Real.log 104) / L * Real.log (τ + 3) := hfinal

/-! ### The local count -/

/-- Enlarging the index set of a sum of multiplicities can only increase it. -/
private lemma finsum_le_finsum_of_subset {A B : Set ℂ} (hB : B.Finite) (hAB : A ⊆ B)
    (f : ℂ → ℕ) : ∑ᶠ ρ ∈ A, f ρ ≤ ∑ᶠ ρ ∈ B, f ρ := by
  have hA := hB.subset hAB
  rw [finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hB]
  exact Finset.sum_le_sum_of_subset (Set.Finite.toFinset_subset_toFinset.mpr hAB)

/-- `N(t + 1)` is `N(t)` plus the multiplicity carried by the window `t < im ρ ≤ t + 1`. -/
private lemma zeroCount_add_one_eq (t : ℝ) :
    zeroCount (t + 1)
      = zeroCount t + ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im}, zeroMultiplicity ρ := by
  classical
  have hA : (nontrivialZeros (t + 1)).Finite := nontrivialZeros_finite _
  have hB : (nontrivialZeros t).Finite := nontrivialZeros_finite _
  have hW : {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im}.Finite := hA.subset fun _ h => h.1
  rw [zeroCount, zeroCount, finsum_mem_eq_finite_toFinset_sum _ hA,
    finsum_mem_eq_finite_toFinset_sum _ hB, finsum_mem_eq_finite_toFinset_sum _ hW]
  have hdisj : Disjoint hB.toFinset hW.toFinset := by
    rw [Finset.disjoint_left]
    intro ρ hρB hρW
    exact absurd (hW.mem_toFinset.1 hρW).2 (not_lt.2 (hB.mem_toFinset.1 hρB).2.2.2.2)
  have hunion : hA.toFinset = hB.toFinset ∪ hW.toFinset := by
    ext ρ
    simp only [Finset.mem_union, Set.Finite.mem_toFinset]
    constructor
    · intro h
      rcases le_or_gt ρ.im t with hle | hlt
      · exact Or.inl ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hle⟩
      · exact Or.inr ⟨h, hlt⟩
    · rintro (h | h)
      · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by linarith [h.2.2.2.2]⟩
      · exact h.1
  rw [hunion, Finset.sum_union hdisj]

/-- The multiplicity carried by a window `t < im ρ ≤ t + 1` is at most twice that carried by its
zeros with `1/2 ≤ re ρ`. -/
private lemma finsum_window_le_two_mul (t : ℝ) :
    ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im}, zeroMultiplicity ρ ≤
      2 * ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ 1 / 2 ≤ ρ.re},
        zeroMultiplicity ρ := by
  classical
  have hA : (nontrivialZeros (t + 1)).Finite := nontrivialZeros_finite _
  have hW : {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im}.Finite := hA.subset fun _ h => h.1
  have hlt : {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ ρ.re < 1 / 2}.Finite :=
    hA.subset fun _ h => h.1
  have hge : {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ 1 / 2 ≤ ρ.re}.Finite :=
    hA.subset fun _ h => h.1
  have hsplit :
      ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im}, zeroMultiplicity ρ
        = (∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ ρ.re < 1 / 2}, zeroMultiplicity ρ)
          + ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ 1 / 2 ≤ ρ.re},
              zeroMultiplicity ρ := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hW, finsum_mem_eq_finite_toFinset_sum _ hlt,
      finsum_mem_eq_finite_toFinset_sum _ hge]
    have hdisj : Disjoint hlt.toFinset hge.toFinset := by
      rw [Finset.disjoint_left]
      intro ρ h1 h2
      exact absurd (hge.mem_toFinset.1 h2).2.2 (not_le.2 (hlt.mem_toFinset.1 h1).2.2)
    have hunion : hW.toFinset = hlt.toFinset ∪ hge.toFinset := by
      ext ρ
      simp only [Finset.mem_union, Set.Finite.mem_toFinset]
      constructor
      · intro h
        rcases lt_or_ge ρ.re (1 / 2) with h' | h'
        · exact Or.inl ⟨h.1, h.2, h'⟩
        · exact Or.inr ⟨h.1, h.2, h'⟩
      · rintro (h | h)
        · exact ⟨h.1, h.2.1⟩
        · exact ⟨h.1, h.2.1⟩
    rw [hunion, Finset.sum_union hdisj]
  have hrefl := finsum_zeroMultiplicity_re_lt_half_le t
  have hgt : ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ 1 / 2 < ρ.re}, zeroMultiplicity ρ ≤
      ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ 1 / 2 ≤ ρ.re}, zeroMultiplicity ρ :=
    finsum_le_finsum_of_subset hge (fun ρ h => ⟨h.1, h.2.1, h.2.2.le⟩) _
  omega

/-- **The local count.** There is a constant `C` such that `N(t + 1) - N(t) ≤ C log (|t| + 3)` for
every real `t`. -/
@[zz_tag "lem_local_count"]
theorem exists_zeroCount_sub_le :
    ∃ C : ℝ, ∀ t : ℝ, (zeroCount (t + 1) : ℝ) - zeroCount t ≤ C * Real.log (|t| + 3) := by
  obtain ⟨C₁, hC₁⟩ := exists_finsum_zeroMultiplicity_disc_le
  have hlog8 : (0 : ℝ) < Real.log 8 := Real.log_pos (by norm_num)
  have hC₁0 : 0 ≤ C₁ := by
    have h := (hC₁ 5 le_rfl).2
    have h8 : (5 : ℝ) + 3 = 8 := by norm_num
    rw [h8] at h
    have h0 : (0 : ℝ) ≤ ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧
        ‖ρ - ((2 : ℂ) + ((5 : ℝ) : ℂ) * I)‖ ≤ 8 / 5}, zeroMultiplicity ρ : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    nlinarith
  refine ⟨max (4 * C₁) (zeroCount 6 : ℝ), fun t => ?_⟩
  have hmax0 : (0 : ℝ) ≤ max (4 * C₁) (zeroCount 6 : ℝ) :=
    le_trans (by linarith) (le_max_left _ _)
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
  have hlog : (1 : ℝ) ≤ Real.log (|t| + 3) :=
    le_trans hlog3.le (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  rcases le_or_gt 5 t with ht | ht
  · have habs : |t| = t := abs_of_nonneg (by linarith)
    have hkey := (hC₁ (t + 1 / 2) (by linarith)).2
    have hwin : ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im ∧ 1 / 2 ≤ ρ.re},
        zeroMultiplicity ρ ≤
        ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧
          ‖ρ - ((2 : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I)‖ ≤ 8 / 5}, zeroMultiplicity ρ := by
      refine finsum_le_finsum_of_subset (hC₁ (t + 1 / 2) (by linarith)).1 (fun ρ hρ => ?_) _
      exact ⟨hρ.1.1, norm_sub_le_of_half_le_re_of_lt_im hρ.2.2 hρ.1.2.2.1 hρ.2.1 hρ.1.2.2.2.2⟩
    have hnat := (finsum_window_le_two_mul t).trans (Nat.mul_le_mul_left 2 hwin)
    have hstep : (zeroCount (t + 1) : ℝ) - zeroCount t
        ≤ 2 * ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧
            ‖ρ - ((2 : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I)‖ ≤ 8 / 5},
            zeroMultiplicity ρ : ℕ) : ℝ) := by
      rw [zeroCount_add_one_eq t, Nat.cast_add]
      have hcast : ((∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | t < ρ.im}, zeroMultiplicity ρ : ℕ) : ℝ)
          ≤ 2 * ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧
            ‖ρ - ((2 : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I)‖ ≤ 8 / 5},
            zeroMultiplicity ρ : ℕ) : ℝ) := by
        exact_mod_cast hnat
      linarith
    have hshift : Real.log (t + 1 / 2 + 3) ≤ 2 * Real.log (t + 3) := by
      have h1 : Real.log (t + 1 / 2 + 3) ≤ Real.log ((t + 3) ^ 2) :=
        Real.log_le_log (by linarith) (by nlinarith)
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith
    have hlog' : (1 : ℝ) ≤ Real.log (t + 3) := by
      have h := hlog
      rwa [habs] at h
    have hlogpos : (0 : ℝ) ≤ Real.log (t + 3) := by linarith
    calc (zeroCount (t + 1) : ℝ) - zeroCount t
        ≤ 2 * ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧
            ‖ρ - ((2 : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I)‖ ≤ 8 / 5},
            zeroMultiplicity ρ : ℕ) : ℝ) := hstep
      _ ≤ 2 * (C₁ * Real.log (t + 1 / 2 + 3)) := by linarith
      _ ≤ 4 * C₁ * Real.log (t + 3) := by
          nlinarith [mul_le_mul_of_nonneg_left hshift hC₁0]
      _ ≤ max (4 * C₁) (zeroCount 6 : ℝ) * Real.log (|t| + 3) := by
          rw [habs]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlogpos
  · have hmono : zeroCount (t + 1) ≤ zeroCount 6 := zeroCount_mono (by linarith)
    have h1 : (zeroCount (t + 1) : ℝ) - zeroCount t ≤ (zeroCount 6 : ℝ) := by
      have hc : ((zeroCount (t + 1) : ℕ) : ℝ) ≤ ((zeroCount 6 : ℕ) : ℝ) := Nat.cast_le.2 hmono
      have h0 : (0 : ℝ) ≤ (zeroCount t : ℝ) := Nat.cast_nonneg _
      linarith
    have h2 : (zeroCount 6 : ℝ) ≤ max (4 * C₁) (zeroCount 6 : ℝ) * Real.log (|t| + 3) := by
      have hn : (0 : ℝ) ≤ (zeroCount 6 : ℝ) := Nat.cast_nonneg _
      nlinarith [le_max_right (4 * C₁) ((zeroCount 6 : ℕ) : ℝ)]
    linarith

end ZetaZeros
