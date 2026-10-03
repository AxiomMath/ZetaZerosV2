/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import ZetaZeros.Analytic.ZetaBounds

/-!
# Backlund's bound for the argument function

The symmetrised zeta function `ζ^sym_T z = (ζ (z + iT) + ζ (z - iT)) / 2`, and the count of the
sign changes of `re ζ` along the horizontal segment `[1/2, 2] + iT`.

For real `x`, `ζ^sym_T x = re ζ (x + iT)`, so the real zeros of `ζ^sym_T` in `[1/2, 2]` are the
points of the segment where `re ζ (· + iT)` vanishes. For `T ≥ 4`, `ζ^sym_T` is analytic on the
closed disc of centre `2` and radius `7/4`, is `O(T)` on its boundary circle and at least `1/4` in
absolute value at the centre, so Jensen's inequality bounds its zeros in the disc of radius `8/5`
by `O(log T)`.

## Main results

* `ZetaZeros.symmetrizedZeta`: the symmetrised zeta function.
* `ZetaZeros.symmetrizedZeta_ofReal`: at a real point it computes `re ζ (x + iT)`.
* `ZetaZeros.analyticOnNhd_symmetrizedZeta`: it is analytic on `‖z - 2‖ ≤ 7/4`.
* `ZetaZeros.exists_norm_symmetrizedZeta_le`: it is `O(T)` on the circle `‖z - 2‖ = 7/4`.
* `ZetaZeros.exists_ncard_zeros_symmetrizedZeta_le`: it has `O(log T)` zeros in `‖z - 2‖ ≤ 8/5`.
* `ZetaZeros.exists_ncard_re_riemannZeta_eq_zero_le`: `re ζ (· + iT)` vanishes at `O(log T)` points
  of `[1/2, 2]`.
-/

@[expose] public section

namespace ZetaZeros

open Complex Metric MeromorphicOn

/-! ### The symmetrised zeta function -/

/-- **The symmetrised zeta function** `ζ^sym_T z = (ζ (z + iT) + ζ (z - iT)) / 2`, the average of
the two horizontal translates of `ζ` by `±iT`. -/
@[zz_tag "def_symmetrised"]
noncomputable def symmetrizedZeta (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + (T : ℂ) * I) + riemannZeta (z - (T : ℂ) * I)) / 2

/-- **The symmetrised function computes a real part.** At a real point `x` one has
`ζ^sym_T x = re ζ (x + iT)`; in particular `ζ^sym_T` is real on the real axis. -/
@[zz_tag "lem_symmetrised_real"]
theorem symmetrizedZeta_ofReal (T x : ℝ) :
    symmetrizedZeta T (x : ℂ) = ((riemannZeta ((x : ℂ) + (T : ℂ) * I)).re : ℂ) := by
  have hconj : (starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * I) = (x : ℂ) - (T : ℂ) * I := by
    simp [Complex.ext_iff]
  rw [symmetrizedZeta, ← hconj, riemannZeta_conj, Complex.add_conj]
  push_cast
  ring

/-! ### Analyticity on the disc of radius `7/4` -/

/-- A point of the closed disc of centre `2` and radius `r` has `|im z| ≤ r`. -/
private lemma abs_im_le_of_mem_closedBall {r : ℝ} {z : ℂ} (hz : z ∈ closedBall (2 : ℂ) r) :
    |z.im| ≤ r := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h := Complex.abs_im_le_norm (z - 2)
  simp only [Complex.sub_im, Complex.im_ofNat, sub_zero] at h
  linarith

/-- **Analyticity of the symmetrised function.** For `T ≥ 4` the function `ζ^sym_T` is analytic on
a neighbourhood of the closed disc `‖z - 2‖ ≤ 7/4`. -/
@[zz_tag "lem_symmetrised_analytic"]
theorem analyticOnNhd_symmetrizedZeta {T : ℝ} (hT : 4 ≤ T) :
    AnalyticOnNhd ℂ (symmetrizedZeta T) (closedBall (2 : ℂ) (7 / 4)) := by
  intro z hz
  have him : |z.im| ≤ 7 / 4 := abs_im_le_of_mem_closedBall hz
  rw [abs_le] at him
  have h₁ : z + (T : ℂ) * I ∈ ({1} : Set ℂ)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h' : z.im = -T := by
      have him' := congrArg Complex.im h
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.one_im, mul_one, zero_mul, add_zero] at him'
      linarith
    linarith [him.1]
  have h₂ : z - (T : ℂ) * I ∈ ({1} : Set ℂ)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h' : z.im = T := by
      have him' := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.one_im, mul_one, zero_mul, add_zero] at him'
      linarith
    linarith [him.2]
  have ha₁ : AnalyticAt ℂ (fun w : ℂ => riemannZeta (w + (T : ℂ) * I)) z :=
    (analyticOn_riemannZeta _ h₁).fun_comp_of_eq (by fun_prop) rfl
  have ha₂ : AnalyticAt ℂ (fun w : ℂ => riemannZeta (w - (T : ℂ) * I)) z :=
    (analyticOn_riemannZeta _ h₂).fun_comp_of_eq (by fun_prop) rfl
  exact (ha₁.add ha₂).div_const

/-! ### The bound on the outer circle -/

/-- On the circle `‖z - 2‖ = 7/4` one has `‖ζ^sym_T z‖ ≤ 26 T` as soon as `T ≥ 4`. -/
private theorem norm_symmetrizedZeta_le_twentySix_mul {T : ℝ} (hT : 4 ≤ T) {z : ℂ}
    (hz : z ∈ sphere (2 : ℂ) (7 / 4)) : ‖symmetrizedZeta T z‖ ≤ 26 * T := by
  rw [mem_sphere_iff_norm] at hz
  have hre : |(z - 2).re| ≤ 7 / 4 := by rw [← hz]; exact Complex.abs_re_le_norm _
  have him : |(z - 2).im| ≤ 7 / 4 := by rw [← hz]; exact Complex.abs_im_le_norm _
  simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat,
    sub_zero] at hre him
  rw [abs_le] at hre him
  have hplus : ‖riemannZeta (z + (T : ℂ) * I)‖ ≤ 26 * T := by
    have hre' : (z + (T : ℂ) * I).re = z.re := by simp
    have habs : |(z + (T : ℂ) * I).im| = z.im + T := by
      rw [show (z + (T : ℂ) * I).im = z.im + T by simp, abs_of_nonneg (by linarith [him.1])]
    have hb := norm_riemannZeta_le_thirteen_mul_abs_im (s := z + (T : ℂ) * I)
      (by rw [hre']; linarith [hre.1]) (by rw [hre']; linarith [hre.2])
      (by rw [habs]; linarith [him.1])
    rw [habs] at hb
    linarith [him.2]
  have hminus : ‖riemannZeta (z - (T : ℂ) * I)‖ ≤ 26 * T := by
    have hre' : (z - (T : ℂ) * I).re = z.re := by simp
    have habs : |(z - (T : ℂ) * I).im| = T - z.im := by
      rw [show (z - (T : ℂ) * I).im = z.im - T by simp, abs_of_nonpos (by linarith [him.2]),
        neg_sub]
    have hb := norm_riemannZeta_le_thirteen_mul_abs_im (s := z - (T : ℂ) * I)
      (by rw [hre']; linarith [hre.1]) (by rw [hre']; linarith [hre.2])
      (by rw [habs]; linarith [him.2])
    rw [habs] at hb
    linarith [him.1]
  have htri := norm_add_le (riemannZeta (z + (T : ℂ) * I)) (riemannZeta (z - (T : ℂ) * I))
  rw [symmetrizedZeta, norm_div]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  linarith

/-- **A bound on the symmetrised function.** There is a constant `C` such that for every `T ≥ 4`
and every `z` on the circle `‖z - 2‖ = 7/4` one has `‖ζ^sym_T z‖ ≤ C T`. -/
@[zz_tag "lem_symmetrised_bound"]
theorem exists_norm_symmetrizedZeta_le :
    ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T → ∀ z : ℂ, ‖z - 2‖ = 7 / 4 → ‖symmetrizedZeta T z‖ ≤ C * T :=
  ⟨26, fun _ hT _ hz => norm_symmetrizedZeta_le_twentySix_mul hT (mem_sphere_iff_norm.mpr hz)⟩

/-! ### The zeros in the disc of radius `8/5` -/

/-- For `T ≥ 4` one has `1 ≤ log T`. -/
private lemma one_le_log_of_four_le {T : ℝ} (hT : 4 ≤ T) : (1 : ℝ) ≤ Real.log T := by
  have hmono : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  nlinarith [Real.log_two_gt_d9]

/-- At the centre `2` the symmetrised function has norm at least `1/4`. -/
private lemma one_quarter_le_norm_symmetrizedZeta_two (T : ℝ) :
    (1 : ℝ) / 4 ≤ ‖symmetrizedZeta T 2‖ := by
  have hval : symmetrizedZeta T 2 = ((riemannZeta ((2 : ℂ) + (T : ℂ) * I)).re : ℂ) := by
    simpa using symmetrizedZeta_ofReal T 2
  have hre : (1 : ℝ) / 4 ≤ (riemannZeta ((2 : ℂ) + (T : ℂ) * I)).re :=
    one_quarter_le_riemannZeta_re (by simp)
  have hnorm : ‖symmetrizedZeta T 2‖ = |(riemannZeta ((2 : ℂ) + (T : ℂ) * I)).re| := by
    rw [hval]; simp
  rw [hnorm]
  exact hre.trans (le_abs_self _)

/-- **Zeros of the symmetrised function in a disc.** There is a constant `C` such that for every
`T ≥ 4` the zeros of `ζ^sym_T` in the closed disc `‖z - 2‖ ≤ 8/5` are finite in number, and there
are at most `C log T` of them. -/
@[zz_tag "lem_symmetrised_disc_count"]
theorem exists_ncard_zeros_symmetrizedZeta_le :
    ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T →
      {z : ℂ | symmetrizedZeta T z = 0 ∧ ‖z - 2‖ ≤ 8 / 5}.Finite ∧
        ({z : ℂ | symmetrizedZeta T z = 0 ∧ ‖z - 2‖ ≤ 8 / 5}.ncard : ℝ) ≤ C * Real.log T := by
  classical
  set L : ℝ := Real.log (7 / 4 / (8 / 5)) with hLdef
  have hLpos : 0 < L := Real.log_pos (by norm_num)
  refine ⟨(1 + Real.log 104) / L, fun T hT => ?_⟩
  set f : ℂ → ℂ := symmetrizedZeta T with hfdef
  set S : Set ℂ := {z : ℂ | f z = 0 ∧ ‖z - 2‖ ≤ 8 / 5} with hSdef
  set U : Set ℂ := closedBall (2 : ℂ) |(8 / 5 : ℝ)| with hUdef
  have habs85 : |(8 / 5 : ℝ)| = 8 / 5 := abs_of_nonneg (by norm_num)
  have habs74 : |(7 / 4 : ℝ)| = 7 / 4 := abs_of_nonneg (by norm_num)
  have hA74 : AnalyticOnNhd ℂ f (closedBall (2 : ℂ) |(7 / 4 : ℝ)|) := by
    rw [habs74]; exact analyticOnNhd_symmetrizedZeta hT
  have hAU : AnalyticOnNhd ℂ f U := by
    refine hA74.mono ?_
    rw [hUdef, habs85, habs74]
    exact closedBall_subset_closedBall (by norm_num)
  have hball : AnalyticOnNhd ℂ f (ball (2 : ℂ) (7 / 4)) := by
    refine hA74.mono ?_
    rw [habs74]
    exact ball_subset_closedBall
  have hcentre : (1 : ℝ) / 4 ≤ ‖f 2‖ := one_quarter_le_norm_symmetrizedZeta_two T
  have hne : f 2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcentre
    linarith
  have hord : ∀ z ∈ U, analyticOrderAt f z ≠ ⊤ := by
    intro z hz htop
    have hzb : z ∈ ball (2 : ℂ) (7 / 4) := by
      rw [hUdef, habs85, mem_closedBall] at hz
      rw [mem_ball]
      linarith
    have heq : f =ᶠ[nhds z] 0 := (analyticOrderAt_eq_top.mp htop).mono fun _ hx => hx
    exact hne (hball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (2 : ℂ) (7 / 4)).isPreconnected hzb heq (mem_ball_self (by norm_num)))
  have hdivnn : ∀ z, 0 ≤ divisor f U z := by
    intro z
    by_cases hz : z ∈ U
    · rw [hAU.divisor_apply hz]
      cases h : analyticOrderAt f z with
      | top => simp
      | coe n => simp
    · rw [(divisor f U).apply_eq_zero_of_notMem hz]
  have hdivS : ∀ z ∈ S, 1 ≤ divisor f U z := by
    intro z hz
    have hzU : z ∈ U := by
      rw [hUdef, habs85, mem_closedBall, dist_eq_norm]
      exact hz.2
    have hne0 : analyticOrderAt f z ≠ 0 := (hAU z hzU).analyticOrderAt_ne_zero.mpr hz.1
    cases h : analyticOrderAt f z with
    | top => exact absurd h (hord z hzU)
    | coe n =>
      have hn : n ≠ 0 := by
        rintro rfl
        rw [h] at hne0
        simp at hne0
      have hval : divisor f U z = (n : ℤ) := by rw [hAU.divisor_apply hzU, h]; simp
      rw [hval]
      omega
  have hcU : IsCompact U := by rw [hUdef]; exact isCompact_closedBall _ _
  have hsuppfin : (Function.support fun u => divisor f U u).Finite :=
    (divisor f U).finiteSupport hcU
  have hSsub : S ⊆ Function.support fun u => divisor f U u := by
    intro z hz
    have h := hdivS z hz
    simp only [Function.mem_support, ne_eq]
    omega
  have hSfin : S.Finite := hsuppfin.subset hSsub
  have jensen : ((∑ᶠ u, divisor f U u : ℤ) : ℝ) ≤ Real.log (26 * T / ‖f 2‖) / L := by
    rw [hUdef]
    refine hA74.sum_divisor_le (by rw [habs85]; norm_num) (by rw [habs85, habs74]; norm_num)
      (by linarith) hne fun z hz => ?_
    exact norm_symmetrizedZeta_le_twentySix_mul hT (by rwa [habs74] at hz)
  have hcard : ((S.ncard : ℤ) : ℝ) ≤ ((∑ᶠ u, divisor f U u : ℤ) : ℝ) := by
    have hsum : (∑ᶠ u, divisor f U u) = ∑ u ∈ hsuppfin.toFinset, divisor f U u :=
      finsum_eq_sum_of_support_subset _ (by intro u hu; simpa using hu)
    have hsub : hSfin.toFinset ⊆ hsuppfin.toFinset := fun z hz =>
      hsuppfin.mem_toFinset.mpr (hSsub (hSfin.mem_toFinset.mp hz))
    have h1 : (S.ncard : ℤ) ≤ ∑ u ∈ hSfin.toFinset, divisor f U u := by
      rw [Set.ncard_eq_toFinset_card S hSfin]
      calc ((hSfin.toFinset.card : ℤ)) = ∑ _u ∈ hSfin.toFinset, (1 : ℤ) := by simp
        _ ≤ ∑ u ∈ hSfin.toFinset, divisor f U u :=
            Finset.sum_le_sum fun z hz => hdivS z (hSfin.mem_toFinset.mp hz)
    have h2 : ∑ u ∈ hSfin.toFinset, divisor f U u ≤ ∑ u ∈ hsuppfin.toFinset, divisor f U u :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hdivnn z
    rw [hsum]
    exact_mod_cast h1.trans h2
  have hnorm0 : (0 : ℝ) < ‖f 2‖ := by linarith
  have hlogT : (1 : ℝ) ≤ Real.log T := one_le_log_of_four_le hT
  have h104 : (0 : ℝ) ≤ Real.log 104 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log (26 * T / ‖f 2‖) ≤ Real.log (104 * T) := by
    refine Real.log_le_log (div_pos (by linarith) hnorm0) ?_
    rw [div_le_iff₀ hnorm0]
    nlinarith
  have hlog2 : Real.log (104 * T) = Real.log 104 + Real.log T :=
    Real.log_mul (by norm_num) (by linarith)
  have hfinal : Real.log (26 * T / ‖f 2‖) / L ≤ (1 + Real.log 104) / L * Real.log T := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hLpos]
    nlinarith
  refine ⟨hSfin, ?_⟩
  calc ((S.ncard : ℕ) : ℝ) ≤ ((∑ᶠ u, divisor f U u : ℤ) : ℝ) := by exact_mod_cast hcard
    _ ≤ Real.log (26 * T / ‖f 2‖) / L := jensen
    _ ≤ (1 + Real.log 104) / L * Real.log T := hfinal

/-! ### The sign changes of `re ζ` along a horizontal segment -/

/-- **Sign changes of the real part along a horizontal segment.** There is a constant `C` such that
for every `T ≥ 4` the set `{x ∈ [1/2, 2] : re ζ (x + iT) = 0}` is finite with at most `C log T`
elements. -/
@[zz_tag "lem_re_zeta_zero_count"]
theorem exists_ncard_re_riemannZeta_eq_zero_le :
    ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T →
      {x : ℝ | x ∈ Set.Icc (1 / 2 : ℝ) 2 ∧ (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0}.Finite ∧
        ({x : ℝ | x ∈ Set.Icc (1 / 2 : ℝ) 2 ∧
          (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0}.ncard : ℝ) ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := exists_ncard_zeros_symmetrizedZeta_le
  refine ⟨C, fun T hT => ?_⟩
  obtain ⟨hfin, hle⟩ := hC T hT
  set S : Set ℂ := {z : ℂ | symmetrizedZeta T z = 0 ∧ ‖z - 2‖ ≤ 8 / 5} with hSdef
  set E : Set ℝ :=
    {x : ℝ | x ∈ Set.Icc (1 / 2 : ℝ) 2 ∧ (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0} with hEdef
  have hmaps : ∀ x ∈ E, (x : ℂ) ∈ S := by
    intro x hx
    obtain ⟨⟨hx₀, hx₁⟩, hzero⟩ := hx
    refine ⟨by rw [symmetrizedZeta_ofReal, hzero, Complex.ofReal_zero], ?_⟩
    have hnorm : ‖(x : ℂ) - 2‖ = |x - 2| := by
      rw [show ((x : ℂ) - 2) = ((x - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs]
    rw [hnorm]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hEfin : E.Finite :=
    (hfin.preimage Complex.ofReal_injective.injOn).subset fun x hx => hmaps x hx
  refine ⟨hEfin, ?_⟩
  have hcard : E.ncard ≤ S.ncard :=
    Set.ncard_le_ncard_of_injOn _ hmaps Complex.ofReal_injective.injOn hfin
  calc ((E.ncard : ℕ) : ℝ) ≤ ((S.ncard : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ C * Real.log T := hle

end ZetaZeros
