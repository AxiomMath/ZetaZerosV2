/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.ZeroCount.ArgumentVariation
public import ZetaZeros.Landau.ContourFold
public import ZetaZeros.ZeroCount.MainTerm
public import ZetaZeros.ZeroCount.LocalCount
public import ZetaZeros.ZeroCount.ThetaAsymptotic
public import ZetaZeros.Zeta.Inputs

/-!
# The Riemann--von Mangoldt formula

The Riemann--von Mangoldt formula `|N(T) - M(T)| ≤ C log T` for `T ≥ 4`, where `N(T)` counts the
non-trivial zeros of `ζ` with imaginary part in `(0, T]` with multiplicity and
`M(T) = (T / 2π) log (T / 2π) - T / 2π`.

Folding the boundary of the counting rectangle turns the rectangle integral of `ξ' / ξ` into
`2 i im I (ξ' / ξ; T)`, while the argument principle turns it into
`2 π i ∑_ρ ord_ρ ξ = 2 π i N(T)`; comparing, `π N(T) = im I (ξ' / ξ; T)`. The splitting of `ξ' / ξ`
into its four factors then evaluates that imaginary part: the two elementary factors `1 / s` and
`1 / (s - 1)` contribute `arctan (2T)` and `π - arctan (2T)`, hence exactly `π` -- the classical
`+1` of the formula -- the `Γ` factor contributes the Riemann--Siegel `θ(T)`, and `ζ' / ζ`
contributes `π S(T)` by definition of `S`. That is the exact formula `N(T) = 1 + θ(T) / π + S(T)`
at a good height, which together with Backlund's bound for `S` and the asymptotic for `θ` gives the
formula.

## Main definitions

* `ZetaZeros.argS`: the argument function `S(T) = im I (ζ' / ζ; T) / π`.

## Main results

* `ZetaZeros.im_foldedPathIntegral_elementary`: `im I (1/s + 1/(s-1); T) = π`.
* `ZetaZeros.im_foldedPathIntegral_gamma`: `im I (digamma (s/2) / 2 - log π / 2; T) = θ(T)`.
* `ZetaZeros.pi_mul_zeroCount_eq_im_foldedPathIntegral`: `π N(T) = im I (ξ' / ξ; T)`.
* `ZetaZeros.zeroCount_eq_one_add_theta_div_pi_add_argS`: the exact formula
  `N(T) = 1 + θ(T) / π + S(T)` at a good height.
* `ZetaZeros.exists_abs_argS_le`: Backlund's bound `|S(T)| ≤ C log T`.
* `ZetaZeros.exists_abs_zeroCount_sub_mainTerm_le_isGoodHeight`: `|N(T) - M(T)| ≤ C log T` at a
  good height.
* `ZetaZeros.exists_abs_zeroCount_sub_mainTerm_le`: the same at every height `T ≥ 4`.
* `ZetaZeros.riemannVonMangoldt`: the statement `ZetaZeros.RiemannVonMangoldt` holds.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory Set

/-! ## Two small preliminaries -/

/-- `log T ≥ 1` for `T ≥ 4`. -/
private lemma one_le_log_of_four_le {T : ℝ} (hT : 4 ≤ T) : 1 ≤ Real.log T := by
  have h4 : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  nlinarith [Real.log_two_gt_d9]

/-- `log x ≤ 2 log T` for `T ≥ 4` and `0 < x ≤ T + 3`. -/
private lemma log_le_two_mul_log {T x : ℝ} (hT : 4 ≤ T) (hx0 : 0 < x) (hx : x ≤ T + 3) :
    Real.log x ≤ 2 * Real.log T := by
  calc Real.log x ≤ Real.log (T ^ 2) := Real.log_le_log hx0 (by nlinarith)
    _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring

/-- A function with a complex primitive on an open set is continuous there. -/
private lemma continuousOn_of_hasDerivAt {V : Set ℂ} (hV : IsOpen V) {h H : ℂ → ℂ}
    (hderiv : ∀ z ∈ V, HasDerivAt H (h z) z) : ContinuousOn h V := by
  have hd : DifferentiableOn ℂ H V := fun z hz =>
    (hderiv z hz).differentiableAt.differentiableWithinAt
  exact ((hd.analyticOnNhd hV).deriv.continuousOn).congr fun z hz => ((hderiv z hz).deriv).symm

/-! ## Linearity of the folded path integral -/

/-- Every point of the folded path lies in the open right half-plane: `re s ≥ 1/2`. -/
private lemma foldedPath_subset_re_pos {T : ℝ} : foldedPath T ⊆ {z : ℂ | 0 < z.re} := by
  rintro s (⟨hre, -, -⟩ | ⟨-, hre, -⟩)
  · rw [Set.mem_ofPred_eq, hre]; norm_num
  · exact lt_of_lt_of_le (by norm_num) hre

/-- **`I` is additive.** If two integrands are continuous on the folded path and their sum agrees
with a third function there, the folded path integral of the third is the sum of the other two. -/
private lemma foldedPathIntegral_add {T : ℝ} (hT : 0 < T) {h h₁ h₂ : ℂ → ℂ}
    (hc₁ : ContinuousOn h₁ (foldedPath T)) (hc₂ : ContinuousOn h₂ (foldedPath T))
    (heq : ∀ s ∈ foldedPath T, h s = h₁ s + h₂ s) :
    foldedPathIntegral h T = foldedPathIntegral h₁ T + foldedPathIntegral h₂ T := by
  have hγv : ContinuousOn (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) (Icc (0 : ℝ) T) :=
    (by fun_prop : Continuous fun t : ℝ => (2 : ℂ) + (t : ℂ) * I).continuousOn
  have hγh : ContinuousOn (fun x : ℝ => (x : ℂ) + (T : ℂ) * I) (Icc (1 / 2 : ℝ) 2) :=
    (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (T : ℂ) * I).continuousOn
  have hv : ∀ g : ℂ → ℂ, ContinuousOn g (foldedPath T) →
      IntervalIntegrable (fun t : ℝ => g (2 + (t : ℂ) * I)) volume 0 T := by
    intro g hg
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hT.le]
    exact hg.comp hγv fun t ht => mem_foldedPath_vertical ht.1 ht.2
  have hh : ∀ g : ℂ → ℂ, ContinuousOn g (foldedPath T) →
      IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (T : ℂ) * I)) volume (1 / 2) 2 := by
    intro g hg
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
    exact hg.comp hγh fun x hx => mem_foldedPath_horizontal hx.1 hx.2
  have hcv : (∫ t in (0 : ℝ)..T, h (2 + (t : ℂ) * I))
      = (∫ t in (0 : ℝ)..T, h₁ (2 + (t : ℂ) * I)) + ∫ t in (0 : ℝ)..T, h₂ (2 + (t : ℂ) * I) := by
    rw [← intervalIntegral.integral_add (hv h₁ hc₁) (hv h₂ hc₂)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hT.le] at ht
    exact heq _ (mem_foldedPath_vertical ht.1 ht.2)
  have hch : (∫ x in (1 / 2 : ℝ)..2, h ((x : ℂ) + (T : ℂ) * I))
      = (∫ x in (1 / 2 : ℝ)..2, h₁ ((x : ℂ) + (T : ℂ) * I))
        + ∫ x in (1 / 2 : ℝ)..2, h₂ ((x : ℂ) + (T : ℂ) * I) := by
    rw [← intervalIntegral.integral_add (hh h₁ hc₁) (hh h₂ hc₂)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
    exact heq _ (mem_foldedPath_horizontal hx.1 hx.2)
  simp only [foldedPathIntegral, hcv, hch]
  ring

/-! ## The elementary factors contribute `π` -/

/-- The domain of the primitive `Log s + Log (s - 1)` of `1 / s + 1 / (s - 1)`. -/
private def logPairDomain : Set ℂ := slitPlane ∩ (fun z : ℂ => z - 1) ⁻¹' slitPlane

private lemma isOpen_logPairDomain : IsOpen logPairDomain :=
  isOpen_slitPlane.inter (isOpen_slitPlane.preimage (by fun_prop))

/-- The folded path avoids both cuts: `re s ≥ 1/2 > 0` puts `s` off its own cut, and either
`re s = 2`, so `re (s - 1) = 1 > 0`, or `im (s - 1) = T ≠ 0`. -/
private lemma foldedPath_subset_logPairDomain {T : ℝ} (hT : 0 < T) :
    foldedPath T ⊆ logPairDomain := by
  rintro s (⟨hre, -, -⟩ | ⟨him, hre, -⟩)
  · refine ⟨mem_slitPlane_iff.2 (Or.inl (by rw [hre]; norm_num)), mem_slitPlane_iff.2 (Or.inl ?_)⟩
    rw [Complex.sub_re, hre, Complex.one_re]
    norm_num
  · refine ⟨mem_slitPlane_iff.2 (Or.inl (by linarith)), mem_slitPlane_iff.2 (Or.inr ?_)⟩
    rw [Complex.sub_im, him, Complex.one_im]
    linarith

/-- `Log s + Log (s - 1)` is a primitive of `1 / s + 1 / (s - 1)` off the two cuts. -/
private lemma hasDerivAt_logPair {z : ℂ} (hz : z ∈ logPairDomain) :
    HasDerivAt (fun w : ℂ => Complex.log w + Complex.log (w - 1)) (1 / z + 1 / (z - 1)) z := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.log w) (1 / z) z := (hasDerivAt_id z).clog hz.1
  have h2 : HasDerivAt (fun w : ℂ => Complex.log (w - 1)) (1 / (z - 1)) z :=
    ((hasDerivAt_id z).sub_const 1).clog hz.2
  exact h1.add h2

private lemma continuousOn_elementary {T : ℝ} (hT : 0 < T) :
    ContinuousOn (fun s : ℂ => 1 / s + 1 / (s - 1)) (foldedPath T) :=
  (continuousOn_of_hasDerivAt isOpen_logPairDomain fun _ hz =>
    hasDerivAt_logPair hz).mono (foldedPath_subset_logPairDomain hT)

/-- `arg (-conj w) = π - arg w` for `0 ≤ re w` and `0 < im w`. -/
private lemma arg_neg_conj {w : ℂ} (hre : 0 ≤ w.re) (him : 0 < w.im) :
    (-(starRingEnd ℂ) w).arg = Real.pi - w.arg := by
  have hconj : ((starRingEnd ℂ) w).im < 0 := by simpa using him
  have hne : w.arg ≠ Real.pi := fun h => by
    rcases Complex.arg_eq_pi_iff.1 h with ⟨h1, -⟩
    linarith
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hconj, Complex.arg_conj, ite_eq_right hne]
  ring

/-- **The elementary factors contribute `π`.** `im I (s ↦ 1/s + 1/(s-1); T) = π` for every `T > 0`.
-/
@[zz_tag "lem_arg_elementary"]
theorem im_foldedPathIntegral_elementary {T : ℝ} (hT : 0 < T) :
    (foldedPathIntegral (fun s : ℂ => 1 / s + 1 / (s - 1)) T).im = Real.pi := by
  have hderiv : ∀ z ∈ logPairDomain,
      HasDerivAt (fun w : ℂ => Complex.log w + Complex.log (w - 1)) (1 / z + 1 / (z - 1)) z :=
    fun _ hz => hasDerivAt_logPair hz
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => Complex.log w + Complex.log (w - 1))
      logPairDomain := fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
  have hA : AnalyticOnNhd ℂ (fun w : ℂ => Complex.log w + Complex.log (w - 1)) logPairDomain :=
    hdiff.analyticOnNhd isOpen_logPairDomain
  rw [foldedPathIntegral_eq_sub_of_hasDerivAt hT (foldedPath_subset_logPairDomain hT) hA hderiv]
  have hsub : (1 / 2 + (T : ℂ) * I) - 1 = -(starRingEnd ℂ) (1 / 2 + (T : ℂ) * I) := by
    apply Complex.ext <;> simp
    norm_num
  have hw : (0 : ℝ) ≤ ((1 : ℂ) / 2 + (T : ℂ) * I).re := by simp
  have hwi : (0 : ℝ) < ((1 : ℂ) / 2 + (T : ℂ) * I).im := by simpa using hT
  have h2 : Complex.log ((2 : ℂ) - 1) = 0 := by norm_num
  simp only [Complex.sub_im, Complex.add_im, Complex.log_im, hsub, h2, Complex.zero_im,
    arg_neg_conj hw hwi]
  have : ((2 : ℂ)).arg = 0 := Complex.arg_eq_zero_iff.2 ⟨by norm_num, by norm_num⟩
  rw [this]
  ring

/-! ## The gamma factor contributes the theta function -/

/-- `ℒ (s / 2) - (log π / 2) s` is a primitive of `digamma (s / 2) / 2 - log π / 2` on the open
right half-plane. -/
private lemma hasDerivAt_gammaPrimitive {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w : ℂ => logGamma (w / 2) - (Real.log Real.pi : ℂ) / 2 * w)
      (digamma (z / 2) / 2 - (Real.log Real.pi : ℂ) / 2) z := by
  have hz2 : 0 < (z / 2).re := by rw [Complex.div_ofNat_re]; linarith
  have h1 : HasDerivAt (fun w : ℂ => w / 2) (1 / 2 : ℂ) z := (hasDerivAt_id z).div_const 2
  have h2 : HasDerivAt (logGamma ∘ fun w : ℂ => w / 2) (digamma (z / 2) * (1 / 2)) z :=
    (hasDerivAt_logGamma hz2).comp z h1
  have h2' : HasDerivAt (fun w : ℂ => logGamma (w / 2)) (digamma (z / 2) / 2) z := by
    rw [show digamma (z / 2) / 2 = digamma (z / 2) * (1 / 2) by ring]
    exact h2
  have h3 : HasDerivAt (fun w : ℂ => (Real.log Real.pi : ℂ) / 2 * w)
      ((Real.log Real.pi : ℂ) / 2) z := by
    have := (hasDerivAt_id z).const_mul ((Real.log Real.pi : ℂ) / 2)
    simpa using this
  exact h2'.sub h3

private lemma continuousOn_gamma {T : ℝ} :
    ContinuousOn (fun s : ℂ => digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2)
      (foldedPath T) :=
  (continuousOn_of_hasDerivAt (isOpen_lt continuous_const Complex.continuous_re)
    fun _ hz => hasDerivAt_gammaPrimitive hz).mono foldedPath_subset_re_pos

/-- **The gamma factor contributes the theta function.**
`im I (s ↦ digamma (s/2) / 2 - log π / 2; T) = θ(T)` for every `T > 0`. -/
@[zz_tag "lem_arg_gamma"]
theorem im_foldedPathIntegral_gamma {T : ℝ} (hT : 0 < T) :
    (foldedPathIntegral (fun s : ℂ => digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) T).im
      = theta T := by
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ => logGamma (w / 2) - (Real.log Real.pi : ℂ) / 2 * w) {z : ℂ | 0 < z.re} :=
    fun z hz => (hasDerivAt_gammaPrimitive hz).differentiableAt.differentiableWithinAt
  have hA : AnalyticOnNhd ℂ (fun w : ℂ => logGamma (w / 2) - (Real.log Real.pi : ℂ) / 2 * w)
      {z : ℂ | 0 < z.re} :=
    hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  rw [foldedPathIntegral_eq_sub_of_hasDerivAt hT foldedPath_subset_re_pos hA
    fun _ hz => hasDerivAt_gammaPrimitive hz]
  have hone : logGamma 1 = 0 := by simp [logGamma]
  have hhalf : ((1 : ℂ) / 2 + (T : ℂ) * I) / 2 = 1 / 4 + (T : ℂ) / 2 * I := by ring
  have htwo : ((2 : ℂ)) / 2 = 1 := by norm_num
  have hval : logGamma ((1 / 2 + (T : ℂ) * I) / 2)
        - (Real.log Real.pi : ℂ) / 2 * (1 / 2 + (T : ℂ) * I)
        - (logGamma ((2 : ℂ) / 2) - (Real.log Real.pi : ℂ) / 2 * 2)
      = logGamma (1 / 4 + (T : ℂ) / 2 * I) + ((3 * Real.log Real.pi / 4 : ℝ) : ℂ)
        - ((T / 2 * Real.log Real.pi : ℝ) : ℂ) * I := by
    rw [hhalf, htwo, hone]
    push_cast
    ring
  rw [hval, theta]
  simp

/-! ## The argument function -/

/-- The **argument function** `S(T) = im I (ζ' / ζ; T) / π`. -/
@[zz_tag "def_S_arg"]
noncomputable def argS (T : ℝ) : ℝ :=
  (foldedPathIntegral (logDeriv riemannZeta) T).im / Real.pi

/-! ## The count as an integral along the folded path -/

/-- **The count as an integral along the folded path:** `π N(T) = im I (ξ' / ξ; T)` at a good
height `T > 0`. -/
@[zz_tag "lem_count_by_path"]
theorem pi_mul_zeroCount_eq_im_foldedPathIntegral {T : ℝ} (hT : IsGoodHeight T) (hT0 : 0 < T) :
    Real.pi * zeroCount T = (foldedPathIntegral (logDeriv riemannXi) T).im := by
  classical
  have hset : {ρ : ℂ | (-1 ≤ ρ.re ∧ ρ.re ≤ 2 ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T) ∧ riemannXi ρ = 0}
      = nontrivialZeros T := by
    rw [← riemannXi_zeros_rectangle_eq T]
    ext ρ
    simp only [Set.mem_ofPred_eq]
    tauto
  have hZ : {ρ : ℂ | (-1 ≤ ρ.re ∧ ρ.re ≤ 2 ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T) ∧ riemannXi ρ = 0}.Finite := by
    rw [hset]; exact nontrivialZeros_finite T
  have hxi : AnalyticOnNhd ℂ riemannXi Set.univ :=
    differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ
  have hargp := rectangleIntegral_logDeriv_eq_sum_analyticOrderNatAt (a := -1) (b := 2) (c := 0)
    (d := T) (by norm_num) hT0 (Set.subset_univ _) hxi
    (fun s h1 h2 h3 h4 hbd => riemannXi_ne_zero_of_mem_rectangleBoundary hT ⟨h1, h2, h3, h4⟩ hbd)
    hZ
  have hcoe : (hZ.toFinset : Set ℂ) = nontrivialZeros T := by
    rw [Set.Finite.coe_toFinset]; exact hset
  have hmul : ∀ ρ ∈ hZ.toFinset,
      ((analyticOrderNatAt riemannXi ρ : ℕ) : ℂ) = ((zeroMultiplicity ρ : ℕ) : ℂ) := by
    intro ρ hρ
    have hmem : ρ ∈ nontrivialZeros T := by
      rw [← hcoe]; exact_mod_cast hρ
    have h0 : 0 < ρ.re := hmem.2.1
    have h1 : ρ.re < 1 := hmem.2.2.1
    rw [analyticOrderNatAt_riemannXi h0 h1]
  have hsum : ∑ ρ ∈ hZ.toFinset, zeroMultiplicity ρ = zeroCount T := by
    rw [zeroCount, ← finsum_mem_coe_finset, hcoe]
  rw [Finset.sum_congr rfl hmul, ← Nat.cast_sum, hsum] at hargp
  have hcorner : ((-1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = -1 := by norm_num
  have hcorner' : ((2 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I = 2 + (T : ℂ) * I := by norm_num
  rw [hcorner, hcorner', rectangleIntegral_logDeriv_riemannXi_eq hT hT0.le] at hargp
  have hkey : (2 : ℂ) * I * (((foldedPathIntegral (logDeriv riemannXi) T).im : ℝ) : ℂ)
      = 2 * I * ((Real.pi * zeroCount T : ℝ) : ℂ) := by
    rw [hargp]
    push_cast
    ring
  have h2I : (2 : ℂ) * I ≠ 0 := by simp [Complex.I_ne_zero]
  exact_mod_cast (mul_left_cancel₀ h2I hkey).symm

/-! ## The exact zero-counting formula -/

/-- `ζ' / ζ` is continuous on the folded path at a good height `T > 0`. -/
private lemma continuousOn_logDeriv_riemannZeta_foldedPath {T : ℝ} (hT : IsGoodHeight T)
    (hT0 : 0 < T) : ContinuousOn (logDeriv riemannZeta) (foldedPath T) := by
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hζ : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := hdiff.analyticOnNhd isOpen_ne
  have hsub : foldedPath T ⊆ {s : ℂ | s ≠ 1} := fun _ hs => ne_one_of_mem_foldedPath hT0 hs
  have hunfold : logDeriv riemannZeta = fun s : ℂ => deriv riemannZeta s / riemannZeta s := by
    funext s
    rw [logDeriv_apply]
  rw [hunfold]
  exact ContinuousOn.div ((hζ.deriv.continuousOn).mono hsub) ((hζ.continuousOn).mono hsub)
    fun _ hs => riemannZeta_ne_zero_of_mem_foldedPath hT hs

/-- **The exact zero-counting formula:** `N(T) = 1 + θ(T) / π + S(T)` at a good height `T > 0`.
-/
@[zz_tag "lem_count_formula"]
theorem zeroCount_eq_one_add_theta_div_pi_add_argS {T : ℝ} (hT : IsGoodHeight T) (hT0 : 0 < T) :
    (zeroCount T : ℝ) = 1 + theta T / Real.pi + argS T := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hc₁ := continuousOn_elementary hT0
  have hc₂ : ContinuousOn (fun s : ℂ => digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2)
      (foldedPath T) := continuousOn_gamma
  have hcζ := continuousOn_logDeriv_riemannZeta_foldedPath hT hT0
  have hsplit : ∀ s ∈ foldedPath T, logDeriv riemannXi s
      = ((1 / s + 1 / (s - 1)) + (digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2))
        + logDeriv riemannZeta s := by
    intro s hs
    have h0 : 0 < s.re := foldedPath_subset_re_pos hs
    have h1 : s ≠ 1 := ne_one_of_mem_foldedPath hT0 hs
    have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_mem_foldedPath hT hs
    rw [logDeriv_riemannXi_eq h0 h1 hζ, logDeriv_apply]
    ring
  have hc₁₂ : ContinuousOn (fun s : ℂ => (1 / s + 1 / (s - 1))
      + (digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2)) (foldedPath T) := hc₁.add hc₂
  have hI : foldedPathIntegral (logDeriv riemannXi) T
      = (foldedPathIntegral (fun s : ℂ => 1 / s + 1 / (s - 1)) T
          + foldedPathIntegral
            (fun s : ℂ => digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) T)
        + foldedPathIntegral (logDeriv riemannZeta) T := by
    rw [foldedPathIntegral_add hT0 hc₁₂ hcζ hsplit,
      foldedPathIntegral_add (h := fun s : ℂ => (1 / s + 1 / (s - 1))
        + (digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2)) hT0 hc₁ hc₂ fun _ _ => rfl]
  have hkey : Real.pi * (zeroCount T : ℝ) = Real.pi + theta T + Real.pi * argS T := by
    rw [pi_mul_zeroCount_eq_im_foldedPathIntegral hT hT0, hI]
    simp only [Complex.add_im, im_foldedPathIntegral_elementary hT0,
      im_foldedPathIntegral_gamma hT0, argS]
    field_simp
  refine mul_left_cancel₀ hπ ?_
  rw [hkey]
  field_simp

/-! ## Backlund's bound -/

/-- **Backlund's bound.** There is a constant `C` with `|S(T)| ≤ C log T` for every good height
`T ≥ 4`. -/
@[zz_tag "lem_S_bound"]
theorem exists_abs_argS_le :
    ∃ C : ℝ, ∀ T : ℝ, IsGoodHeight T → 4 ≤ T → |argS T| ≤ C * Real.log T := by
  obtain ⟨C₁, hC₁⟩ := exists_abs_im_integral_logDeriv_riemannZeta_le_mul_log
  refine ⟨(Real.pi / 2 + max C₁ 0) / Real.pi, fun T hgood hT => ?_⟩
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog : 1 ≤ Real.log T := one_le_log_of_four_le hT
  have hvert := abs_im_mul_I_integral_logDeriv_riemannZeta_le_pi_div_two T
  have hhoriz : |(∫ x in (1 / 2 : ℝ)..2, logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im|
      ≤ max C₁ 0 * Real.log T :=
    le_trans (hC₁ T hgood hT)
      (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by linarith))
  have hsub : (foldedPathIntegral (logDeriv riemannZeta) T).im
      = (I * ∫ t in (0 : ℝ)..T, logDeriv riemannZeta (2 + (t : ℂ) * I)).im
        - (∫ x in (1 / 2 : ℝ)..2, logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im := by
    rw [foldedPathIntegral, Complex.sub_im]
  have habs : |(foldedPathIntegral (logDeriv riemannZeta) T).im|
      ≤ Real.pi / 2 + max C₁ 0 * Real.log T := by
    rw [hsub]
    exact le_trans (abs_sub _ _) (by linarith)
  have hCπ : (Real.pi / 2 + max C₁ 0) / Real.pi * Real.log T * Real.pi
      = (Real.pi / 2 + max C₁ 0) * Real.log T := by
    field_simp
  rw [argS, abs_div, abs_of_pos hπ, div_le_iff₀ hπ, hCπ]
  have hmax : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
  nlinarith [habs]

/-! ## The formula at a good height -/

/-- **The formula at a good height.** There is a constant `C` with `|N(T) - M(T)| ≤ C log T` for
every good height `T ≥ 4`. -/
@[zz_tag "lem_N_main_term_good"]
theorem exists_abs_zeroCount_sub_mainTerm_le_isGoodHeight :
    ∃ C : ℝ, ∀ T : ℝ, IsGoodHeight T → 4 ≤ T →
      |(zeroCount T : ℝ) - mainTerm T| ≤ C * Real.log T := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_theta_sub_le
  obtain ⟨C₂, hC₂⟩ := exists_abs_argS_le
  refine ⟨1 + C₁ / Real.pi + C₂, fun T hgood hT => ?_⟩
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog : 1 ≤ Real.log T := one_le_log_of_four_le hT
  have hform := zeroCount_eq_one_add_theta_div_pi_add_argS hgood (by linarith)
  have hS := hC₂ T hgood hT
  have hθ := hC₁ T (by linarith)
  have heq : theta T / Real.pi - mainTerm T
      = (theta T - (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)) / Real.pi := by
    rw [mainTerm]
    field_simp
  have hθ' : |theta T / Real.pi - mainTerm T| ≤ C₁ / Real.pi * Real.log T := by
    rw [heq, abs_div, abs_of_pos hπ]
    calc |theta T - (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)| / Real.pi
        ≤ C₁ * Real.log T / Real.pi := by gcongr
      _ = C₁ / Real.pi * Real.log T := by ring
  have hrw : (zeroCount T : ℝ) - mainTerm T
      = 1 + (theta T / Real.pi - mainTerm T) + argS T := by rw [hform]; ring
  have h1 := abs_add_le (1 + (theta T / Real.pi - mainTerm T)) (argS T)
  have h2 := abs_add_le (1 : ℝ) (theta T / Real.pi - mainTerm T)
  rw [abs_one] at h2
  rw [hrw]
  nlinarith [h1, h2, hθ', hS, hlog]

/-! ## Riemann--von Mangoldt, main term -/

/-- **Riemann--von Mangoldt, main term.** There is a constant `C` with `|N(T) - M(T)| ≤ C log T`
for every real `T ≥ 4`. -/
@[zz_tag "lem_N_main_term"]
theorem exists_abs_zeroCount_sub_mainTerm_le :
    ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T → |(zeroCount T : ℝ) - mainTerm T| ≤ C * Real.log T := by
  obtain ⟨C₁, hC₁⟩ := exists_zeroCount_sub_le
  obtain ⟨C₂, hC₂⟩ := exists_abs_mainTerm_sub_le
  obtain ⟨C₃, hC₃⟩ := exists_abs_zeroCount_sub_mainTerm_le_isGoodHeight
  refine ⟨2 * max C₁ 0 + max C₂ 0 + 2 * max C₃ 0, fun T hT => ?_⟩
  have hlog : 1 ≤ Real.log T := one_le_log_of_four_le hT
  obtain ⟨T', hgood, hT1, hT2⟩ := exists_isGoodHeight (a := T) (by linarith)
  have hT'4 : (4 : ℝ) ≤ T' := by linarith
  have hmono : (zeroCount T : ℝ) ≤ (zeroCount T' : ℝ) :=
    Nat.cast_le.2 (zeroCount_mono hT1.le)
  have hmono' : (zeroCount T' : ℝ) ≤ (zeroCount (T + 1) : ℝ) :=
    Nat.cast_le.2 (zeroCount_mono hT2)
  have hloc : (zeroCount (T + 1) : ℝ) - zeroCount T ≤ max C₁ 0 * Real.log (|T| + 3) :=
    le_trans (hC₁ T) (mul_le_mul_of_nonneg_right (le_max_left C₁ 0)
      (Real.log_nonneg (by linarith [abs_nonneg T])))
  have hlog3 : Real.log (|T| + 3) ≤ 2 * Real.log T := by
    refine log_le_two_mul_log hT (by linarith [abs_nonneg T]) ?_
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)]
  have hN : (zeroCount T' : ℝ) - zeroCount T ≤ 2 * max C₁ 0 * Real.log T := by
    have h0 : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
    nlinarith [hloc, hlog3, hmono']
  have hM : |mainTerm T' - mainTerm T| ≤ max C₂ 0 * Real.log T :=
    le_trans (hC₂ T T' hT hT1.le hT2)
      (mul_le_mul_of_nonneg_right (le_max_left C₂ 0) (by linarith))
  have hgood' : |(zeroCount T' : ℝ) - mainTerm T'| ≤ max C₃ 0 * Real.log T' :=
    le_trans (hC₃ T' hgood hT'4)
      (mul_le_mul_of_nonneg_right (le_max_left C₃ 0) (Real.log_nonneg (by linarith)))
  have hlogT' : Real.log T' ≤ 2 * Real.log T :=
    log_le_two_mul_log hT (by linarith) (by linarith)
  have hgood'' : |(zeroCount T' : ℝ) - mainTerm T'| ≤ 2 * max C₃ 0 * Real.log T := by
    have h0 : (0 : ℝ) ≤ max C₃ 0 := le_max_right _ _
    nlinarith [hgood', hlogT']
  rw [abs_le] at hM hgood'' ⊢
  constructor <;> linarith [hM.1, hM.2, hgood''.1, hgood''.2]

/-! ## Riemann--von Mangoldt -/

/-- **Riemann--von Mangoldt formula.** There is a constant `C` with `|N(T) - M(T)| ≤ C log T` for
every `T ≥ 4`. -/
@[zz_tag "lem_rvm"]
theorem riemannVonMangoldt : RiemannVonMangoldt :=
  exists_abs_zeroCount_sub_mainTerm_le

end ZetaZeros
