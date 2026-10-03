/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Foundations
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
public import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
public import ZetaZeros.Meta.Attr

/-!
# The completed zeta function, the digamma function and rectangle integrals

Basic facts about the completed zeta function `ξ`, the digamma function, boundary integrals over
rectangles, and the local behaviour of an analytic function at its zeros, stated in the form used
throughout the library. The completed zeta function and the digamma function are Mathlib's
`Complex.riemannXi` and `Complex.digamma`.

## Main results

* `ZetaZeros.riemannXi_eq_mul_riemannZeta` and `ZetaZeros.riemannXi_one`:
  `ξ s = π ^ (-s / 2) Γ (s / 2 + 1) (s - 1) ζ s` for `s ≠ 1` with `-2 < re s`, and `ξ 1 = 1 / 2`.
* `ZetaZeros.analyticOnNhd_riemannXi`, `ZetaZeros.riemannXi_functional_equation`: analyticity of
  `ξ` on `-2 < re s`, and `ξ (1 - s) = ξ s`.
* `ZetaZeros.digamma_eq_deriv_Gamma_div_Gamma`, `ZetaZeros.analyticOnNhd_digamma`:
  `Complex.digamma` is `Γ' / Γ`, and is analytic on the open right half-plane.
* `ZetaZeros.rectangleIntegral_eq_boundary_integrals`,
  `ZetaZeros.rectangleIntegral_inv_sub_eq`: `RectangleIntegral` is the sum of the four edge
  integrals, and its value on `s ↦ (s - p)⁻¹` is `2 π i`.
* `ZetaZeros.bddAbove_logDeriv_sub_principal_part`: `f' / f` minus its principal part is bounded
  near a zero.
* `ZetaZeros.exists_isOpen_zeros_subset`: a subset of the domain has a neighbourhood carrying no
  further zeros.
-/
@[expose] public section

namespace ZetaZeros

open Complex Filter Topology Set Asymptotics intervalIntegral

/-! ## The completed zeta function -/

/-- For `s ≠ 1` with `-2 < re s`, the completed zeta function satisfies
`ξ s = π ^ (-s / 2) Γ (s / 2 + 1) (s - 1) ζ s`. -/
@[zz_tag "def_xi"]
theorem riemannXi_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) (hs' : -2 < s.re) :
    riemannXi s = (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2 + 1) * (s - 1) * riemannZeta s := by
  have hre : 0 < (s / 2 + 1).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.div_re]
    norm_num
    linarith
  have hG : Gamma (s / 2 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hre
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by simp [Real.pi_ne_zero]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [riemannZeta_eq_mul_completedRiemannZeta₀, riemannXi]
  set G := Complex.Gamma (s / 2 + 1) with hGdef
  set P := (Real.pi : ℂ) ^ (-s / 2) with hPdef
  field_simp
  ring

/-- The value `ξ 1 = 1 / 2`. -/
@[zz_tag "def_xi"]
theorem riemannXi_one : riemannXi 1 = 1 / 2 := by simp [riemannXi]

/-- `ξ` is analytic on the half-plane `-2 < re s`. -/
@[zz_tag "lem_xi_analytic"]
theorem analyticOnNhd_riemannXi : AnalyticOnNhd ℂ riemannXi {s : ℂ | -2 < s.re} :=
  differentiable_riemannXi.differentiableOn.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- The functional equation `ξ (1 - s) = ξ s`, for every `s`. -/
@[zz_tag "lem_xi_functional_eq"]
theorem riemannXi_functional_equation (s : ℂ) : riemannXi (1 - s) = riemannXi s :=
  Complex.riemannXi_one_sub s

/-! ## The digamma function -/

/-- The digamma function is the logarithmic derivative `Γ' / Γ` of the Gamma function. -/
@[zz_tag "def_digamma"]
theorem digamma_eq_deriv_Gamma_div_Gamma (z : ℂ) : digamma z = deriv Gamma z / Gamma z := by
  rw [digamma_def, logDeriv_apply]

/-- The digamma function is analytic on the open right half-plane. -/
@[zz_tag "lem_digamma_analytic"]
theorem analyticOnNhd_digamma : AnalyticOnNhd ℂ digamma {z : ℂ | 0 < z.re} := by
  have h : DifferentiableOn ℂ digamma {z : ℂ | 0 < z.re} :=
    fun z hz => (differentiableAt_digamma_of_re_pos hz).differentiableWithinAt
  exact h.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-! ## Integration over the boundary of a rectangle -/

/-- The boundary integral over the rectangle with corners `a + i c` and `b + i d` is
`∫ h (x + i c) dx + i ∫ h (b + i y) dy - ∫ h (x + i d) dx - i ∫ h (a + i y) dy`. -/
@[zz_tag "def_rect_integral"]
theorem rectangleIntegral_eq_boundary_integrals (h : ℂ → ℂ) (a b c d : ℝ) :
    RectangleIntegral h (a + c * I) (b + d * I) =
      (∫ x in a..b, h (x + c * I)) + I * (∫ y in c..d, h (b + y * I))
        - (∫ x in a..b, h (x + d * I)) - I * (∫ y in c..d, h (a + y * I)) := by
  simp only [RectangleIntegral, HIntegral, VIntegral, add_re, add_im, ofReal_re, ofReal_im,
    mul_re, mul_im, I_re, I_im, smul_eq_mul]
  norm_num
  abel

/-- The boundary integral of `s ↦ (s - p)⁻¹` over a rectangle containing `p` in its interior is
`2 π i`. -/
@[zz_tag "lem_rect_inv_integral"]
theorem rectangleIntegral_inv_sub_eq (a b c d : ℝ) (p : ℂ) (ha : a < p.re) (hb : p.re < b)
    (hc : c < p.im) (hd : p.im < d) :
    RectangleIntegral (fun s => (s - p)⁻¹) (a + c * I) (b + d * I) = 2 * Real.pi * I := by
  have hmem : Rectangle ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (d : ℂ) * I) ∈ 𝓝 p := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm]
    constructor
    · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
        sub_zero, add_zero]
      rw [Set.uIoo_of_le (by linarith : a ≤ b)]
      exact ⟨ha, hb⟩
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one, zero_mul,
        add_zero, zero_add]
      rw [Set.uIoo_of_le (by linarith : c ≤ d)]
      exact ⟨hc, hd⟩
  have key := ResidueTheoremInRectangle (c := 1) (z := (a : ℂ) + (c : ℂ) * I)
    (w := (b : ℂ) + (d : ℂ) * I) (p := p)
    (by simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
          sub_zero, add_zero]; linarith)
    (by simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one, zero_mul,
          add_zero, zero_add]; linarith)
    hmem
  rw [RectangleIntegral', smul_eq_mul] at key
  rw [mul_comm ((c : ℝ) : ℂ) I, mul_comm ((d : ℝ) : ℂ) I]
  field_simp [one_div] at key
  simpa [one_div] using key

/-! ## Local behaviour at a zero -/

/-- Near a zero `p` of order `n` of an analytic function `f`, the logarithmic derivative minus its
principal part, `f' / f - n / (s - p)`, is bounded on a punctured neighbourhood of `p`. -/
@[zz_tag "lem_log_deriv_principal_part"]
theorem bddAbove_logDeriv_sub_principal_part {f : ℂ → ℂ} {p : ℂ} {n : ℕ} (hf : AnalyticAt ℂ f p)
    (horder : analyticOrderAt f p = n) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ (logDeriv f - fun s : ℂ => (n : ℂ) / (s - p)) '' (U \ {p})) :=
  IsBigO_to_BddAbove
    (Kadiri.kadiri_logDeriv_analytic_zero_principal_part_remainder_bound hf horder)

/-- A subset `K` of the domain `U` of an analytic function `f` that does not vanish identically has
an open neighbourhood `V` with `K ⊆ V ⊆ U` in which `f` has no zeros beyond those already in `K`.
-/
@[zz_tag "lem_isolated_zeros_neighbourhood"]
theorem exists_isOpen_zeros_subset {f : ℂ → ℂ} {U K : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hf : AnalyticOnNhd ℂ f U) {x : ℂ} (hx : x ∈ U) (hfx : f x ≠ 0) (hK : K ⊆ U) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ ∀ z ∈ V, f z = 0 → z ∈ K := by
  have hcod := hf.preimage_zero_mem_codiscreteWithin hfx hx hUc
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hcod
  have key : ∀ y ∈ K, ∃ N, IsOpen N ∧ y ∈ N ∧ ∀ z ∈ N, z ∈ U → f z = 0 → z = y := by
    intro y hy
    obtain ⟨t, ht, hyt, hsub⟩ := mem_nhdsWithin.mp (hcod y (hK hy))
    refine ⟨t, ht, hyt, fun z hz hzU hfz => ?_⟩
    by_contra hne
    rcases hsub ⟨hz, hne⟩ with h | h
    · exact h hfz
    · exact h hzU
  choose N hNopen hNmem hNuniq using key
  refine ⟨⋃ y : K, N y y.2 ∩ U, isOpen_iUnion fun y => (hNopen y y.2).inter hU,
    fun y hy => ?_, ?_, ?_⟩
  · exact mem_iUnion.mpr ⟨⟨y, hy⟩, hNmem y hy, hK hy⟩
  · exact iUnion_subset fun y => inter_subset_right
  · intro z hz hfz
    obtain ⟨y, hzN, hzU⟩ := mem_iUnion.mp hz
    exact hNuniq y y.2 z hzN hzU hfz ▸ y.2

end ZetaZeros
