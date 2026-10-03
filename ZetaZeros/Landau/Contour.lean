/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Landau.HeightWindowJump
public import ZetaZeros.Landau.HorizontalEdges
public import ZetaZeros.Landau.Kernel
public import ZetaZeros.Landau.LeftEdge
public import ZetaZeros.Landau.RightEdge
public import ZetaZeros.Landau.ZeroOrdinateGaps

/-!
# Landau's explicit formula, symmetrically truncated

For `x > 1` not a prime power and `s` which is neither `1`, nor a zero of `ζ`, nor a trivial zero,
the symmetric partial sums over the non-trivial zeros satisfy

`lim_{U → ∞} ∑_{ρ ∈ 𝒩*, |im ρ| ≤ U} m_ρ x^{ρ - s} / (s - ρ) = R (x, s)`,

where `R (x, s)` is `ZetaZeros.landauRHS`. The proof integrates the Landau kernel

`K (w) = (ζ'/ζ) (w) ⬝ x^{w - s} / (w - s)`

over the rectangle `[-(2N+1), b] × [-U, U]`, applies the residue identity
`ZetaZeros.rectangleIntegral_landauKernel_eq`, and lets `U → ∞` along heights separated from the
zero ordinates with `N` tied to `U`, using the edge estimates of `ZetaZeros.Landau.RightEdge`,
`ZetaZeros.Landau.LeftEdge` and `ZetaZeros.Landau.HorizontalEdges`, and the jump bound of
`ZetaZeros.Landau.HeightWindowJump`.

## Main results

* `ZetaZeros.rectangleIntegral_landauKernel_eq_edges`: the rectangle integral of the Landau kernel
  written as its four edges.
* `ZetaZeros.tendsto_div_atTop_of_isLittleO`: `f (U + c) / U → 0` whenever `f = o (id)`.
* `ZetaZeros.landauTruncatedLimit`: Landau's explicit formula, symmetrically truncated.
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter Topology

/-! ### The assembly -/

/-- The four edges of the rectangle `[a₀, b₀] × [-c₀, c₀]`, written out. -/
theorem rectangleIntegral_landauKernel_eq_edges (x : ℝ) (s : ℂ) (a₀ b₀ c₀ : ℝ) :
    RectangleIntegral (landauKernel x s) ((a₀ : ℂ) + ((-c₀ : ℝ) : ℂ) * I)
        ((b₀ : ℂ) + ((c₀ : ℝ) : ℂ) * I)
      = (∫ σ in a₀..b₀, landauKernel x s ((σ : ℂ) + ((-c₀ : ℝ) : ℂ) * I))
        - (∫ σ in a₀..b₀, landauKernel x s ((σ : ℂ) + ((c₀ : ℝ) : ℂ) * I))
        + I * (∫ y in (-c₀)..c₀, landauKernel x s ((b₀ : ℂ) + (y : ℂ) * I))
        - I * ∫ y in (-c₀)..c₀, landauKernel x s ((a₀ : ℂ) + (y : ℂ) * I) := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  norm_num

/-- **The residue identity solved for the window sum.** At a height `U ≥ 3` separated from the
zero ordinates,

`2 π i ⬝ ∑_{|im ρ| ≤ U} m_ρ x^{ρ-s}/(s-ρ) = 2 π i ⬝ ((ζ'/ζ)(s) - x^{1-s}/(1-s)
  - ∑_{n ≤ N} x^{-2n-s}/(2n+s)) - (bottom - top + i ⬝ right - i ⬝ left)`,

where bottom, top, right and left are the edge integrals of the Landau kernel over the rectangle
`[-(2N+1), b] × [-U, U]`. -/
private theorem two_pi_I_mul_sum_heightWindow_eq {x : ℝ} (hx : 0 < x) {s : ℂ} (hs1 : s ≠ 1)
    (hsz : riemannZeta s ≠ 0) {b U gp : ℝ} {N : ℕ} (hb : 1 < b) (hbs : s.re < b)
    (hN : -(2 * (N : ℝ) + 1) < s.re) (hU : |s.im| < U) (h3 : 3 ≤ U) (hgp : 0 < gp)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → gp ≤ |(U - |ρ.im|)|) :
    2 * (Real.pi : ℂ) * I * ∑ ρ ∈ heightWindow U, landauZeroTerm x s ρ
      = 2 * (Real.pi : ℂ) * I * (logDeriv riemannZeta s - (x : ℂ) ^ (1 - s) / (1 - s)
          - ∑ n ∈ Finset.Icc 1 N, (x : ℂ) ^ (-(2 * (n : ℂ)) - s) / (2 * (n : ℂ) + s))
        - ((∫ σ in (-(2 * (N : ℝ) + 1))..b, landauKernel x s ((σ : ℂ) + ((-U : ℝ) : ℂ) * I))
            - (∫ σ in (-(2 * (N : ℝ) + 1))..b, landauKernel x s ((σ : ℂ) + ((U : ℝ) : ℂ) * I))
            + I * (∫ y in (-U)..U, landauKernel x s ((b : ℂ) + (y : ℂ) * I))
            - I * ∫ y in (-U)..U,
                landauKernel x s ((-(2 * (N : ℝ) + 1) : ℝ) + (y : ℂ) * I)) := by
  have hUz : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≠ U := by
    refine fun ρ hz => abs_im_ne_of_gap h3 hgp (fun τ h1 h2 h4 => ?_) hz
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ U)]
    exact hgap τ h1 h2 h4
  have hres := rectangleIntegral_landauKernel_eq hx hs1 hsz hb hbs hN hU hUz
  rw [rectangleIntegral_landauKernel_eq_edges] at hres
  linear_combination hres

/-- `f (U + c) / U → 0` as `U → ∞`, whenever `f = o (id)`. -/
theorem tendsto_div_atTop_of_isLittleO {f : ℝ → ℝ} (hf : f =o[atTop] (id : ℝ → ℝ)) (c : ℝ) :
    Tendsto (fun U : ℝ => f (U + c) / U) atTop (nhds 0) := by
  have hc : Tendsto (fun U : ℝ => U + c) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have h1 : Tendsto (fun U : ℝ => f (U + c) / (U + c)) atTop (nhds 0) :=
    hf.tendsto_div_nhds_zero.comp hc
  have h2 : Tendsto (fun U : ℝ => (U + c) / U) atTop (nhds 1) := by
    have h3 : Tendsto (fun U : ℝ => 1 + c / U) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => c) atTop _).div_atTop tendsto_id)
    refine h3.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with U hU
    field_simp
  have h4 := h1.mul h2
  rw [zero_mul] at h4
  refine h4.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 0 (-c))] with U hU
  have hU0 : (0 : ℝ) < U := lt_of_le_of_lt (le_max_left _ _) hU
  have hUc : (0 : ℝ) < U + c := by
    have := lt_of_le_of_lt (le_max_right (0 : ℝ) (-c)) hU
    linarith
  field_simp

/-- `log² = o (id)`. -/
private theorem isLittleO_log_sq_id : (fun t : ℝ => Real.log t * Real.log t) =o[atTop] (id : ℝ → ℝ)
    :=
  by
  have h1 := isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)
  refine (h1.mul_isBigO h1.isBigO).congr' (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  rw [← Real.rpow_add ht]
  norm_num

/-- **Landau's explicit formula, symmetrically truncated.** For `x > 1` not a prime power and
`s` which is neither `1`, nor a zero of `ζ`, nor a trivial zero,

`lim_{U → ∞} ∑_{ρ ∈ 𝒩*, |im ρ| ≤ U} m_ρ x^{ρ - s} / (s - ρ) = R (x, s)`,

where `R (x, s)` is `ZetaZeros.landauRHS`. -/
@[zz_tag "lem_landau_explicit"]
theorem landauTruncatedLimit : LandauTruncatedLimit := by
  intro x hx hxpp s hs1 hsz hsn
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hLx : 0 < Real.log x := Real.log_pos hx
  obtain ⟨b, hb32, hbs⟩ : ∃ b : ℝ, 3 / 2 ≤ b ∧ s.re < b :=
    ⟨max (3 / 2) (s.re + 1), le_max_left _ _, lt_of_lt_of_le (by linarith) (le_max_right _ _)⟩
  have hb1 : (1 : ℝ) < b := by linarith
  obtain ⟨C₀, hC₀, hheight⟩ := exists_height_far_from_zeros
  have hex : ∀ U₀ : ℝ, ∃ U : ℝ, 3 ≤ U₀ → U₀ ≤ U ∧ U ≤ U₀ + 1 ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → C₀ / Real.log U₀ ≤ |(U - |ρ.im|)| := by
    intro U₀
    by_cases h : 3 ≤ U₀
    · obtain ⟨U, h1, h2, h3⟩ := hheight U₀ h
      exact ⟨U, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun hc => absurd hc h⟩
  choose V hV using hex
  have hVtop : Tendsto V atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with U₀ hU₀ using (hV U₀ hU₀).1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, |s.re| + 1 ≤ (M : ℝ) :=
    ⟨⌈|s.re|⌉₊ + 1, by push_cast; linarith [Nat.le_ceil (|s.re|)]⟩
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  obtain ⟨NN, hNN⟩ : ∃ NN : ℝ → ℕ,
      ∀ U₀ : ℝ, NN U₀ = M + ⌈2 * Real.log U₀ / Real.log x⌉₊ := ⟨_, fun _ => rfl⟩
  have hNM : ∀ U₀ : ℝ, (M : ℝ) ≤ (NN U₀ : ℝ) := by
    intro U₀
    rw [hNN]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌈2 * Real.log U₀ / Real.log x⌉₊]
  have hNlog : ∀ U₀ : ℝ, 2 * Real.log U₀ / Real.log x ≤ (NN U₀ : ℝ) := by
    intro U₀
    rw [hNN]
    push_cast
    linarith [Nat.le_ceil (2 * Real.log U₀ / Real.log x)]
  have hNub : ∀ U₀ : ℝ, 0 ≤ 2 * Real.log U₀ / Real.log x →
      (NN U₀ : ℝ) ≤ (M : ℝ) + 2 * Real.log U₀ / Real.log x + 1 := by
    intro U₀ h
    rw [hNN]
    push_cast
    linarith [Nat.ceil_lt_add_one h]
  have hNtop : Tendsto NN atTop atTop := by
    have htend : Tendsto (fun U₀ : ℝ => 2 * Real.log U₀ / Real.log x) atTop atTop :=
      (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_div_const hLx
    refine tendsto_atTop_mono (fun U₀ => ?_) (tendsto_nat_ceil_atTop.comp htend)
    rw [hNN]
    exact Nat.le_add_left _ _
  have hT : Tendsto (fun U₀ : ℝ => ∑ n ∈ Finset.Icc 1 (NN U₀),
      (x : ℂ) ^ (-(2 * (n : ℂ)) - s) / (2 * (n : ℂ) + s)) atTop
      (nhds (landauTrivialSum x s)) := (tendsto_sum_landauTrivialTerm hx s).comp hNtop
  have hIR : ∀ w : ℂ, 2 * (Real.pi : ℂ) * I * ((1 / (2 * (Real.pi : ℂ))) * w) = I * w := by
    intro w
    have h1 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    field_simp
  have hRaux := tendsto_integral_landauKernel_right hx0 hxpp (s := s) (σ := b - s.re)
    (by linarith) (by linarith)
  rw [show b - s.re + s.re = b from by ring] at hRaux
  have hRI : Tendsto (fun U₀ : ℝ => I * ∫ y in (-(V U₀))..(V U₀),
      landauKernel x s ((b : ℂ) + (y : ℂ) * I)) atTop
      (nhds (2 * (Real.pi : ℂ) * I * -landauPrimeSum x s)) :=
    ((hRaux.comp hVtop).const_mul (2 * (Real.pi : ℂ) * I)).congr fun U₀ => hIR _
  obtain ⟨CL, hCL0, hCL⟩ := exists_norm_deriv_riemannZeta_div_le_of_re_eq_neg_odd
  have hR₀ : (0 : ℝ) < 2 * (M : ℝ) + 10 + 4 / Real.log x := by
    have h := div_pos (by norm_num : (0 : ℝ) < 4) hLx
    linarith
  have hL0 : Tendsto (fun U₀ : ℝ => ∫ y in (-(V U₀))..(V U₀),
      landauKernel x s ((-(2 * (NN U₀ : ℝ) + 1) : ℝ) + (y : ℂ) * I)) atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun U₀ : ℝ =>
      CL * (2 * (M : ℝ) + 10 + 4 / Real.log x) * (2 * (M : ℝ) + 10 + 4 / Real.log x)
        * x ^ (-1 - s.re) * U₀ ^ (-2 : ℝ)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with U₀ hU₀
      have hU0 : (0 : ℝ) < U₀ := by linarith
      have h3V : (3 : ℝ) ≤ V U₀ := le_trans hU₀ (hV U₀ hU₀).1
      have hVub : V U₀ ≤ U₀ + 1 := (hV U₀ hU₀).2.1
      have hNr : |s.re| + 1 ≤ (NN U₀ : ℝ) := le_trans hM (hNM U₀)
      have hlogU : 0 < Real.log U₀ := Real.log_pos (by linarith)
      have hlogle : Real.log U₀ ≤ U₀ := by
        linarith [Real.log_le_sub_one_of_pos hU0]
      have hy : 2 * Real.log U₀ / Real.log x ≤ 2 * U₀ / Real.log x :=
        (div_le_div_iff_of_pos_right hLx).2 (by linarith)
      have hy0 : (0 : ℝ) ≤ 2 * Real.log U₀ / Real.log x := by positivity
      have hNle := hNub U₀ hy0
      have ha1 : 2 * V U₀ ≤ (2 * (M : ℝ) + 10 + 4 / Real.log x) * U₀ := by
        nlinarith [div_pos (by norm_num : (0 : ℝ) < 4) hLx, mul_nonneg hMnn hU0.le]
      have ha2 : 2 * (NN U₀ : ℝ) + 3 + V U₀ ≤ (2 * (M : ℝ) + 10 + 4 / Real.log x) * U₀ := by
        have he : 2 * U₀ / Real.log x = 4 / Real.log x * U₀ / 2 := by ring
        nlinarith [mul_nonneg hMnn (by linarith : (0 : ℝ) ≤ U₀ - 1),
          div_pos (by norm_num : (0 : ℝ) < 4) hLx]
      have hstep : 4 * Real.log U₀ ≤ 2 * (NN U₀ : ℝ) * Real.log x := by
        have h := mul_le_mul_of_nonneg_right (hNlog U₀) hLx.le
        rw [div_mul_cancel₀ _ hLx.ne'] at h
        linarith
      have ha3 : x ^ (-(2 * (NN U₀ : ℝ) + 1) - s.re) ≤ x ^ (-1 - s.re) * U₀ ^ (-4 : ℝ) := by
        rw [show -(2 * (NN U₀ : ℝ) + 1) - s.re = (-1 - s.re) + -(2 * (NN U₀ : ℝ)) from by ring,
          Real.rpow_add hx0]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos hx0 _).le
        rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hU0]
        exact Real.exp_le_exp.2 (by nlinarith)
      have hU2 : U₀ * U₀ * U₀ ^ (-4 : ℝ) = U₀ ^ (-2 : ℝ) := by
        rw [show U₀ * U₀ * U₀ ^ (-4 : ℝ) = U₀ ^ (1 : ℝ) * U₀ ^ (1 : ℝ) * U₀ ^ (-4 : ℝ) from by
          rw [Real.rpow_one], ← Real.rpow_add hU0, ← Real.rpow_add hU0]
        norm_num
      refine le_trans (norm_integral_landauKernel_left_le hx (by linarith) hNr hCL0 hCL) ?_
      have hq0 : (0 : ℝ) ≤ 2 * (NN U₀ : ℝ) + 3 + V U₀ := by
        linarith [Nat.cast_nonneg (α := ℝ) (NN U₀)]
      have hs1' : 2 * V U₀ * (CL * (2 * (NN U₀ : ℝ) + 3 + V U₀))
          ≤ (2 * (M : ℝ) + 10 + 4 / Real.log x) * U₀
            * (CL * ((2 * (M : ℝ) + 10 + 4 / Real.log x) * U₀)) :=
        mul_le_mul ha1 (mul_le_mul_of_nonneg_left ha2 hCL0.le) (mul_nonneg hCL0.le hq0)
          (mul_nonneg hR₀.le hU0.le)
      refine le_trans (mul_le_mul hs1' ha3 (Real.rpow_pos_of_pos hx0 _).le
        (mul_nonneg (mul_nonneg hR₀.le hU0.le)
          (mul_nonneg hCL0.le (mul_nonneg hR₀.le hU0.le)))) (le_of_eq ?_)
      rw [← hU2]
      ring
    · have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul
        (CL * (2 * (M : ℝ) + 10 + 4 / Real.log x) * (2 * (M : ℝ) + 10 + 4 / Real.log x)
          * x ^ (-1 - s.re))
      rw [mul_zero] at h
      exact h
  have hLzero : Tendsto (fun U₀ : ℝ => I * ∫ y in (-(V U₀))..(V U₀),
      landauKernel x s ((-(2 * (NN U₀ : ℝ) + 1) : ℝ) + (y : ℂ) * I)) atTop (nhds 0) := by
    have h := hL0.const_mul I
    rwa [mul_zero] at h
  obtain ⟨E, hE0, hEb⟩ := exists_norm_integral_landauKernel_horizontal_le hx s hb32
  have hlogsq : Tendsto (fun U₀ : ℝ =>
      2 * E * (1 + 1 / C₀) * (Real.log (U₀ + 4) * Real.log (U₀ + 4) / U₀)) atTop (nhds 0) := by
    have h := (tendsto_div_atTop_of_isLittleO isLittleO_log_sq_id 4).const_mul
      (2 * E * (1 + 1 / C₀))
    rwa [mul_zero] at h
  have hedge : ∀ W : ℝ → ℝ, (∀ U₀ : ℝ, 3 ≤ U₀ → |W U₀| = V U₀) →
      Tendsto (fun U₀ : ℝ => ∫ σ in (-(2 * (NN U₀ : ℝ) + 1))..b,
        landauKernel x s ((σ : ℂ) + ((W U₀ : ℝ) : ℂ) * I)) atTop (nhds 0) := by
    intro W hW
    refine squeeze_zero_norm' ?_ hlogsq
    filter_upwards [Filter.eventually_ge_atTop (3 : ℝ),
      Filter.eventually_ge_atTop (2 * |s.im| + 2)] with U₀ hU₀ hU₀'
    have hU0 : (0 : ℝ) < U₀ := by linarith
    have h3V : (3 : ℝ) ≤ V U₀ := le_trans hU₀ (hV U₀ hU₀).1
    have hVlb : U₀ ≤ V U₀ := (hV U₀ hU₀).1
    have hVub : V U₀ ≤ U₀ + 1 := (hV U₀ hU₀).2.1
    have hWa : |W U₀| = V U₀ := hW U₀ hU₀
    have hlogU : 0 < Real.log U₀ := Real.log_pos (by linarith)
    have hgp : 0 < C₀ / Real.log U₀ := div_pos hC₀ hlogU
    have hsim : |s.im| + 1 ≤ |W U₀| := by rw [hWa]; linarith [abs_nonneg s.im]
    have hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        C₀ / Real.log U₀ ≤ |(|W U₀| - |ρ.im|)| := by
      intro ρ h1 h2 h3
      rw [hWa]
      exact (hV U₀ hU₀).2.2 ρ h1 h2 h3
    refine le_trans (hEb (W U₀) (C₀ / Real.log U₀) (-(2 * (NN U₀ : ℝ) + 1)) (by rw [hWa]; linarith)
      hgp hsim (by linarith [Nat.cast_nonneg (α := ℝ) (NN U₀)]) hgap) ?_
    rw [hWa]
    have hL4 : (1 : ℝ) ≤ Real.log (U₀ + 4) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hLmono : Real.log (V U₀ + 3) ≤ Real.log (U₀ + 4) :=
      Real.log_le_log (by linarith) (by linarith)
    have hLmono' : Real.log U₀ ≤ Real.log (U₀ + 4) := Real.log_le_log hU0 (by linarith)
    have hd0 : (0 : ℝ) < U₀ / 2 := by linarith
    have hdb : U₀ / 2 ≤ V U₀ - |s.im| := by linarith
    have hinv : 1 / (C₀ / Real.log U₀) = Real.log U₀ / C₀ := by
      rw [one_div_div]
    have hnum : E * Real.log (V U₀ + 3) * (1 + 1 / (C₀ / Real.log U₀))
        ≤ E * (1 + 1 / C₀) * (Real.log (U₀ + 4) * Real.log (U₀ + 4)) := by
      rw [hinv]
      have h1 : (1 : ℝ) + Real.log U₀ / C₀ ≤ Real.log (U₀ + 4) * (1 + 1 / C₀) := by
        have h2 : Real.log U₀ / C₀ ≤ Real.log (U₀ + 4) * (1 / C₀) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right hLmono' (by positivity)
        nlinarith
      have hB0 : (0 : ℝ) ≤ 1 + Real.log U₀ / C₀ := by positivity
      have hA' : (0 : ℝ) ≤ E * Real.log (U₀ + 4) :=
        mul_nonneg hE0.le (Real.log_nonneg (by linarith))
      calc E * Real.log (V U₀ + 3) * (1 + Real.log U₀ / C₀)
          ≤ E * Real.log (U₀ + 4) * (Real.log (U₀ + 4) * (1 + 1 / C₀)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hLmono hE0.le) h1 hB0 hA'
        _ = E * (1 + 1 / C₀) * (Real.log (U₀ + 4) * Real.log (U₀ + 4)) := by ring
    have hnum0 : (0 : ℝ) ≤ E * Real.log (V U₀ + 3) * (1 + 1 / (C₀ / Real.log U₀)) :=
      mul_nonneg (mul_nonneg hE0.le
        (Real.log_nonneg (by linarith : (1 : ℝ) ≤ V U₀ + 3))) (by positivity)
    refine le_trans (div_le_div_of_nonneg_left hnum0 hd0 hdb) ?_
    refine le_trans ((div_le_div_iff_of_pos_right hd0).2 hnum) (le_of_eq ?_)
    field_simp
  have hHt := hedge (fun U₀ => V U₀) (fun U₀ hU₀ => abs_of_nonneg
    (by linarith [le_trans hU₀ (hV U₀ hU₀).1]))
  have hHb := hedge (fun U₀ => -(V U₀)) (fun U₀ hU₀ => by
    rw [abs_neg, abs_of_nonneg (by linarith [le_trans hU₀ (hV U₀ hU₀).1])])
  have hbig : Tendsto (fun U₀ : ℝ => 2 * (Real.pi : ℂ) * I *
      ∑ ρ ∈ heightWindow (V U₀), landauZeroTerm x s ρ) atTop
      (nhds (2 * (Real.pi : ℂ) * I * landauRHS x s)) := by
    have hc : Tendsto (fun U₀ : ℝ => 2 * (Real.pi : ℂ) * I *
        (logDeriv riemannZeta s - (x : ℂ) ^ (1 - s) / (1 - s)
          - ∑ n ∈ Finset.Icc 1 (NN U₀), (x : ℂ) ^ (-(2 * (n : ℂ)) - s) / (2 * (n : ℂ) + s))
        - ((∫ σ in (-(2 * (NN U₀ : ℝ) + 1))..b,
                landauKernel x s ((σ : ℂ) + ((-(V U₀) : ℝ) : ℂ) * I))
            - (∫ σ in (-(2 * (NN U₀ : ℝ) + 1))..b,
                landauKernel x s ((σ : ℂ) + ((V U₀ : ℝ) : ℂ) * I))
            + I * (∫ y in (-(V U₀))..(V U₀), landauKernel x s ((b : ℂ) + (y : ℂ) * I))
            - I * ∫ y in (-(V U₀))..(V U₀),
                landauKernel x s ((-(2 * (NN U₀ : ℝ) + 1) : ℝ) + (y : ℂ) * I))) atTop
        (nhds (2 * (Real.pi : ℂ) * I * landauRHS x s)) := by
      have hval : 2 * (Real.pi : ℂ) * I * (logDeriv riemannZeta s
              - (x : ℂ) ^ (1 - s) / (1 - s) - landauTrivialSum x s)
            - (0 - 0 + 2 * (Real.pi : ℂ) * I * -landauPrimeSum x s - 0)
          = 2 * (Real.pi : ℂ) * I * landauRHS x s := by
        simp only [landauRHS]
        ring
      rw [← hval]
      exact ((tendsto_const_nhds.sub hT).const_mul (2 * (Real.pi : ℂ) * I)).sub
        (((hHb.sub hHt).add hRI).sub hLzero)
    refine hc.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (3 : ℝ),
      Filter.eventually_ge_atTop (|s.im| + 1)] with U₀ hU₀ hU₀'
    have hlogU : 0 < Real.log U₀ := Real.log_pos (by linarith)
    have hNs : -(2 * (NN U₀ : ℝ) + 1) < s.re := by
      have h := le_trans hM (hNM U₀)
      linarith [neg_abs_le s.re]
    exact (two_pi_I_mul_sum_heightWindow_eq hx0 hs1 hsz hb1 hbs hNs
      (by linarith [(hV U₀ hU₀).1]) (le_trans hU₀ (hV U₀ hU₀).1) (div_pos hC₀ hlogU)
      (hV U₀ hU₀).2.2).symm
  have hpiI : 2 * (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))
      Complex.I_ne_zero
  have hZV : Tendsto (fun U₀ : ℝ => ∑ ρ ∈ heightWindow (V U₀), landauZeroTerm x s ρ) atTop
      (nhds (landauRHS x s)) := by
    have h := hbig.const_mul (2 * (Real.pi : ℂ) * I)⁻¹
    rw [inv_mul_cancel_left₀ hpiI] at h
    exact h.congr fun U₀ => inv_mul_cancel_left₀ hpiI _
  obtain ⟨CJ, hCJ0, hCJ⟩ := exists_norm_sum_heightWindow_sub_le hx s
  have hjump : Tendsto (fun U₀ : ℝ => (∑ ρ ∈ heightWindow (V U₀), landauZeroTerm x s ρ)
      - ∑ ρ ∈ heightWindow U₀, landauZeroTerm x s ρ) atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun U₀ : ℝ => CJ * Real.log (U₀ + 4) / U₀) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (3 : ℝ),
        Filter.eventually_ge_atTop (2 * |s.im| + 2)] with U₀ hU₀ hU₀'
      exact hCJ U₀ (V U₀) hU₀' (hV U₀ hU₀).1 (hV U₀ hU₀).2.1
    · have h := (tendsto_div_atTop_of_isLittleO Real.isLittleO_log_id_atTop 4).const_mul CJ
      rw [mul_zero] at h
      exact h.congr fun U₀ => by ring
  have hfinal := hZV.sub hjump
  rw [sub_zero] at hfinal
  exact hfinal.congr fun U₀ => by ring

end ZetaZeros
