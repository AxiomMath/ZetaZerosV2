/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeNumberTheoremAnd.PerronFormula

/-!
# The truncated Perron formula, by the smoothed kernel

A truncated Perron formula for the kernel `x ^ s / s`, deduced from the smoothed Perron formula
`Perron.formulaGtOne` for `x ^ s / (s (s + 1))`: for `x > 0` with `x ≠ 1`, `c > 0` and `T > 0`,

`‖(1 / 2 π i) ∫_{c - iT}^{c + iT} x ^ s / s ds - [x > 1]‖ ≤ 2 x ^ c max 1 x / (π T |x - 1|)`.

The identity `1 / s = 1 / (s (s + 1)) + 1 / (s + 1)` relates the truncated integral at `c` to the
smoothed one at `c` and the truncated one at `c + 1`, and the rectangle `[c, c + 1] × [-T, T]`,
which contains no pole, relates the truncated integrals at `c` and at `c + 1`. At `x = 1` the
truncated integral is computed exactly. The sharper bound `x ^ c / (π T |log x|)` is
`ZetaZeros.norm_perronTruncated_sub_indicator_le`.

## Main results

* `ZetaZeros.norm_vIntegral'_cpow_div_self_sub_le`: the truncated Perron formula with the bound
  `2 x ^ c max 1 x / (π T |x - 1|)`.
* `ZetaZeros.tendsto_vIntegral'_cpow_div_self`: the truncated integral tends to `[x > 1]` as
  `T → ∞`.
* `ZetaZeros.vIntegral'_one_cpow_div_self`: at `x = 1` the truncated integral is
  `arctan (T / c) / π`.
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter MeasureTheory Set Topology

variable {x c T : ℝ}

/-! ## Two elementary facts -/

/-- Comparing quotients when the numerator grows and the denominator shrinks. -/
private theorem div_le_div_of_le_of_le {a b d e : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hd : 0 < d)
    (hde : d ≤ e) : a / e ≤ b / d := by
  rw [div_le_div_iff₀ (lt_of_lt_of_le hd hde) hd]
  nlinarith

/-- A point of the vertical line `re s = σ` is nonzero as soon as `σ ≠ 0`. -/
private theorem ofReal_add_mul_I_ne_zero {σ : ℝ} (hσ : σ ≠ 0) (t : ℝ) : (σ : ℂ) + t * I ≠ 0 :=
  fun h => hσ (by simpa using congrArg re h)

/-! ## Regularity of the two kernels -/

/-- **The Perron kernel `x ^ s / s` is holomorphic off the origin.** -/
private theorem differentiableOn_cpow_div_self (hx : 0 < x) :
    DifferentiableOn ℂ (fun s : ℂ ↦ (x : ℂ) ^ s / s) {0}ᶜ := by
  intro s hs
  have hs0 : s ≠ 0 := by simpa using hs
  have h1 : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) s :=
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl (by exact_mod_cast hx.ne'))
  exact (h1.div differentiableAt_id hs0).differentiableWithinAt

/-- **The Perron kernel is continuous along a vertical line** off the imaginary axis. -/
private theorem continuous_cpow_div_self_line (hx : 0 < x) {σ : ℝ} (hσ : σ ≠ 0) :
    Continuous fun t : ℝ ↦ (x : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I) :=
  (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))).div
    (by fun_prop) (ofReal_add_mul_I_ne_zero hσ)

/-- **The smoothed kernel is continuous along a vertical line** off `re s = 0` and `re s = -1`. -/
private theorem continuous_perronSmooth_line (hx : 0 < x) {σ : ℝ} (hσ : σ ≠ 0) (hσ1 : σ ≠ -1) :
    Continuous fun t : ℝ ↦ Perron.f x ((σ : ℂ) + t * I) := by
  have hne : ∀ t : ℝ, ((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1) ≠ 0 := by
    intro t
    refine mul_ne_zero (ofReal_add_mul_I_ne_zero hσ t) fun h => hσ1 ?_
    have h' := congrArg re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.one_re, Complex.zero_re] at h'
    linarith
  exact (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))).div
    (by fun_prop) hne

/-! ## The algebraic identity behind the unsmoothing -/

/-- **Unsmoothing, pointwise.** `1 / s = 1 / (s (s + 1)) + 1 / (s + 1)`, multiplied by `x ^ s` and
with `x ^ s / (s + 1)` rewritten as `x⁻¹ x ^ (s + 1) / (s + 1)`, so that the second summand is the
Perron kernel itself, evaluated one unit to the right. -/
private theorem cpow_div_self_eq (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    (x : ℂ) ^ s / s
      = (x : ℂ) ^ s / (s * (s + 1)) + (x : ℂ)⁻¹ * ((x : ℂ) ^ (s + 1) / (s + 1)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
  field_simp
  ring

/-- **Unsmoothing, on the truncated segment.** The truncated Perron integral at `c` is the
truncated *smoothed* integral at `c` plus `x⁻¹` times the truncated Perron integral at `c + 1`. -/
private theorem vIntegral_cpow_div_self_eq (hx : 0 < x) (hc : 0 < c) (T : ℝ) :
    VIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) c (-T) T
      = VIntegral (Perron.f x) c (-T) T
        + (x : ℂ)⁻¹ * VIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) (c + 1) (-T) T := by
  have hne1 : ∀ t : ℝ, (c : ℂ) + t * I + 1 ≠ 0 := by
    intro t h
    have h' := congrArg re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.one_re, Complex.zero_re] at h'
    linarith
  have key : ∀ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
        = Perron.f x ((c : ℂ) + t * I)
          + (x : ℂ)⁻¹ *
            ((x : ℂ) ^ (((c + 1 : ℝ) : ℂ) + t * I) / (((c + 1 : ℝ) : ℂ) + t * I)) := by
    intro t
    have hcast : ((c + 1 : ℝ) : ℂ) + t * I = (c : ℂ) + t * I + 1 := by push_cast; ring
    rw [hcast]
    exact cpow_div_self_eq hx (ofReal_add_mul_I_ne_zero hc.ne' t) (hne1 t)
  have hint1 : IntervalIntegrable (fun t : ℝ ↦ Perron.f x ((c : ℂ) + t * I)) volume (-T) T :=
    (continuous_perronSmooth_line hx hc.ne' (by linarith)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ (x : ℂ)⁻¹ *
      ((x : ℂ) ^ (((c + 1 : ℝ) : ℂ) + t * I) / (((c + 1 : ℝ) : ℂ) + t * I))) volume (-T) T :=
    ((continuous_cpow_div_self_line hx (by positivity : c + 1 ≠ 0)).const_mul
      _).intervalIntegrable _ _
  simp only [VIntegral, smul_eq_mul]
  rw [intervalIntegral.integral_congr (fun t _ => key t),
    intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_const_mul]
  ring

/-! ## The pole-free horizontal shift -/

/-- **The horizontal shift of the truncated Perron integral.** The rectangle
`[c, c + 1] × [-T, T]` avoids the only pole of `x ^ s / s`, so its boundary integral vanishes and
moving the vertical segment from `re s = c` to `re s = c + 1` costs exactly the two horizontal
sides. -/
private theorem vIntegral_cpow_div_self_shift (hx : 0 < x) (hc : 0 < c) (T : ℝ) :
    VIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) (c + 1) (-T) T
        - VIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) c (-T) T
      = HIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) c (c + 1) T
        - HIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) c (c + 1) (-T) := by
  have hz : ((c : ℂ) - T * I).re = c := by simp
  have hz' : ((c : ℂ) - T * I).im = -T := by simp
  have hw : (((c + 1 : ℝ) : ℂ) + T * I).re = c + 1 := by simp
  have hw' : (((c + 1 : ℝ) : ℂ) + T * I).im = T := by simp
  have hsub : Rectangle ((c : ℂ) - T * I) (((c + 1 : ℝ) : ℂ) + T * I) ⊆ ({0} : Set ℂ)ᶜ := by
    intro p hp
    have hre : p.re ∈ Set.uIcc (((c : ℂ) - T * I).re) ((((c + 1 : ℝ) : ℂ) + T * I).re) := hp.1
    rw [hz, hw, Set.uIcc_of_le (by linarith)] at hre
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    rw [h, Complex.zero_re] at hre
    linarith [hre.1]
  have hrect := HolomorphicOn.vanishesOnRectangle (differentiableOn_cpow_div_self hx) hsub
  simp only [RectangleIntegral] at hrect
  rw [hz, hz', hw, hw'] at hrect
  linear_combination hrect

/-- **The horizontal sides are small.** On the segment `im s = y`, `c ≤ re s ≤ c + 1`, the Perron
kernel is at most `x ^ c max 1 x / |y|`, and the segment has length `1`. -/
private theorem norm_hIntegral_cpow_div_self_le (hx : 0 < x) {y : ℝ} (hy : y ≠ 0) :
    ‖HIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) c (c + 1) y‖ ≤ x ^ c * max 1 x / |y| := by
  have hy' : 0 < |y| := abs_pos.mpr hy
  have hmax : x ^ c * max 1 x = max (x ^ c) (x ^ (c + 1)) := by
    rw [Real.rpow_add_one hx.ne' c, mul_max_of_nonneg _ _ (Real.rpow_nonneg hx.le c), mul_one]
  have hbd : ∀ σ ∈ Set.uIoc c (c + 1),
      ‖(x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I)‖ ≤ x ^ c * max 1 x / |y| := by
    intro σ hσ
    rw [Set.uIoc_of_le (by linarith)] at hσ
    obtain ⟨h1, h2⟩ := hσ
    have hnum : x ^ σ ≤ x ^ c * max 1 x := by
      rw [hmax]
      rcases le_total 1 x with h | h
      · exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le h h2)
      · exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_ge hx h h1.le)
    have hden : |y| ≤ ‖(σ : ℂ) + y * I‖ := by
      simpa using Complex.abs_im_le_norm ((σ : ℂ) + y * I)
    have hre : ((σ : ℂ) + y * I).re = σ := by simp
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
    exact div_le_div_of_le_of_le (Real.rpow_nonneg hx.le σ) hnum hy' hden
  simpa [HIntegral] using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-! ## The truncation error of the smoothed integral -/

/-- The modulus of the smoothed kernel on a vertical line is `O(x ^ c / t ^ 2)`: both factors of
the denominator have imaginary part `t`. -/
private theorem norm_perronSmooth_line_le (hx : 0 < x) {t : ℝ} (ht : t ≠ 0) :
    ‖Perron.f x ((c : ℂ) + t * I)‖ ≤ x ^ c * |t| ^ (-2 : ℝ) := by
  have ht' : 0 < |t| := abs_pos.mpr ht
  have h1 : |t| ≤ ‖(c : ℂ) + t * I‖ := by simpa using Complex.abs_im_le_norm ((c : ℂ) + t * I)
  have h2 : |t| ≤ ‖(c : ℂ) + t * I + 1‖ := by
    simpa using Complex.abs_im_le_norm ((c : ℂ) + t * I + 1)
  have hre : ((c : ℂ) + t * I).re = c := by simp
  have hpow : x ^ c * |t| ^ (-2 : ℝ) = x ^ c / (|t| * |t|) := by
    rw [Real.rpow_neg (abs_nonneg t), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    ring
  simp only [Perron.f]
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, norm_mul, hpow]
  exact div_le_div_of_le_of_le (Real.rpow_nonneg hx.le c) le_rfl (by positivity)
    (mul_le_mul h1 h2 (abs_nonneg t) ((abs_nonneg t).trans h1))

/-- A tail bound: an integral over `(T, ∞)` of something dominated by `M t ^ (-2)`. -/
private theorem norm_integral_Ioi_le_of_norm_le (hT : 0 < T) {M : ℝ} {G : ℝ → ℂ}
    (hGle : ∀ t ∈ Set.Ioi T, ‖G t‖ ≤ M * t ^ (-2 : ℝ)) :
    ‖∫ t in Set.Ioi T, G t‖ ≤ M / T := by
  have hdom : IntegrableOn (fun t : ℝ ↦ M * t ^ (-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul M
  calc ‖∫ t in Set.Ioi T, G t‖ ≤ ∫ t in Set.Ioi T, ‖G t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi T, M * t ^ (-2 : ℝ) := by
        refine integral_mono_of_nonneg (.of_forall fun t ↦ norm_nonneg _) hdom ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hGle t ht
    _ = M / T := by
        rw [MeasureTheory.integral_const_mul,
          integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT,
          show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp

/-- **The smoothed integral may be truncated at height `T` for the price `2 x ^ c / T`.** -/
private theorem norm_vIntegral_sub_verticalIntegral_le (hx : 0 < x) (hc : 0 < c) (hT : 0 < T) :
    ‖VIntegral (Perron.f x) c (-T) T - VerticalIntegral (Perron.f x) c‖ ≤ 2 * x ^ c / T := by
  have hintF : Integrable fun t : ℝ ↦ Perron.f x ((c : ℂ) + t * I) :=
    Perron.isIntegrable hx hc.ne' (by linarith)
  have hb1 : ‖∫ t in Set.Ioi T, Perron.f x ((c : ℂ) + t * I)‖ ≤ x ^ c / T := by
    refine norm_integral_Ioi_le_of_norm_le hT fun t ht => ?_
    have htpos : 0 < t := hT.trans ht
    have h := norm_perronSmooth_line_le (c := c) hx htpos.ne'
    rwa [abs_of_pos htpos] at h
  have hb2 : ‖∫ t in Set.Iic (-T), Perron.f x ((c : ℂ) + t * I)‖ ≤ x ^ c / T := by
    have hIic : (∫ t in Set.Iic (-T), Perron.f x ((c : ℂ) + t * I))
        = ∫ t in Set.Ioi T, Perron.f x ((c : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      have h := integral_comp_neg_Iic (-T)
        (fun u : ℝ ↦ Perron.f x ((c : ℂ) + ((-u : ℝ) : ℂ) * I))
      simp only [neg_neg] at h
      exact h
    rw [hIic]
    refine norm_integral_Ioi_le_of_norm_le hT fun t ht => ?_
    have htpos : 0 < t := hT.trans ht
    have h := norm_perronSmooth_line_le (c := c) hx (t := -t) (by linarith)
    rw [abs_neg, abs_of_pos htpos] at h
    exact h
  rw [verticalIntegral_split_three (f := Perron.f x) (σ := c) (-T) T hintF,
    MeasureTheory.integral_Ici_eq_integral_Ioi,
    show ∀ u v w : ℂ, u - (v + u + w) = -v - w from fun _ _ _ => by ring]
  calc ‖-(I • ∫ t in Set.Iic (-T), Perron.f x ((c : ℂ) + t * I))
          - I • ∫ t in Set.Ioi T, Perron.f x ((c : ℂ) + t * I)‖
      ≤ ‖-(I • ∫ t in Set.Iic (-T), Perron.f x ((c : ℂ) + t * I))‖
          + ‖I • ∫ t in Set.Ioi T, Perron.f x ((c : ℂ) + t * I)‖ := norm_sub_le _ _
    _ = ‖∫ t in Set.Iic (-T), Perron.f x ((c : ℂ) + t * I)‖
          + ‖∫ t in Set.Ioi T, Perron.f x ((c : ℂ) + t * I)‖ := by
        simp only [norm_neg, norm_smul, Complex.norm_I, one_mul]
    _ ≤ x ^ c / T + x ^ c / T := add_le_add hb2 hb1
    _ = 2 * x ^ c / T := by ring

/-! ## The truncated Perron formula -/

/-- **The truncated Perron formula.** For `x > 0` with `x ≠ 1`, `c > 0` and `T > 0`,

`‖(1 / 2 π i) ∫_{c - iT}^{c + iT} x ^ s / s ds - [x > 1]‖ ≤ 2 x ^ c max 1 x / (π T |x - 1|)`. -/
theorem norm_vIntegral'_cpow_div_self_sub_le
    (hx : 0 < x) (hx1 : x ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    ‖VIntegral' (fun s : ℂ ↦ (x : ℂ) ^ s / s) c (-T) T - (if 1 < x then 1 else 0)‖
      ≤ 2 * x ^ c * max 1 x / (Real.pi * T * |x - 1|) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hxc : (0 : ℝ) < x ^ c := Real.rpow_pos_of_pos hx c
  have habs : (0 : ℝ) < |x - 1| := abs_pos.mpr (sub_ne_zero.mpr hx1)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  simp only [VIntegral', smul_eq_mul]
  set A := VIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) c (-T) T with hA
  set A' := VIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) (c + 1) (-T) T with hA'
  set B := VIntegral (Perron.f x) c (-T) T with hB
  set Binf := VerticalIntegral (Perron.f x) c with hBinf
  set H := HIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) c (c + 1) T
    - HIntegral (fun s : ℂ ↦ (x : ℂ) ^ s / s) c (c + 1) (-T) with hH
  set k : ℂ := 1 / (2 * (Real.pi : ℂ) * I) with hk
  set m : ℂ := if 1 < x then 1 else 0 with hm
  have h1 : A = B + (x : ℂ)⁻¹ * A' := vIntegral_cpow_div_self_eq hx hc T
  have h2 : A' - A = H := vIntegral_cpow_div_self_shift hx hc T
  have hval : m * (1 - (x : ℂ)⁻¹) = k * Binf := by
    by_cases hgt : 1 < x
    · have hf := Perron.formulaGtOne (x := x) (σ := c) hgt hc
      rw [show (fun s : ℂ ↦ (x : ℂ) ^ s / (s * (s + 1))) = Perron.f x from rfl] at hf
      simp only [VerticalIntegral', smul_eq_mul, ← hBinf, ← hk] at hf
      have hm1 : m = 1 := by simp [hm, hgt]
      rw [hm1, one_mul, ← one_div]
      exact hf.symm
    · have hlt : x < 1 := lt_of_le_of_ne (not_lt.mp hgt) hx1
      have hf := Perron.formulaLtOne (x := x) (σ := c) hx hlt hc
      have hm0 : m = 0 := by simp [hm, hgt]
      rw [hm0, hBinf, hf]
      ring
  have hkey : (k * A - m) * (1 - (x : ℂ)⁻¹) = k * (B - Binf) + (x : ℂ)⁻¹ * (k * H) := by
    have hA_eq : A * (1 - (x : ℂ)⁻¹) = B + (x : ℂ)⁻¹ * H := by rw [← h2, h1]; ring
    calc (k * A - m) * (1 - (x : ℂ)⁻¹)
        = k * (A * (1 - (x : ℂ)⁻¹)) - m * (1 - (x : ℂ)⁻¹) := by ring
      _ = k * (B + (x : ℂ)⁻¹ * H) - k * Binf := by rw [hA_eq, hval]
      _ = k * (B - Binf) + (x : ℂ)⁻¹ * (k * H) := by ring
  have hknorm : ‖k‖ = 1 / (2 * Real.pi) := by rw [hk]; simp [abs_of_pos hpi]
  have hxinv : ‖(x : ℂ)⁻¹‖ = x⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  have hone : ‖(1 : ℂ) - (x : ℂ)⁻¹‖ = |x - 1| / x := by
    rw [show (1 : ℂ) - (x : ℂ)⁻¹ = ((1 - x⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, show (1 : ℝ) - x⁻¹ = (x - 1) / x by field_simp, abs_div, abs_of_pos hx]
  have hBerr : ‖B - Binf‖ ≤ 2 * x ^ c / T := norm_vIntegral_sub_verticalIntegral_le hx hc hT
  have hHerr : ‖H‖ ≤ 2 * (x ^ c * max 1 x) / T := by
    have e1 := norm_hIntegral_cpow_div_self_le (c := c) hx (y := T) hT.ne'
    have e2 := norm_hIntegral_cpow_div_self_le (c := c) hx (y := -T) (by linarith)
    rw [abs_of_pos hT] at e1
    rw [abs_of_neg (by linarith : -T < 0), neg_neg] at e2
    rw [hH]
    refine (norm_sub_le _ _).trans ?_
    have : x ^ c * max 1 x / T + x ^ c * max 1 x / T = 2 * (x ^ c * max 1 x) / T := by ring
    linarith
  have hmul : ‖k * A - m‖ * (|x - 1| / x)
      ≤ 1 / (2 * Real.pi) * (2 * x ^ c / T)
        + x⁻¹ * (1 / (2 * Real.pi) * (2 * (x ^ c * max 1 x) / T)) := by
    have hnorms := congrArg (‖·‖) hkey
    simp only [norm_mul, hone] at hnorms
    have hp : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
    have hq : (0 : ℝ) ≤ x⁻¹ := by positivity
    calc ‖k * A - m‖ * (|x - 1| / x)
        = ‖k * (B - Binf) + (x : ℂ)⁻¹ * (k * H)‖ := hnorms
      _ ≤ ‖k * (B - Binf)‖ + ‖(x : ℂ)⁻¹ * (k * H)‖ := norm_add_le _ _
      _ ≤ 1 / (2 * Real.pi) * (2 * x ^ c / T)
            + x⁻¹ * (1 / (2 * Real.pi) * (2 * (x ^ c * max 1 x) / T)) := by
          simp only [norm_mul, hknorm, hxinv]
          exact add_le_add (mul_le_mul_of_nonneg_left hBerr hp)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHerr hp) hq)
  refine le_of_mul_le_mul_right (hmul.trans ?_) (div_pos habs hx)
  rw [show 2 * x ^ c * max 1 x / (Real.pi * T * |x - 1|) * (|x - 1| / x)
      = 2 * x ^ c * max 1 x / (Real.pi * T * x) by field_simp,
    show 1 / (2 * Real.pi) * (2 * x ^ c / T)
        + x⁻¹ * (1 / (2 * Real.pi) * (2 * (x ^ c * max 1 x) / T))
      = x ^ c * (x + max 1 x) / (Real.pi * T * x) by field_simp]
  have hmx : x ≤ max 1 x := le_max_right 1 x
  have hnum : x ^ c * (x + max 1 x) ≤ 2 * x ^ c * max 1 x := by
    nlinarith [mul_nonneg hxc.le (sub_nonneg.mpr hmx)]
  exact div_le_div_of_le_of_le (by positivity) hnum (by positivity) le_rfl

/-- **The truncated Perron formula as a limit.** The truncated integral tends to `1` when `x > 1`
and to `0` when `0 < x < 1`. -/
theorem tendsto_vIntegral'_cpow_div_self (hx : 0 < x) (hx1 : x ≠ 1) (hc : 0 < c) :
    Tendsto (fun T : ℝ ↦ VIntegral' (fun s : ℂ ↦ (x : ℂ) ^ s / s) c (-T) T) atTop
      (𝓝 (if 1 < x then 1 else 0)) := by
  have habs : (0 : ℝ) < |x - 1| := abs_pos.mpr (sub_ne_zero.mpr hx1)
  have hzero : Tendsto (fun T : ℝ ↦ 2 * x ^ c * max 1 x / (Real.pi * |x - 1|) / T) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  refine (norm_vIntegral'_cpow_div_self_sub_le hx hx1 hc hT).trans_eq ?_
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp

/-! ## The excluded case `x = 1`, exactly -/

/-- **The truncated Perron integral at `x = 1`, in closed form:**
`(1 / 2 π i) ∫_{c - iT}^{c + iT} ds / s = arctan (T / c) / π`. -/
theorem vIntegral'_one_cpow_div_self (hc : 0 < c) (T : ℝ) :
    VIntegral' (fun s : ℂ ↦ (1 : ℂ) ^ s / s) c (-T) T
      = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hint : (∫ t in (-T)..T, (1 : ℂ) / ((c : ℂ) + t * I))
      = 2 * ((Real.arctan (T / c) : ℝ) : ℂ) := by
    rw [integral_const_div_re_add_self (A := 1) (x := c) (y₁ := -T) (y₂ := T) hc.ne',
      show ((-T : ℝ)) ^ 2 = T ^ 2 from neg_sq T,
      show Real.arctan (T / -c) = -Real.arctan (T / c) by rw [div_neg, Real.arctan_neg],
      show Real.arctan (-T / -c) = Real.arctan (T / c) by rw [neg_div_neg_eq]]
    push_cast
    field_simp
    ring
  simp only [VIntegral', VIntegral, smul_eq_mul, Complex.one_cpow]
  rw [hint]
  push_cast
  field_simp

end ZetaZeros
