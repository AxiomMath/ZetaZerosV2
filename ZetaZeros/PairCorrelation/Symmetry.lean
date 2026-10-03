/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import ZetaZeros.Zeta.OrderConj

/-!
# Reflection of the zeros and a residue integral

Two ingredients of the symmetry of the pair-correlation function: the invariance of the
multiplicity of a zero of `ζ` under the reflection `ρ ↦ 1 - conj ρ`, and the residue integral

`∫ dt / ((1 + t²)(1 + (t + a)²)) = 2π / (4 + a²)` for `|im a| < 1`,

which turns the pair kernel into the weight `w`.

The reflection is the composition of the two symmetries of the zero set: conjugation, which fixes
the real part, and the functional equation `s ↦ 1 - s`, which is available on the open critical
strip. Each preserves the order of vanishing, hence so does their composition.

The residue integral is evaluated on the line rather than on a contour. Writing
`(1 + t²)(1 + (t + a)²) = P(t) Q(t)` with `P(t) = (t - i)(t + a + i)` and
`Q(t) = (t + i)(t + a - i)`, each of `P` and `Q` is a quadratic with one root in each open
half-plane -- this is exactly where `|im a| < 1` enters -- and `Q - P = 2ia`, so for `a ≠ 0` the
integrand is `(2ia)⁻¹ (P⁻¹ - Q⁻¹)`. The line integral of the reciprocal of such a quadratic is
`2πi / (z - w)`, where `z` is the root above the axis and `w` the one below: the function
`t ↦ (log (t - z) - log (t - w)) / (z - w)` is a primitive, both logarithms staying on one side of
the branch cut because `t - z` never leaves the open lower half-plane and `t - w` never leaves the
open upper one, and the whole of the residue is the jump `-2πi` of the difference of the arguments
at `-∞`. The excluded case `a = 0` is a double pole, and is treated by the same primitive together
with `∫ (t - z)⁻² dt = 0`, rather than by a limit from `a ≠ 0`.

The reality of `F` (`ZetaZeros.conj_pairCorrelation`, `ZetaZeros.normalizedPairCorrelation_im`)
reindexes the double sum by the reflection, and its non-negativity
(`ZetaZeros.zero_le_pairCorrelation_re`, `ZetaZeros.zero_le_normalizedPairCorrelation_re`) turns
the weight into an integral of the pair kernel over the line, where the double sum becomes a square
modulus.

## Main results

* `ZetaZeros.zeroMultiplicity_one_sub_conj`: the reflection `ρ ↦ 1 - conj ρ` preserves the
  multiplicity of a zero of `ζ` in the open critical strip.
* `ZetaZeros.integral_inv_ofReal_sub_mul_sub`: the line integral of `((t - z)(t - w))⁻¹` is
  `2πi / (z - w)` when `z` lies above the real axis and `w` below it.
* `ZetaZeros.integral_inv_ofReal_sub_sq`: the line integral of `(t - z)⁻²` vanishes for `z` off the
  real axis.
* `ZetaZeros.integral_inv_one_add_sq_mul_one_add_add_sq`: the residue integral itself.

## Implementation notes

The two line integrals are stated for arbitrary poles off the real axis rather than for the four
poles `±i`, `-a ± i` at hand: nothing in either proof uses more than the position of a pole
relative to the axis, and the residue integral needs them at three different pairs of poles.
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter MeasureTheory Topology

/-! ### Reflection preserves multiplicity -/

/-- **Reflection preserves the multiplicity of a zero.** For `ρ` in the open critical strip the
multiplicity of `1 - conj ρ` as a zero of `ζ` equals that of `ρ`, the two symmetries of the zero
set composed. -/
@[zz_tag "lem_reflect_mult"]
theorem zeroMultiplicity_one_sub_conj {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    zeroMultiplicity (1 - (starRingEnd ℂ) ρ) = zeroMultiplicity ρ := by
  have hre : ((starRingEnd ℂ) ρ).re = ρ.re := Complex.conj_re ρ
  have hne : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  rw [zeroMultiplicity_one_sub (by rw [hre]; exact h0) (by rw [hre]; exact h1),
    zeroMultiplicity_conj hne]

/-! ### Line integrals of a rational function with poles off the real axis -/

section LineIntegral

variable {z w : ℂ}

/-- A point off the real axis is not real. -/
private lemma ofReal_sub_ne_zero (hz : z.im ≠ 0) (t : ℝ) : (t : ℂ) - z ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact hz (by rw [← h]; simp)

private lemma norm_ofReal_sub_sq (z : ℂ) (t : ℝ) :
    ‖(t : ℂ) - z‖ ^ 2 = (t - z.re) ^ 2 + z.im ^ 2 := by
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]
  simp
  ring

private lemma tendsto_norm_ofReal_sub_atTop {l : Filter ℝ}
    (hl : Tendsto (fun t : ℝ => |t|) l atTop) (z : ℂ) :
    Tendsto (fun t : ℝ => ‖(t : ℂ) - z‖) l atTop := by
  refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right l (-‖z‖) hl)
  simpa [sub_eq_add_neg] using norm_sub_norm_le ((t : ℂ)) z

private lemma continuous_inv_ofReal_sub_mul_sub (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Continuous fun t : ℝ => (((t : ℂ) - z) * ((t : ℂ) - w))⁻¹ :=
  ((Complex.continuous_ofReal.sub continuous_const).mul
      (Complex.continuous_ofReal.sub continuous_const)).inv₀ fun t =>
    mul_ne_zero (ofReal_sub_ne_zero hz t) (ofReal_sub_ne_zero hw t)

/-- The Poisson-type majorant `‖t - z‖⁻²` is integrable on the line, for `z` off the real axis. -/
private theorem integrable_inv_norm_ofReal_sub_sq (hz : z.im ≠ 0) :
    Integrable fun t : ℝ => (‖(t : ℂ) - z‖ ^ 2)⁻¹ := by
  have h := ((integrable_inv_one_add_sq.comp_div hz).comp_sub_right z.re).const_mul
    ((z.im ^ 2)⁻¹ : ℝ)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [norm_ofReal_sub_sq]
  have h2 : z.im ^ 2 ≠ 0 := pow_ne_zero 2 hz
  field_simp
  ring

/-- `(t - z)⁻²` is integrable on the line, for `z` off the real axis. -/
theorem integrable_inv_ofReal_sub_sq (hz : z.im ≠ 0) :
    Integrable fun t : ℝ => (((t : ℂ) - z) ^ 2)⁻¹ := by
  refine (integrable_inv_norm_ofReal_sub_sq hz).mono'
    (((Complex.continuous_ofReal.sub continuous_const).pow 2).inv₀ (fun t =>
      pow_ne_zero 2 (ofReal_sub_ne_zero hz t))).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  simp

/-- `((t - z)(t - w))⁻¹` is integrable on the line, for `z` and `w` off the real axis. -/
theorem integrable_inv_ofReal_sub_mul_sub (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Integrable fun t : ℝ => (((t : ℂ) - z) * ((t : ℂ) - w))⁻¹ := by
  refine (((integrable_inv_norm_ofReal_sub_sq hz).add
      (integrable_inv_norm_ofReal_sub_sq hw)).const_mul ((2 : ℝ)⁻¹)).mono'
    (continuous_inv_ofReal_sub_mul_sub hz hw).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, norm_inv, norm_mul, mul_inv, ← inv_pow]
  have h := two_mul_le_add_sq ‖(t : ℂ) - z‖⁻¹ ‖(t : ℂ) - w‖⁻¹
  linarith

/-- The fundamental theorem of calculus on the whole line: an integrable derivative integrates to
the jump of its primitive between the two ends. -/
private lemma integral_eq_of_hasDerivAt_of_tendsto {f F : ℝ → ℂ} {c d : ℂ} (hf : Integrable f)
    (hF : ∀ t, HasDerivAt F (f t) t) (hbot : Tendsto F atBot (𝓝 c))
    (htop : Tendsto F atTop (𝓝 d)) : ∫ t : ℝ, f t = d - c := by
  have h1 : Tendsto (fun R : ℝ => ∫ t in (-R)..R, f t) atTop (𝓝 (∫ t : ℝ, f t)) :=
    intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id
  have h2 : ∀ R : ℝ, (∫ t in (-R)..R, f t) = F R - F (-R) := fun R =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hf.intervalIntegrable
  simp only [h2] at h1
  refine tendsto_nhds_unique h1 (htop.sub ?_)
  exact hbot.comp tendsto_neg_atTop_atBot

/-- **The line integral of `(t - z)⁻²` vanishes** for `z` off the real axis: its primitive
`-(t - z)⁻¹` has the same limit at both ends of the line. -/
theorem integral_inv_ofReal_sub_sq (hz : z.im ≠ 0) : ∫ t : ℝ, (((t : ℂ) - z) ^ 2)⁻¹ = 0 := by
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => -((s : ℂ) - z)⁻¹) ((((t : ℂ) - z) ^ 2)⁻¹) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℂ => u - z) 1 (t : ℂ) := (hasDerivAt_id _).sub_const z
    have h2 := (h1.inv (ofReal_sub_ne_zero hz t)).neg
    have h3 : -(-1 / ((t : ℂ) - z) ^ 2) = (((t : ℂ) - z) ^ 2)⁻¹ := by
      rw [neg_div, neg_neg, one_div]
    rw [← h3]
    exact h2.comp_ofReal
  have hlim : ∀ l : Filter ℝ, Tendsto (fun t : ℝ => |t|) l atTop →
      Tendsto (fun s : ℝ => -((s : ℂ) - z)⁻¹) l (𝓝 0) := by
    intro l hl
    rw [← neg_zero]
    refine Tendsto.neg ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    simpa [Pi.inv_def] using (tendsto_norm_ofReal_sub_atTop hl z).inv_tendsto_atTop
  have := integral_eq_of_hasDerivAt_of_tendsto (integrable_inv_ofReal_sub_sq hz) hF
    (hlim atBot tendsto_abs_atBot_atTop) (hlim atTop tendsto_abs_atTop_atTop)
  simpa using this


/-- Along the positive end of the line the argument of `t - z` tends to `0`. -/
private lemma tendsto_arg_ofReal_sub_atTop (z : ℂ) :
    Tendsto (fun t : ℝ => ((t : ℂ) - z).arg) atTop (𝓝 0) := by
  have h1 : ∀ᶠ t : ℝ in atTop, ((t : ℂ) - z).arg = Real.arcsin (-z.im / ‖(t : ℂ) - z‖) := by
    filter_upwards [eventually_ge_atTop z.re] with t ht
    rw [Complex.arg_of_re_nonneg (by simp only [Complex.sub_re, Complex.ofReal_re]; linarith)]
    simp
  rw [tendsto_congr' h1]
  have h2 : Tendsto (fun t : ℝ => -z.im / ‖(t : ℂ) - z‖) atTop (𝓝 0) :=
    (tendsto_norm_ofReal_sub_atTop tendsto_abs_atTop_atTop z).const_div_atTop _
  simpa [Function.comp_def] using (Real.continuous_arcsin.tendsto 0).comp h2

/-- Along the negative end of the line the argument of `t - z` tends to `-π` for `z` above the real
axis: the point `t - z` approaches the negative real axis from below. -/
private lemma tendsto_arg_ofReal_sub_atBot_of_im_pos (hz : 0 < z.im) :
    Tendsto (fun t : ℝ => ((t : ℂ) - z).arg) atBot (𝓝 (-Real.pi)) := by
  have h1 : ∀ᶠ t : ℝ in atBot,
      ((t : ℂ) - z).arg = Real.arcsin (z.im / ‖(t : ℂ) - z‖) - Real.pi := by
    filter_upwards [eventually_lt_atBot z.re] with t ht
    rw [Complex.arg_of_re_neg_of_im_neg (by simp only [Complex.sub_re, Complex.ofReal_re]; linarith)
      (by simp only [Complex.sub_im, Complex.ofReal_im, zero_sub]; linarith)]
    simp
  rw [tendsto_congr' h1]
  have h2 : Tendsto (fun t : ℝ => z.im / ‖(t : ℂ) - z‖) atBot (𝓝 0) :=
    (tendsto_norm_ofReal_sub_atTop tendsto_abs_atBot_atTop z).const_div_atTop _
  have h3 := (Real.continuous_arcsin.tendsto 0).comp h2
  simp only [Real.arcsin_zero, Function.comp_def] at h3
  simpa using h3.sub_const Real.pi

/-- Along the negative end of the line the argument of `t - w` tends to `π` for `w` below the real
axis: the point `t - w` approaches the negative real axis from above. -/
private lemma tendsto_arg_ofReal_sub_atBot_of_im_neg (hw : w.im < 0) :
    Tendsto (fun t : ℝ => ((t : ℂ) - w).arg) atBot (𝓝 Real.pi) := by
  have h1 : ∀ᶠ t : ℝ in atBot,
      ((t : ℂ) - w).arg = Real.arcsin (w.im / ‖(t : ℂ) - w‖) + Real.pi := by
    filter_upwards [eventually_lt_atBot w.re] with t ht
    rw [Complex.arg_of_re_neg_of_im_nonneg
      (by simp only [Complex.sub_re, Complex.ofReal_re]; linarith)
      (by simp only [Complex.sub_im, Complex.ofReal_im, zero_sub]; linarith)]
    simp
  rw [tendsto_congr' h1]
  have h2 : Tendsto (fun t : ℝ => w.im / ‖(t : ℂ) - w‖) atBot (𝓝 0) :=
    (tendsto_norm_ofReal_sub_atTop tendsto_abs_atBot_atTop w).const_div_atTop _
  have h3 := (Real.continuous_arcsin.tendsto 0).comp h2
  simp only [Real.arcsin_zero, Function.comp_def] at h3
  simpa using h3.add_const Real.pi

/-- The logarithms of the two distances differ by `o(1)` at either end of the line: their ratio
tends to `1`. -/
private lemma tendsto_log_norm_sub_log_norm {l : Filter ℝ}
    (hl : Tendsto (fun t : ℝ => |t|) l atTop) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Tendsto (fun t : ℝ => Real.log ‖(t : ℂ) - z‖ - Real.log ‖(t : ℂ) - w‖) l (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => (w - z) / ((t : ℂ) - w)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_div]
    exact (tendsto_norm_ofReal_sub_atTop hl w).const_div_atTop _
  have heq : ∀ t : ℝ, ((t : ℂ) - z) / ((t : ℂ) - w) = 1 + (w - z) / ((t : ℂ) - w) := fun t => by
    field_simp [ofReal_sub_ne_zero hw t]
    ring
  have hratio : Tendsto (fun t : ℝ => ((t : ℂ) - z) / ((t : ℂ) - w)) l (𝓝 1) := by
    rw [tendsto_congr heq]
    simpa using tendsto_const_nhds.add h0
  have hnorm : Tendsto (fun t : ℝ => ‖(t : ℂ) - z‖ / ‖(t : ℂ) - w‖) l (𝓝 1) := by
    simpa [Function.comp_def, norm_div] using (continuous_norm.tendsto (1 : ℂ)).comp hratio
  have h4 := (Real.continuousAt_log one_ne_zero).tendsto.comp hnorm
  simp only [Real.log_one, Function.comp_def] at h4
  exact h4.congr fun t => Real.log_div (norm_ne_zero_iff.mpr (ofReal_sub_ne_zero hz t))
    (norm_ne_zero_iff.mpr (ofReal_sub_ne_zero hw t))

private lemma log_eq_log_norm_add_arg (x : ℂ) :
    Complex.log x = (Real.log ‖x‖ : ℂ) + (x.arg : ℂ) * I := Complex.ext rfl rfl

/-- The difference of the two logarithms is governed by the difference of the two arguments: the
moduli contribute nothing at either end of the line. -/
private lemma tendsto_log_sub_sub_log_sub {l : Filter ℝ} {c : ℝ}
    (hl : Tendsto (fun t : ℝ => |t|) l atTop) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (harg : Tendsto (fun t : ℝ => ((t : ℂ) - z).arg - ((t : ℂ) - w).arg) l (𝓝 c)) :
    Tendsto (fun t : ℝ => Complex.log ((t : ℂ) - z) - Complex.log ((t : ℂ) - w)) l
      (𝓝 ((c : ℂ) * I)) := by
  have h1 := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_log_norm_sub_log_norm hl hz hw)
  have h2 := ((Complex.continuous_ofReal.tendsto c).comp harg).mul_const I
  have h3 := h1.add h2
  simp only [Function.comp_def, Complex.ofReal_zero, zero_add] at h3
  refine h3.congr fun t => ?_
  rw [log_eq_log_norm_add_arg, log_eq_log_norm_add_arg]
  push_cast
  ring

/-- **The line integral of `((t - z)(t - w))⁻¹`** for a pole `z` above the real axis and a pole `w`
below it: it is `2πi` times the residue `(z - w)⁻¹` at the pole above the axis. The primitive
`(log (t - z) - log (t - w)) / (z - w)` never meets the branch cut, and the whole of the residue is
the jump `-2πi` of the difference of the arguments at the negative end of the line. -/
theorem integral_inv_ofReal_sub_mul_sub (hz : 0 < z.im) (hw : w.im < 0) :
    ∫ t : ℝ, (((t : ℂ) - z) * ((t : ℂ) - w))⁻¹ = 2 * (Real.pi : ℂ) * I / (z - w) := by
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hw' : w.im ≠ 0 := ne_of_lt hw
  have hzw : z - w ≠ 0 := by
    intro h
    have him : z.im - w.im = 0 := by rw [← Complex.sub_im, h]; simp
    linarith
  have hF : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (Complex.log ((s : ℂ) - z) - Complex.log ((s : ℂ) - w)) / (z - w))
      ((((t : ℂ) - z) * ((t : ℂ) - w))⁻¹) t := by
    intro t
    have hslit : ∀ v : ℂ, v.im ≠ 0 → (t : ℂ) - v ∈ Complex.slitPlane := by
      intro v hv
      rw [Complex.mem_slitPlane_iff]
      exact Or.inr (by simpa using hv)
    have e1 : HasDerivAt (fun u : ℂ => Complex.log (u - z)) (((t : ℂ) - z)⁻¹) (t : ℂ) := by
      exact HasDerivAt.comp_sub_const (t : ℂ) z (Complex.hasDerivAt_log (hslit z hz'))
    have e2 : HasDerivAt (fun u : ℂ => Complex.log (u - w)) (((t : ℂ) - w)⁻¹) (t : ℂ) := by
      exact HasDerivAt.comp_sub_const (t : ℂ) w (Complex.hasDerivAt_log (hslit w hw'))
    have alg : (((t : ℂ) - z)⁻¹ - ((t : ℂ) - w)⁻¹) / (z - w)
        = (((t : ℂ) - z) * ((t : ℂ) - w))⁻¹ := by
      have hA := ofReal_sub_ne_zero hz' t
      have hB := ofReal_sub_ne_zero hw' t
      field_simp
      ring
    rw [← alg]
    exact ((e1.sub e2).div_const (z - w)).comp_ofReal
  have htop : Tendsto
      (fun s : ℝ => (Complex.log ((s : ℂ) - z) - Complex.log ((s : ℂ) - w)) / (z - w)) atTop
      (𝓝 0) := by
    have harg : Tendsto (fun t : ℝ => ((t : ℂ) - z).arg - ((t : ℂ) - w).arg) atTop (𝓝 0) := by
      simpa using (tendsto_arg_ofReal_sub_atTop z).sub (tendsto_arg_ofReal_sub_atTop w)
    simpa using (tendsto_log_sub_sub_log_sub tendsto_abs_atTop_atTop hz' hw' harg).div_const (z - w)
  have hbot : Tendsto
      (fun s : ℝ => (Complex.log ((s : ℂ) - z) - Complex.log ((s : ℂ) - w)) / (z - w)) atBot
      (𝓝 (((-(2 * Real.pi) : ℝ) : ℂ) * I / (z - w))) := by
    have harg : Tendsto (fun t : ℝ => ((t : ℂ) - z).arg - ((t : ℂ) - w).arg) atBot
        (𝓝 (-(2 * Real.pi))) := by
      have h := (tendsto_arg_ofReal_sub_atBot_of_im_pos hz).sub
        (tendsto_arg_ofReal_sub_atBot_of_im_neg hw)
      have e : -Real.pi - Real.pi = -(2 * Real.pi) := by ring
      rwa [e] at h
    exact (tendsto_log_sub_sub_log_sub tendsto_abs_atBot_atTop hz' hw' harg).div_const (z - w)
  rw [integral_eq_of_hasDerivAt_of_tendsto (integrable_inv_ofReal_sub_mul_sub hz' hw') hF hbot htop]
  push_cast
  ring

end LineIntegral

/-! ### The residue integral -/

/-- **A residue integral.** For every `a` with `|im a| < 1`,
`∫ dt / ((1 + t²)(1 + (t + a)²)) = 2π / (4 + a²)`.

The denominator factors as `((t - i)(t + a + i)) ((t + a - i)(t + i))`, each bracket a quadratic
with one root above the real axis and one below, and the two brackets differ by the constant `2ia`.
-/
@[zz_tag "lem_residue_integral"]
theorem integral_inv_one_add_sq_mul_one_add_add_sq {a : ℂ} (ha : |a.im| < 1) :
    ∫ t : ℝ, ((1 + (t : ℂ) ^ 2) * (1 + ((t : ℂ) + a) ^ 2))⁻¹
      = 2 * (Real.pi : ℂ) / (4 + a ^ 2) := by
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  have hI : (0 : ℝ) < (I : ℂ).im := by simp
  have hnegI : (-I : ℂ).im < 0 := by simp
  have hlow : (-a - I).im < 0 := by
    simp only [Complex.sub_im, Complex.neg_im, Complex.I_im]
    linarith
  have hup : (0 : ℝ) < (I - a).im := by
    simp only [Complex.sub_im, Complex.I_im]
    linarith
  have hfac1 : ∀ t : ℝ, (1 : ℂ) + (t : ℂ) ^ 2 = ((t : ℂ) - I) * ((t : ℂ) - -I) := fun t => by
    linear_combination Complex.I_sq
  have hfac2 : ∀ t : ℝ, (1 : ℂ) + ((t : ℂ) + a) ^ 2
      = ((t : ℂ) - (-a - I)) * ((t : ℂ) - (I - a)) := fun t => by
    linear_combination Complex.I_sq
  by_cases ha0 : a = 0
  · subst ha0
    have hA : Integrable (fun t : ℝ => (2 : ℂ)⁻¹ * (((t : ℂ) - I) * ((t : ℂ) - -I))⁻¹) :=
      (integrable_inv_ofReal_sub_mul_sub (by simp) (by simp)).const_mul _
    have hB : Integrable (fun t : ℝ => (4 : ℂ)⁻¹ * (((t : ℂ) - I) ^ 2)⁻¹) :=
      (integrable_inv_ofReal_sub_sq (by simp)).const_mul _
    have hC : Integrable (fun t : ℝ => (4 : ℂ)⁻¹ * (((t : ℂ) - -I) ^ 2)⁻¹) :=
      (integrable_inv_ofReal_sub_sq (by simp)).const_mul _
    have hBC : Integrable (fun t : ℝ => (4 : ℂ)⁻¹ * (((t : ℂ) - I) ^ 2)⁻¹
        + (4 : ℂ)⁻¹ * (((t : ℂ) - -I) ^ 2)⁻¹) := hB.add hC
    have key : ∀ t : ℝ, ((1 + (t : ℂ) ^ 2) * (1 + ((t : ℂ) + 0) ^ 2))⁻¹
        = (2 : ℂ)⁻¹ * (((t : ℂ) - I) * ((t : ℂ) - -I))⁻¹
          - ((4 : ℂ)⁻¹ * (((t : ℂ) - I) ^ 2)⁻¹ + (4 : ℂ)⁻¹ * (((t : ℂ) - -I) ^ 2)⁻¹) := by
      intro t
      have h1 : (t : ℂ) - I ≠ 0 := ofReal_sub_ne_zero (by simp) t
      have h2 : (t : ℂ) - -I ≠ 0 := ofReal_sub_ne_zero (by simp) t
      rw [add_zero, hfac1 t]
      field_simp [Complex.I_sq]
      linear_combination 8 * Complex.I_sq
    simp only [key]
    rw [integral_sub hA hBC, integral_add hB hC, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_inv_ofReal_sub_mul_sub hI hnegI,
      integral_inv_ofReal_sub_sq (by simp), integral_inv_ofReal_sub_sq (by simp),
      show (I : ℂ) - -I = 2 * I by ring]
    field_simp
    ring
  · have hIa : (2 : ℂ) * I * a ≠ 0 := by
      simp [Complex.I_ne_zero, ha0]
    have hp : a + 2 * I ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.mul_im, Complex.re_ofNat, Complex.I_im,
        Complex.im_ofNat, Complex.I_re, Complex.zero_im] at him
      norm_num at him
      linarith
    have hm : 2 * I - a ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat, Complex.I_im,
        Complex.im_ofNat, Complex.I_re, Complex.zero_im] at him
      norm_num at him
      linarith
    have hprod : (a + 2 * I) * (2 * I - a) = -(4 + a ^ 2) := by
      linear_combination 4 * Complex.I_sq
    have h4z : (4 : ℂ) + a ^ 2 ≠ 0 := by
      intro h
      rw [h, neg_zero] at hprod
      exact mul_ne_zero hp hm hprod
    have key : ∀ t : ℝ, ((1 + (t : ℂ) ^ 2) * (1 + ((t : ℂ) + a) ^ 2))⁻¹
        = (2 * I * a)⁻¹ * ((((t : ℂ) - I) * ((t : ℂ) - (-a - I)))⁻¹
          - (((t : ℂ) - (I - a)) * ((t : ℂ) - -I))⁻¹) := by
      intro t
      have h1 : (t : ℂ) - I ≠ 0 := ofReal_sub_ne_zero (by simp) t
      have h2 : (t : ℂ) - -I ≠ 0 := ofReal_sub_ne_zero (by simp) t
      have h3 : (t : ℂ) - (-a - I) ≠ 0 := ofReal_sub_ne_zero (ne_of_lt hlow) t
      have h4 : (t : ℂ) - (I - a) ≠ 0 := ofReal_sub_ne_zero (ne_of_gt hup) t
      rw [hfac1 t, hfac2 t]
      field_simp
      ring
    simp only [key]
    rw [integral_const_mul, integral_sub
        (integrable_inv_ofReal_sub_mul_sub (by simp) (ne_of_lt hlow))
        (integrable_inv_ofReal_sub_mul_sub (ne_of_gt hup) (by simp)),
      integral_inv_ofReal_sub_mul_sub hI hlow, integral_inv_ofReal_sub_mul_sub hup hnegI,
      show I - (-a - I) = a + 2 * I by ring, show I - a - -I = 2 * I - a by ring,
      div_sub_div _ _ hp hm, hprod]
    field_simp
    ring

end ZetaZeros
