/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationEstimate
import ZetaZeros.Unconditional.PairCorrelationFourier
import Zeta23.RvM.Halving

/-!
# The Lorentzian second moment for a finite zero window

This file records the exact finite identity underlying Montgomery's pair-function argument.
The conjugated zero factor is reindexed by the critical-line reflection
`rho |-> 1 - conj rho`; this is why the identity is unconditional rather than an RH-only
calculation.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set

/-- The finite set of nontrivial zeros with ordinate in `(0, T]`. -/
noncomputable def finiteZeroWindow (T : ℝ) : Finset ℂ :=
  (Zeta23.zerosIn_finite 0 T).toFinset

@[simp] theorem mem_finiteZeroWindow {T : ℝ} {rho : ℂ} :
    rho ∈ finiteZeroWindow T ↔ rho ∈ Zeta23.zerosIn 0 T := by
  simp [finiteZeroWindow]

/-- Critical-line reflection preserves the finite positive-ordinate window. -/
theorem reflect_mem_finiteZeroWindow {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ finiteZeroWindow T) :
    Zeta23.reflect rho ∈ finiteZeroWindow T := by
  rw [mem_finiteZeroWindow] at hrho ⊢
  rcases hrho with ⟨hzero, him_lower, him_upper⟩
  exact ⟨Zeta23.zetaSeam.reflect_zero rho hzero,
    by simpa using him_lower, by simpa using him_upper⟩

theorem image_reflect_finiteZeroWindow (T : ℝ) :
    (finiteZeroWindow T).image Zeta23.reflect = finiteZeroWindow T := by
  classical
  ext rho
  constructor
  · simp only [Finset.mem_image]
    rintro ⟨sigma, hsigma, rfl⟩
    exact reflect_mem_finiteZeroWindow hsigma
  · intro hrho
    simp only [Finset.mem_image]
    exact ⟨Zeta23.reflect rho, reflect_mem_finiteZeroWindow hrho,
      Zeta23.reflect_reflect rho⟩

theorem sum_comp_reflect_finiteZeroWindow (T : ℝ) (f : ℂ → ℂ) :
    ∑ rho ∈ finiteZeroWindow T, f (Zeta23.reflect rho) =
      ∑ rho ∈ finiteZeroWindow T, f rho := by
  classical
  rw [← Finset.sum_image]
  · rw [image_reflect_finiteZeroWindow]
  · exact fun _ _ _ _ h => Zeta23.reflect_injective h

/-- The unit-Lorentzian factor centered at the (possibly complex) ordinate of `rho`. -/
noncomputable def zeroLorentzian (rho : ℂ) (t : ℝ) : ℂ :=
  1 / (1 + ((t : ℂ) + Complex.I * (rho - 1 / 2)) ^ 2)

/-- The finite-window zero sum occurring on the zero side of Montgomery's explicit formula.
The harmless common phase `x ^ (-it)` has been omitted, since it has norm one. -/
noncomputable def finiteWindowLorentzianSum (x T t : ℝ) : ℂ :=
  ∑ rho ∈ finiteZeroWindow T,
    (2 * Zeta23.zeroMult rho : ℂ) * pairPower x (rho - 1 / 2) *
      zeroLorentzian rho t

@[simp] theorem zeroLorentzian_reflect_conj (rho : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (zeroLorentzian (Zeta23.reflect rho) t) =
      zeroLorentzian rho t := by
  simp only [zeroLorentzian, Zeta23.reflect, map_div₀, map_one, map_add, map_pow,
    Complex.conj_ofReal, map_mul, Complex.conj_I, map_sub, map_ofNat,
    Complex.conj_conj]
  congr 4
  ring

theorem pairPower_reflect_conj (x : ℝ) (rho : ℂ) :
    (starRingEnd ℂ) (pairPower x (Zeta23.reflect rho - 1 / 2)) =
      pairPower x (-(rho - 1 / 2)) := by
  simp only [pairPower, Zeta23.reflect, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, map_sub, map_one, map_div₀, map_ofNat, Complex.conj_conj]
  congr 1
  ring

/-- The complex shift attached to a zero in the critical strip stays between the two
Lorentzian poles. -/
theorem zero_shift_im_abs_lt_one {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ finiteZeroWindow T) :
    |(Complex.I * (rho - 1 / 2)).im| < 1 := by
  rw [mem_finiteZeroWindow] at hrho
  rcases hrho.1 with ⟨_, hre_lower, hre_upper⟩
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re,
    Complex.one_re, Complex.div_re]
  norm_num
  rw [abs_lt]
  constructor <;> linarith

/-- Every Lorentzian belonging to the finite zero window is integrable. -/
theorem zeroLorentzian_integrable {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ finiteZeroWindow T) :
    Integrable (zeroLorentzian rho) := by
  change Integrable (fun t : ℝ ↦
    1 / (1 + ((t : ℂ) + Complex.I * (rho - 1 / 2)) ^ 2))
  exact shiftedLorentzian_integrable (Complex.I * (rho - 1 / 2))
    (zero_shift_im_abs_lt_one hrho)

/-- A window Lorentzian is uniformly bounded on the real axis. -/
theorem zeroLorentzian_norm_le {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ finiteZeroWindow T) (t : ℝ) :
    ‖zeroLorentzian rho t‖ ≤ (4 / 3 : ℝ) := by
  rw [mem_finiteZeroWindow] at hrho
  rcases hrho.1 with ⟨_, hre_lower, hre_upper⟩
  let u : ℝ := t - rho.im
  let delta : ℝ := rho.re - 1 / 2
  have hdelta : |delta| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    dsimp [delta]
    constructor <;> linarith
  have hshift :
      ((t : ℂ) + Complex.I * (rho - 1 / 2)) =
        (u : ℂ) + Complex.I * (delta : ℂ) := by
    apply Complex.ext
    all_goals
      simp only [u, delta, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, Complex.div_re, Complex.ofReal_re,
        Complex.ofReal_im]
    all_goals norm_num
    all_goals ring
  have hlower : (3 / 4 : ℝ) ≤
      ‖(1 : ℂ) + ((t : ℂ) + Complex.I * (rho - 1 / 2)) ^ 2‖ := by
    rw [hshift]
    have h := shiftedLorentzian_norm_lower u delta hdelta
    nlinarith [sq_nonneg u]
  have hpos : 0 <
      ‖(1 : ℂ) + ((t : ℂ) + Complex.I * (rho - 1 / 2)) ^ 2‖ :=
    lt_of_lt_of_le (by norm_num) hlower
  simp only [zeroLorentzian, norm_div, norm_one]
  rw [one_div]
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith

/-- The product of two window Lorentzians is integrable. -/
theorem zeroLorentzian_mul_integrable {T : ℝ} {rho rho' : ℂ}
    (hrho : rho ∈ finiteZeroWindow T) (hrho' : rho' ∈ finiteZeroWindow T) :
    Integrable (fun t : ℝ ↦ zeroLorentzian rho t * zeroLorentzian rho' t) := by
  exact (zeroLorentzian_integrable hrho).mul_bdd (c := 4 / 3)
    (zeroLorentzian_integrable hrho').aestronglyMeasurable
    (Filter.Eventually.of_forall (zeroLorentzian_norm_le hrho'))

/-- Conjugating the finite zero sum and reindexing by critical-line reflection removes all
conjugates from the Lorentzian factors. -/
theorem finiteWindowLorentzianSum_conj (x T t : ℝ) :
    (starRingEnd ℂ) (finiteWindowLorentzianSum x T t) =
      ∑ rho ∈ finiteZeroWindow T,
        (2 * Zeta23.zeroMult rho : ℂ) * pairPower x (-(rho - 1 / 2)) *
          zeroLorentzian rho t := by
  classical
  unfold finiteWindowLorentzianSum
  rw [map_sum]
  rw [← sum_comp_reflect_finiteZeroWindow T (fun rho ↦
    (starRingEnd ℂ) ((2 * Zeta23.zeroMult rho : ℂ) *
      pairPower x (rho - 1 / 2) * zeroLorentzian rho t))]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hzero : Zeta23.IsNontrivialZero rho :=
    (mem_finiteZeroWindow.mp hrho).1
  rw [map_mul, map_mul, map_mul, pairPower_reflect_conj, zeroLorentzian_reflect_conj,
    Zeta23.zetaSeam.mult_reflect rho hzero, map_ofNat, map_natCast]

/-- Pair powers turn subtraction of spectral parameters into multiplication. -/
theorem pairPower_mul_neg (x : ℝ) (rho rho' : ℂ) :
    pairPower x (rho - 1 / 2) * pairPower x (-(rho' - 1 / 2)) =
      pairPower x (rho - rho') := by
  simp only [pairPower, ← Complex.exp_add]
  congr 1
  ring

/-- The elementary Lorentzian convolution specialized to two zeros in the finite window. -/
theorem integral_zeroLorentzian_mul {T : ℝ} {rho rho' : ℂ}
    (hrho : rho ∈ finiteZeroWindow T) (hrho' : rho' ∈ finiteZeroWindow T) :
    (∫ t : ℝ, zeroLorentzian rho t * zeroLorentzian rho' t) =
      2 * Real.pi / (4 - (rho - rho') ^ 2) := by
  let a : ℂ := Complex.I * (rho - 1 / 2)
  let b : ℂ := Complex.I * (rho' - 1 / 2)
  calc
    (∫ t : ℝ, zeroLorentzian rho t * zeroLorentzian rho' t) =
        ∫ t : ℝ, 1 / ((1 + ((t : ℂ) + a) ^ 2) *
          (1 + ((t : ℂ) + b) ^ 2)) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [zeroLorentzian, a, b, one_div, mul_inv_rev]
      ring
    _ = 2 * Real.pi / (4 + (a - b) ^ 2) :=
      shiftedLorentzian_convolution a b
        (by simpa only [a] using zero_shift_im_abs_lt_one hrho)
        (by simpa only [b] using zero_shift_im_abs_lt_one hrho')
    _ = 2 * Real.pi / (4 - (rho - rho') ^ 2) := by
      congr 2
      dsimp [a, b]
      rw [show Complex.I * (rho - 1 / 2) - Complex.I * (rho' - 1 / 2) =
        Complex.I * (rho - rho') by ring, mul_pow, Complex.I_sq]
      ring

/-- Pointwise expansion of the squared finite-window zero sum. -/
theorem finiteWindowLorentzianSum_mul_conj (x T t : ℝ) :
    finiteWindowLorentzianSum x T t *
        (starRingEnd ℂ) (finiteWindowLorentzianSum x T t) =
      ∑ rho ∈ finiteZeroWindow T, ∑ rho' ∈ finiteZeroWindow T,
        ((4 : ℂ) * ((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ) *
          pairPower x (rho - rho')) *
            (zeroLorentzian rho t * zeroLorentzian rho' t) := by
  classical
  rw [finiteWindowLorentzianSum_conj, finiteWindowLorentzianSum,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  apply Finset.sum_congr rfl
  intro rho' hrho'
  rw [← pairPower_mul_neg x rho rho']
  push_cast
  ring

/-- Exact finite-window second-moment identity.  Critical-line reflection, rather than the
Riemann hypothesis, is what turns the conjugated zero into the second ordered zero. -/
theorem finiteWindowLorentzianSum_secondMoment (x T : ℝ) :
    (∫ t : ℝ, finiteWindowLorentzianSum x T t *
      (starRingEnd ℂ) (finiteWindowLorentzianSum x T t)) =
        2 * Real.pi * finitePairFunction x T := by
  classical
  let coefficient : ℂ → ℂ → ℂ := fun rho rho' ↦
    (4 : ℂ) * ((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ) *
      pairPower x (rho - rho')
  have hterm (rho rho' : ℂ) (hrho : rho ∈ finiteZeroWindow T)
      (hrho' : rho' ∈ finiteZeroWindow T) :
      Integrable (fun t : ℝ ↦ coefficient rho rho' *
        (zeroLorentzian rho t * zeroLorentzian rho' t)) := by
    simpa only [smul_eq_mul] using
      (zeroLorentzian_mul_integrable hrho hrho').const_mul (coefficient rho rho')
  calc
    (∫ t : ℝ, finiteWindowLorentzianSum x T t *
        (starRingEnd ℂ) (finiteWindowLorentzianSum x T t)) =
        ∫ t : ℝ, ∑ rho ∈ finiteZeroWindow T, ∑ rho' ∈ finiteZeroWindow T,
          coefficient rho rho' *
            (zeroLorentzian rho t * zeroLorentzian rho' t) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [finiteWindowLorentzianSum_mul_conj]
    _ = ∑ rho ∈ finiteZeroWindow T, ∑ rho' ∈ finiteZeroWindow T,
          coefficient rho rho' *
            (∫ t : ℝ, zeroLorentzian rho t * zeroLorentzian rho' t) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro rho hrho
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro rho' hrho'
          rw [integral_const_mul]
        · intro rho' hrho'
          exact hterm rho rho' hrho hrho'
      · intro rho hrho
        apply integrable_finsetSum
        intro rho' hrho'
        exact hterm rho rho' hrho hrho'
    _ = ∑ rho ∈ finiteZeroWindow T, ∑ rho' ∈ finiteZeroWindow T,
          coefficient rho rho' * (2 * Real.pi / (4 - (rho - rho') ^ 2)) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      apply Finset.sum_congr rfl
      intro rho' hrho'
      rw [integral_zeroLorentzian_mul hrho hrho']
    _ = 2 * Real.pi * finitePairFunction x T := by
      rw [finitePairFunction_eq_finset_sum]
      simp only [finiteZeroWindow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      apply Finset.sum_congr rfl
      intro rho' hrho'
      dsimp only [coefficient, finitePairKernel]
      ring

/-- The squared finite-window zero sum is integrable. -/
theorem finiteWindowLorentzianSum_mul_conj_integrable (x T : ℝ) :
    Integrable (fun t : ℝ ↦ finiteWindowLorentzianSum x T t *
      (starRingEnd ℂ) (finiteWindowLorentzianSum x T t)) := by
  classical
  rw [show (fun t : ℝ ↦ finiteWindowLorentzianSum x T t *
      (starRingEnd ℂ) (finiteWindowLorentzianSum x T t)) =
      fun t : ℝ ↦ ∑ rho ∈ finiteZeroWindow T, ∑ rho' ∈ finiteZeroWindow T,
        ((4 : ℂ) * ((Zeta23.zeroMult rho * Zeta23.zeroMult rho' : ℕ) : ℂ) *
          pairPower x (rho - rho')) *
            (zeroLorentzian rho t * zeroLorentzian rho' t) by
    funext t
    exact finiteWindowLorentzianSum_mul_conj x T t]
  apply integrable_finsetSum
  intro rho hrho
  apply integrable_finsetSum
  intro rho' hrho'
  exact (zeroLorentzian_mul_integrable hrho hrho').const_mul _

/-- The exact second moment written as an integral of the real squared norm. -/
theorem finiteWindowLorentzianSum_norm_sq_secondMoment (x T : ℝ) :
    (((∫ t : ℝ, ‖finiteWindowLorentzianSum x T t‖ ^ 2) : ℝ) : ℂ) =
      2 * Real.pi * finitePairFunction x T := by
  rw [← finiteWindowLorentzianSum_secondMoment]
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Stability of a squared complex norm under an additive perturbation. -/
theorem norm_mul_conj_sub_mul_conj_le (z w : ℂ) :
    ‖z * (starRingEnd ℂ) z - w * (starRingEnd ℂ) w‖ ≤
      ‖z - w‖ * (‖z‖ + ‖w‖) := by
  rw [show z * (starRingEnd ℂ) z - w * (starRingEnd ℂ) w =
      (z - w) * (starRingEnd ℂ) z +
        w * (starRingEnd ℂ) (z - w) by
    rw [map_sub]
    ring]
  calc
    ‖(z - w) * (starRingEnd ℂ) z + w * (starRingEnd ℂ) (z - w)‖ ≤
        ‖(z - w) * (starRingEnd ℂ) z‖ +
          ‖w * (starRingEnd ℂ) (z - w)‖ := norm_add_le _ _
    _ = ‖z - w‖ * (‖z‖ + ‖w‖) := by
      simp only [norm_mul, Complex.norm_conj]
      ring

/-- Quantitative transfer from a model for the zero-side function to Montgomery's finite
pair function.  The two error terms respectively measure the model's second moment and the
pointwise comparison with the finite zero sum. -/
theorem finitePairFunction_normalized_sub_model_norm_le_of_comparison
    (x T : ℝ) (N M : ℂ) (g : ℝ → ℂ) (B : ℝ → ℝ)
    (E_main E_error : ℝ)
    (hN : N ≠ 0)
    (hg2 : Integrable (fun t ↦ g t * (starRingEnd ℂ) (g t)))
    (hB : Integrable B)
    (hcompare : ∀ t,
      ‖finiteWindowLorentzianSum x T t - g t‖ *
        (‖finiteWindowLorentzianSum x T t‖ + ‖g t‖) ≤ B t)
    (hmain :
      ‖(∫ t, g t * (starRingEnd ℂ) (g t)) -
        ((2 * Real.pi : ℝ) : ℂ) * N * M‖ ≤
          2 * Real.pi * ‖N‖ * E_main)
    (hBint :
      ∫ t, B t ≤ 2 * Real.pi * ‖N‖ * E_error) :
    ‖finitePairFunction x T / N - M‖ ≤ E_main + E_error := by
  let S : ℝ → ℂ := finiteWindowLorentzianSum x T
  let I : ℂ := ∫ t, S t * (starRingEnd ℂ) (S t)
  let J : ℂ := ∫ t, g t * (starRingEnd ℂ) (g t)
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ)
  have hS2 : Integrable (fun t ↦ S t * (starRingEnd ℂ) (S t)) :=
    finiteWindowLorentzianSum_mul_conj_integrable x T
  have hpoint (t : ℝ) :
      ‖S t * (starRingEnd ℂ) (S t) -
          g t * (starRingEnd ℂ) (g t)‖ ≤ B t :=
    (norm_mul_conj_sub_mul_conj_le (S t) (g t)).trans (hcompare t)
  have hcomparison : ‖I - J‖ ≤ ∫ t, B t := by
    change ‖(∫ t, S t * (starRingEnd ℂ) (S t)) -
      ∫ t, g t * (starRingEnd ℂ) (g t)‖ ≤ ∫ t, B t
    rw [← integral_sub hS2 hg2]
    exact norm_integral_le_of_norm_le hB
      (Filter.Eventually.of_forall hpoint)
  have hcpos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hNnorm : 0 < ‖N‖ := norm_pos_iff.mpr hN
  have hdenpos : 0 < 2 * Real.pi * ‖N‖ := mul_pos hcpos hNnorm
  have hcNnorm : ‖c * N‖ = 2 * Real.pi * ‖N‖ := by
    norm_num [c, norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have htotal : ‖I - c * N * M‖ ≤
      2 * Real.pi * ‖N‖ * (E_main + E_error) := by
    calc
      ‖I - c * N * M‖ = ‖(J - c * N * M) + (I - J)‖ := by
        congr 1
        ring
      _ ≤ ‖J - c * N * M‖ + ‖I - J‖ := norm_add_le _ _
      _ ≤ 2 * Real.pi * ‖N‖ * E_main + ∫ t, B t :=
        add_le_add hmain hcomparison
      _ ≤ 2 * Real.pi * ‖N‖ * E_main +
          2 * Real.pi * ‖N‖ * E_error := add_le_add (le_refl _) hBint
      _ = 2 * Real.pi * ‖N‖ * (E_main + E_error) := by ring
  have hidentity : finitePairFunction x T / N - M =
      (I - c * N * M) / (c * N) := by
    have hcne : c ≠ 0 := by
      change (((2 * Real.pi : ℝ) : ℂ) ≠ 0)
      exact_mod_cast ne_of_gt hcpos
    dsimp only [I, S, c]
    rw [finiteWindowLorentzianSum_secondMoment]
    field_simp [hcne, hN]
    push_cast
    ring
  rw [hidentity, norm_div, hcNnorm]
  apply (div_le_iff₀ hdenpos).2
  calc
    ‖I - c * N * M‖ ≤
        2 * Real.pi * ‖N‖ * (E_main + E_error) := htotal
    _ = (E_main + E_error) * (2 * Real.pi * ‖N‖) := by ring

end ZetaZeros.Unconditional.PairCorrelationProof
