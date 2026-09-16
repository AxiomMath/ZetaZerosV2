/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationExplicit
import ZetaZeros.Unconditional.PairCorrelationSecondMoment

/-!
# Comparing the full and finite-window Lorentzian zero sums

The complex power in the explicit formula differs from the power used in the finite pair
function by a common unit-modulus phase.  This file records that exact algebra and identifies
the restriction of the full zero sum to the positive-ordinate window with the finite-window
Lorentzian sum.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex

/-- A summand of the full zero side of Montgomery's explicit formula. -/
noncomputable def fullZeroLorentzianSummand (x t : ℝ)
    (rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier) : ℂ :=
  (2 * Zeta23.zeroMult rho : ℂ) *
    (x : ℂ) ^ ((rho : ℂ) - 1 / 2 - Complex.I * t) /
      (1 - ((rho : ℂ) - 1 / 2 - Complex.I * t) ^ 2)

/-- Splitting off the imaginary translation in the complex power leaves the pair power. -/
theorem cpow_sub_I_mul_eq_phase_mul_pairPower
    (x : ℝ) (hx : 0 < x) (t : ℝ) (z : ℂ) :
    (x : ℂ) ^ (z - Complex.I * t) =
      (x : ℂ) ^ (-Complex.I * t) * pairPower x z := by
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [show z - Complex.I * t = -Complex.I * t + z by ring,
    Complex.cpow_add _ _ hxne]
  congr 1
  rw [pairPower, Complex.cpow_def_of_ne_zero hxne,
    ← Complex.ofReal_log (le_of_lt hx)]
  congr 1
  ring

/-- The phase introduced by translating Montgomery's kernel has norm one. -/
theorem norm_cpow_neg_I_mul (x : ℝ) (hx : 0 < x) (t : ℝ) :
    ‖(x : ℂ) ^ (-Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  norm_num [Complex.mul_re]

/-- The explicit-formula denominator is exactly the shifted Lorentzian denominator. -/
theorem one_sub_zero_shift_sq (rho : ℂ) (t : ℝ) :
    1 - (rho - 1 / 2 - Complex.I * t) ^ 2 =
      1 + ((t : ℂ) + Complex.I * (rho - 1 / 2)) ^ 2 := by
  ring_nf
  norm_num [Complex.I_mul_I]
  ring

/-- Pointwise, a full zero summand in the window is the common phase times the corresponding
finite-window summand. -/
theorem fullZeroLorentzianSummand_eq_phase_mul
    (x : ℝ) (hx : 0 < x) (t : ℝ)
    (rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier) :
    fullZeroLorentzianSummand x t rho =
      (x : ℂ) ^ (-Complex.I * t) *
        ((2 * Zeta23.zeroMult rho : ℂ) *
          pairPower x ((rho : ℂ) - 1 / 2) * zeroLorentzian rho t) := by
  rw [fullZeroLorentzianSummand, cpow_sub_I_mul_eq_phase_mul_pairPower x hx,
    one_sub_zero_shift_sq, zeroLorentzian]
  ring

/-- The embedding of a zero supplied with finite-window membership into the full zero carrier. -/
noncomputable def finiteZeroWindowEmbedding (T : ℝ) :
    {rho // rho ∈ finiteZeroWindow T} ↪
      (Zeta23.zetaZeros Zeta23.zetaSeam).carrier :=
    { toFun := fun rho =>
        ⟨rho.1, (mem_finiteZeroWindow.mp rho.2).1⟩
      inj' := fun rho sigma h => by
        apply Subtype.ext
        exact congrArg
          (fun z : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier => (z : ℂ)) h }

@[simp] theorem coe_finiteZeroWindowEmbedding (T : ℝ)
    (rho : {rho // rho ∈ finiteZeroWindow T}) :
    ((finiteZeroWindowEmbedding T rho :
        (Zeta23.zetaZeros Zeta23.zetaSeam).carrier) : ℂ) = (rho : ℂ) := by
  rfl

/-- The positive-ordinate finite window, regarded as a finite subset of the full zero carrier. -/
noncomputable def finiteZeroCarrierWindow (T : ℝ) :
    Finset (Zeta23.zetaZeros Zeta23.zetaSeam).carrier :=
  (finiteZeroWindow T).attach.map (finiteZeroWindowEmbedding T)

@[simp] theorem mem_finiteZeroCarrierWindow {T : ℝ}
    {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier} :
    rho ∈ finiteZeroCarrierWindow T ↔ (rho : ℂ) ∈ finiteZeroWindow T := by
  classical
  constructor
  · intro hrho
    simp only [finiteZeroCarrierWindow, Finset.mem_map] at hrho
    rcases hrho with ⟨sigma, hsigma, hσρ⟩
    have hval : (sigma : ℂ) = (rho : ℂ) :=
      congrArg
        (fun z : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier => (z : ℂ)) hσρ
    rw [← hval]
    exact sigma.2
  · intro hrho
    simp only [finiteZeroCarrierWindow, Finset.mem_map]
    refine ⟨⟨(rho : ℂ), hrho⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext (by rfl)

/-- Restricting the full explicit-formula zero sum to the positive-ordinate window leaves only
the common unit phase multiplying the finite-window Lorentzian sum. -/
theorem fullZeroLorentzianSummand_sum_window
    (x : ℝ) (hx : 0 < x) (T t : ℝ) :
    (∑ rho ∈ finiteZeroCarrierWindow T,
        fullZeroLorentzianSummand x t rho) =
      (x : ℂ) ^ (-Complex.I * t) * finiteWindowLorentzianSum x T t := by
  classical
  rw [finiteZeroCarrierWindow, Finset.sum_map]
  simp only [fullZeroLorentzianSummand_eq_phase_mul x hx,
    coe_finiteZeroWindowEmbedding]
  let f : ℂ → ℂ := fun rho =>
    (x : ℂ) ^ (-Complex.I * t) *
      ((2 * Zeta23.zeroMult rho : ℂ) * pairPower x (rho - 1 / 2) *
        zeroLorentzian rho t)
  change (∑ rho ∈ (finiteZeroWindow T).attach, f rho) = _
  rw [Finset.sum_attach]
  simp only [f, finiteWindowLorentzianSum, Finset.mul_sum]

/-- The finite-window restriction of the full sum has the same norm as the phase-free
finite-window Lorentzian sum. -/
theorem norm_fullZeroLorentzianSummand_sum_window
    (x : ℝ) (hx : 0 < x) (T t : ℝ) :
    ‖∑ rho ∈ finiteZeroCarrierWindow T,
        fullZeroLorentzianSummand x t rho‖ =
      ‖finiteWindowLorentzianSum x T t‖ := by
  rw [fullZeroLorentzianSummand_sum_window x hx, norm_mul,
    norm_cpow_neg_I_mul x hx, one_mul]

/-- The full zero series is the finite positive-ordinate window plus its complementary tail.
The finite term is written in the phase-free normalization used by the second-moment identity. -/
theorem fullZeroLorentzianSummand_window_add_compl
    (x : ℝ) (hx : 1 ≤ x) (T t : ℝ) :
    (x : ℂ) ^ (-Complex.I * t) * finiteWindowLorentzianSum x T t +
        (∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
            rho ∉ finiteZeroCarrierWindow T},
          fullZeroLorentzianSummand x t rho) =
      ∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        fullZeroLorentzianSummand x t rho := by
  have hsummable : Summable (fullZeroLorentzianSummand x t) := by
    apply (zeroLorentzianSummand_summable x hx t).congr
    intro rho
    rw [fullZeroLorentzianSummand]
  rw [← fullZeroLorentzianSummand_sum_window x (zero_lt_one.trans_le hx) T t]
  exact hsummable.sum_add_tsum_subtype_compl (finiteZeroCarrierWindow T)

/-- The error between the phased finite-window sum and the full zero series is exactly the
negative complementary tail. -/
theorem phase_mul_finiteWindowLorentzianSum_sub_full_tsum
    (x : ℝ) (hx : 1 ≤ x) (T t : ℝ) :
    (x : ℂ) ^ (-Complex.I * t) * finiteWindowLorentzianSum x T t -
        (∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
          fullZeroLorentzianSummand x t rho) =
      -(∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
          rho ∉ finiteZeroCarrierWindow T},
        fullZeroLorentzianSummand x t rho) := by
  have hsplit := fullZeroLorentzianSummand_window_add_compl x hx T t
  linear_combination hsplit

end ZetaZeros.Unconditional.PairCorrelationProof
