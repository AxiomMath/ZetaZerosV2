/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationBasic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Montgomery's finite pair function

This file fixes a challenge-independent normalization of the finite pair sum from
`blueprint/unconditional.tex`, `def_F_pair`.  In particular, `pairPower x z` means
`exp (z * log x)`, including when `z` is not real.  The elementary lemmas below are the exact
rewrites needed to pass between the Fourier-transform normalization in the challenge and the
pair-function normalization in the analytic estimate.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Set

/-- The complex power convention `x ^ z = exp (z log x)` used in the pair-correlation
blueprint. -/
noncomputable def pairPower (x : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * (Real.log x : ℂ))

/-- The weight in Montgomery's finite pair function. -/
noncomputable def finitePairKernel (z : ℂ) : ℂ :=
  4 / (4 - z ^ 2)

/-- Montgomery's finite pair function, with both zeros in the ordinate window `(0, T]` and
with analytic multiplicities. -/
noncomputable def finitePairFunction (x T : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ Zeta23.zerosIn 0 T, ∑ᶠ ρ' ∈ Zeta23.zerosIn 0 T,
    ((Zeta23.zeroMult ρ * Zeta23.zeroMult ρ' : ℕ) : ℂ) *
      pairPower x (ρ - ρ') * finitePairKernel (ρ - ρ')

/-- The `finsum` definition of `finitePairFunction` is an ordinary double finite sum. -/
theorem finitePairFunction_eq_finset_sum (x T : ℝ) :
    finitePairFunction x T =
      ∑ ρ ∈ (Zeta23.zerosIn_finite 0 T).toFinset,
        ∑ ρ' ∈ (Zeta23.zerosIn_finite 0 T).toFinset,
          ((Zeta23.zeroMult ρ * Zeta23.zeroMult ρ' : ℕ) : ℂ) *
            pairPower x (ρ - ρ') * finitePairKernel (ρ - ρ') := by
  exact nested_finsum_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite 0 T)

/-- Real powers in the frequency parameter use exactly the exponential convention of
`pairPower`. -/
theorem pairPower_rpow (T a : ℝ) (z : ℂ) (hT : 0 < T) :
    pairPower (T ^ a) z =
      Complex.exp ((a : ℂ) * z * (Real.log T : ℂ)) := by
  rw [pairPower, Real.log_rpow hT]
  push_cast
  congr 1
  ring

/-- The pair power at `T ^ a` depends continuously on the real frequency `a`. -/
theorem continuous_pairPower_rpow (T : ℝ) (z : ℂ) (hT : 0 < T) :
    Continuous (fun a : ℝ => pairPower (T ^ a) z) := by
  have heq :
      (fun a : ℝ => pairPower (T ^ a) z) =
        fun a : ℝ => Complex.exp ((a : ℂ) * z * (Real.log T : ℂ)) := by
    funext a
    exact pairPower_rpow T a z hT
  rw [heq]
  fun_prop

/-- Multiplication by the pair power preserves integrability for a test function supported on
`[-1, 1]`. -/
theorem integrable_mul_pairPower_rpow (f : ℝ → ℝ) (hf : Integrable f)
    (hsupp : ∀ a : ℝ, 1 < |a| → f a = 0) (T : ℝ) (hT : 0 < T) (z : ℂ) :
    Integrable (fun a : ℝ => (f a : ℂ) * pairPower (T ^ a) z) := by
  have hlocal : IntegrableOn
      (fun a : ℝ => (f a : ℂ) * pairPower (T ^ a) z) (Icc (-1) 1) :=
    hf.ofReal.integrableOn.mul_continuousOn
      (continuous_pairPower_rpow T z hT).continuousOn isCompact_Icc
  refine hlocal.integrable_of_forall_notMem_eq_zero ?_
  intro a ha
  simp only [mem_Icc, not_and_or, not_le] at ha
  have habs : 1 < |a| := by
    rcases ha with ha | ha
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      exact ha
  rw [hsupp a habs]
  norm_num

/-- The exponential in the challenge's `fourierC` at a rescaled zero difference is precisely
the pair power at `x = T ^ a`. -/
theorem fourierExponent_rescaled_eq_pairPower (T a : ℝ) (z : ℂ) (hT : 0 < T) :
    Complex.exp
        (-(2 * (Real.pi : ℂ)) * Complex.I *
          (Complex.I * z * ((Real.log T / (2 * Real.pi) : ℝ) : ℂ)) * (a : ℂ)) =
      pairPower (T ^ a) z := by
  rw [pairPower, Real.log_rpow hT]
  congr 1
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]
  rw [Complex.I_sq]
  ring

/-- Integral form of `fourierExponent_rescaled_eq_pairPower`.  This is the exact bridge from
the Fourier transform in the challenge to one summand of `finitePairFunction`. -/
theorem fourierIntegral_rescaled_eq_pairPower (f : ℝ → ℝ) (T : ℝ) (z : ℂ) (hT : 0 < T) :
    (∫ a : ℝ, (f a : ℂ) *
        Complex.exp
          (-(2 * (Real.pi : ℂ)) * Complex.I *
            (Complex.I * z * ((Real.log T / (2 * Real.pi) : ℝ) : ℂ)) * (a : ℂ))) =
      ∫ a : ℝ, (f a : ℂ) * pairPower (T ^ a) z := by
  apply integral_congr_ae
  filter_upwards [] with a
  rw [fourierExponent_rescaled_eq_pairPower T a z hT]

/-- The finite pair kernel is even. -/
@[simp] theorem finitePairKernel_neg (z : ℂ) :
    finitePairKernel (-z) = finitePairKernel z := by
  simp only [finitePairKernel]
  ring_nf

end ZetaZeros.Unconditional.PairCorrelationProof
