/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ExplicitFormula.lean  —  the explicit formula, normalisations (paper App. A [app:EF]).

The *normalisation chain*: the passage from a literature-verbatim explicit formula to the paper's
density ν_X = μ + Π_X + P_X [eq:mudef]–[eq:nudef], with every 2π and every sign:

  * `EF.literatureRHS` / `EF_lit` : the right-hand side of [eq:EFstd] (App. A, first display), i.e. the
    Weil explicit formula in the form the paper quotes from [IK04, Thm 5.12] / [Wei52] / [Bom00],
    for a single test function k ∈ C_c²(ℝ) with h(z) := ∫ k(u) e^{izu} du;

The paper-specific density assembly is omitted from this pruned copy; only the literature
form and Fourier/analytic helpers needed by the unconditional proof are retained.

The truth of [eq:EFstd] itself (contour integration of
h((s-1/2)/i)·ξ'/ξ(s)) is the hypothesis `EF_lit`, stated for the zero configuration
abstractly. It is proved for the actual zeta zeros in the retained WeilEF development.

CONVENTIONS (paper [Notation]).  Paper Fourier transform:
    f̂(τ) = h_f(τ) := ∫_ℝ f(u) e^{iτu} du,   inversion  f(u) = (1/2π) ∫_ℝ h_f(r) e^{-iru} dr.
Mathlib: 𝓕 f w = ∫ v, exp(-2πi v w) • f v.  Dictionary (proved below, `paperFT_ofReal_eq_fourier`):
    h_f(τ) = 𝓕 f (-τ/(2π)).
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Zeta23.Defs

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23
namespace EF

/-! ## The literature form [eq:EFstd] -/

/-- The Gamma-factor bracket in [eq:EFstd]: `Re Γ'/Γ(1/4 + ir/2) − log π`
( = Γ_ℝ'/Γ_ℝ(1/2+ir) + Γ_ℝ'/Γ_ℝ(1/2−ir), Γ_ℝ(s) = π^{-s/2}Γ(s/2); equals 2π μ(r) by [eq:mudef]).
Γ'/Γ is spelled `Complex.digamma` (= logDeriv Gamma), identically to `Zeta23.mu` in Defs.lean. -/
def gammaBracket (r : ℝ) : ℝ := (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log π

/-- Right-hand side of [eq:EFstd] (App. A, first display), VERBATIM:
`h(i/2) + h(−i/2) − Σ_{n≥1} Λ(n) n^{-1/2} (k(log n) + k(−log n)) + (1/2π) ∫_ℝ h(r) [Re Γ'/Γ(1/4 + ir/2) − log π] dr`
with `h := paperFT k`.  The n-sum is written over all `n : ℕ` (Λ(0) = Λ(1) = 0); for compactly supported k it
has finite support. -/
def literatureRHS (k : ℝ → ℂ) : ℂ :=
  paperFT k (I / 2) + paperFT k (-I / 2)
  - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (k (Real.log n) + k (-Real.log n))
  + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (gammaBracket r : ℂ)

/-- **H-EF, literature form** ([eq:EFstd]; [IK04, Thm 5.12] specialised to ζ / [Wei52] / [Bom00]):
for every `k ∈ C_c²(ℝ)` with `h(z) := ∫ k(u)e^{izu}du`,
`Σ_ρ m_ρ h(γ_ρ) = literatureRHS k`, the zero sum converging absolutely (paper: "here absolutely
convergent since h(r) ≪_k (1+|r|)^{-2} on |Im r| ≤ 1/2").  It is a hypothesis
interface for the explicit formula, never a Lean axiom. -/
def EF_lit (Z : ZeroConfig) : Prop :=
  ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k →
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) ∧
    ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) = literatureRHS k

/-! ## ℂ-specialised integral helpers

(In this toolchain `rw [← integral_const_mul]` fails to key-match on ℂ-valued integrals because the
RCLike-generic lemma elaborates `Mul ℂ`/`NormedAddCommGroup ℂ` through a different instance path than
a goal written with `*`; restating the lemmas at ℂ (proved by `exact`) makes `rw` usable.) -/

theorem cintegral_const_mul (c : ℂ) (f : ℝ → ℂ) : ∫ x, c * f x = c * ∫ x, f x :=
  integral_const_mul c f

/-! ## Dictionary with Mathlib's Fourier transform -/

/-- `h_k(τ) = 𝓕 k (−τ/(2π))` for real τ. -/
theorem paperFT_ofReal_eq_fourier (k : ℝ → ℂ) (τ : ℝ) :
    paperFT k τ = 𝓕 k (-τ / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold paperFT
  congr 1; ext u
  rw [smul_eq_mul, mul_comm (k u)]
  congr 1
  have : (-2 * π * u * (-τ / (2 * π))) = τ * u := by
    field_simp
  rw [this]
  push_cast
  ring_nf

/-- `h_k` is integrable on the real line when `𝓕 k` is (dictionary + linear substitution). -/
theorem integrable_paperFT_ofReal {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) :
    Integrable (fun τ : ℝ => paperFT k τ) := by
  have : (fun τ : ℝ => paperFT k τ) = fun τ => (𝓕 k) ((-(1 / (2 * π))) * τ) := by
    ext τ; rw [paperFT_ofReal_eq_fourier, show -(1 / (2 * π)) * τ = -τ / (2 * π) by ring]
  rw [this]
  exact hFk.comp_mul_left' (neg_ne_zero.mpr (by positivity))

/-- Paper inversion `k(u) = (1/2π) ∫ h(r) e^{−iru} dr` (App. A, "so that …"), from Mathlib's
`Continuous.fourierInv_fourier_eq` and the substitution `v = −r/(2π)`. -/
theorem paper_inversion {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) (u : ℝ) :
    k u = (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * cexp (-I * r * u) := by
  have hinv := congrFun (hk.fourierInv_fourier_eq hki hFk) u
  rw [← hinv, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  have key : (fun r : ℝ => paperFT k r * cexp (-I * r * u))
      = fun r => (fun v : ℝ => 𝓕 k v * cexp (2 * π * I * v * u)) ((-(1 / (2 * π))) * r) := by
    ext r
    rw [paperFT_ofReal_eq_fourier, show -(1 / (2 * π)) * r = -r / (2 * π) by ring]
    congr 1
    push_cast
    field_simp
  rw [key, Measure.integral_comp_mul_left (fun v : ℝ => 𝓕 k v * cexp (2 * π * I * v * u))]
  have habs : |(-(1 / (2 * π)) : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, abs_neg, one_div, inv_inv, abs_of_pos (by positivity)]
  rw [habs, Complex.real_smul, ← mul_assoc]
  have h2π : (1 / (2 * π) : ℂ) * ((2 * π : ℝ) : ℂ) = 1 := by
    push_cast; field_simp
  rw [h2π, one_mul]
  congr 1; ext v
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast; ring

/-! ## The test function k = f ⋆ g̃ -/

/-! ## App. A: the three identifications -/

/-- *Gamma term*: `(1/2π) ∫ h(r)[Re Γ'/Γ(1/4+ir/2) − log π] dr = ∫ h μ` — definitional ([eq:mudef]). -/
theorem gamma_term (k : ℝ → ℂ) :
    (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (gammaBracket r : ℂ)
      = ∫ τ : ℝ, paperFT k τ * (mu τ : ℂ) := by
  rw [← cintegral_const_mul]
  congr 1; ext r
  simp only [gammaBracket, mu]
  push_cast
  ring

/-! ### Pole term: inversion + Fubini, and the two explicit integrals -/

/-! ### Integrability of the three densities against h (from the computations above) -/

/-! ## Adding up -/

/-! ## [prop:EF] from the literature form -/

end EF
end Zeta23
