/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Hypotheses.lean — retained interfaces for classical analytic inputs.

This pruned copy retains the Riemann--von Mangoldt, Montgomery--Vaughan and Gamma
interfaces used by the unconditional proof. These are definitions and structures, not
Lean axioms. Their concrete proofs are supplied elsewhere in the retained development.
The upstream paper's equation labels and literature references are preserved below.
-/
import Zeta23.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped BigOperators ArithmeticFunction ComplexConjugate ContDiff
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

/-! ## H-RvM — Riemann–von Mangoldt + local zero count  [eq:RvM], [prop:tail] first line -/

/-- **H-RvM**.
* main [eq:RvM], verbatim: "By the Riemann–von Mangoldt formula, with l := log(T/2π),
  N(T,2T) = (T/2π)(l + 2 log 2 − 1) + O(log T)."  (ell1 T = l T + 2 log 2 − 1.) Source: [Tit86, Thm 9.4].
* local_count [prop:tail]: "Let A₀ ≥ 1 be an absolute constant such that N(t+1) − N(t) ≤ A₀ log(t+3)
  for all t ≥ 0" — "classical [Tit86, Theorem 9.2]".
  Deviation (deliberate): stated two-sided, for all real t with
  log(|t|+3), i.e. also for windows of negative ordinate. The paper's proof of prop:tail bounds the
  zeros with γ ≤ 0 using the γ ↦ −γ symmetry of the zero set, which it states in [subsec:weil] but
  which is not a field of ZeroConfig; the two-sided local count is an equally classical consequence
  of [Tit86, 9.2] + that symmetry and removes the extra seam obligation. -/
structure RiemannVonMangoldt (Z : ZeroConfig) : Prop where
  main : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(Z.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T
  local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)

/-! ## H-MV — Montgomery–Vaughan weighted Hilbert inequality  [lem:MV] -/

/-- The weighted ("generalised") Hilbert inequality with constant C [lem:MV], verbatim:
"Let λ_1,…,λ_R be distinct real numbers, δ_r := min_{s≠r} |λ_r − λ_s|, and x_r, z_r ∈ ℂ. Then
  |Σ_{r≠s} x_r conj(z_s)/(λ_r − λ_s)| ≤ (3π/2) (Σ_r |x_r|²/δ_r)^{1/2} (Σ_r |z_r|²/δ_r)^{1/2}."
Source: [MV74, Theorem 2] for z = x (the paper citation); the bilinear form is derived in the paper by a
3-line operator-norm argument. "Any absolute constant in place of 3π/2 would suffice below."
Shape notes: index set = any Fintype ι with DecidableEq; distinctness = injectivity of freq; instead
of δ_r := min_{s≠r}|λ_r−λ_s| (undefined for R = 1) we allow ANY admissible weights 0 < δ_r ≤
|λ_r − λ_s| (s ≠ r) — equivalent to the paper's statement since the right side is antitone in δ.
The bilinear (x,z) form is assumed directly (it is what prop:PP/prop:cross consume). -/
def MVHilbert (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x z : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) → (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (z s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * Real.sqrt (∑ r, ‖x r‖ ^ 2 / δ r) * Real.sqrt (∑ r, ‖z r‖ ^ 2 / δ r)

/-! ## H-Γ — Stirling-type facts for μ  [eq:mufacts], [eq:muints] -/

/-- **H-Γ** [eq:mufacts], verbatim: "μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1,
  μ(τ) = (1/2π) log(|τ|/2π) + O(τ⁻²),  μ'(τ) ≪ |τ|⁻¹  (|τ| ≥ 1)"
("(eq:mufacts) is Stirling's formula and Re Γ'/Γ(σ+it) = −γ_E + Σ_{n≥0}(1/(n+1) − (n+σ)/((n+σ)²+t²))"),
and the pure-Γ halves of [eq:muints]:
  "∫_T^{2T} μ(τ) dτ = Tℓ₁/(2π) + O(1/T)",   "∫_T^{2T} μ(τ)² dτ = (Tℓ₁²/4π²)(1 + O(l⁻²))".
(The remaining clause of [eq:muints], "= N(T,2T) + O(l)", is [eq:RvM] and is NOT restated here.)
Source: Stirling for Γ'/Γ (e.g. [MV07, App. C]). This structure only STATES the facts; they are
proved in Zeta23/GammaFacts/Complete.lean (`gammaFacts : GammaFacts`, via the digamma series and a
vertical-line Stirling estimate in Zeta23/GammaFacts/*). "increasing" is rendered as MonotoneOn on [0,∞)
(nondecreasing), which is all prop:trace's Riemann-sum comparison uses. -/
structure GammaFacts : Prop where
  even : ∀ τ : ℝ, mu (-τ) = mu τ
  smooth : ContDiff ℝ ∞ mu
  monotoneOn : MonotoneOn mu (Ici 0)
  mu_zero_le : ∀ τ : ℝ, mu 0 ≤ mu τ
  neg_one_lt_mu_zero : -1 < mu 0
  stirling : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2
  deriv_bound : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv mu τ| ≤ C / |τ|
  int_mu : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ) - T * ell1 T / (2 * Real.pi)| ≤ C / T
  int_mu_sq : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ ^ 2) - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ C * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2

end Zeta23
