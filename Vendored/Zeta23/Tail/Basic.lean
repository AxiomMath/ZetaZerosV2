/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Basic.lean — shared elementary definitions for prop:tail (the paper §4.2).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace Zeta23
namespace Tail

/-- Local zero-count hypothesis of [prop:tail]: "Let A₀ ≥ 1 be an absolute constant such
that N(t+1) − N(t) ≤ A₀ log(t+3) for all t ≥ 0" [Tit86, Thm 9.2], for an abstract family of
ordinates γ : ι → ℝ with multiplicities m : ι → ℕ. We use the two-sided unit-window form
(all real t, bound A₀·log(|t|+3)) as in PaperInputs.RvM.local: it is
equally classical and covers the zeros with γ ≤ 0 — which are in the tail
(paper: "zeros with γ ≤ 0 have D ≥ T and contribute at most ∑_{j≥0} A₀ log(j+4)(T+j)⁻³",
silently using the γ ↦ −γ symmetry and ζ(σ) ≠ 0 for 0<σ<1) — with no separate seam fact.
Stated for finite sub-families so that no summability is presupposed; instantiated from
ZeroConfig + PaperInputs.RvM.local in Zeta23/Tail.lean (LocalCount.ofWindowCount). -/
structure LocalCount {ι : Type*} (γ : ι → ℝ) (m : ι → ℕ) (A₀ : ℝ) : Prop where
  one_le : 1 ≤ A₀
  window : ∀ t : ℝ, ∀ s : Finset ι, (∀ ρ ∈ s, t < γ ρ ∧ γ ρ ≤ t + 1) →
    (∑ ρ ∈ s, (m ρ : ℝ)) ≤ A₀ * Real.log (|t| + 3)

lemma LocalCount.A₀_pos {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ : ℝ}
    (h : LocalCount γ m A₀) : 0 < A₀ := lt_of_lt_of_le one_pos h.one_le

end Tail
end Zeta23
