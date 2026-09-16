/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Count.lean — the zero-count sum in the proof of [prop:tail] (the paper §4.2).

Paper, verbatim: "It remains to bound ∑_{γ∉I'} m_ρ D⁻³ (zeros counted with multiplicity).
Zeros with γ > 2T+D₀: grouping them into γ ∈ (2T+D₀+j, 2T+D₀+j+1], j ≥ 0, this part is at
most ∑_{j≥0} A₀ log(2T+D₀+j+4)(D₀+j)⁻³ ≤ (3/2)A₀ log(4T) D₀⁻² for T large (split at j = T
and use D₀ ≥ 2). Zeros with 0 < γ < T−D₀ contribute likewise at most (3/2)A₀ log(4T)D₀⁻²,
and zeros with γ ≤ 0 have D ≥ T and contribute at most ∑_{j≥0} A₀ log(j+4)(T+j)⁻³
≪ T⁻² log T. Altogether ∑_{γ∉I'} m_ρ D⁻³ ≤ 4A₀ log(4T) D₀⁻² for T ≥ T₀."

We prove the bound for every FINITE sub-family of tail zeros (which yields both the
summability and the bound for the full series downstream), with the explicit absolute
threshold T₀ of Zeta23/Tail/Basic.lean. Only the final constant 4 is load-bearing (it is
the 4 in θ₀); we do not follow the paper's intermediate 3/2 + 3/2 + o(1) split. Our
grouping: unit windows indexed by the integer distance j from the nearer endpoint of
I = [T,2T] (lower side: T−j−1 < γ ≤ T−j, which also covers ALL γ ≤ 0; upper side:
2T+j < γ ≤ 2T+j+1), each window weighted by max(D₀, j)⁻³ and counted by the two-sided
local count ≤ A₀ log(2T+4+j); integrals are replaced by telescoping sums.
-/
import Zeta23.Tail.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

open Finset Real

namespace Zeta23
namespace Tail

/-! #### Telescoping sums replacing ∫ x⁻³ and ∫ x⁻² -/

lemma inv_pow_two_step {a : ℝ} (ha : 0 < a) :
    ((a + 1) ^ 2)⁻¹ ≤ a⁻¹ - (a + 1)⁻¹ := by
  rw [← sub_nonneg]
  have key : a⁻¹ - (a + 1)⁻¹ - ((a + 1) ^ 2)⁻¹ = 1 / (a * (a + 1) ^ 2) := by
    field_simp; ring
  rw [key]; positivity

lemma sum_inv_pow_two_le_telescope {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range (n + 1), ((D + i) ^ 2)⁻¹ ≤ (D ^ 2)⁻¹ + (D⁻¹ - (D + n)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hstep := inv_pow_two_step (a := D + n) (by positivity)
    have e : (D + ((n + 1 : ℕ) : ℝ)) = D + n + 1 := by push_cast; ring
    rw [e]
    calc _ ≤ (D ^ 2)⁻¹ + (D⁻¹ - (D + n)⁻¹) + ((D + n)⁻¹ - (D + n + 1)⁻¹) :=
          add_le_add ih hstep
      _ = _ := by ring

/-- ∑_{i<n} (D + i)⁻² ≤ D⁻² + D⁻¹ for D > 0 (any n). -/
lemma sum_inv_pow_two_le {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range n, ((D + i) ^ 2)⁻¹ ≤ (D ^ 2)⁻¹ + D⁻¹ := by
  cases n with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ n =>
    refine (sum_inv_pow_two_le_telescope hD n).trans ?_
    have : 0 ≤ (D + n)⁻¹ := by positivity
    linarith

/-! #### Summing the window weights -/

/-! #### One side of the tail, abstractly -/

/-! #### Numerics at T ≥ T₀ -/

/-! #### The zero-count sum -/

/-! #### The boundary count N(I' ∖ I) -/

/-- Counting by unit windows: if every zero of s falls in one of K windows (key < K) and each
window holds total multiplicity ≤ C, then ∑_s m ≤ K·C. -/
lemma sum_mult_le_of_windows {ι : Type*} (s : Finset ι) (m : ι → ℕ) (key : ι → ℕ) (K : ℕ)
    {C : ℝ} (hkey : ∀ ρ ∈ s, key ρ < K)
    (hcount : ∀ j < K, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) ≤ C) :
    ∑ ρ ∈ s, (m ρ : ℝ) ≤ K * C := by
  rw [← sum_fiberwise_of_maps_to (g := key) (t := range K)
    (fun ρ hρ => mem_range.mpr (hkey ρ hρ))]
  calc ∑ j ∈ range K, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ)
      ≤ ∑ j ∈ range K, C := sum_le_sum fun j hj => hcount j (mem_range.mp hj)
    _ = K * C := by rw [sum_const, card_range, nsmul_eq_mul]

end Tail
end Zeta23
