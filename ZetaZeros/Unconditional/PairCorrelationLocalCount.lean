/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationZeroSum

/-!
# A quantitative shifted zero-count estimate

This file upgrades absolute convergence of the shifted Lorentzian zero sum to the uniform
logarithmic estimate needed in the pair-correlation argument.  We group ordinates into unit
windows after translating by the center and apply the two-sided local Riemann--von Mangoldt
bound in each window.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex

/-- The multiplicity-weighted Lorentzian zero sum centered at `t` is `O(log (|t| + 3))`,
uniformly for all real centers `t`. -/
theorem shiftedZeroLorentzian_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      (∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
          (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)) ≤
        C * Real.log (|t| + 3) := by
  classical
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount
    (Zeta23.zetaZeros Zeta23.zetaSeam) hA₀ (fun u => by
      rw [Zeta23.zetaZeros_N]
      exact hloc u)
  have hW := Zeta23.WeilEF.summable_weight
  have hWnonneg : 0 ≤ Zeta23.WeilEF.totalWeight :=
    tsum_nonneg fun n =>
      div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  let C : ℝ := 8 * A₀ * (Zeta23.WeilEF.totalWeight + 1)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun t => ?_⟩
  have hlogt : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    linarith [Real.exp_one_lt_d9, abs_nonneg t]
  have hpartial : ∀ s : Finset (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
      ∑ ρ ∈ s, (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) ≤
        8 * A₀ * Real.log (|t| + 3) * Zeta23.WeilEF.totalWeight := by
    intro s
    set κ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier → ℤ :=
      fun ρ => Zeta23.WeilEF.key ((ρ : ℂ).im - t) with hκ
    rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ)
      (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
    have hfiber : ∀ n ∈ s.image κ,
        ∑ ρ ∈ s with κ ρ = n,
            (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) ≤
          8 * A₀ * Real.log (|t| + 3) *
            (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
      intro n _
      have hwin := hLC.window (t + (n : ℝ)) (s.filter fun ρ => κ ρ = n)
        (fun ρ hρ => by
          simp only [Finset.mem_filter] at hρ
          have hleft : (n : ℝ) < (ρ : ℂ).im - t := by
            rw [← hρ.2]
            exact Zeta23.WeilEF.key_lt _
          have hright : (ρ : ℂ).im - t ≤ (n : ℝ) + 1 := by
            rw [← hρ.2]
            exact Zeta23.WeilEF.le_key_add_one _
          constructor <;> linarith)
      have harg : |t + (n : ℝ)| + 3 ≤ (|t| + 3) * (|(n : ℝ)| + 3) := by
        calc
          |t + (n : ℝ)| + 3 ≤ |t| + |(n : ℝ)| + 3 := by
            linarith [abs_add_le t (n : ℝ)]
          _ ≤ (|t| + 3) * (|(n : ℝ)| + 3) := by
            nlinarith [abs_nonneg t, abs_nonneg (n : ℝ),
              mul_nonneg (abs_nonneg t) (abs_nonneg (n : ℝ))]
      have hlogn : 1 ≤ Real.log (|(n : ℝ)| + 3) := by
        rw [← Real.log_exp 1]
        apply Real.log_le_log (Real.exp_pos 1)
        linarith [Real.exp_one_lt_d9, abs_nonneg (n : ℝ)]
      have hlogshift :
          Real.log (|t + (n : ℝ)| + 3) ≤
            2 * Real.log (|t| + 3) * Real.log (|(n : ℝ)| + 3) := by
        have hlogprod := Real.log_le_log (by positivity : 0 < |t + (n : ℝ)| + 3) harg
        rw [Real.log_mul (by positivity) (by positivity)] at hlogprod
        have hproduct :
            Real.log (|t| + 3) + Real.log (|(n : ℝ)| + 3) ≤
              2 * Real.log (|t| + 3) * Real.log (|(n : ℝ)| + 3) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hlogt) (sub_nonneg.mpr hlogn),
            mul_nonneg (show 0 ≤ Real.log (|t| + 3) by linarith)
              (show 0 ≤ Real.log (|(n : ℝ)| + 3) by linarith)]
        exact hlogprod.trans hproduct
      have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
          (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) ≤
            (4 / (1 + (n : ℝ) ^ 2)) * (Zeta23.zeroMult ρ : ℝ) := by
        intro ρ hρ
        simp only [Finset.mem_filter] at hρ
        have hleft : (n : ℝ) < (ρ : ℂ).im - t := by
          rw [← hρ.2]
          exact Zeta23.WeilEF.key_lt _
        have hright : (ρ : ℂ).im - t ≤ (n : ℝ) + 1 := by
          rw [← hρ.2]
          exact Zeta23.WeilEF.le_key_add_one _
        have hge := Zeta23.WeilEF.one_add_sq_ge hleft hright
        have hinv :
            1 / (1 + (t - (ρ : ℂ).im) ^ 2) ≤ 4 / (1 + (n : ℝ) ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hge]
        have hm : (0 : ℝ) ≤ Zeta23.zeroMult (ρ : ℂ) := Nat.cast_nonneg _
        calc
          (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) =
              (Zeta23.zeroMult ρ : ℝ) *
                (1 / (1 + (t - (ρ : ℂ).im) ^ 2)) := by ring
          _ ≤ (Zeta23.zeroMult ρ : ℝ) * (4 / (1 + (n : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hinv hm
          _ = (4 / (1 + (n : ℝ) ^ 2)) * (Zeta23.zeroMult ρ : ℝ) := by ring
      calc
        ∑ ρ ∈ s with κ ρ = n,
            (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) ≤
            ∑ ρ ∈ s with κ ρ = n,
              (4 / (1 + (n : ℝ) ^ 2)) * (Zeta23.zeroMult ρ : ℝ) :=
          Finset.sum_le_sum hpt
        _ = (4 / (1 + (n : ℝ) ^ 2)) *
              ∑ ρ ∈ s with κ ρ = n, (Zeta23.zeroMult ρ : ℝ) := by
          rw [Finset.mul_sum]
        _ ≤ (4 / (1 + (n : ℝ) ^ 2)) *
              (A₀ * Real.log (|t + (n : ℝ)| + 3)) :=
          mul_le_mul_of_nonneg_left hwin (by positivity)
        _ ≤ (4 / (1 + (n : ℝ) ^ 2)) *
              (A₀ * (2 * Real.log (|t| + 3) * Real.log (|(n : ℝ)| + 3))) := by
          gcongr
        _ = 8 * A₀ * Real.log (|t| + 3) *
              (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by ring
    calc
      ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n,
          (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) ≤
          ∑ n ∈ s.image κ, 8 * A₀ * Real.log (|t| + 3) *
            (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) :=
        Finset.sum_le_sum hfiber
      _ = (8 * A₀ * Real.log (|t| + 3)) *
            ∑ n ∈ s.image κ,
              Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ (8 * A₀ * Real.log (|t| + 3)) * Zeta23.WeilEF.totalWeight := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hW.sum_le_tsum _ fun n _ =>
          div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  have htsum := Real.tsum_le_of_sum_le
    (fun ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier => by positivity) hpartial
  calc
    (∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)) ≤
        8 * A₀ * Real.log (|t| + 3) * Zeta23.WeilEF.totalWeight := htsum
    _ = (8 * A₀ * Zeta23.WeilEF.totalWeight) * Real.log (|t| + 3) := by ring
    _ ≤ (8 * A₀ * (Zeta23.WeilEF.totalWeight + 1)) * Real.log (|t| + 3) := by
      gcongr
      linarith
    _ = C * Real.log (|t| + 3) := by rfl

end ZetaZeros.Unconditional.PairCorrelationProof
