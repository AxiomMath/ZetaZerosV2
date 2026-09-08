/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Zeta.Transfer
public import ZetaZeros.Hilbert.Propositions
public import ZetaZeros.Zeta.TransferCounts

/-!
# The finite-set bounds transferred to the zeros

Each mirrors `simpleOnLineCount_lower`: apply the proposition to the rescaled zeros, then rewrite
the three pieces -- the total mass, the kernel sum, and the count -- into their zeta-side names.
-/

@[expose] public section

namespace ZetaZeros

/-- **(2.5) transferred** (`lem_N_simple_plus_on_line_lower`). -/
@[zz_tag "lem_N_simple_plus_on_line_lower"]
theorem simpleZeroCount_add_onLineCount_lower {lam T : ℝ} {eta : ℝ → ℝ}
    (hT : 1 < T) (hzeros : (nontrivialZeros T).Nonempty) (hη : IsAdmissible lam eta) :
    3 * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re
      ≤ (simpleZeroCount T : ℝ) + (onLineCount T : ℝ) := by
  have hZne : (rescaledZerosFinset T).Nonempty := by
    obtain ⟨ρ, hρ⟩ := hzeros
    refine ⟨rescale T ρ, ?_⟩
    simp only [rescaledZerosFinset, Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨ρ, hρ, rfl⟩
  have hbound := card_simplePart_add_realMass_lower hη (rescaledZeros_isConjInvariant hT) hZne
  have hsum : ∑ z ∈ rescaledZerosFinset T, (rescaledMult T z : ℝ) = (zeroCount T : ℝ) := by
    exact_mod_cast sum_rescaledMult_eq_zeroCount hT
  have hkernel := congrArg Complex.re
    (rescaled_kernel_sum_eq_unweightedKernelSum hT hη)
  simp only [Nat.cast_mul] at hkernel
  have hcard : ((simplePart (rescaledZerosFinset T) (rescaledMult T)).card : ℝ)
      = (simpleZeroCount T : ℝ) := by
    exact_mod_cast card_simplePart_rescaled_eq_simpleZeroCount hT
  have hmass : ∑ z ∈ allRealPart (rescaledZerosFinset T), (rescaledMult T z : ℝ)
      = (onLineCount T : ℝ) := by
    exact_mod_cast sum_allRealPart_rescaled_eq_onLineCount hT
  rwa [hsum, hkernel, hcard, hmass] at hbound

/-- **(2.6) transferred** (`lem_N_simple_or_on_line_lower`). Carries the side condition
`1 ≤ A < 2` and the second-moment bound through. -/
@[zz_tag "lem_N_simple_or_on_line_lower"]
theorem simpleOrOnLineCount_lower {lam T Ac : ℝ} {eta : ℝ → ℝ}
    (hT : 1 < T) (hzeros : (nontrivialZeros T).Nonempty) (hη : IsAdmissible lam eta)
    (hA1 : 1 ≤ Ac) (hA2 : Ac < 2)
    (hbnd : (unweightedKernelSum eta T).re ≤ Ac * (zeroCount T : ℝ)) :
    (5 + 2 * Real.sqrt 2 - 2 * Ac) / (3 + 2 * Real.sqrt 2) * (zeroCount T : ℝ)
      ≤ (simpleOrOnLineCount T : ℝ) := by
  have hZne : (rescaledZerosFinset T).Nonempty := by
    obtain ⟨ρ, hρ⟩ := hzeros
    refine ⟨rescale T ρ, ?_⟩
    simp only [rescaledZerosFinset, Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨ρ, hρ, rfl⟩
  have hsum : ∑ z ∈ rescaledZerosFinset T, (rescaledMult T z : ℝ) = (zeroCount T : ℝ) := by
    exact_mod_cast sum_rescaledMult_eq_zeroCount hT
  have hkernel := congrArg Complex.re
    (rescaled_kernel_sum_eq_unweightedKernelSum hT hη)
  simp only [Nat.cast_mul] at hkernel
  have hbnd' : (∑ z ∈ rescaledZerosFinset T, ∑ s ∈ rescaledZerosFinset T,
      (rescaledMult T z * rescaledMult T s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ Ac * ∑ z ∈ rescaledZerosFinset T, (rescaledMult T z : ℝ) := by
    rw [hsum, hkernel]; exact hbnd
  have hbound := simpleOrRealMass_lower hη (rescaledZeros_isConjInvariant hT) hZne hA1 hA2 hbnd'
  have hmass : ∑ z ∈ simpleOrRealPart (rescaledZerosFinset T) (rescaledMult T),
      (rescaledMult T z : ℝ) = (simpleOrOnLineCount T : ℝ) := by
    exact_mod_cast sum_simpleOrRealPart_rescaled_eq_simpleOrOnLineCount hT
  rwa [hsum, hmass] at hbound

end ZetaZeros
