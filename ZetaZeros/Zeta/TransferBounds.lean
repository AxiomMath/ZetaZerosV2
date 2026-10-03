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
# Lower bounds for the simple-plus-on-line and simple-or-on-line counts

The finite-set inequalities `card_simplePart_add_realMass_lower` and `simpleOrRealMass_lower`,
applied to the rescaled zeros up to height `T`, give lower bounds for
`simpleZeroCount T + onLineCount T` and for `simpleOrOnLineCount T` in terms of `zeroCount T` and
the kernel sum `unweightedKernelSum eta T`.

## Main results

* `simpleZeroCount_add_onLineCount_lower`: the lower bound for
  `simpleZeroCount T + onLineCount T`.
* `simpleOrOnLineCount_lower`: the lower bound for `simpleOrOnLineCount T`.
-/

@[expose] public section

namespace ZetaZeros

/-- **Lower bound for the simple-plus-on-line count.** For an admissible `eta` and `T > 1` with a
zero up to height `T`, `3 N(T) - Re (unweightedKernelSum eta T)` is at most the number of simple
zeros plus the number of zeros on the critical line counted with multiplicity. -/
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

/-- **Lower bound for the simple-or-on-line count.** For an admissible `eta`, `T > 1` with a zero
up to height `T`, and `1 ≤ A < 2` with `Re (unweightedKernelSum eta T) ≤ A N(T)`, the zeros that
are simple or on the critical line, counted with multiplicity, number at least
`(5 + 2√2 - 2A) / (3 + 2√2) N(T)`. -/
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
