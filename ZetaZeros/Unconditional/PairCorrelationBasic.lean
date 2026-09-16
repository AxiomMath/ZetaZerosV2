/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import Zeta23.Statement.SeamClosed

/-!
# Basic zeta-zero facts for pair correlation

This file records the small definitional bridges from the vendored `Zeta23` reference in a form
that can be reused by the unconditional pair-correlation proof without importing the challenge
module.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex Set

/-- A doubly restricted `finsum` over a finite set is the corresponding nested `Finset.sum`.
This is the finite-sum interchange interface used for the ordered pair of zeros. -/
theorem nested_finsum_eq_finite_toFinset_sum {α M : Type*} [AddCommMonoid M]
    (f : α → α → M) {s : Set α} (hs : s.Finite) :
    ∑ᶠ x ∈ s, ∑ᶠ y ∈ s, f x y =
      ∑ x ∈ hs.toFinset, ∑ y ∈ hs.toFinset, f x y := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs]
  apply Finset.sum_congr rfl
  intro x hx
  rw [finsum_mem_eq_finite_toFinset_sum _ hs]

end ZetaZeros.Unconditional.PairCorrelationProof
