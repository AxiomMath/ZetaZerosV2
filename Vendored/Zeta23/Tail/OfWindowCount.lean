/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

VENDORED into ZetaZerosInternal from anthropics/formal-math (zeta23/Zeta23/Tail.lean),
Apache-2.0. This file contains the single lemma `LocalCount.ofWindowCount`, copied verbatim
from the `Zeta23/Tail.lean` umbrella so that `Zeta23.WeilEF.ZeroSummability` and
`Zeta23.WeilEF.GoodHeights` can import it without the rest of that umbrella (whose other
contents belong to the Alpöge–Furman rank-trace argument and are not vendored here).
-/
import Zeta23.Defs
import Zeta23.Tail.Basic

namespace Zeta23
namespace Tail

/-- From the two-sided local count on Z.N (PaperInputs.RvM.local) to the
finite-sub-family form LocalCount used by Zeta23/Tail/Count.lean, for the family of all
distinct zeros ρ ∈ Z.carrier with ordinate γ_ρ = Im ρ and multiplicity m_ρ = Z.mult ρ. -/
theorem LocalCount.ofWindowCount (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    LocalCount (fun ρ : Z.carrier => (ρ : ℂ).im) (fun ρ : Z.carrier => Z.mult ρ) A₀ where
  one_le := hA₀
  window t s hs := by
    classical
    refine le_trans ?_ (hloc t)
    have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨ρ, hρ, rfl⟩ := hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2, hs ρ hρ⟩
    have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
    rw [Finset.sum_map] at h
    exact_mod_cast h

end Tail
end Zeta23
