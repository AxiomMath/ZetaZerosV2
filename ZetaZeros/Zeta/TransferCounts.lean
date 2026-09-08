/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Hilbert.AlphaExpansion
public import ZetaZeros.Defs
public import ZetaZeros.Hilbert.Support

/-!
# The rescaled zeros carry the simple and on-line counts

Each of these transports a count along the multiplicity-preserving bijection `rescale T`. A
rescaled point is real exactly when the zero is on the critical line, and has multiplicity one
exactly when the zero does, so each selection of the support corresponds to the matching selection
of the zeros.
-/

@[expose] public section

namespace ZetaZeros

/-- **The rescaled zeros carry the simple count** (`lem_Z_T_simple_count`). -/
@[zz_tag "lem_Z_T_simple_count"]
theorem card_simplePart_rescaled_eq_simpleZeroCount {T : ℝ} (hT : 1 < T) :
    (simplePart (rescaledZerosFinset T) (rescaledMult T)).card = simpleZeroCount T := by
  classical
  have hfin := nontrivialZeros_finite T
  have hsub : {rho ∈ nontrivialZeros T | zeroMultiplicity rho = 1}.Finite :=
    hfin.subset fun x hx => hx.1
  have hset : simplePart (rescaledZerosFinset T) (rescaledMult T)
      = (hfin.toFinset.filter fun rho => zeroMultiplicity rho = 1).image (rescale T) := by
    ext w
    simp only [simplePart, rescaledZerosFinset, Finset.mem_filter, Finset.mem_image,
      Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨rho, hrho, rfl⟩, hm⟩
      refine ⟨rho, ⟨hrho, ?_⟩, rfl⟩
      rwa [rescaledMult_rescale hT] at hm
    · rintro ⟨rho, ⟨hrho, hm⟩, rfl⟩
      refine ⟨⟨rho, hrho, rfl⟩, ?_⟩
      rw [rescaledMult_rescale hT]; exact hm
  rw [hset, Finset.card_image_of_injective _ (rescale_injective hT), simpleZeroCount,
    Set.ncard_eq_toFinset_card _ hsub]
  congr 1
  ext rho
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_ofPred_eq]

/-- **The rescaled zeros carry the on-line mass** (`lem_Z_T_on_line_mass`). Counted with
multiplicity, matching the source's `N₀`. -/
@[zz_tag "lem_Z_T_on_line_mass"]
theorem sum_allRealPart_rescaled_eq_onLineCount {T : ℝ} (hT : 1 < T) :
    ∑ z ∈ allRealPart (rescaledZerosFinset T), rescaledMult T z = onLineCount T := by
  classical
  have hfin := nontrivialZeros_finite T
  have hset : allRealPart (rescaledZerosFinset T)
      = (hfin.toFinset.filter fun rho => rho.re = 1 / 2).image (rescale T) := by
    ext w
    simp only [allRealPart, rescaledZerosFinset, Finset.mem_filter, Finset.mem_image,
      Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨rho, hrho, rfl⟩, him⟩
      exact ⟨rho, ⟨hrho, (rescale_im_eq_zero_iff hT rho).mp him⟩, rfl⟩
    · rintro ⟨rho, ⟨hrho, hre⟩, rfl⟩
      exact ⟨⟨rho, hrho, rfl⟩, (rescale_im_eq_zero_iff hT rho).mpr hre⟩
  have hmul : ∀ rho ∈ hfin.toFinset.filter fun rho => rho.re = 1 / 2,
      rescaledMult T (rescale T rho) = zeroMultiplicity rho :=
    fun rho _ => rescaledMult_rescale hT rho
  have hcoe : (↑(hfin.toFinset.filter fun rho => rho.re = 1 / 2) : Set ℂ)
      = {rho ∈ nontrivialZeros T | rho.re = 1 / 2} := by
    ext rho
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rw [hset, Finset.sum_image fun a _ b _ hab => rescale_injective hT hab,
    Finset.sum_congr rfl hmul, onLineCount, ← finsum_mem_coe_finset, hcoe]

/-- **The rescaled zeros carry the simple-or-on-line mass**
(`lem_Z_T_simple_or_on_line_mass`). Counted with multiplicity, matching the source's `N_{s∪0}`. -/
@[zz_tag "lem_Z_T_simple_or_on_line_mass"]
theorem sum_simpleOrRealPart_rescaled_eq_simpleOrOnLineCount {T : ℝ} (hT : 1 < T) :
    ∑ z ∈ simpleOrRealPart (rescaledZerosFinset T) (rescaledMult T), rescaledMult T z
      = simpleOrOnLineCount T := by
  classical
  have hfin := nontrivialZeros_finite T
  have hset : simpleOrRealPart (rescaledZerosFinset T) (rescaledMult T)
      = (hfin.toFinset.filter fun rho => zeroMultiplicity rho = 1 ∨ rho.re = 1 / 2).image
          (rescale T) := by
    ext w
    simp only [simpleOrRealPart, rescaledZerosFinset, Finset.mem_filter, Finset.mem_image,
      Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨rho, hrho, rfl⟩, hor⟩
      refine ⟨rho, ⟨hrho, ?_⟩, rfl⟩
      rcases hor with hm | him
      · left; rwa [rescaledMult_rescale hT] at hm
      · right; exact (rescale_im_eq_zero_iff hT rho).mp him
    · rintro ⟨rho, ⟨hrho, hor⟩, rfl⟩
      refine ⟨⟨rho, hrho, rfl⟩, ?_⟩
      rcases hor with hm | hre
      · left; rw [rescaledMult_rescale hT]; exact hm
      · right; exact (rescale_im_eq_zero_iff hT rho).mpr hre
  have hmul : ∀ rho ∈ hfin.toFinset.filter
      fun rho => zeroMultiplicity rho = 1 ∨ rho.re = 1 / 2,
      rescaledMult T (rescale T rho) = zeroMultiplicity rho :=
    fun rho _ => rescaledMult_rescale hT rho
  have hcoe : (↑(hfin.toFinset.filter fun rho => zeroMultiplicity rho = 1 ∨ rho.re = 1 / 2)
      : Set ℂ) = {rho ∈ nontrivialZeros T | zeroMultiplicity rho = 1 ∨ rho.re = 1 / 2} := by
    ext rho
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rw [hset, Finset.sum_image fun a _ b _ hab => rescale_injective hT hab,
    Finset.sum_congr rfl hmul, simpleOrOnLineCount, ← finsum_mem_coe_finset, hcoe]

end ZetaZeros
