/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Hilbert.AlphaExpansion
public import ZetaZeros.Hilbert.Parts

/-!
# The refined first-range bound

Equation (2.11) of the source. Where `sum_alphaOf_re_first_lower` bounds the first-range coefficient
sum below by `2|R₂| + |S|` using only `m ≥ 1` on the non-real part, the refinement here uses `m ≥ 2`
on `S₂` and so gets `2|R₂| + |S₁| + 2|S₂|`. Only the closing cardinality step differs; the Parseval
and Bessel work is the same.
-/

@[expose] public section

namespace ZetaZeros

variable {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}

@[zz_tag "lem_alpha_first_lower_refined"]
theorem sum_alphaOf_re_first_lower_refined (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m)
    {psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam}
    (hb : IsAdaptedBasis h Z m psi) (hsym : ∀ j, IsSymmetricL2 (psi j)) :
    2 * ((multipleRealPart Z m).card : ℝ) + ((simpleNonRealPart Z m).card : ℝ)
        + 2 * ((multipleNonRealPart Z m).card : ℝ)
      ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (Module.finrank ℂ (subspaceW h Z m)) =>
          (j : ℕ) < Module.finrank ℂ (subspaceU h Z m)),
        (alphaOf eta lam Z m (psi j)).re := by
  classical
  let s := Finset.univ.filter (fun j : Fin (Module.finrank ℂ (subspaceW h Z m)) =>
    (j : ℕ) < Module.finrank ℂ (subspaceU h Z m))
  have hspan : Submodule.span ℂ (psi '' (s : Set _)) = subspaceU h Z m := by
    simpa [s] using hb.span_U
  have hfz : ∀ x ∈ multipleRealPart Z m,
      fzL2 h x ∈ Submodule.span ℂ (psi '' (s : Set _)) := by
    intro x hx
    rw [hspan, subspaceU]
    exact Submodule.subset_span (Set.mem_union_left _ ⟨x, by simpa using hx, rfl⟩)
  have hgz : ∀ z ∈ nonRealPart Z,
      gzL2 h z ∈ Submodule.span ℂ (psi '' (s : Set _)) := by
    intro z hz
    rw [hspan, subspaceU]
    exact Submodule.subset_span (Set.mem_union_right _ ⟨z, by simpa using hz, rfl⟩)
  have hone_f : ∀ x ∈ multipleRealPart Z m,
      ∑ j ∈ s, ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 = 1 := by
    intro x hx
    rw [sum_sq_norm_inner_eq_norm_sq_of_mem_span_finset hb.orthonormal s (hfz x hx)]
    exact norm_fzL2_sq_eq_one h ((Finset.mem_filter.mp hx).2).1
  have hg_parseval : ∀ z ∈ nonRealPart Z,
      ∑ j ∈ s, ‖inner ℂ (psi j) (gzL2 h z)‖ ^ 2 = ‖gzL2 h z‖ ^ 2 := by
    intro z hz
    exact sum_sq_norm_inner_eq_norm_sq_of_mem_span_finset hb.orthonormal s (hgz z hz)
  have hh_bessel : ∀ z : ℂ,
      ∑ j ∈ s, ‖inner ℂ (psi j) (hzL2 h z)‖ ^ 2 ≤ ‖hzL2 h z‖ ^ 2 := by
    intro z
    exact hb.orthonormal.sum_inner_products_le (s := s) (hzL2 h z)
  rw [show (∑ j ∈ Finset.univ.filter
      (fun j : Fin (Module.finrank ℂ (subspaceW h Z m)) =>
        (j : ℕ) < Module.finrank ℂ (subspaceU h Z m)),
      (alphaOf eta lam Z m (psi j)).re) =
      ∑ j ∈ s, (alphaOf eta lam Z m (psi j)).re by rfl]
  simp_rw [alphaOf_re_eq_sum_norm h hZ (hsym _)]
  rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (s := s) (t := nonRealPart Z)]
  have hR1nonneg : 0 ≤ ∑ x ∈ simpleRealPart Z m,
      ∑ j ∈ s, (m x : ℝ) * ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 := by positivity
  rw [Finset.sum_union disjoint_simpleRealPart_multipleRealPart]
  have hR2 : ∑ x ∈ multipleRealPart Z m,
      ∑ j ∈ s, (m x : ℝ) * ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2
      = ∑ x ∈ multipleRealPart Z m, (m x : ℝ) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.mul_sum, hone_f x hx, mul_one]
  rw [hR2]
  have hS : ∑ z ∈ nonRealPart Z,
      ∑ j ∈ s, (m z : ℝ) *
        (‖inner ℂ (psi j) (gzL2 h z)‖ ^ 2 - ‖inner ℂ (psi j) (hzL2 h z)‖ ^ 2)
      ≥ ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
    refine Finset.sum_le_sum fun z hz => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hg_parseval z hz]
    have hm : (0 : ℝ) ≤ (m z : ℝ) := by positivity
    have hd := hh_bessel z
    have hdef := norm_gzL2_sq_sub_norm_hzL2_sq h z
    nlinarith
  have hR2card : 2 * ((multipleRealPart Z m).card : ℝ)
      ≤ ∑ x ∈ multipleRealPart Z m, (m x : ℝ) := by
    calc
      2 * ((multipleRealPart Z m).card : ℝ)
          = ∑ _x ∈ multipleRealPart Z m, (2 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ x ∈ multipleRealPart Z m, (m x : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        exact_mod_cast ((Finset.mem_filter.mp hx).2).2
  have hScard : ((simpleNonRealPart Z m).card : ℝ)
      + 2 * ((multipleNonRealPart Z m).card : ℝ)
      ≤ ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
    rw [sum_nonRealPart_eq_sum_simpleNonRealPart_add_sum_multipleNonRealPart hZ]
    have e1 : ∑ z ∈ simpleNonRealPart Z m, (m z : ℝ)
        = ((simpleNonRealPart Z m).card : ℝ) := by
      have hone : ∀ z ∈ simpleNonRealPart Z m, (m z : ℝ) = 1 := by
        intro z hz
        simp only [simpleNonRealPart, Finset.mem_filter] at hz
        rw [hz.2.2]; norm_num
      rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
    have e2 : 2 * ((multipleNonRealPart Z m).card : ℝ)
        ≤ ∑ z ∈ multipleNonRealPart Z m, (m z : ℝ) := by
      have htwo : ∀ z ∈ multipleNonRealPart Z m, (2 : ℝ) ≤ (m z : ℝ) := by
        intro z hz
        simp only [multipleNonRealPart, Finset.mem_filter] at hz
        exact_mod_cast hz.2.2
      calc 2 * ((multipleNonRealPart Z m).card : ℝ)
          = ∑ _z ∈ multipleNonRealPart Z m, (2 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ z ∈ multipleNonRealPart Z m, (m z : ℝ) := Finset.sum_le_sum htwo
    linarith
  linarith

end ZetaZeros
