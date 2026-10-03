/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Meta.Attr
public import ZetaZeros.Hilbert.AlphaExpansion.KernelBessel

/-!
# The kernel second moment and the three-range estimates

The kernel second moment as an integral of `‖F‖²`, the first-range coefficient estimate, and the
three-range estimates that turn the coefficient estimates into lower bounds for the number of
simple real elements and for the number of distinct elements.

## Main results

* `sum_testKernel_sq_re_eq_integral_norm_bigF_sq`: the second moment as an integral of `‖F‖²`.
* `sum_alphaOf_re_first_lower`: the coefficients with `j < dim U` sum to at least `2|R₂| + |S|`.
* `card_simpleRealPart_lower`: the lower bound for the number of simple real elements.
* `card_lower`: the lower bound for the number of distinct elements.
-/
@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ} {eta : ℝ → ℝ}

variable {Z : Finset ℂ} {m : ℂ → ℕ}

variable {delta : ℝ} {psi : ℝ → ℝ}

/-! ## The kernel second moment -/

/-- Expanding `F * conj F` gives the sum over ordered pairs of support points. -/
private lemma sum_pair_fz_mul_conj_eq_bigF_mul_conj_alpha
    (Z : Finset ℂ) (m : ℂ → ℕ) (u v : ℝ) :
    ∑ p ∈ Z ×ˢ Z, (m p.1 * m p.2 : ℂ) *
        (fz eta p.1 u * (starRingEnd ℂ) (fz eta p.2 u)) *
        (fz eta p.1 v * (starRingEnd ℂ) (fz eta p.2 v))
      = bigF eta Z m u v * (starRingEnd ℂ) (bigF eta Z m u v) := by
  simp only [Finset.sum_product, bigF, map_sum, map_mul, Complex.conj_natCast]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- The unconjugated finite kernel sum is the product-space second moment of `bigF`. -/
private theorem sum_testKernel_sq_eq_integral_norm_bigF_sq
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) :
    ∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          ((‖bigF eta Z m u v‖ ^ 2 : ℝ) : ℂ) := by
  rw [sum_testKernel_sq_eq_sum_conj hZ]
  have hint : ∀ p ∈ Z ×ˢ Z,
      Integrable
        (fun u => (fz eta p.1 u * (starRingEnd ℂ) (fz eta p.2 u)) * (1 : ℂ))
        (volume.restrict (Set.Ioo (-lam) lam)) := by
    intro p hp
    simp only [mul_one]
    change Integrable (fz eta p.1 * star (fz eta p.2))
      (volume.restrict (Set.Ioo (-lam) lam))
    exact (memLp_fz h p.1).integrable_mul (memLp_fz h p.2).star
  have hfactor := integral_double_finsetSum (Z ×ˢ Z)
    (fun p => (m p.1 * m p.2 : ℂ))
    (fun p u => fz eta p.1 u * (starRingEnd ℂ) (fz eta p.2 u))
    (fun _ => (1 : ℂ)) lam hint
  simp only [mul_one] at hfactor
  calc
    (∑ z ∈ Z, ∑ s ∈ Z,
        (m z * m s : ℂ) * testKernel eta (z - (starRingEnd ℂ) s) ^ 2) =
        ∑ p ∈ Z ×ˢ Z, (m p.1 * m p.2 : ℂ) *
          (∫ u in Set.Ioo (-lam) lam,
            fz eta p.1 u * (starRingEnd ℂ) (fz eta p.2 u)) ^ 2 := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro s hs
      rw [testKernel_sub_conj h z s]
    _ = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        ∑ p ∈ Z ×ˢ Z, (m p.1 * m p.2 : ℂ) *
          (fz eta p.1 u * (starRingEnd ℂ) (fz eta p.2 u)) *
          (fz eta p.1 v * (starRingEnd ℂ) (fz eta p.2 v)) := hfactor.symm
    _ = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        bigF eta Z m u v * (starRingEnd ℂ) (bigF eta Z m u v) := by
      apply integral_congr_ae
      filter_upwards [] with u
      apply integral_congr_ae
      filter_upwards [] with v
      exact sum_pair_fz_mul_conj_eq_bigF_mul_conj_alpha Z m u v
    _ = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        ((‖bigF eta Z m u v‖ ^ 2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with u
      apply integral_congr_ae
      filter_upwards [] with v
      rw [Complex.mul_conj']
      norm_cast

/-- Real-valued form of the second-moment identity, matching the right side of Bessel's
inequality. -/
theorem sum_testKernel_sq_re_eq_integral_norm_bigF_sq
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) :
    (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          ‖bigF eta Z m u v‖ ^ 2 := by
  rw [sum_testKernel_sq_eq_integral_norm_bigF_sq h hZ]
  simp only [integral_complex_ofReal, Complex.ofReal_re]

/-! ## The first-range coefficient estimate -/

/-- The real part of the Bessel coefficient of a symmetric `L²` element, expressed in squared
norms of Hilbert-space pairings. -/
theorem alphaOf_re_eq_sum_norm (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m) {phi : L2Interval lam}
    (hsym : IsSymmetricL2 phi) :
    (alphaOf eta lam Z m phi).re
      = (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
          (m x : ℝ) * ‖inner ℂ phi (fzL2 h x)‖ ^ 2)
        + ∑ z ∈ nonRealPart Z, (m z : ℝ) *
            (‖inner ℂ phi (gzL2 h z)‖ ^ 2 - ‖inner ℂ phi (hzL2 h z)‖ ^ 2) := by
  classical
  rw [alphaOf_eq h hZ, Complex.add_re, Complex.re_sum, Complex.re_sum]
  congr 1
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hxre : x.im = 0 := by
      rcases Finset.mem_union.mp hx with hx' | hx'
      · exact ((Finset.mem_filter.mp hx').2).1
      · exact ((Finset.mem_filter.mp hx').2).1
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x)]
    refine natCast_mul_sq_re ?_ _
    exact inner_symmetricL2_im_eq_zero hsym (fzL2_mem_symmetricSubspace h hxre)
  · refine Finset.sum_congr rfl fun z _ => ?_
    have hgim : (inner ℂ phi (gzL2 h z) : ℂ).im = 0 :=
      inner_symmetricL2_im_eq_zero hsym (gzL2_mem_symmetricSubspace h z)
    have hhim : (inner ℂ phi (hzL2 h z) : ℂ).im = 0 :=
      inner_symmetricL2_im_eq_zero hsym (hzL2_mem_symmetricSubspace h z)
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_gzL2 h z),
      integral_mul_conj_eq_inner_of_ae (coeFn_hzL2 h z)]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im, sq,
      Complex.natCast_re, Complex.natCast_im, hgim, hhim]
    ring

/-- **First range: lower bound for the coefficient sum.** Summed over `j < dim U`, the real parts
of the Bessel coefficients against a symmetric adapted basis are at least `2|R₂| + |S|`. -/
@[zz_tag "lem_alpha_first_lower"]
theorem sum_alphaOf_re_first_lower (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m)
    {psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam}
    (hb : IsAdaptedBasis h Z m psi) (hsym : ∀ j, IsSymmetricL2 (psi j)) :
    2 * ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ)
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
  have hScard : ((nonRealPart Z).card : ℝ)
      ≤ ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
    calc
      ((nonRealPart Z).card : ℝ) = ∑ _z ∈ nonRealPart Z, (1 : ℝ) := by simp
      _ ≤ ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
        refine Finset.sum_le_sum fun z hz => ?_
        exact_mod_cast hZ.one_le z (Finset.mem_filter.mp hz).1
  linarith

/-! ## Three-range algebra -/

/-- The numerical three-range estimate used for the simple-real-point bound.

The first range uses `a² + 4 ≥ 4a`, the middle range uses `a² + 1 ≥ 2a`, and the
last range uses `a ≤ 0`. -/
theorem three_range_simple {N dU dV R1 R2 S : ℕ} (a : Fin N → ℝ)
    (hdUV : dU ≤ dV) (hdVN : dV ≤ N)
    (hdU : dU ≤ R2 + S / 2) (hdGap : dV ≤ dU + R1)
    (hfirst : 2 * (R2 : ℝ) + (S : ℝ) ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU), a j)
    (hthird : ∀ j : Fin N, dV ≤ (j : ℕ) → a j ≤ 0) :
    2 * ∑ j, a j - (R1 : ℝ) ≤ ∑ j, a j ^ 2 := by
  classical
  let A := Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU)
  let B := Finset.univ.filter (fun j : Fin N => dU ≤ (j : ℕ) ∧ (j : ℕ) < dV)
  let C := Finset.univ.filter (fun j : Fin N => dV ≤ (j : ℕ))
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjA hjB
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
    omega
  have hABC : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjAB hjC
    rw [Finset.mem_union] at hjAB
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hjC
    rcases hjAB with hjA | hjB
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
      omega
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
      omega
  have hcover : A ∪ B ∪ C = Finset.univ := by
    ext j
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    omega
  have hABeq : A ∪ B = Finset.univ.filter (fun j : Fin N => (j : ℕ) < dV) := by
    ext j
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hcardA : A.card = dU := by
    rw [show A = Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU) from rfl,
      Fin.card_filter_val_lt, Nat.min_eq_right (le_trans hdUV hdVN)]
  have hcardAB : (A ∪ B).card = dV := by
    rw [hABeq, Fin.card_filter_val_lt, Nat.min_eq_right hdVN]
  have hcardB_le : B.card ≤ R1 := by
    rw [Finset.card_union_of_disjoint hAB, hcardA] at hcardAB
    omega
  have htwodim_nat : 2 * dU ≤ 2 * R2 + S := by
    omega
  have htwodim : 2 * (dU : ℝ) ≤ 2 * (R2 : ℝ) + (S : ℝ) := by
    exact_mod_cast htwodim_nat
  have hsqA_base :
      4 * (∑ j ∈ A, a j) - 4 * (A.card : ℝ) ≤ ∑ j ∈ A, a j ^ 2 := by
    calc
      4 * (∑ j ∈ A, a j) - 4 * (A.card : ℝ)
          = ∑ j ∈ A, (4 * a j - 4) := by simp [Finset.mul_sum]; ring
      _ ≤ ∑ j ∈ A, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        nlinarith [sq_nonneg (a j - 2)]
  have hsqA : 2 * (∑ j ∈ A, a j) ≤ ∑ j ∈ A, a j ^ 2 := by
    rw [hcardA] at hsqA_base
    have hfirstA : 2 * (R2 : ℝ) + (S : ℝ) ≤ ∑ j ∈ A, a j := by
      exact hfirst
    nlinarith
  have hsqB_base :
      2 * (∑ j ∈ B, a j) - (B.card : ℝ) ≤ ∑ j ∈ B, a j ^ 2 := by
    calc
      2 * (∑ j ∈ B, a j) - (B.card : ℝ)
          = ∑ j ∈ B, (2 * a j - 1) := by simp [Finset.mul_sum]
      _ ≤ ∑ j ∈ B, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        nlinarith [sq_nonneg (a j - 1)]
  have hcardB_real : (B.card : ℝ) ≤ (R1 : ℝ) := by exact_mod_cast hcardB_le
  have hsqB : 2 * (∑ j ∈ B, a j) - (R1 : ℝ) ≤ ∑ j ∈ B, a j ^ 2 := by
    linarith
  have hsqC : 2 * (∑ j ∈ C, a j) ≤ ∑ j ∈ C, a j ^ 2 := by
    calc
      2 * (∑ j ∈ C, a j) = ∑ j ∈ C, 2 * a j := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ C, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : dV ≤ (j : ℕ) := by simpa [C] using hj
        have ha := hthird j hj'
        nlinarith [sq_nonneg (a j)]
  have hsum (f : Fin N → ℝ) :
      ∑ j, f j = (∑ j ∈ A, f j) + (∑ j ∈ B, f j) + ∑ j ∈ C, f j := by
    rw [← hcover, Finset.sum_union hABC, Finset.sum_union hAB]
  rw [hsum a, hsum (fun j => a j ^ 2)]
  linarith

/-- **Lower bound for the simple real elements.** -/
@[zz_tag "prop_simple_real_lower"]
theorem card_simpleRealPart_lower (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m) (_hZne : Z.Nonempty) :
    2 * (∑ z ∈ Z, (m z : ℝ))
        - (∑ z ∈ Z, ∑ s ∈ Z,
            (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ ((simpleRealPart Z m).card : ℝ) := by
  classical
  obtain ⟨psi, hb, hsym⟩ := exists_symmetric_adapted_basis h Z m
  let a : Fin (Module.finrank ℂ (subspaceW h Z m)) → ℝ :=
    fun j => (alphaOf eta lam Z m (psi j)).re
  have hdUV : Module.finrank ℂ (subspaceU h Z m) ≤
      Module.finrank ℂ (subspaceV h Z m) :=
    Submodule.finrank_mono (subspaceU_le_subspaceV h Z m)
  have hdVN : Module.finrank ℂ (subspaceV h Z m) ≤
      Module.finrank ℂ (subspaceW h Z m) :=
    Submodule.finrank_mono (subspaceV_le_subspaceW h Z m)
  have hrange := three_range_simple a hdUV hdVN
    (finrank_subspaceU_le h hZ) (finrank_subspaceV_le h Z m)
    (sum_alphaOf_re_first_lower h hZ hb hsym)
    (fun j hj => alphaOf_re_nonpos h hZ hb (hsym j) hj)
  have htotal := sum_alphaOf_re_eq_sum_mult h hZ hb hsym
  have hbessel := sum_alphaOf_re_sq_le_integral_norm_bigF_sq_adapted h Z m hZ hb hsym
  have hmoment := sum_testKernel_sq_re_eq_integral_norm_bigF_sq h hZ
  change 2 * (∑ j, a j) - ((simpleRealPart Z m).card : ℝ)
      ≤ ∑ j, a j ^ 2 at hrange
  change ∑ j, a j = ∑ z ∈ Z, (m z : ℝ) at htotal
  change ∑ j, a j ^ 2 ≤ _ at hbessel
  rw [← hmoment] at hbessel
  linarith

/-- The numerical three-range estimate used for the distinct-point bound.

Compared with `three_range_simple`, all three ranges retain a factor four. On the middle range,
the upper bound on its coefficient sum supplies the extra factor two. -/
theorem three_range_distinct {N dU dV R1 R2 S : ℕ} (a : Fin N → ℝ)
    (hdUV : dU ≤ dV) (hdVN : dV ≤ N)
    (hdU : dU ≤ R2 + S / 2) (hdGap : dV ≤ dU + R1)
    (hsecond :
      ∑ j ∈ Finset.univ.filter
          (fun j : Fin N => dU ≤ (j : ℕ) ∧ (j : ℕ) < dV), a j
        ≤ (R1 : ℝ))
    (hthird : ∀ j : Fin N, dV ≤ (j : ℕ) → a j ≤ 0)
    (hmult : (R1 : ℝ) + 2 * (R2 : ℝ) + (S : ℝ) ≤ ∑ j, a j) :
    3 * ∑ j, a j - 2 * ((R1 : ℝ) + (R2 : ℝ) + (S : ℝ))
      ≤ ∑ j, a j ^ 2 := by
  classical
  let A := Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU)
  let B := Finset.univ.filter (fun j : Fin N => dU ≤ (j : ℕ) ∧ (j : ℕ) < dV)
  let C := Finset.univ.filter (fun j : Fin N => dV ≤ (j : ℕ))
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjA hjB
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
    omega
  have hABC : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjAB hjC
    rw [Finset.mem_union] at hjAB
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hjC
    rcases hjAB with hjA | hjB
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
      omega
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
      omega
  have hcover : A ∪ B ∪ C = Finset.univ := by
    ext j
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    omega
  have hABeq : A ∪ B = Finset.univ.filter (fun j : Fin N => (j : ℕ) < dV) := by
    ext j
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hcardA : A.card = dU := by
    rw [show A = Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU) from rfl,
      Fin.card_filter_val_lt, Nat.min_eq_right (le_trans hdUV hdVN)]
  have hcardAB : (A ∪ B).card = dV := by
    rw [hABeq, Fin.card_filter_val_lt, Nat.min_eq_right hdVN]
  have hcardB_le : B.card ≤ R1 := by
    rw [Finset.card_union_of_disjoint hAB, hcardA] at hcardAB
    omega
  have hfourdim_nat : 4 * dU ≤ 4 * R2 + 2 * S := by
    omega
  have hfourdim : 4 * (dU : ℝ) ≤ 4 * (R2 : ℝ) + 2 * (S : ℝ) := by
    exact_mod_cast hfourdim_nat
  have hsqA_base :
      4 * (∑ j ∈ A, a j) - 4 * (A.card : ℝ) ≤ ∑ j ∈ A, a j ^ 2 := by
    calc
      4 * (∑ j ∈ A, a j) - 4 * (A.card : ℝ)
          = ∑ j ∈ A, (4 * a j - 4) := by simp [Finset.mul_sum]; ring
      _ ≤ ∑ j ∈ A, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        nlinarith [sq_nonneg (a j - 2)]
  have hsqA :
      4 * (∑ j ∈ A, a j) - 4 * (R2 : ℝ) - 2 * (S : ℝ)
        ≤ ∑ j ∈ A, a j ^ 2 := by
    rw [hcardA] at hsqA_base
    linarith
  have hsqB_base :
      2 * (∑ j ∈ B, a j) - (B.card : ℝ) ≤ ∑ j ∈ B, a j ^ 2 := by
    calc
      2 * (∑ j ∈ B, a j) - (B.card : ℝ)
          = ∑ j ∈ B, (2 * a j - 1) := by simp [Finset.mul_sum]
      _ ≤ ∑ j ∈ B, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        nlinarith [sq_nonneg (a j - 1)]
  have hcardB_real : (B.card : ℝ) ≤ (R1 : ℝ) := by exact_mod_cast hcardB_le
  have hsecondB : (∑ j ∈ B, a j) ≤ (R1 : ℝ) := hsecond
  have hsqB : 4 * (∑ j ∈ B, a j) - 3 * (R1 : ℝ)
      ≤ ∑ j ∈ B, a j ^ 2 := by
    linarith
  have hsqC : 4 * (∑ j ∈ C, a j) ≤ ∑ j ∈ C, a j ^ 2 := by
    calc
      4 * (∑ j ∈ C, a j) = ∑ j ∈ C, 4 * a j := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ C, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : dV ≤ (j : ℕ) := by simpa [C] using hj
        have ha := hthird j hj'
        nlinarith [sq_nonneg (a j)]
  have hsum (f : Fin N → ℝ) :
      ∑ j, f j = (∑ j ∈ A, f j) + (∑ j ∈ B, f j) + ∑ j ∈ C, f j := by
    rw [← hcover, Finset.sum_union hABC, Finset.sum_union hAB]
  rw [hsum a] at hmult ⊢
  rw [hsum (fun j => a j ^ 2)]
  linarith

/-- **Lower bound for the distinct elements.** -/
@[zz_tag "prop_distinct_lower"]
theorem card_lower (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m) (_hZne : Z.Nonempty) :
    (3 / 2 : ℝ) * (∑ z ∈ Z, (m z : ℝ))
        - (1 / 2 : ℝ) *
          (∑ z ∈ Z, ∑ s ∈ Z,
            (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ (Z.card : ℝ) := by
  classical
  obtain ⟨psi, hb, hsym⟩ := exists_symmetric_adapted_basis h Z m
  let a : Fin (Module.finrank ℂ (subspaceW h Z m)) → ℝ :=
    fun j => (alphaOf eta lam Z m (psi j)).re
  have hdUV : Module.finrank ℂ (subspaceU h Z m) ≤
      Module.finrank ℂ (subspaceV h Z m) :=
    Submodule.finrank_mono (subspaceU_le_subspaceV h Z m)
  have hdVN : Module.finrank ℂ (subspaceV h Z m) ≤
      Module.finrank ℂ (subspaceW h Z m) :=
    Submodule.finrank_mono (subspaceV_le_subspaceW h Z m)
  have hR1mult : ((simpleRealPart Z m).card : ℝ) =
      ∑ x ∈ simpleRealPart Z m, (m x : ℝ) := by
    calc
      ((simpleRealPart Z m).card : ℝ) =
          ∑ _x ∈ simpleRealPart Z m, (1 : ℝ) := by simp
      _ = ∑ x ∈ simpleRealPart Z m, (m x : ℝ) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        exact_mod_cast ((Finset.mem_filter.mp hx).2).2.symm
  have hR2mult : 2 * ((multipleRealPart Z m).card : ℝ) ≤
      ∑ x ∈ multipleRealPart Z m, (m x : ℝ) := by
    calc
      2 * ((multipleRealPart Z m).card : ℝ) =
          ∑ _x ∈ multipleRealPart Z m, (2 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ x ∈ multipleRealPart Z m, (m x : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        exact_mod_cast ((Finset.mem_filter.mp hx).2).2
  have hSmult : ((nonRealPart Z).card : ℝ) ≤
      ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
    calc
      ((nonRealPart Z).card : ℝ) =
          ∑ _z ∈ nonRealPart Z, (1 : ℝ) := by simp
      _ ≤ ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
        refine Finset.sum_le_sum fun z hz => ?_
        exact_mod_cast hZ.one_le z (Finset.mem_filter.mp hz).1
  have hmult : ((simpleRealPart Z m).card : ℝ)
        + 2 * ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ)
      ≤ ∑ z ∈ Z, (m z : ℝ) := by
    calc
      ((simpleRealPart Z m).card : ℝ)
            + 2 * ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ)
          ≤ (∑ x ∈ simpleRealPart Z m, (m x : ℝ))
              + (∑ x ∈ multipleRealPart Z m, (m x : ℝ))
              + ∑ z ∈ nonRealPart Z, (m z : ℝ) := by linarith
      _ = ∑ z ∈ Z, (m z : ℝ) := by
        rw [← Finset.sum_union disjoint_simpleRealPart_multipleRealPart,
          ← Finset.sum_union disjoint_realPart_nonRealPart,
          union_realPart_nonRealPart hZ]
  have htotal := sum_alphaOf_re_eq_sum_mult h hZ hb hsym
  change ∑ j, a j = ∑ z ∈ Z, (m z : ℝ) at htotal
  have hmult_a : ((simpleRealPart Z m).card : ℝ)
        + 2 * ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ)
      ≤ ∑ j, a j := by
    rw [htotal]
    exact hmult
  have hrange := three_range_distinct a hdUV hdVN
    (finrank_subspaceU_le h hZ) (finrank_subspaceV_le h Z m)
    (sum_alphaOf_re_le_card_simpleRealPart h hZ hb hsym)
    (fun j hj => alphaOf_re_nonpos h hZ hb (hsym j) hj) hmult_a
  have hbessel := sum_alphaOf_re_sq_le_integral_norm_bigF_sq_adapted h Z m hZ hb hsym
  have hmoment := sum_testKernel_sq_re_eq_integral_norm_bigF_sq h hZ
  have hcardNat : (simpleRealPart Z m).card + (multipleRealPart Z m).card
        + (nonRealPart Z).card = Z.card := by
    rw [← Finset.card_union_of_disjoint disjoint_simpleRealPart_multipleRealPart,
      ← Finset.card_union_of_disjoint disjoint_realPart_nonRealPart,
      union_realPart_nonRealPart hZ]
  have hcard : ((simpleRealPart Z m).card : ℝ)
        + ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ)
      = (Z.card : ℝ) := by exact_mod_cast hcardNat
  change 3 * (∑ j, a j) -
      2 * (((simpleRealPart Z m).card : ℝ) +
        ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ))
      ≤ ∑ j, a j ^ 2 at hrange
  change ∑ j, a j ^ 2 ≤ _ at hbessel
  rw [← hmoment] at hbessel
  linarith

end ZetaZeros
