/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Meta.Attr
public import ZetaZeros.Hilbert.AlphaExpansion.Coefficients

/-!
# Sums of the Bessel coefficients over an orthonormal family

Alternating-series bracketing; the second-range estimate for the Bessel coefficients; the
positivity of the cutoff normalising constant and the orthonormality of the tensor squares; and
the total Bessel sum.

## Main results

* `alternating_series_bracket`: partial sums of an alternating series bracket its limit.
* `sum_alphaOf_re_le_card_simpleRealPart`: the coefficients with `dim U ≤ j < dim V` sum to at
  most `|R₁|`.
* `cutoffNormaliser_pos`: the normalising constant is positive.
* `integral_tensor_square_pairing`: the tensor squares pair as the square of the inner product.
* `sum_alphaOf_re_eq_sum_mult`: over the whole basis the coefficients sum to the total
  multiplicity.
-/
@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ} {eta : ℝ → ℝ}

variable {Z : Finset ℂ} {m : ℂ → ℕ}

/-!
### Alternating series
-/

/-- **Alternating series bracketing.** The partial sums of an alternating series with antitone
terms bracket its limit: even-length sums from below, odd-length from above. -/
@[zz_tag "lem_alt_bracket"]
theorem alternating_series_bracket {a : ℕ → ℝ} (ha : Antitone a) {L : ℝ}
    (hL : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * a i)
      Filter.atTop (nhds L)) (n : ℕ) :
    (∑ i ∈ Finset.range (2 * n), (-1 : ℝ) ^ i * a i) ≤ L ∧
      L ≤ ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℝ) ^ i * a i :=
  ⟨ha.alternating_series_le_tendsto hL n, ha.tendsto_le_alternating_series hL n⟩

/-!
### Bessel input for the second-range estimate
-/

/-- The squared `L²` norm as an integral of squared pointwise norms. -/
private theorem norm_sq_eq_integral (F : L2Interval lam) :
    ‖F‖ ^ 2 = ∫ u in Set.Ioo (-lam) lam, ‖(F : ℝ → ℂ) u‖ ^ 2 := by
  have hL : (∫ u in Set.Ioo (-lam) lam,
      (F : ℝ → ℂ) u * (starRingEnd ℂ) ((F : ℝ → ℂ) u))
      = ((∫ u in Set.Ioo (-lam) lam, ‖(F : ℝ → ℂ) u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only [Complex.mul_conj, ← Complex.sq_norm]
  rw [integral_mul_conj_eq_inner F F, inner_self_eq_norm_sq_to_K] at hL
  have hcast : ((‖F‖ ^ 2 : ℝ) : ℂ)
      = ((∫ u in Set.Ioo (-lam) lam, ‖(F : ℝ → ℂ) u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact hL
  exact Complex.ofReal_inj.mp hcast

/-- At a real point the twisted function is a unit vector of `L²`. -/
theorem norm_fzL2_sq_eq_one (h : IsAdmissible lam eta) {x : ℂ} (hx : x.im = 0) :
    ‖fzL2 h x‖ ^ 2 = 1 := by
  rw [norm_sq_eq_integral]
  rw [show (∫ u in Set.Ioo (-lam) lam, ‖((fzL2 h x : L2Interval lam) : ℝ → ℂ) u‖ ^ 2)
      = ∫ u in Set.Ioo (-lam) lam, ‖fz eta x u‖ ^ 2 from
    integral_congr_ae (by filter_upwards [coeFn_fzL2 h x] with u hu; rw [hu])]
  exact integral_norm_fz_sq h hx

/-- **Orthogonality to an initial segment's span.** If the first `d` members of an orthonormal
family span `K`, then every later member is orthogonal to all of `K`. -/
private theorem inner_eq_zero_of_span_initial {N : ℕ} {psi : Fin N → L2Interval lam}
    (horth : Orthonormal ℂ psi) {d : ℕ} {K : Submodule ℂ (L2Interval lam)}
    (hspan : Submodule.span ℂ (psi '' {i | (i : ℕ) < d}) = K)
    {j : Fin N} (hj : d ≤ (j : ℕ)) :
    ∀ w ∈ K, inner ℂ (psi j) w = 0 := by
  intro w hw
  rw [← hspan] at hw
  refine inner_eq_zero_of_mem_span ?_ hw
  rintro y ⟨i, hi, rfl⟩
  have hlt : (i : ℕ) < d := hi
  refine horth.2 ?_
  intro hEq
  rw [hEq] at hj
  omega

/-- `R₁` and `R₂` are disjoint: multiplicity exactly one versus at least two. -/
theorem disjoint_simpleRealPart_multipleRealPart :
    Disjoint (simpleRealPart Z m) (multipleRealPart Z m) := by
  classical
  refine Finset.disjoint_left.mpr fun x hx1 hx2 => ?_
  have h1 : m x = 1 := ((Finset.mem_filter.mp hx1).2).2
  have h2 : 2 ≤ m x := ((Finset.mem_filter.mp hx2).2).2
  omega

/-- **The second-range estimate.** Summed over `dim U ≤ j < dim V`, the Bessel coefficients are
bounded by the number of simple real points. -/
@[zz_tag "lem_alpha_second_upper"]
theorem sum_alphaOf_re_le_card_simpleRealPart (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m)
    {psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam}
    (hb : IsAdaptedBasis h Z m psi) (hsym : ∀ j, IsSymmetricL2 (psi j)) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (Module.finrank ℂ (subspaceW h Z m)) =>
        Module.finrank ℂ (subspaceU h Z m) ≤ (j : ℕ) ∧
          (j : ℕ) < Module.finrank ℂ (subspaceV h Z m)),
      (alphaOf eta lam Z m (psi j)).re
      ≤ (simpleRealPart Z m).card := by
  classical
  set s := Finset.univ.filter (fun j : Fin (Module.finrank ℂ (subspaceW h Z m)) =>
    Module.finrank ℂ (subspaceU h Z m) ≤ (j : ℕ) ∧
      (j : ℕ) < Module.finrank ℂ (subspaceV h Z m)) with hs
  have hstep : ∀ j : Fin (Module.finrank ℂ (subspaceW h Z m)),
      Module.finrank ℂ (subspaceU h Z m) ≤ (j : ℕ) →
      (alphaOf eta lam Z m (psi j)).re
        ≤ ∑ x ∈ simpleRealPart Z m, ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 := by
    intro j hj
    have hU := inner_eq_zero_of_span_initial hb.orthonormal hb.span_U hj
    have hf2 : ∀ x ∈ multipleRealPart Z m,
        (∫ u in Set.Ioo (-lam) lam,
          fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) = 0 := by
      intro x hx
      rw [integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x)]
      exact hU _ (Submodule.subset_span (Set.mem_union_left _ ⟨x, by simpa using hx, rfl⟩))
    have hgz : ∀ z ∈ nonRealPart Z,
        (∫ u in Set.Ioo (-lam) lam,
          gz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) = 0 := by
      intro z hz
      rw [integral_mul_conj_eq_inner_of_ae (coeFn_gzL2 h z)]
      exact hU _ (Submodule.subset_span (Set.mem_union_right _ ⟨z, by simpa using hz, rfl⟩))
    have hR1 : ∀ x ∈ simpleRealPart Z m,
        ((m x : ℂ) * (∫ u in Set.Ioo (-lam) lam,
          fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2).re
        = ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 := by
      intro x hx
      have hm : m x = 1 := ((Finset.mem_filter.mp hx).2).2
      have hxre : x.im = 0 := ((Finset.mem_filter.mp hx).2).1
      have hbridge := integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x) (psi j)
      have hIim : (inner ℂ (psi j) (fzL2 h x) : ℂ).im = 0 := by
        exact inner_symmetricL2_im_eq_zero (hsym j) (fzL2_mem_symmetricSubspace h hxre)
      rw [hm, hbridge, Complex.sq_norm, Complex.normSq_apply]
      simp only [Nat.cast_one, one_mul, sq, Complex.mul_re, hIim]
      ring
    have hR2 : ∑ x ∈ multipleRealPart Z m,
        ((m x : ℂ) * (∫ u in Set.Ioo (-lam) lam,
          fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2).re = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [hf2 x hx]
      simp
    have hSneg : ∑ z ∈ nonRealPart Z,
        ((m z : ℂ) * ((∫ u in Set.Ioo (-lam) lam,
            gz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2
          - (∫ u in Set.Ioo (-lam) lam,
            hz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2)).re ≤ 0 := by
      refine Finset.sum_nonpos fun z hzmem => ?_
      rw [hgz z hzmem]
      set I := ∫ u in Set.Ioo (-lam) lam,
        hz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u) with hIdef
      have hIre : I = (I.re : ℂ) :=
        Complex.ext rfl (by
          simp only [hIdef, integral_mul_conj_eq_inner_of_ae (coeFn_hzL2 h z)]
          exact inner_symmetricL2_im_eq_zero (hsym j) (hzL2_mem_symmetricSubspace h z))
      have hterm : (m z : ℂ) * ((0 : ℂ) ^ 2 - (I.re : ℂ) ^ 2)
          = ((-((m z : ℝ) * I.re ^ 2) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hIre, hterm, Complex.ofReal_re]
      have hnn : (0 : ℝ) ≤ (m z : ℝ) * I.re ^ 2 := by positivity
      linarith
    rw [alphaOf_eq h hZ, Complex.add_re, Complex.re_sum, Complex.re_sum,
      Finset.sum_union disjoint_simpleRealPart_multipleRealPart,
      Finset.sum_congr rfl hR1]
    linarith
  calc ∑ j ∈ s, (alphaOf eta lam Z m (psi j)).re
      ≤ ∑ j ∈ s, ∑ x ∈ simpleRealPart Z m, ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 :=
        Finset.sum_le_sum fun j hj => hstep j ((Finset.mem_filter.mp hj).2).1
    _ = ∑ x ∈ simpleRealPart Z m, ∑ j ∈ s, ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 :=
        Finset.sum_comm
    _ ≤ ∑ _x ∈ simpleRealPart Z m, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hxre : x.im = 0 := ((Finset.mem_filter.mp hx).2).1
        have hbessel := hb.orthonormal.sum_inner_products_le (s := s) (fzL2 h x)
        rw [norm_fzL2_sq_eq_one h hxre] at hbessel
        exact hbessel
    _ = (simpleRealPart Z m).card := by simp

/-!
### The cutoff normalising constant
-/

/-- The extremal test function is non-negative everywhere: positive on `[-1/2, 1/2]` and zero
off it. -/
theorem extremalTest_nonneg (x : ℝ) : 0 ≤ extremalTest x := by
  rcases le_or_gt |x| (1 / 2) with hx | hx
  · exact (extremalTest_pos hx).le
  · have hz : extremalTest x = 0 := by rw [extremalTest, ite_eq_right (not_le.mpr hx)]
    exact hz.ge

/-- **The normalising constant is positive.** The integrand `ψ²f₀` is non-negative, and on
`|x| ≤ 1/2 - δ` it equals `f₀ > 0`, a set of positive measure. -/
@[zz_tag "lem_normaliser_pos"]
theorem cutoffNormaliser_pos {delta : ℝ} (hd : 0 < delta) (hd4 : delta < 1 / 4) {psi : ℝ → ℝ}
    (hpsi : IsCutoff delta psi) : 0 < cutoffNormaliser psi := by
  have hzero : ∀ x ∉ Set.Icc (-(1/2) : ℝ) (1/2), psi x ^ 2 * extremalTest x = 0 := by
    intro x hx
    have h : 1 / 2 ≤ |x| := by
      by_contra hlt
      exact hx (Set.mem_Icc.mpr (abs_le.mp (le_of_lt (not_le.mp hlt))))
    rw [hpsi.support x h]
    ring
  have hcont : ContinuousOn (fun x => psi x ^ 2 * extremalTest x)
      (Set.Icc (-(1/2) : ℝ) (1/2)) := by
    have hG : Continuous fun x : ℝ => psi x ^ 2 *
        (Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))) :=
      (hpsi.smooth.continuous.pow 2).mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).div_const _)
    refine hG.continuousOn.congr ?_
    intro x hx
    have hx' : |x| ≤ 1 / 2 := abs_le.mpr (Set.mem_Icc.mp hx)
    change psi x ^ 2 * extremalTest x
        = psi x ^ 2 * (Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)))
    rw [extremalTest, ite_eq_left hx']
  have hint : MeasureTheory.IntegrableOn (fun x => psi x ^ 2 * extremalTest x)
      (Set.Icc (-(1/2) : ℝ) (1/2)) := hcont.integrableOn_Icc
  have hnonneg : (0 : ℝ → ℝ)
      ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (-(1/2) : ℝ) (1/2))]
      fun x => psi x ^ 2 * extremalTest x :=
    Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (extremalTest_nonneg x)
  rw [cutoffNormaliser, ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hhalf : (0 : ℝ) < 1 / 2 - delta := by linarith
  have hsub : Set.Ioo (-(1/2 - delta)) (1/2 - delta)
      ⊆ Function.support (fun x => psi x ^ 2 * extremalTest x)
        ∩ Set.Icc (-(1/2) : ℝ) (1/2) := by
    intro x hx
    have habs : |x| ≤ 1 / 2 - delta := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    have hx12 : |x| ≤ 1 / 2 := by linarith
    refine ⟨?_, Set.mem_Icc.mpr (abs_le.mp hx12)⟩
    have h1 : psi x = 1 := hpsi.eq_one x habs
    have h2 : 0 < extremalTest x := extremalTest_pos hx12
    simp only [Function.mem_support, ne_eq, h1, one_pow, one_mul]
    exact ne_of_gt h2
  have hvol : 0 < MeasureTheory.volume (Set.Ioo (-(1/2 - delta)) (1/2 - delta)) := by
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]
    linarith
  exact lt_of_lt_of_le hvol (MeasureTheory.measure_mono hsub)

/-- **Parseval at elements of the span.** For a finite orthonormal family and an element of its
span, the squared norm is the sum of the squared norms of the inner products with the family. -/
theorem sum_sq_norm_inner_eq_norm_sq_of_mem_span {N : ℕ} {psi : Fin N → L2Interval lam}
    (horth : Orthonormal ℂ psi) {x : L2Interval lam}
    (hx : x ∈ Submodule.span ℂ (Set.range psi)) :
    ∑ j, ‖inner ℂ (psi j) x‖ ^ 2 = ‖x‖ ^ 2 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  subst hc
  simp only [horth.inner_right_fintype c]
  have hself : (inner ℂ (∑ j, c j • psi j) (∑ j, c j • psi j) : ℂ)
      = ((∑ j, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
    rw [horth.inner_sum c c Finset.univ]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
  have hre : RCLike.re (inner ℂ (∑ j, c j • psi j) (∑ j, c j • psi j))
      = ‖∑ j, c j • psi j‖ ^ 2 := inner_self_eq_norm_sq _
  rw [hself] at hre
  simpa [← Complex.ofReal_pow] using hre

/-- **The tensor squares pair as the square of the inner product**, hence are orthonormal in
`L²(I²)` when the family is orthonormal. -/
@[zz_tag "lem_Psi_orthonormal"]
theorem integral_tensor_square_pairing {lam : ℝ} {ι : Type*} [DecidableEq ι]
    (psi : ι → Lp ℂ 2 (volume.restrict (Set.Ioo (-lam) lam)))
    (h : Orthonormal ℂ psi) (j l : ι) :
    (∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        ((psi j : ℝ → ℂ) u * (psi j : ℝ → ℂ) v) *
          (starRingEnd ℂ) ((psi l : ℝ → ℂ) u * (psi l : ℝ → ℂ) v))
      = if j = l then 1 else 0 := by
  let s : Set ℝ := Set.Ioo (-lam) lam
  let μ : Measure ℝ := volume.restrict s
  let a : ℝ → ℂ := fun x => (psi j : ℝ → ℂ) x * (starRingEnd ℂ) ((psi l : ℝ → ℂ) x)
  have ha : ∫ x, a x ∂μ = (if j = l then 1 else 0 : ℂ) := by
    have hij := (orthonormal_iff_ite.mp h) l j
    rw [MeasureTheory.L2.inner_def] at hij
    simpa [a, μ, RCLike.inner_apply', mul_comm, eq_comm] using hij
  change ∫ u, ∫ v, ((psi j : ℝ → ℂ) u * (psi j : ℝ → ℂ) v) *
          (starRingEnd ℂ) ((psi l : ℝ → ℂ) u * (psi l : ℝ → ℂ) v) ∂μ ∂μ =
      (if j = l then 1 else 0 : ℂ)
  calc
    ∫ u, ∫ v, ((psi j : ℝ → ℂ) u * (psi j : ℝ → ℂ) v) *
          (starRingEnd ℂ) ((psi l : ℝ → ℂ) u * (psi l : ℝ → ℂ) v) ∂μ ∂μ
        = ∫ u, ∫ v, a u * a v ∂μ ∂μ := by
            simp [a, mul_assoc, mul_left_comm, mul_comm]
    _ = ∫ u, a u * (∫ v, a v ∂μ) ∂μ := by
            simp [MeasureTheory.integral_const_mul]
    _ = (∫ u, a u ∂μ) * (∫ v, a v ∂μ) := by
            simp [MeasureTheory.integral_mul_const]
    _ = (if j = l then 1 else 0 : ℂ) := by
            rw [ha]
            by_cases h_eq : j = l <;> simp [h_eq]

/-!
### The total Bessel sum
-/

/-- `gzL2` has the squared norm of `gz`. -/
private theorem norm_gzL2_sq (h : IsAdmissible lam eta) (z : ℂ) :
    ‖gzL2 h z‖ ^ 2 = ∫ u in Set.Ioo (-lam) lam, ‖gz eta z u‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  exact integral_congr_ae (by filter_upwards [coeFn_gzL2 h z] with u hu; rw [hu])

/-- `hzL2` has the squared norm of `hz`. -/
private theorem norm_hzL2_sq (h : IsAdmissible lam eta) (z : ℂ) :
    ‖hzL2 h z‖ ^ 2 = ∫ u in Set.Ioo (-lam) lam, ‖hz eta z u‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  exact integral_congr_ae (by filter_upwards [coeFn_hzL2 h z] with u hu; rw [hu])

/-- `‖gzL2 z‖² - ‖hzL2 z‖² = 1`. -/
theorem norm_gzL2_sq_sub_norm_hzL2_sq (h : IsAdmissible lam eta) (z : ℂ) :
    ‖gzL2 h z‖ ^ 2 - ‖hzL2 h z‖ ^ 2 = 1 := by
  rw [norm_gzL2_sq, norm_hzL2_sq]
  exact integral_norm_gz_sq_sub_integral_norm_hz_sq h z

/-- The real part of a natural multiple of the square of a real complex number. -/
theorem natCast_mul_sq_re {w : ℂ} (hw : w.im = 0) (n : ℕ) :
    ((n : ℂ) * w ^ 2).re = (n : ℝ) * ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sq, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, hw]
  ring

/-- **The total Bessel sum.** Over the whole basis the coefficients sum to the total
multiplicity. -/
@[zz_tag "lem_alpha_sum_total"]
theorem sum_alphaOf_re_eq_sum_mult (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m)
    {psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam}
    (hb : IsAdaptedBasis h Z m psi) (hsym : ∀ j, IsSymmetricL2 (psi j)) :
    ∑ j, (alphaOf eta lam Z m (psi j)).re = ∑ z ∈ Z, (m z : ℝ) := by
  classical
  have hmemW : ∀ y ∈ (fzL2 h '' ((simpleRealPart Z m ∪ multipleRealPart Z m : Finset ℂ) : Set ℂ))
      ∪ (gzL2 h '' (nonRealPart Z : Set ℂ)) ∪ (hzL2 h '' (nonRealPart Z : Set ℂ)),
      y ∈ Submodule.span ℂ (Set.range psi) := by
    intro y hy
    rw [hb.span_W, subspaceW]
    exact Submodule.subset_span hy
  have hfz : ∀ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
      fzL2 h x ∈ Submodule.span ℂ (Set.range psi) := fun x hx =>
    hmemW _ (Set.mem_union_left _ (Set.mem_union_left _ ⟨x, by simpa using hx, rfl⟩))
  have hgz : ∀ z ∈ nonRealPart Z, gzL2 h z ∈ Submodule.span ℂ (Set.range psi) := fun z hz =>
    hmemW _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨z, by simpa using hz, rfl⟩))
  have hhz : ∀ z ∈ nonRealPart Z, hzL2 h z ∈ Submodule.span ℂ (Set.range psi) := fun z hz =>
    hmemW _ (Set.mem_union_right _ ⟨z, by simpa using hz, rfl⟩)
  have hterm : ∀ j,
      (alphaOf eta lam Z m (psi j)).re
        = (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
            (m x : ℝ) * ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2)
          + ∑ z ∈ nonRealPart Z, (m z : ℝ) *
              (‖inner ℂ (psi j) (gzL2 h z)‖ ^ 2 - ‖inner ℂ (psi j) (hzL2 h z)‖ ^ 2) := by
    intro j
    rw [alphaOf_eq h hZ, Complex.add_re, Complex.re_sum, Complex.re_sum]
    congr 1
    · refine Finset.sum_congr rfl fun x hx => ?_
      have hxre : x.im = 0 := by
        rcases Finset.mem_union.mp hx with hx' | hx'
        · exact ((Finset.mem_filter.mp hx').2).1
        · exact ((Finset.mem_filter.mp hx').2).1
      rw [integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x)]
      refine natCast_mul_sq_re ?_ _
      exact inner_symmetricL2_im_eq_zero (hsym j) (fzL2_mem_symmetricSubspace h hxre)
    · refine Finset.sum_congr rfl fun z _ => ?_
      have hgim : (inner ℂ (psi j) (gzL2 h z) : ℂ).im = 0 := by
        exact inner_symmetricL2_im_eq_zero (hsym j) (gzL2_mem_symmetricSubspace h z)
      have hhim : (inner ℂ (psi j) (hzL2 h z) : ℂ).im = 0 := by
        exact inner_symmetricL2_im_eq_zero (hsym j) (hzL2_mem_symmetricSubspace h z)
      rw [integral_mul_conj_eq_inner_of_ae (coeFn_gzL2 h z),
        integral_mul_conj_eq_inner_of_ae (coeFn_hzL2 h z)]
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im, sq,
        Complex.natCast_re, Complex.natCast_im, hgim, hhim]
      ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := nonRealPart Z)]
  have hone : ∀ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
      ∑ j, (m x : ℝ) * ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 = (m x : ℝ) := by
    intro x hx
    have hxre : x.im = 0 := by
      rcases Finset.mem_union.mp hx with hx' | hx'
      · exact ((Finset.mem_filter.mp hx').2).1
      · exact ((Finset.mem_filter.mp hx').2).1
    rw [← Finset.mul_sum,
      sum_sq_norm_inner_eq_norm_sq_of_mem_span hb.orthonormal (hfz x hx),
      norm_fzL2_sq_eq_one h hxre, mul_one]
  have htwo : ∀ z ∈ nonRealPart Z,
      ∑ j, (m z : ℝ) *
        (‖inner ℂ (psi j) (gzL2 h z)‖ ^ 2 - ‖inner ℂ (psi j) (hzL2 h z)‖ ^ 2) = (m z : ℝ) := by
    intro z hz
    rw [← Finset.mul_sum, Finset.sum_sub_distrib,
      sum_sq_norm_inner_eq_norm_sq_of_mem_span hb.orthonormal (hgz z hz),
      sum_sq_norm_inner_eq_norm_sq_of_mem_span hb.orthonormal (hhz z hz),
      norm_gzL2_sq_sub_norm_hzL2_sq h z, mul_one]
  rw [Finset.sum_congr rfl hone, Finset.sum_congr rfl htwo,
    ← Finset.sum_union disjoint_realPart_nonRealPart, union_realPart_nonRealPart hZ]

end ZetaZeros
