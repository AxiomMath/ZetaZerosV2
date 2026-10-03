/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Hilbert.Dimensions
public import ZetaZeros.Hilbert.FIdentity
public import ZetaZeros.Hilbert.InnerRealL2
public import ZetaZeros.Hilbert.Integrals
public import ZetaZeros.Meta.Attr
public import ZetaZeros.Zeta.Basic
public import ZetaZeros.Zeta.OrderConj

/-!
# The Bessel coefficients: integrability, realness, and the third range

The Bessel coefficient `alphaOf` of an element of `L²((-lam, lam))` against the two-variable kernel
`bigF`: its expansion in one-variable integrals, its realness at symmetric elements, and its sign
past `dim V`; also the norm defect between the even and odd parts, and the dimension of `U`.

## Main definitions

* `alphaOf`: the Bessel coefficient of a single `L²` element.

## Main results

* `alphaCoeff_eq`: the Bessel coefficient in terms of one-variable integrals.
* `alphaCoeff_im_eq_zero`: the Bessel coefficient against a symmetric function is real.
* `alphaOf_re_nonpos`: past `dim V` the Bessel coefficient is non-positive.
* `integral_norm_gz_sq_sub_integral_norm_hz_sq`: `‖g_z‖² - ‖h_z‖² = 1`.
* `finrank_subspaceU_le`: `dim U ≤ |R₂| + |S| / 2`.
-/
@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ} {eta : ℝ → ℝ}

/-- A conjugated `L²` element is still in `L²`. -/
private theorem memLp_conj_coeFn (ψ : L2Interval lam) :
    MemLp (fun u => (starRingEnd ℂ) ((ψ : ℝ → ℂ) u)) 2
      (volume.restrict (Set.Ioo (-lam) lam)) := by
  have heq : (fun u => (starRingEnd ℂ) ((ψ : ℝ → ℂ) u)) = star (ψ : ℝ → ℂ) := by
    funext u
    rfl
  rw [heq]
  exact (Lp.memLp ψ).star

/-- A twisted function against a conjugated `L²` element is integrable: Hölder with `p = q = 2`. -/
theorem integrable_fz_mul_conj (h : IsAdmissible lam eta) (x : ℂ) (ψ : L2Interval lam) :
    Integrable (fun u => fz eta x u * (starRingEnd ℂ) ((ψ : ℝ → ℂ) u))
      (volume.restrict (Set.Ioo (-lam) lam)) :=
  (memLp_fz h x).integrable_mul (memLp_conj_coeFn ψ)

/-- The even part against a conjugated `L²` element is integrable. -/
private theorem integrable_gz_mul_conj (h : IsAdmissible lam eta) (z : ℂ) (ψ : L2Interval lam) :
    Integrable (fun u => gz eta z u * (starRingEnd ℂ) ((ψ : ℝ → ℂ) u))
      (volume.restrict (Set.Ioo (-lam) lam)) :=
  (memLp_gz h z).integrable_mul (memLp_conj_coeFn ψ)

/-- The odd part against a conjugated `L²` element is integrable. -/
private theorem integrable_hz_mul_conj (h : IsAdmissible lam eta) (z : ℂ) (ψ : L2Interval lam) :
    Integrable (fun u => hz eta z u * (starRingEnd ℂ) ((ψ : ℝ → ℂ) u))
      (volume.restrict (Set.Ioo (-lam) lam)) :=
  (memLp_hz h z).integrable_mul (memLp_conj_coeFn ψ)

/-- **The double integral of a finite sum of separable terms.** Over `(-lam, lam)²`, the integral
of `(∑ i ∈ s, c i * Φ i u * Φ i v) * (k u * k v)` is `∑ i ∈ s, c i * (∫ u, Φ i u * k u) ^ 2`,
provided each `Φ i * k` is integrable. -/
theorem integral_double_finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Φ : ι → ℝ → ℂ)
    (k : ℝ → ℂ) (lam : ℝ)
    (hint : ∀ i ∈ s, Integrable (fun u => Φ i u * k u)
      (volume.restrict (Set.Ioo (-lam) lam))) :
    (∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        (∑ i ∈ s, c i * Φ i u * Φ i v) * (k u * k v))
      = ∑ i ∈ s, c i * (∫ u in Set.Ioo (-lam) lam, Φ i u * k u) ^ 2 := by
  have hstep : ∀ u : ℝ,
      (∫ v in Set.Ioo (-lam) lam, (∑ i ∈ s, c i * Φ i u * Φ i v) * (k u * k v))
        = ∑ i ∈ s, c i * Φ i u * k u * ∫ v in Set.Ioo (-lam) lam, Φ i v * k v := by
    intro u
    have hfun : (fun v => (∑ i ∈ s, c i * Φ i u * Φ i v) * (k u * k v))
        = (fun v => ∑ i ∈ s, (c i * Φ i u * k u) * (Φ i v * k v)) := by
      funext v
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfun, MeasureTheory.integral_finsetSum _ fun i hi => (hint i hi).const_mul _]
    exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
  rw [setIntegral_congr_fun measurableSet_Ioo fun u _ => hstep u]
  have hfun2 : (fun x => ∑ i ∈ s, c i * Φ i x * k x * ∫ v in Set.Ioo (-lam) lam, Φ i v * k v)
      = (fun x => ∑ i ∈ s,
          (c i * ∫ v in Set.Ioo (-lam) lam, Φ i v * k v) * (Φ i x * k x)) := by
    funext x
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun2, MeasureTheory.integral_finsetSum _ fun i hi => (hint i hi).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_const_mul, sq]
  ring

variable {Z : Finset ℂ} {m : ℂ → ℕ}

/-- **The integral of `Φ * conj Ψ` is the `L²` inner product `⟪Ψ, Φ⟫`.** -/
theorem integral_mul_conj_eq_inner (Φ Ψ : L2Interval lam) :
    (∫ u in Set.Ioo (-lam) lam, (Φ : ℝ → ℂ) u * (starRingEnd ℂ) ((Ψ : ℝ → ℂ) u))
      = inner ℂ Ψ Φ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [RCLike.inner_apply]

/-- **The Bessel coefficient in terms of one-variable integrals.** Stated for an arbitrary family
`psi`; it need not be an adapted orthonormal basis. -/
@[zz_tag "lem_alpha_expansion"]
theorem alphaCoeff_eq (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m)
    (psi : ℕ → L2Interval lam) (j : ℕ) :
    alphaCoeff eta lam Z m psi j
      = (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
          (m x : ℂ) * (∫ u in Set.Ioo (-lam) lam,
            fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2)
        + ∑ z ∈ nonRealPart Z, (m z : ℂ) *
            ((∫ u in Set.Ioo (-lam) lam,
                gz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2
              - (∫ u in Set.Ioo (-lam) lam,
                  hz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2) := by
  classical
  set c : ℂ ⊕ ℂ ⊕ ℂ → ℂ :=
    Sum.elim (fun x => (m x : ℂ)) (Sum.elim (fun z => (m z : ℂ)) fun z => -(m z : ℂ)) with hc
  set Phi : ℂ ⊕ ℂ ⊕ ℂ → ℝ → ℂ :=
    Sum.elim (fun x => fz eta x) (Sum.elim (fun z => gz eta z) fun z => hz eta z) with hPhi
  set S : Finset (ℂ ⊕ ℂ ⊕ ℂ) :=
    (simpleRealPart Z m ∪ multipleRealPart Z m).disjSum
      ((nonRealPart Z).disjSum (nonRealPart Z)) with hS
  have hint : ∀ i ∈ S, Integrable (fun u => Phi i u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u))
      (volume.restrict (Set.Ioo (-lam) lam)) := by
    rintro (x | z | z) -
    · exact integrable_fz_mul_conj h x (psi j)
    · exact integrable_gz_mul_conj h z (psi j)
    · exact integrable_hz_mul_conj h z (psi j)
  have hkernel : ∀ u v : ℝ,
      bigF eta Z m u v * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u * (psi j : ℝ → ℂ) v)
        = (∑ i ∈ S, c i * Phi i u * Phi i v)
          * ((starRingEnd ℂ) ((psi j : ℝ → ℂ) u)
              * (starRingEnd ℂ) ((psi j : ℝ → ℂ) v)) := by
    intro u v
    have hB : ∑ z ∈ nonRealPart Z,
          (m z : ℂ) * (gz eta z u * gz eta z v - hz eta z u * hz eta z v)
        = (∑ z ∈ nonRealPart Z, (m z : ℂ) * gz eta z u * gz eta z v)
          + ∑ z ∈ nonRealPart Z, -(m z : ℂ) * hz eta z u * hz eta z v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [bigF_eq hZ, map_mul, hB, hS, Finset.sum_disjSum, Finset.sum_disjSum]
    simp only [hc, hPhi, Sum.elim_inl, Sum.elim_inr]
  calc alphaCoeff eta lam Z m psi j
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          (∑ i ∈ S, c i * Phi i u * Phi i v)
            * ((starRingEnd ℂ) ((psi j : ℝ → ℂ) u)
                * (starRingEnd ℂ) ((psi j : ℝ → ℂ) v)) := by
        simp only [alphaCoeff, hkernel]
    _ = ∑ i ∈ S, c i * (∫ u in Set.Ioo (-lam) lam,
          Phi i u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2 :=
        integral_double_finsetSum S c Phi
          (fun u => (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) lam hint
    _ = _ := by
        rw [hS, Finset.sum_disjSum, Finset.sum_disjSum]
        simp only [hc, hPhi, Sum.elim_inl, Sum.elim_inr]
        rw [← Finset.sum_add_distrib]
        refine congrArg (_ + ·) (Finset.sum_congr rfl fun z _ => by ring)

/-- The Bessel coefficient of a single `L²` element. -/
noncomputable def alphaOf (eta : ℝ → ℝ) (lam : ℝ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (psi : L2Interval lam) : ℂ :=
  ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
    bigF eta Z m u v * (starRingEnd ℂ) ((psi : ℝ → ℂ) u * (psi : ℝ → ℂ) v)

/-- `alphaCoeff` is `alphaOf` at the indexed member. -/
private theorem alphaCoeff_eq_alphaOf (psi : ℕ → L2Interval lam) (j : ℕ) :
    alphaCoeff eta lam Z m psi j = alphaOf eta lam Z m (psi j) :=
  rfl

/-- The pairing of two symmetric functions over the symmetric interval is real. -/
private theorem integral_symmetric_im_eq_zero {Φ₁ Φ₂ : ℝ → ℂ} (h1 : IsSymmetric Φ₁) (h2 :
    IsSymmetric Φ₂)
    (lam : ℝ) :
    (∫ u in Set.Ioo (-lam) lam, Φ₁ u * (starRingEnd ℂ) (Φ₂ u)).im = 0 := by
  refine Complex.conj_eq_iff_im.mp ?_
  rw [← integral_conj]
  have hpt : ∀ u : ℝ, (starRingEnd ℂ) (Φ₁ u * (starRingEnd ℂ) (Φ₂ u))
      = Φ₁ (-u) * (starRingEnd ℂ) (Φ₂ (-u)) := by
    intro u
    rw [map_mul, Complex.conj_conj, h1 u]
    congr 1
    rw [h2 (-u), neg_neg]
  calc ∫ u in Set.Ioo (-lam) lam, (starRingEnd ℂ) (Φ₁ u * (starRingEnd ℂ) (Φ₂ u))
      = ∫ u in Set.Ioo (-lam) lam, Φ₁ (-u) * (starRingEnd ℂ) (Φ₂ (-u)) :=
        integral_congr_ae (.of_forall hpt)
    _ = ∫ u in Set.Ioo (-lam) lam, Φ₁ u * (starRingEnd ℂ) (Φ₂ u) :=
        integral_comp_neg_Ioo (fun v => Φ₁ v * (starRingEnd ℂ) (Φ₂ v)) lam

/-- **The Bessel coefficients are real.** The coefficient against a symmetric function is real. -/
@[zz_tag "lem_alpha_real"]
theorem alphaCoeff_im_eq_zero (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m)
    (psi : ℕ → L2Interval lam) (j : ℕ) (hpsi : IsSymmetric ((psi j : ℝ → ℂ))) :
    (alphaCoeff eta lam Z m psi j).im = 0 := by
  classical
  rw [alphaCoeff_eq h hZ psi j, Complex.add_im, Complex.im_sum, Complex.im_sum]
  have hreal : ∀ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m, x.im = 0 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ((Finset.mem_filter.mp hx).2).1
    · exact ((Finset.mem_filter.mp hx).2).1
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro z _
    have hg := integral_symmetric_im_eq_zero (isSymmetric_gz h z) hpsi lam
    have hh := integral_symmetric_im_eq_zero (isSymmetric_hz h z) hpsi lam
    simp [Complex.mul_im, Complex.sub_im, sq, hg, hh]
  · intro x hx
    have hf := integral_symmetric_im_eq_zero (isSymmetric_fz h (hreal x hx)) hpsi lam
    simp [Complex.mul_im, sq, hf]

/-- Orthogonality to a spanning set extends to the span. -/
theorem inner_eq_zero_of_mem_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Set E} {v w : E} (hv : ∀ y ∈ s, inner ℂ v y = 0) (hw : w ∈ Submodule.span ℂ s) :
    inner ℂ v w = 0 := by
  induction hw using Submodule.span_induction with
  | mem y hy => exact hv y hy
  | zero => exact inner_zero_right v
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- `fzL2` agrees a.e. with `fz`. -/
theorem coeFn_fzL2 (h : IsAdmissible lam eta) (z : ℂ) :
    (fzL2 h z : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo (-lam) lam)] fz eta z :=
  MemLp.coeFn_toLp (memLp_fz h z)

/-- `gzL2` agrees a.e. with `gz`. -/
theorem coeFn_gzL2 (h : IsAdmissible lam eta) (z : ℂ) :
    (gzL2 h z : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo (-lam) lam)] gz eta z :=
  MemLp.coeFn_toLp (memLp_gz h z)

/-- `hzL2` agrees a.e. with `hz`. -/
theorem coeFn_hzL2 (h : IsAdmissible lam eta) (z : ℂ) :
    (hzL2 h z : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo (-lam) lam)] hz eta z :=
  MemLp.coeFn_toLp (memLp_hz h z)

/-- Pointwise symmetry of a representing function gives a.e. symmetry of the `L²` element. -/
private theorem isSymmetricL2_of_isSymmetric {F : L2Interval lam} {phi : ℝ → ℂ}
    (hF : (F : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo (-lam) lam)] phi)
    (hphi : IsSymmetric phi) : IsSymmetricL2 F := by
  filter_upwards [hF, ae_restrict_Ioo_neg hF] with u h1 h2
  rw [h1, h2, hphi u]

/-- At a real point the twisted function is a symmetric `L²` element. -/
theorem fzL2_mem_symmetricSubspace (h : IsAdmissible lam eta) {x : ℂ} (hx : x.im = 0) :
    fzL2 h x ∈ symmetricSubspace lam :=
  isSymmetricL2_of_isSymmetric (coeFn_fzL2 h x) (isSymmetric_fz h hx)

/-- The even part is a symmetric `L²` element. -/
theorem gzL2_mem_symmetricSubspace (h : IsAdmissible lam eta) (z : ℂ) :
    gzL2 h z ∈ symmetricSubspace lam :=
  isSymmetricL2_of_isSymmetric (coeFn_gzL2 h z) (isSymmetric_gz h z)

/-- The odd part is a symmetric `L²` element. -/
theorem hzL2_mem_symmetricSubspace (h : IsAdmissible lam eta) (z : ℂ) :
    hzL2 h z ∈ symmetricSubspace lam :=
  isSymmetricL2_of_isSymmetric (coeFn_hzL2 h z) (isSymmetric_hz h z)

/-- Inner products of symmetric `L²` elements are real. -/
theorem inner_symmetricL2_im_eq_zero {F G : L2Interval lam}
    (hF : IsSymmetricL2 F) (hG : IsSymmetricL2 G) :
    (inner ℂ F G : ℂ).im = 0 := by
  refine Complex.conj_eq_iff_im.mp ?_
  rw [MeasureTheory.L2.inner_def, ← integral_conj]
  calc ∫ u in Set.Ioo (-lam) lam,
        (starRingEnd ℂ) (inner ℂ ((F : ℝ → ℂ) u) ((G : ℝ → ℂ) u))
      = ∫ u in Set.Ioo (-lam) lam, (F : ℝ → ℂ) u * (starRingEnd ℂ) ((G : ℝ → ℂ) u) := by
        refine integral_congr_ae (.of_forall fun u => ?_)
        simp only [RCLike.inner_apply, map_mul, Complex.conj_conj]
        ring
    _ = ∫ u in Set.Ioo (-lam) lam, (F : ℝ → ℂ) u * (G : ℝ → ℂ) (-u) := by
        refine integral_congr_ae ?_
        filter_upwards [hG] with u hu
        rw [hu]
    _ = ∫ u in Set.Ioo (-lam) lam, (F : ℝ → ℂ) (-u) * (G : ℝ → ℂ) u := by
        have h := integral_comp_neg_Ioo
          (fun v => (F : ℝ → ℂ) v * (G : ℝ → ℂ) (-v)) lam
        simp only [neg_neg] at h
        exact h.symm
    _ = ∫ u in Set.Ioo (-lam) lam, inner ℂ ((F : ℝ → ℂ) u) ((G : ℝ → ℂ) u) := by
        refine integral_congr_ae ?_
        filter_upwards [hF] with u hu
        simp only [RCLike.inner_apply, ← hu]
        ring

/-- The integral of `Φ * conj ψ`, for a function `Φ` agreeing a.e. with an `L²` element, is the
inner product `⟪ψ, Φ⟫`. -/
theorem integral_mul_conj_eq_inner_of_ae {Φ : ℝ → ℂ} {F : L2Interval lam}
    (hF : (F : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo (-lam) lam)] Φ) (ψ : L2Interval lam) :
    (∫ u in Set.Ioo (-lam) lam, Φ u * (starRingEnd ℂ) ((ψ : ℝ → ℂ) u)) = inner ℂ ψ F := by
  rw [← integral_mul_conj_eq_inner F ψ]
  refine integral_congr_ae ?_
  filter_upwards [hF] with u hu
  rw [hu]

/-- The Bessel coefficient of a single `L²` element in terms of one-variable integrals. -/
theorem alphaOf_eq (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (φ : L2Interval lam) :
    alphaOf eta lam Z m φ
      = (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
          (m x : ℂ) * (∫ u in Set.Ioo (-lam) lam,
            fz eta x u * (starRingEnd ℂ) ((φ : ℝ → ℂ) u)) ^ 2)
        + ∑ z ∈ nonRealPart Z, (m z : ℂ) *
            ((∫ u in Set.Ioo (-lam) lam,
                gz eta z u * (starRingEnd ℂ) ((φ : ℝ → ℂ) u)) ^ 2
              - (∫ u in Set.Ioo (-lam) lam,
                  hz eta z u * (starRingEnd ℂ) ((φ : ℝ → ℂ) u)) ^ 2) :=
  alphaCoeff_eq h hZ (fun _ => φ) 0

/-- A Bessel coefficient against a symmetric `L²` element is real. -/
theorem alphaOf_im_eq_zero_l2 (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m) {φ : L2Interval lam}
    (hsym : IsSymmetricL2 φ) :
    (alphaOf eta lam Z m φ).im = 0 := by
  classical
  rw [alphaOf_eq h hZ, Complex.add_im, Complex.im_sum, Complex.im_sum]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro z _
    have hg : (inner ℂ φ (gzL2 h z) : ℂ).im = 0 :=
      inner_symmetricL2_im_eq_zero hsym (gzL2_mem_symmetricSubspace h z)
    have hh : (inner ℂ φ (hzL2 h z) : ℂ).im = 0 :=
      inner_symmetricL2_im_eq_zero hsym (hzL2_mem_symmetricSubspace h z)
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_gzL2 h z),
      integral_mul_conj_eq_inner_of_ae (coeFn_hzL2 h z)]
    simp [Complex.mul_im, Complex.sub_im, sq, hg, hh]
  · intro x hx
    have hxre : x.im = 0 := by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ((Finset.mem_filter.mp hx).2).1
      · exact ((Finset.mem_filter.mp hx).2).1
    have hf : (inner ℂ φ (fzL2 h x) : ℂ).im = 0 :=
      inner_symmetricL2_im_eq_zero hsym (fzL2_mem_symmetricSubspace h hxre)
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x)]
    simp [Complex.mul_im, sq, hf]

/-- **Past `dim V` the Bessel coefficient is non-positive.** -/
@[zz_tag "lem_alpha_third_nonpos"]
theorem alphaOf_re_nonpos (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m)
    {psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam}
    (hb : IsAdaptedBasis h Z m psi) {j : Fin (Module.finrank ℂ (subspaceW h Z m))}
    (hsym : IsSymmetricL2 (psi j))
    (hj : Module.finrank ℂ (subspaceV h Z m) ≤ (j : ℕ)) :
    (alphaOf eta lam Z m (psi j)).re ≤ 0 := by
  classical
  have hV : ∀ w ∈ subspaceV h Z m, inner ℂ (psi j) w = 0 := by
    intro w hw
    rw [← hb.span_V] at hw
    refine inner_eq_zero_of_mem_span ?_ hw
    rintro y ⟨i, hi, rfl⟩
    have hlt : (i : ℕ) < Module.finrank ℂ (subspaceV h Z m) := hi
    refine hb.orthonormal.2 ?_
    intro hEq
    rw [hEq] at hj
    omega
  have hf : ∀ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
      (∫ u in Set.Ioo (-lam) lam, fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) = 0 := by
    intro x hx
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x)]
    exact hV _ (Submodule.subset_span (Set.mem_union_left _ ⟨x, by simpa using hx, rfl⟩))
  have hg : ∀ z ∈ nonRealPart Z,
      (∫ u in Set.Ioo (-lam) lam, gz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) = 0 := by
    intro z hz
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_gzL2 h z)]
    exact hV _ (Submodule.subset_span (Set.mem_union_right _ ⟨z, by simpa using hz, rfl⟩))
  have hA : (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
      (m x : ℂ) * (∫ u in Set.Ioo (-lam) lam,
        fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hf x hx]
    ring
  rw [alphaOf_eq h hZ, hA, zero_add, Complex.re_sum]
  refine Finset.sum_nonpos fun z hzmem => ?_
  rw [hg z hzmem]
  set I := ∫ u in Set.Ioo (-lam) lam,
    hz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u) with hIdef
  have hIre : I = (I.re : ℂ) :=
    Complex.ext rfl (by
      simp only [hIdef, integral_mul_conj_eq_inner_of_ae (coeFn_hzL2 h z)]
      exact inner_symmetricL2_im_eq_zero hsym (hzL2_mem_symmetricSubspace h z))
  have hterm : (m z : ℂ) * ((0 : ℂ) ^ 2 - (I.re : ℂ) ^ 2)
      = ((-((m z : ℝ) * I.re ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hIre, hterm, Complex.ofReal_re]
  have hnn : (0 : ℝ) ≤ (m z : ℝ) * I.re ^ 2 := by positivity
  linarith

/-- The conjugate of a twisted function is still square-integrable. -/
private theorem memLp_conj_fz (h : IsAdmissible lam eta) (w : ℂ) :
    MemLp (fun u => (starRingEnd ℂ) (fz eta w u)) 2
      (volume.restrict (Set.Ioo (-lam) lam)) := by
  have heq : (fun u => (starRingEnd ℂ) (fz eta w u)) = star (fz eta w) := by
    funext u
    rfl
  rw [heq]
  exact (memLp_fz h w).star

/-- **The even and odd parts differ by exactly one in squared `L²` norm.** The kernel at `0` is
`1`, and it is the pairing of `f_z` against `f_{conj z}`, whose real part is
`‖g_z‖² - ‖h_z‖²`. -/
@[zz_tag "lem_g_h_norm_diff"]
theorem integral_norm_gz_sq_sub_integral_norm_hz_sq (h : IsAdmissible lam eta) (z : ℂ) :
    (∫ u in Set.Ioo (-lam) lam, ‖gz eta z u‖ ^ 2)
      - (∫ u in Set.Ioo (-lam) lam, ‖hz eta z u‖ ^ 2) = 1 := by
  have hker : (∫ u in Set.Ioo (-lam) lam,
      fz eta z u * (starRingEnd ℂ) (fz eta ((starRingEnd ℂ) z) u)) = 1 := by
    have hfac := testKernel_sub_conj h z ((starRingEnd ℂ) z)
    rw [Complex.conj_conj, sub_self] at hfac
    rw [← hfac, testKernel]
    exact h.fourier_sq_zero
  have hint : Integrable
      (fun u => fz eta z u * (starRingEnd ℂ) (fz eta ((starRingEnd ℂ) z) u))
      (volume.restrict (Set.Ioo (-lam) lam)) :=
    (memLp_fz h z).integrable_mul (memLp_conj_fz h ((starRingEnd ℂ) z))
  have hnorm : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    intro w
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hpt : ∀ u : ℝ, ‖gz eta z u‖ ^ 2 - ‖hz eta z u‖ ^ 2
      = (fz eta z u * (starRingEnd ℂ) (fz eta ((starRingEnd ℂ) z) u)).re := by
    intro u
    rw [fz_eq_gz_add_I_mul_hz eta z u, fz_eq_gz_add_I_mul_hz eta ((starRingEnd ℂ) z) u]
    simp only [gz_conj, hz_conj, hnorm, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im]
    ring
  have hgi : Integrable (fun u => ‖gz eta z u‖ ^ 2)
      (volume.restrict (Set.Ioo (-lam) lam)) :=
    (memLp_two_iff_integrable_sq_norm (memLp_gz h z).aestronglyMeasurable).mp (memLp_gz h z)
  have hhi : Integrable (fun u => ‖hz eta z u‖ ^ 2)
      (volume.restrict (Set.Ioo (-lam) lam)) :=
    (memLp_two_iff_integrable_sq_norm (memLp_hz h z).aestronglyMeasurable).mp (memLp_hz h z)
  calc (∫ u in Set.Ioo (-lam) lam, ‖gz eta z u‖ ^ 2)
        - (∫ u in Set.Ioo (-lam) lam, ‖hz eta z u‖ ^ 2)
      = ∫ u in Set.Ioo (-lam) lam, (‖gz eta z u‖ ^ 2 - ‖hz eta z u‖ ^ 2) :=
        (integral_sub hgi hhi).symm
    _ = ∫ u in Set.Ioo (-lam) lam,
          (fz eta z u * (starRingEnd ℂ) (fz eta ((starRingEnd ℂ) z) u)).re :=
        integral_congr_ae (.of_forall hpt)
    _ = (∫ u in Set.Ioo (-lam) lam,
          fz eta z u * (starRingEnd ℂ) (fz eta ((starRingEnd ℂ) z) u)).re :=
        integral_re hint
    _ = 1 := by rw [hker, Complex.one_re]

/-- Conjugating the index leaves the even part unchanged as an `L²` element. -/
private theorem gzL2_conj (h : IsAdmissible lam eta) (z : ℂ) :
    gzL2 h ((starRingEnd ℂ) z) = gzL2 h z := by
  simp only [gzL2, gz_conj]

/-- Membership in the non-real support, unfolded. -/
private theorem mem_nonRealPart {z : ℂ} : z ∈ nonRealPart Z ↔ z ∈ Z ∧ z.im ≠ 0 :=
  Finset.mem_filter

/-- Conjugation is injective on the complex numbers. -/
theorem conj_injective : Function.Injective (starRingEnd ℂ) := by
  intro a b hab
  have h := congrArg (starRingEnd ℂ) hab
  simpa [Complex.conj_conj] using h

/-- Conjugation maps the non-real support to itself. -/
private theorem conj_mem_nonRealPart (hZ : IsConjInvariant Z m) {z : ℂ}
    (hz : z ∈ nonRealPart Z) : (starRingEnd ℂ) z ∈ nonRealPart Z := by
  obtain ⟨hzZ, hzim⟩ := mem_nonRealPart.mp hz
  refine mem_nonRealPart.mpr ⟨hZ.conj_mem z hzZ, ?_⟩
  rw [Complex.conj_im]
  simpa using hzim

/-- The lower half of the non-real support is exactly the conjugate image of the upper half.
Conjugation has no fixed point there, since every point has non-zero imaginary part. -/
private theorem filter_not_pos_eq_image_filter_pos (hZ : IsConjInvariant Z m) :
    ((nonRealPart Z).filter fun z => ¬ 0 < z.im)
      = ((nonRealPart Z).filter fun z => 0 < z.im).image (starRingEnd ℂ) := by
  classical
  ext w
  simp only [Finset.mem_image]
  constructor
  · intro hw
    obtain ⟨hwT, hwle⟩ := Finset.mem_filter.mp hw
    have hwim : w.im ≠ 0 := (mem_nonRealPart.mp hwT).2
    refine ⟨(starRingEnd ℂ) w, Finset.mem_filter.mpr
      ⟨conj_mem_nonRealPart hZ hwT, ?_⟩, Complex.conj_conj w⟩
    rw [Complex.conj_im]
    have hneg : w.im < 0 := lt_of_le_of_ne (not_lt.mp hwle) hwim
    linarith
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzT, hzpos⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨conj_mem_nonRealPart hZ hzT, ?_⟩
    rw [Complex.conj_im, not_lt]
    linarith

/-- The non-real support has exactly twice as many points as its upper half. -/
private theorem card_nonRealPart_eq_two_mul (hZ : IsConjInvariant Z m) :
    (nonRealPart Z).card
      = 2 * ((nonRealPart Z).filter fun z => 0 < z.im).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := nonRealPart Z) (p := fun z : ℂ => 0 < z.im)
  rw [filter_not_pos_eq_image_filter_pos hZ,
    Finset.card_image_of_injective _ conj_injective] at hsplit
  omega

/-- **The dimension of `U`.** It is spanned by one vector per multiple real point together with the
even parts at the non-real points, and conjugation identifies those in pairs, so they contribute
only half of `|S|`, which is even. -/
@[zz_tag "lem_dim_U"]
theorem finrank_subspaceU_le (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) :
    Module.finrank ℂ (subspaceU h Z m)
      ≤ (multipleRealPart Z m).card + (nonRealPart Z).card / 2 := by
  classical
  set P := (nonRealPart Z).filter fun z => 0 < z.im with hP
  have hTsplit : nonRealPart Z = P ∪ P.image (starRingEnd ℂ) := by
    rw [hP, ← filter_not_pos_eq_image_filter_pos hZ, Finset.filter_union_filter_not_eq]
  have himg : gzL2 h '' (nonRealPart Z : Set ℂ) = gzL2 h '' (P : Set ℂ) := by
    rw [hTsplit, Finset.coe_union, Set.image_union, Finset.coe_image, Set.image_image]
    simp only [gzL2_conj]
    rw [Set.union_self]
  have hsup : subspaceU h Z m
      = Submodule.span ℂ (fzL2 h '' (multipleRealPart Z m : Set ℂ))
        ⊔ Submodule.span ℂ (gzL2 h '' (P : Set ℂ)) := by
    rw [subspaceU, ← Submodule.span_union, himg]
  have : FiniteDimensional ℂ
      (Submodule.span ℂ (fzL2 h '' (multipleRealPart Z m : Set ℂ))) :=
    FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet _).image _)
  have : FiniteDimensional ℂ (Submodule.span ℂ (gzL2 h '' (P : Set ℂ))) :=
    FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet _).image _)
  have hle : Module.finrank ℂ (subspaceU h Z m)
      ≤ Module.finrank ℂ (Submodule.span ℂ (fzL2 h '' (multipleRealPart Z m : Set ℂ)))
        + Module.finrank ℂ (Submodule.span ℂ (gzL2 h '' (P : Set ℂ))) := by
    rw [hsup]
    exact finrank_sup_le _ _
  have hf : Module.finrank ℂ
      (Submodule.span ℂ (fzL2 h '' (multipleRealPart Z m : Set ℂ)))
      ≤ (multipleRealPart Z m).card := by
    rw [show fzL2 h '' (multipleRealPart Z m : Set ℂ)
        = (((multipleRealPart Z m).image (fzL2 h) : Finset (L2Interval lam)) : Set _) by
      rw [Finset.coe_image]]
    exact le_trans (finrank_span_finset_le_card _) Finset.card_image_le
  have hg : Module.finrank ℂ (Submodule.span ℂ (gzL2 h '' (P : Set ℂ))) ≤ P.card := by
    rw [show gzL2 h '' (P : Set ℂ)
        = ((P.image (gzL2 h) : Finset (L2Interval lam)) : Set _) by rw [Finset.coe_image]]
    exact le_trans (finrank_span_finset_le_card _) Finset.card_image_le
  have hhalf := card_nonRealPart_eq_two_mul (m := m) hZ
  rw [← hP] at hhalf
  omega

end ZetaZeros
