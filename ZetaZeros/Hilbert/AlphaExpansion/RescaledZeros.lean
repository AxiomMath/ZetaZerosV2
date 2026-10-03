/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Meta.Attr
public import ZetaZeros.Hilbert.AlphaExpansion.AdaptedBasis

/-!
# The rescaled zeros, their counts, and the normalised test function

Every non-trivial zero has multiplicity at least one; the rescaling is a multiplicity-preserving
bijection onto `rescaledZerosFinset`, so the counts of zeros transfer to the rescaled multiset;
and the normalised test function has total mass one.

## Main results

* `one_le_zeroMultiplicity`: every non-trivial zero has multiplicity at least one.
* `sum_rescaledMult_eq_zeroCount`: the rescaled zeros carry the counted total.
* `card_rescaledZerosFinset_eq_distinctZeroCount`: the rescaled zeros carry the distinct count.
* `card_simpleRealPart_rescaled_eq_simpleOnLineCount`: the rescaled zeros carry the
  simple-on-line count.
* `integral_cutoffTestSq`: the normalised test function has total mass one.
-/
@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ} {eta : ℝ → ℝ}

variable {Z : Finset ℂ} {m : ℂ → ℕ}

/-!
### Multiplicity of a non-trivial zero
-/

/-- **Every non-trivial zero has multiplicity at least one.** -/
@[zz_tag "lem_mult_pos"]
theorem one_le_zeroMultiplicity {T : ℝ} {rho : ℂ} (hrho : rho ∈ nontrivialZeros T) :
    1 ≤ zeroMultiplicity rho := by
  obtain ⟨hzero, -, hre1, -, -⟩ := hrho
  have hne1 : rho ≠ 1 := by
    intro hEq
    rw [hEq] at hre1
    simp at hre1
  have hanaOn : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ := by
    intro w hw
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_ne.mem_nhds hw] with v hv
    exact differentiableAt_riemannZeta hv
  have hana : AnalyticAt ℂ riemannZeta rho := hanaOn rho hne1
  have hnetop : analyticOrderAt riemannZeta rho ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro hev
    have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have hEqOn := hanaOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hne1 hev
    have h2 : riemannZeta 2 = 0 := hEqOn (by norm_num : (2 : ℂ) ≠ 1)
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num) h2
  have hne0 : analyticOrderAt riemannZeta rho ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    push Not
    exact ⟨hana, hzero⟩
  have hcast := Nat.cast_analyticOrderNatAt hnetop
  simp only [zeroMultiplicity]
  refine Nat.one_le_iff_ne_zero.mpr fun h0 => hne0 ?_
  rw [← hcast, h0]
  rfl

/-!
### The rescaled zeros carry the three counts
-/

/-- The rescaling is injective: it is affine with non-zero linear coefficient. -/
@[zz_tag "lem_Z_T_bijection"]
theorem rescale_injective {T : ℝ} (hT : 1 < T) : Function.Injective (rescale T) := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hc : ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  intro a b hab
  simp only [rescale] at hab
  have h1 := mul_right_cancel₀ hc hab
  have h2 := mul_left_cancel₀ Complex.I_ne_zero h1
  linear_combination h2

/-- The transported multiplicity agrees with the original at a rescaled point. -/
@[zz_tag "lem_Z_T_bijection"]
theorem rescaledMult_rescale {T : ℝ} (hT : 1 < T) (rho : ℂ) :
    rescaledMult T (rescale T rho) = zeroMultiplicity rho := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hc : ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  simp only [rescaledMult, rescale]
  congr 1
  field_simp
  ring

/-- **The rescaled zeros carry the counted total.** -/
@[zz_tag "lem_Z_T_counts"]
theorem sum_rescaledMult_eq_zeroCount {T : ℝ} (hT : 1 < T) :
    ∑ z ∈ rescaledZerosFinset T, rescaledMult T z = zeroCount T := by
  classical
  rw [rescaledZerosFinset, Finset.sum_image fun a _ b _ hab => rescale_injective hT hab]
  rw [zeroCount, ← finsum_mem_coe_finset]
  rw [Set.Finite.coe_toFinset]
  exact finsum_congr fun rho => by
    by_cases hmem : rho ∈ nontrivialZeros T <;>
      simp [hmem, rescaledMult_rescale hT]

/-- **The rescaled zeros carry the distinct count.** -/
@[zz_tag "lem_Z_T_counts"]
theorem card_rescaledZerosFinset_eq_distinctZeroCount {T : ℝ} (hT : 1 < T) :
    (rescaledZerosFinset T).card = distinctZeroCount T := by
  classical
  rw [rescaledZerosFinset, Finset.card_image_of_injective _ (rescale_injective hT),
    distinctZeroCount, Set.ncard_eq_toFinset_card _ (nontrivialZeros_finite T)]

/-- **The rescaled zeros carry the simple-on-line count.** A rescaled point is real exactly when
the zero is on the critical line (`rescale_im_eq_zero_iff`), and has multiplicity one exactly when
the zero does. -/
@[zz_tag "lem_Z_T_counts"]
theorem card_simpleRealPart_rescaled_eq_simpleOnLineCount {T : ℝ} (hT : 1 < T) :
    (simpleRealPart (rescaledZerosFinset T) (rescaledMult T)).card = simpleOnLineCount T := by
  classical
  have hfin := nontrivialZeros_finite T
  have hsub : {rho ∈ nontrivialZeros T | rho.re = 1 / 2 ∧ zeroMultiplicity rho = 1}.Finite :=
    hfin.subset fun x hx => hx.1
  have hset : simpleRealPart (rescaledZerosFinset T) (rescaledMult T)
      = (hfin.toFinset.filter fun rho => rho.re = 1 / 2 ∧ zeroMultiplicity rho = 1).image
          (rescale T) := by
    ext w
    simp only [simpleRealPart, rescaledZerosFinset, Finset.mem_filter, Finset.mem_image,
      Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨rho, hrho, rfl⟩, him, hm⟩
      refine ⟨rho, ⟨hrho, (rescale_im_eq_zero_iff hT rho).mp him, ?_⟩, rfl⟩
      rwa [rescaledMult_rescale hT] at hm
    · rintro ⟨rho, ⟨hrho, hre, hm⟩, rfl⟩
      refine ⟨⟨rho, hrho, rfl⟩, (rescale_im_eq_zero_iff hT rho).mpr hre, ?_⟩
      rw [rescaledMult_rescale hT]
      exact hm
  rw [hset, Finset.card_image_of_injective _ (rescale_injective hT), simpleOnLineCount,
    Set.ncard_eq_toFinset_card _ hsub]
  congr 1
  ext rho
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_ofPred_eq]

/-- **Parseval at elements of the span**, for an arbitrary finite index type. -/
private theorem sum_sq_norm_inner_eq_norm_sq_of_span {iota : Type*} [Fintype iota]
    {psi : iota → L2Interval lam} (horth : Orthonormal ℂ psi) {x : L2Interval lam}
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

/-- **Parseval over a sub-family**, at elements of that sub-family's span. -/
theorem sum_sq_norm_inner_eq_norm_sq_of_mem_span_finset {iota : Type*}
    {psi : iota → L2Interval lam} (horth : Orthonormal ℂ psi)
    (s : Finset iota) {x : L2Interval lam}
    (hx : x ∈ Submodule.span ℂ (psi '' (s : Set iota))) :
    ∑ j ∈ s, ‖inner ℂ (psi j) x‖ ^ 2 = ‖x‖ ^ 2 := by
  classical
  have hsub : Orthonormal ℂ fun i : {i // i ∈ s} => psi (i : iota) :=
    horth.comp _ Subtype.val_injective
  have hrange : Set.range (fun i : {i // i ∈ s} => psi (i : iota)) = psi '' (s : Set iota) := by
    ext y
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe, Subtype.exists]
    tauto
  rw [← Finset.sum_coe_sort s fun j => ‖inner ℂ (psi j) x‖ ^ 2]
  exact sum_sq_norm_inner_eq_norm_sq_of_span hsub (by rw [hrange]; exact hx)

/-!
## The normalised test function has total mass one
-/

variable {delta : ℝ} {psi : ℝ → ℝ}

/-- The normalised square, written out: `f_psi = psi² f₀ / A_psi`. The square roots cancel because
both `f₀` and `A_psi` are non-negative. -/
theorem cutoffTestSq_eq (hd : 0 < delta) (hd4 : delta < 1 / 4) (h : IsCutoff delta psi) (x : ℝ) :
    cutoffTestSq psi x = psi x ^ 2 * extremalTest x / cutoffNormaliser psi := by
  have hA := cutoffNormaliser_pos hd hd4 h
  simp only [cutoffTestSq, cutoffTest, Pi.pow_apply]
  rw [div_pow, mul_pow, Real.sq_sqrt (extremalTest_nonneg x), Real.sq_sqrt hA.le]

/-- **The normalised test function has total mass one.** -/
@[zz_tag "lem_f_psi_integral"]
theorem integral_cutoffTestSq (hd : 0 < delta) (hd4 : delta < 1 / 4) (h : IsCutoff delta psi) :
    ∫ x : ℝ, cutoffTestSq psi x = 1 := by
  have hA := cutoffNormaliser_pos hd hd4 h
  rw [integral_congr_ae (.of_forall fun x => cutoffTestSq_eq hd hd4 h x),
    MeasureTheory.integral_div, ← cutoffNormaliser]
  exact div_self (ne_of_gt hA)

/-- **The Fourier transform of the normalised test function at zero is one.** -/
@[zz_tag "lem_f_psi_integral"]
theorem fourierC_cutoffTestSq_zero (hd : 0 < delta) (hd4 : delta < 1 / 4)
    (h : IsCutoff delta psi) : fourierC (cutoffTestSq psi) 0 = 1 := by
  have hpt : ∀ u : ℝ, ((cutoffTestSq psi u : ℝ) : ℂ) *
      Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * 0 * (u : ℂ))
        = ((cutoffTestSq psi u : ℝ) : ℂ) := by
    intro u
    simp
  rw [fourierC, integral_congr_ae (.of_forall hpt), integral_complex_ofReal,
    integral_cutoffTestSq hd hd4 h]
  norm_num

end ZetaZeros
