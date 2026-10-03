/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Meta.Attr
public import ZetaZeros.Hilbert.AlphaExpansion.RescaledZeros

/-!
# Bessel's inequality for the two-variable kernel

Bessel's inequality for a kernel against tensor squares on a product measure, and its instance for
the two-variable kernel `bigF`; the admissibility of the normalised cutoff test function; the
reindexing of kernel sums along the rescaling; a symmetric adapted basis of `W`; the Fourier
transform of a self-convolution and the second moment of the kernel; and the
conjugation-invariance of the rescaled zeros.

## Main results

* `isAdmissible_cutoffTest`: the normalised cutoff test function is `1/2`-admissible.
* `sum_testKernel_sq_eq_finsum_rescaledDiff`: the kernel sums over the zeros and over the rescaled
  zeros agree.
* `exists_isAdaptedBasis_symmetric`: a symmetric adapted orthonormal basis exists.
* `fourierC_cutoffSelfConv`: the transform of `Q_psi` is the square of the kernel.
* `sum_testKernel_sq_eq_integral_bigF_mul_conj`: the second moment is the `L²(I²)` norm of the
  two-variable kernel.
* `sum_alphaOf_re_sq_le_integral_norm_bigF_sq`: Bessel's inequality for the two-variable kernel.
* `isConjInvariant_rescaledZerosFinset`: the rescaled multiset is conjugation-invariant.
-/
@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ} {eta : ℝ → ℝ}

variable {Z : Finset ℂ} {m : ℂ → ℕ}

variable {delta : ℝ} {psi : ℝ → ℝ}

/-! ## Bessel for a kernel against tensor squares -/

open MeasureTheory

/-- The `L²` inner product of two kernels on the product measure equals the iterated integral of
`f * conj g`. -/
private lemma inner_toLp_eq_iterated (lam : ℝ) (f g : ℝ → ℝ → ℂ)
    (hf : MemLp (fun p : ℝ × ℝ => f p.1 p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))))
    (hg : MemLp (fun p : ℝ × ℝ => g p.1 p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam)))) :
    inner ℂ (hg.toLp _) (hf.toLp _)
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          f u v * (starRingEnd ℂ) (g u v) := by
  have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioo (-lam) lam)).prod
      (volume.restrict (Set.Ioo (-lam) lam))),
      inner ℂ ((hg.toLp _ : Lp ℂ 2 _) p) ((hf.toLp _ : Lp ℂ 2 _) p)
        = f p.1 p.2 * (starRingEnd ℂ) (g p.1 p.2) := by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with p hp hq
    simp [hp, hq, RCLike.inner_apply]
  have hint : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * (starRingEnd ℂ) (g p.1 p.2))
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))) :=
    (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hg.toLp _) (hf.toLp _)).congr hae
  rw [MeasureTheory.L2.inner_def, integral_integral hint]
  exact integral_congr_ae hae

/-- **Bessel for a kernel paired against tensor squares.**

`phi` is a finite family whose tensor squares are orthonormal in the iterated-integral pairing
(`horth`). Then the squared pairings of the kernel `K` against them are dominated by the squared
`L²` norm of `K`. -/
private theorem sum_sq_pairing_le_integral_norm_sq {lam : ℝ} {N : ℕ}
    (K : ℝ → ℝ → ℂ) (phi : Fin N → ℝ → ℂ)
    (hK : MemLp (fun p : ℝ × ℝ => K p.1 p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))))
    (hphi : ∀ j, MemLp (fun p : ℝ × ℝ => phi j p.1 * phi j p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))))
    (horth : ∀ j l : Fin N,
      (∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        (phi j u * phi j v) * (starRingEnd ℂ) (phi l u * phi l v))
        = if j = l then 1 else 0) :
    ∑ j, ‖∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          K u v * (starRingEnd ℂ) (phi j u * phi j v)‖ ^ 2
      ≤ ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam, ‖K u v‖ ^ 2 := by
  classical
  have horthE : Orthonormal ℂ (fun j : Fin N =>
      (hphi j).toLp (fun p : ℝ × ℝ => phi j p.1 * phi j p.2)) := by
    rw [orthonormal_iff_ite]
    intro j l
    rw [inner_toLp_eq_iterated lam (fun u v => phi l u * phi l v)
      (fun u v => phi j u * phi j v) (hphi l) (hphi j), horth l j]
    by_cases h : j = l
    · subst h; simp
    · simp [h, Ne.symm h]
  have hbessel := horthE.sum_inner_products_le
    (hK.toLp (fun p : ℝ × ℝ => K p.1 p.2)) (s := Finset.univ)
  have hpair : ∀ j : Fin N,
      inner ℂ ((hphi j).toLp (fun p : ℝ × ℝ => phi j p.1 * phi j p.2))
        (hK.toLp (fun p : ℝ × ℝ => K p.1 p.2))
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          K u v * (starRingEnd ℂ) (phi j u * phi j v) := fun j =>
    inner_toLp_eq_iterated lam K (fun u v => phi j u * phi j v) hK (hphi j)
  have hnorm : ‖hK.toLp (fun p : ℝ × ℝ => K p.1 p.2)‖ ^ 2
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam, ‖K u v‖ ^ 2 := by
    have h1 := inner_toLp_eq_iterated lam K K hK hK
    have h2 : ∀ u : ℝ, (∫ v in Set.Ioo (-lam) lam, K u v * (starRingEnd ℂ) (K u v))
        = ((∫ v in Set.Ioo (-lam) lam, ‖K u v‖ ^ 2 : ℝ) : ℂ) := by
      intro u
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp [Complex.mul_conj']
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h1]
    simp only [h2]
    rw [integral_complex_ofReal]
    simp
  rw [← hnorm]
  refine le_trans (le_of_eq ?_) hbessel
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hpair j]

/-- The tensor product of two `L²` functions is `L²` for the product measure. -/
private theorem memLp_tensor_two {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    {mu : Measure alpha} {nu : Measure beta}
    {f : alpha → ℂ} {g : beta → ℂ} (hf : MemLp f 2 mu) (hg : MemLp g 2 nu) :
    MemLp (fun p : alpha × beta => f p.1 * g p.2) 2 (mu.prod nu) := by
  have h1 : Integrable (fun x => ‖f x‖ ^ 2) mu := (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  have h2 : Integrable (fun y => ‖g y‖ ^ 2) nu := (memLp_two_iff_integrable_sq_norm hg.1).mp hg
  have hmul : Integrable (fun z : alpha × beta => ‖f z.1‖ ^ 2 * ‖g z.2‖ ^ 2) (mu.prod nu) :=
    h1.mul_prod h2
  have hmeas : AEStronglyMeasurable (fun p : alpha × beta => f p.1 * g p.2) (mu.prod nu) :=
    hf.1.comp_fst.mul hg.1.comp_snd
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hmul.congr ?_
  filter_upwards with z
  simp [mul_pow]

/-- **The normalised cutoff test function is `1/2`-admissible.** -/
@[zz_tag "lem_eta_psi_admissible"]
theorem isAdmissible_cutoffTest {delta : ℝ} (hd : 0 < delta) (hd4 : delta < 1 / 4) {psi : ℝ → ℝ}
    (h : IsCutoff delta psi) : IsAdmissible (1 / 2) (cutoffTest psi) where
  memLp := (cutoffTest_contDiff h).continuous.memLp_of_hasCompactSupport
    (cutoffTest_hasCompactSupport h)
  even := cutoffTest_neg h
  support := fun _ => cutoffTest_eq_zero_of_half_le_abs h
  fourier_sq_zero := fourierC_cutoffTestSq_zero hd hd4 h

/-! ### The kernel sums agree

The double sum over the rescaled zeros and the double sum over the zeros are the same sum,
reindexed along the rescaling: the rescaling is injective, and it turns a difference of zeros into
the rescaled difference. No admissibility of `eta` is needed. -/

/-- The rescaling turns a difference of zeros into the rescaled difference. -/
theorem rescale_sub_rescale (T : ℝ) (rho rho' : ℂ) :
    rescale T rho - rescale T rho' = rescaledDiff T rho rho' := by
  simp only [rescale, rescaledDiff]
  ring

/-- **The kernel sums agree.** -/
@[zz_tag "lem_kernel_sum_identity"]
theorem sum_testKernel_sq_eq_finsum_rescaledDiff {T : ℝ} (hT : 1 < T) (eta : ℝ → ℝ) :
    ∑ z ∈ rescaledZerosFinset T, ∑ s ∈ rescaledZerosFinset T,
        ((rescaledMult T z * rescaledMult T s : ℕ) : ℂ) * testKernel eta (z - s) ^ 2 =
      ∑ᶠ rho ∈ nontrivialZeros T, ∑ᶠ rho' ∈ nontrivialZeros T,
        ((zeroMultiplicity rho * zeroMultiplicity rho' : ℕ) : ℂ) *
          testKernel eta (rescaledDiff T rho rho') ^ 2 := by
  classical
  have hinj : ∀ a ∈ (nontrivialZeros_finite T).toFinset,
      ∀ b ∈ (nontrivialZeros_finite T).toFinset, rescale T a = rescale T b → a = b :=
    fun a _ b _ hab => rescale_injective hT hab
  have hinner : ∀ rho : ℂ, ∑ rho' ∈ (nontrivialZeros_finite T).toFinset,
      ((zeroMultiplicity rho * zeroMultiplicity rho' : ℕ) : ℂ) *
          testKernel eta (rescaledDiff T rho rho') ^ 2 =
        ∑ᶠ rho' ∈ nontrivialZeros T,
          ((zeroMultiplicity rho * zeroMultiplicity rho' : ℕ) : ℂ) *
            testKernel eta (rescaledDiff T rho rho') ^ 2 := fun _ => by
    rw [← finsum_mem_coe_finset, Set.Finite.coe_toFinset]
  rw [rescaledZerosFinset]
  simp only [Finset.sum_image hinj, rescaledMult_rescale hT, rescale_sub_rescale, hinner]
  rw [← finsum_mem_coe_finset, Set.Finite.coe_toFinset]

/-- The ordered spanning family of `W` as a list: the twisted functions at the multiple real
points, the even parts at the non-real points, the twisted functions at the simple real points,
and the odd parts at the non-real points. -/
noncomputable def adaptedList (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    List (L2Interval lam) :=
  (multipleRealPart Z m).toList.map (fzL2 h) ++
    (nonRealPart Z).toList.map (gzL2 h) ++
      (simpleRealPart Z m).toList.map (fzL2 h) ++
        (nonRealPart Z).toList.map (hzL2 h)

/-- Every member of the ordered family is a symmetric `L²` element. -/
private theorem adaptedList_mem_symmetricSubspace (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ →
    ℕ)
    {y : L2Interval lam} (hy : y ∈ adaptedList h Z m) : y ∈ symmetricSubspace lam := by
  classical
  simp only [adaptedList, List.mem_append, List.mem_map, Finset.mem_toList] at hy
  rcases hy with ((⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩) | ⟨x, hx, rfl⟩) | ⟨z, hz, rfl⟩
  · exact fzL2_mem_symmetricSubspace h ((Finset.mem_filter.mp hx).2).1
  · exact gzL2_mem_symmetricSubspace h z
  · exact fzL2_mem_symmetricSubspace h ((Finset.mem_filter.mp hx).2).1
  · exact hzL2_mem_symmetricSubspace h z

/-! ### The adapted basis of `U`, `V`, `W`

The image of an initial segment of indices of `adaptedFamily` is the set of members of a
`List.take` of `adaptedList`, and `take` of an append at a block boundary is that block. So the
initial segments at `cutU` and `cutV` generate `U` and `V`, and the whole family generates `W`. -/

section AdaptedBasis

/-- The image of an initial segment of indices under `L.get` is the set of members of
`L.take k`. -/
private theorem image_lt_eq_setOf_mem_take {α : Type*} (L : List α) (k : ℕ) :
    (fun i : Fin L.length => L.get i) '' {i | (i : ℕ) < k} = {x | x ∈ L.take k} := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.get_eq_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by simpa using lt_min hi i.isLt, by simp⟩
  · intro hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, hgj⟩ := hx
    rw [List.length_take] at hj
    exact ⟨⟨j, lt_of_lt_of_le hj (min_le_right _ _)⟩,
      lt_of_lt_of_le hj (min_le_left _ _), by simpa using hgj⟩

/-- The members of a mapped `Finset.toList` are the image of the `Finset`. -/
private theorem setOf_mem_map_toList {α β : Type*} (F : Finset α) (f : α → β) :
    {x | x ∈ F.toList.map f} = f '' (F : Set α) := by
  ext x
  simp [Set.mem_image]

/-- `take` at exactly the prefix length is the prefix. -/
private theorem take_length_left {α : Type*} (l₁ l₂ : List α) : (l₁ ++ l₂).take l₁.length = l₁ := by
  induction l₁ with
  | nil => simp
  | cons a t ih => simp [ih]

/-- Members of an append split as a union. -/
private theorem setOf_mem_append {α : Type*} (L₁ L₂ : List α) :
    {x | x ∈ L₁ ++ L₂} = {x | x ∈ L₁} ∪ {x | x ∈ L₂} := by
  ext x
  simp

variable (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ)

/-- The ordered family, read off `adaptedList` by index. -/
noncomputable def adaptedFamily : Fin (adaptedList h Z m).length → L2Interval lam :=
  fun i => (adaptedList h Z m).get i

/-- The first cut-point: the `R₂` block followed by the `S` block. -/
noncomputable def cutU : ℕ := (multipleRealPart Z m).card + (nonRealPart Z).card

/-- The second cut-point: adding the `R₁` block. -/
noncomputable def cutV : ℕ := cutU Z m + (simpleRealPart Z m).card

/-- The `R₂` block. -/
noncomputable def blockR2 : List (L2Interval lam) := (multipleRealPart Z m).toList.map (fzL2 h)

/-- The `S` block of even parts. -/
noncomputable def blockG : List (L2Interval lam) := (nonRealPart Z).toList.map (gzL2 h)

/-- The `R₁` block. -/
noncomputable def blockR1 : List (L2Interval lam) := (simpleRealPart Z m).toList.map (fzL2 h)

/-- The `S` block of odd parts. -/
noncomputable def blockH : List (L2Interval lam) := (nonRealPart Z).toList.map (hzL2 h)

/-- The second real block lists the multiple real points, one entry each. -/
private theorem length_blockR2 : (blockR2 h Z m).length = (multipleRealPart Z m).card := by
  simp [blockR2]

/-- The middle block lists the non-real points, one entry each. -/
private theorem length_blockG : (blockG h Z).length = (nonRealPart Z).card := by
  simp [blockG]

/-- The first real block lists the simple real points, one entry each. -/
theorem length_blockR1 : (blockR1 h Z m).length = (simpleRealPart Z m).card := by
  simp [blockR1]

/-- At the first cut-point the initial segment is exactly the first two blocks. -/
private theorem take_cutU :
    (adaptedList h Z m).take (cutU Z m) = blockR2 h Z m ++ blockG h Z := by
  have hsplit : adaptedList h Z m
      = (blockR2 h Z m ++ blockG h Z) ++ (blockR1 h Z m ++ blockH h Z) := by
    simp only [adaptedList, blockR2, blockG, blockR1, blockH, List.append_assoc]
  have hlen : cutU Z m = (blockR2 h Z m ++ blockG h Z).length := by
    simp [cutU, blockR2, blockG]
  rw [hsplit, hlen, take_length_left]

/-- At the second cut-point the initial segment is exactly the first three blocks. -/
private theorem take_cutV :
    (adaptedList h Z m).take (cutV Z m)
      = (blockR2 h Z m ++ blockG h Z) ++ blockR1 h Z m := by
  have hsplit : adaptedList h Z m
      = ((blockR2 h Z m ++ blockG h Z) ++ blockR1 h Z m) ++ blockH h Z := by
    simp only [adaptedList, blockR2, blockG, blockR1, blockH]
  have hlen : cutV Z m = ((blockR2 h Z m ++ blockG h Z) ++ blockR1 h Z m).length := by
    simp only [cutV, cutU, blockR2, blockG, blockR1, List.length_append, List.length_map,
      Finset.length_toList]
  rw [hsplit, hlen, take_length_left]

/-- The adapted family enumerates exactly the members of the adapted list: its range is that
list's underlying set. -/
theorem range_adaptedFamily :
    Set.range (adaptedFamily h Z m) = {x | x ∈ adaptedList h Z m} := by
  have huniv : {i : Fin (adaptedList h Z m).length | (i : ℕ) < (adaptedList h Z m).length}
      = Set.univ := Set.eq_univ_of_forall fun i => i.isLt
  have hrw : Set.range (adaptedFamily h Z m)
      = (fun i : Fin (adaptedList h Z m).length => (adaptedList h Z m).get i) ''
          {i | (i : ℕ) < (adaptedList h Z m).length} := by
    rw [huniv, Set.image_univ]
    rfl
  rw [hrw, image_lt_eq_setOf_mem_take, List.take_length]

/-- The image of an initial segment of indices is the corresponding prefix of the adapted list. -/
theorem image_lt_cut (k : ℕ) :
    adaptedFamily h Z m '' {j | (j : ℕ) < k} = {x | x ∈ (adaptedList h Z m).take k} :=
  image_lt_eq_setOf_mem_take (adaptedList h Z m) k

/-- **The first two blocks generate `U`.** -/
private theorem span_image_cutU :
    Submodule.span ℂ (adaptedFamily h Z m '' {j | (j : ℕ) < cutU Z m}) = subspaceU h Z m := by
  rw [image_lt_cut, take_cutU]
  simp only [blockR2, blockG, setOf_mem_append, setOf_mem_map_toList, subspaceU]

/-- **The first three blocks generate `V`.** -/
private theorem span_image_cutV :
    Submodule.span ℂ (adaptedFamily h Z m '' {j | (j : ℕ) < cutV Z m}) = subspaceV h Z m := by
  rw [image_lt_cut, take_cutV]
  simp only [blockR2, blockG, blockR1, setOf_mem_append, setOf_mem_map_toList, subspaceV]
  congr 1
  rw [Finset.coe_union, Set.image_union]
  ext x
  simp only [Set.mem_union]
  tauto

/-- **All four blocks generate `W`.** -/
private theorem span_range_adaptedFamily :
    Submodule.span ℂ (Set.range (adaptedFamily h Z m)) = subspaceW h Z m := by
  rw [range_adaptedFamily]
  simp only [adaptedList, setOf_mem_append, setOf_mem_map_toList, subspaceW]
  congr 1
  rw [Finset.coe_union, Set.image_union]
  ext x
  simp only [Set.mem_union]
  tauto

/-- The adapted list's length, block by block: multiple real, non-real, simple real, non-real
again -- the last block repeating because each non-real point is paired with its conjugate. -/
theorem length_adaptedList : (adaptedList h Z m).length
    = (multipleRealPart Z m).card + (nonRealPart Z).card + (simpleRealPart Z m).card
      + (nonRealPart Z).card := by
  simp only [adaptedList, List.length_append, List.length_map, Finset.length_toList]

/-- Reindexing along `finCongr` does not move an initial segment: the underlying natural is
unchanged, so the images of `{j | j < k}` agree. -/
private theorem image_comp_finCongr_symm {n n' : ℕ} (hn : n = n') {β : Type*} (f : Fin n → β) (k :
    ℕ) :
    (f ∘ (finCongr hn).symm) '' {j : Fin n' | (j : ℕ) < k} = f '' {i : Fin n | (i : ℕ) < k} := by
  subst hn
  simp

/-- Re-indexing along an equality of lengths does not change a family's range. -/
theorem range_comp_finCongr_symm {n n' : ℕ} (hn : n = n') {β : Type*} (f : Fin n → β) :
    Set.range (f ∘ (finCongr hn).symm) = Set.range f := by
  subst hn
  simp

/-- **A symmetric adapted orthonormal basis exists**, for any finite `Z` and multiplicity `m`. -/
@[zz_tag "lem_adapted_basis_exists"]
theorem exists_isAdaptedBasis_symmetric (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    ∃ psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam,
      IsAdaptedBasis h Z m psi ∧ ∀ j, IsSymmetricL2 (psi j) := by
  classical
  have hUV : cutU Z m ≤ cutV Z m := by simp [cutV]
  have hVn : cutV Z m ≤ (adaptedList h Z m).length := by
    simp only [cutV, cutU, length_adaptedList]
    omega
  obtain ⟨psi, horth, hmem, hW, hU, hV⟩ :=
    exists_adapted_orthonormal_basis (symmetricSubspace lam)
      (fun _ ha _ hb => inner_symmetricL2_im_eq_zero ha hb)
      (adaptedFamily h Z m)
      (fun i => adaptedList_mem_symmetricSubspace h Z m (List.get_mem _ _))
      (cutU Z m) (cutV Z m) hUV hVn
  have hrk : Module.finrank ℂ (Submodule.span ℂ (Set.range (adaptedFamily h Z m)))
      = Module.finrank ℂ (subspaceW h Z m) := by rw [span_range_adaptedFamily]
  refine ⟨psi ∘ (finCongr hrk).symm, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact horth.comp _ (finCongr hrk).symm.injective
  · rw [range_comp_finCongr_symm, hW, span_range_adaptedFamily]
  · rw [image_comp_finCongr_symm, ← span_image_cutU h Z m, hU]
  · rw [image_comp_finCongr_symm, ← span_image_cutV h Z m, hV]
  · exact fun j => hmem _

end AdaptedBasis

/-! ### The Fourier transform of the self-convolution

The convolution theorem at a complex frequency, for any continuous `E : ℝ → ℂ` with
`E (a + b) = E a * E b` in place of the character.

### The second moment

A double integral whose integrand is a finite double sum with factored terms equals the double sum
of the products of the single integrals. -/

section FourierSelfConv

/-- For any continuous `E` with `E (a + b) = E a * E b`, the integral of a self-convolution of a
compactly supported continuous `f` against `E` is the square of the integral of `f` against `E`.
-/
private theorem selfConv_aux (f : ℝ → ℝ) (hf : Continuous f) (hsupp : HasCompactSupport f)
    (E : ℝ → ℂ) (hEadd : ∀ a b : ℝ, E (a + b) = E a * E b) (hEcont : Continuous E) :
    ∫ x : ℝ, ((∫ t : ℝ, f t * f (x - t) : ℝ) : ℂ) * E x = (∫ u : ℝ, (f u : ℂ) * E u) ^ 2 := by
  set F : ℝ → ℂ := fun u => (f u : ℂ) * E u with hFdef
  have hFcont : Continuous F := (Complex.continuous_ofReal.comp hf).mul hEcont
  have hFsupp : HasCompactSupport F := by
    apply HasCompactSupport.intro hsupp
    intro x hx
    simp [hFdef, image_eq_zero_of_notMem_tsupport hx]
  have hFint : Integrable F := hFcont.integrable_of_hasCompactSupport hFsupp
  have hEsplit : ∀ x t : ℝ, E (x - t) * E t = E x := by
    intro x t
    rw [← hEadd]
    congr 1
    ring
  have hcast : ∀ x : ℝ, ((∫ t : ℝ, f t * f (x - t) : ℝ) : ℂ)
      = ∫ t : ℝ, (f t : ℂ) * (f (x - t) : ℂ) := by
    intro x
    rw [← integral_complex_ofReal]
    simp only [Complex.ofReal_mul]
  have hint2 : Integrable (Function.uncurry fun x t : ℝ => (f t : ℂ) * (f (x - t) : ℂ) * E x)
      ((volume : Measure ℝ).prod volume) := by
    have h1 : Integrable (fun z : ℝ × ℝ => F z.1 * F z.2) ((volume : Measure ℝ).prod volume) :=
      hFint.mul_prod hFint
    have h2 := (measurePreserving_sub_prod (volume : Measure ℝ)
      (volume : Measure ℝ)).integrable_comp_of_integrable h1
    have heq : ((fun z : ℝ × ℝ => F z.1 * F z.2) ∘ fun z : ℝ × ℝ => (z.1 - z.2, z.2))
        = Function.uncurry fun x t : ℝ => (f t : ℂ) * (f (x - t) : ℂ) * E x := by
      funext z
      obtain ⟨x, t⟩ := z
      simp only [Function.comp_apply, Function.uncurry_apply_pair, hFdef]
      rw [← hEsplit x t]
      ring
    rwa [heq] at h2
  calc ∫ x : ℝ, ((∫ t : ℝ, f t * f (x - t) : ℝ) : ℂ) * E x
      = ∫ x : ℝ, ∫ t : ℝ, (f t : ℂ) * (f (x - t) : ℂ) * E x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change ((∫ t : ℝ, f t * f (x - t) : ℝ) : ℂ) * E x
            = ∫ t : ℝ, (f t : ℂ) * (f (x - t) : ℂ) * E x
        rw [hcast x, ← integral_mul_const]
    _ = ∫ t : ℝ, ∫ x : ℝ, (f t : ℂ) * (f (x - t) : ℂ) * E x := integral_integral_swap hint2
    _ = ∫ t : ℝ, F t * ∫ y : ℝ, F y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        change (∫ x : ℝ, (f t : ℂ) * (f (x - t) : ℂ) * E x) = F t * ∫ y : ℝ, F y
        rw [← integral_add_right_eq_self (fun x => (f t : ℂ) * (f (x - t) : ℂ) * E x) t]
        have hpt : ∀ y : ℝ, (f t : ℂ) * (f (y + t - t) : ℂ) * E (y + t) = F t * F y := by
          intro y
          rw [hEadd]
          simp only [hFdef, add_sub_cancel_right]
          ring
        simp only [hpt]
        exact integral_const_mul _ _
    _ = (∫ u : ℝ, F u) ^ 2 := by rw [integral_mul_const, sq]

/-- **The transform of a self-convolution is the square of the transform.** -/
private theorem fourierC_selfConv (f : ℝ → ℝ) (hf : Continuous f) (hsupp : HasCompactSupport f) (ξ :
    ℂ) :
    fourierC (fun x => ∫ t : ℝ, f t * f (x - t)) ξ = fourierC f ξ ^ 2 := by
  have key := selfConv_aux f hf hsupp
      (fun u : ℝ => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ξ * (u : ℂ)))
      (fun a b => by rw [← Complex.exp_add]; congr 1; push_cast; ring)
      (Complex.continuous_exp.comp (by fun_prop))
  simpa only [fourierC] using key

/-- **A double integral of a factored double sum.** -/
private theorem integral_integral_double_sum_factored {iota : Type*} (F : Finset iota) (mu : Measure
    ℝ)
    (c : iota → iota → ℂ) (a : iota → iota → ℝ → ℂ) (ha : ∀ i j, Integrable (a i j) mu) :
    (∫ u, ∫ v, ∑ i ∈ F, ∑ j ∈ F, c i j * a i j u * a i j v ∂mu ∂mu)
      = ∑ i ∈ F, ∑ j ∈ F, c i j * (∫ u, a i j u ∂mu) * (∫ v, a i j v ∂mu) := by
  have key : ∀ (g : iota → iota → ℂ) (b : iota → iota → ℝ → ℂ),
      (∀ i j, Integrable (b i j) mu) →
      (∫ u, ∑ i ∈ F, ∑ j ∈ F, g i j * b i j u ∂mu)
        = ∑ i ∈ F, ∑ j ∈ F, g i j * ∫ u, b i j u ∂mu := by
    intro g b hb
    rw [integral_finsetSum _
      (fun i _ => integrable_finsetSum _ (fun j _ => (hb i j).const_mul (g i j)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hb i j).const_mul (g i j))]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have h2 : ∀ u, (∫ v, ∑ i ∈ F, ∑ j ∈ F, c i j * a i j u * a i j v ∂mu)
      = ∑ i ∈ F, ∑ j ∈ F, (c i j * ∫ v, a i j v ∂mu) * a i j u := by
    intro u
    rw [key (fun i j => c i j * a i j u) a ha]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [show (∫ u, ∫ v, ∑ i ∈ F, ∑ j ∈ F, c i j * a i j u * a i j v ∂mu ∂mu)
      = ∫ u, ∑ i ∈ F, ∑ j ∈ F, (c i j * ∫ v, a i j v ∂mu) * a i j u ∂mu from by
    simp only [h2]]
  rw [key (fun i j => c i j * ∫ v, a i j v ∂mu) a ha]

/-! ### The two instantiations -/

/-- **The transform of `Q_psi` is the square of the kernel.** -/
@[zz_tag "lem_Q_psi_hat"]
theorem fourierC_cutoffSelfConv {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi) (z : ℂ) :
    fourierC (cutoffSelfConv psi) z = testKernel (cutoffTest psi) z ^ 2 := by
  have hQ : cutoffSelfConv psi
      = fun x => ∫ t : ℝ, cutoffTestSq psi t * cutoffTestSq psi (x - t) := rfl
  rw [hQ, fourierC_selfConv _ (cutoffTestSq_contDiff h).continuous
    (cutoffTestSq_hasCompactSupport h) z]
  rfl

/-- A twisted function against another twisted function's conjugate is integrable. -/
private theorem integrable_fz_mul_conj_fz (h : IsAdmissible lam eta) (z s : ℂ) :
    Integrable (fun u => fz eta z u * (starRingEnd ℂ) (fz eta s u))
      (volume.restrict (Set.Ioo (-lam) lam)) :=
  (memLp_fz h z).integrable_mul ((memLp_fz h s).star)

/-- **The second moment is the `L²(I²)` norm of the two-variable kernel.** -/
@[zz_tag "lem_second_moment"]
theorem sum_testKernel_sq_eq_integral_bigF_mul_conj (h : IsAdmissible lam eta)
    (Z : Finset ℂ) (m : ℂ → ℕ) :
    ∑ z ∈ Z, ∑ s ∈ Z, ((m z * m s : ℕ) : ℂ) * testKernel eta (z - (starRingEnd ℂ) s) ^ 2 =
      ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        bigF eta Z m u v * (starRingEnd ℂ) (bigF eta Z m u v) := by
  classical
  have hexp : ∀ u v : ℝ, bigF eta Z m u v * (starRingEnd ℂ) (bigF eta Z m u v)
      = ∑ z ∈ Z, ∑ t ∈ Z, ((m t * m z : ℕ) : ℂ) *
          (fz eta t u * (starRingEnd ℂ) (fz eta z u)) *
            (fz eta t v * (starRingEnd ℂ) (fz eta z v)) := by
    intro u v
    simp only [bigF, map_sum, Finset.sum_mul, Finset.mul_sum, map_mul, Complex.conj_natCast,
      Nat.cast_mul]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => by ring
  simp only [hexp]
  rw [integral_integral_double_sum_factored Z _ (fun z t => ((m t * m z : ℕ) : ℂ))
    (fun z t u => fz eta t u * (starRingEnd ℂ) (fz eta z u))
    (fun z t => integrable_fz_mul_conj_fz h t z), Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun z _ => by
    rw [testKernel_sub_conj h z s]; ring

end FourierSelfConv

/-! ### Bessel's inequality for the two-variable kernel

`bigF` is a finite sum of tensor products, so it is in `L²` of the square, as are the tensor
squares of the basis members. Since `(re a)^2 ≤ ‖a‖^2` for every complex `a`, the norm form of
Bessel's inequality implies the form with real parts, with no realness of the coefficients needed.
-/

/-- The two-variable kernel is `L²` on the square: it is a finite sum of tensor products. -/
private theorem memLp_bigF (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    MemLp (fun p : ℝ × ℝ => bigF eta Z m p.1 p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))) := by
  have hsum : (fun p : ℝ × ℝ => bigF eta Z m p.1 p.2)
      = fun p : ℝ × ℝ => ∑ z ∈ Z, ((m z : ℂ) * fz eta z p.1) * fz eta z p.2 := rfl
  rw [hsum]
  exact memLp_finsetSum Z fun z _ =>
    memLp_tensor_two ((memLp_fz h z).const_mul (m z : ℂ)) (memLp_fz h z)

/-- The tensor square of an `L²` element is `L²` on the square. -/
private theorem memLp_tensor_square (psi : L2Interval lam) :
    MemLp (fun p : ℝ × ℝ => (psi : ℝ → ℂ) p.1 * (psi : ℝ → ℂ) p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))) :=
  memLp_tensor_two (Lp.memLp psi) (Lp.memLp psi)

/-- **Bessel's inequality for the kernel, in norm form.** -/
private theorem sum_norm_alphaOf_sq_le_integral_norm_bigF_sq (h : IsAdmissible lam eta) {Z : Finset
    ℂ}
    {m : ℂ → ℕ} {N : ℕ} (psi : Fin N → L2Interval lam) (horth : Orthonormal ℂ psi) :
    ∑ j, ‖alphaOf eta lam Z m (psi j)‖ ^ 2
      ≤ ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam, ‖bigF eta Z m u v‖ ^ 2 := by
  classical
  exact sum_sq_pairing_le_integral_norm_sq (bigF eta Z m) (fun j => (psi j : ℝ → ℂ))
    (memLp_bigF h Z m) (fun j => memLp_tensor_square (psi j))
    (fun j l => integral_tensor_square_pairing psi horth j l)

/-- **Bessel's inequality for the kernel.** No conjugation-invariance of `(Z, m)` and no symmetry
of the basis members is needed. -/
@[zz_tag "lem_bessel_F"]
theorem sum_alphaOf_re_sq_le_integral_norm_bigF_sq (h : IsAdmissible lam eta) {Z : Finset ℂ}
    {m : ℂ → ℕ} {N : ℕ} (psi : Fin N → L2Interval lam) (horth : Orthonormal ℂ psi) :
    ∑ j, (alphaOf eta lam Z m (psi j)).re ^ 2
      ≤ ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam, ‖bigF eta Z m u v‖ ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun j _ => ?_)
    (sum_norm_alphaOf_sq_le_integral_norm_bigF_sq h psi horth)
  have hn : ‖alphaOf eta lam Z m (psi j)‖ ^ 2
      = (alphaOf eta lam Z m (psi j)).re ^ 2 + (alphaOf eta lam Z m (psi j)).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hn]
  nlinarith [sq_nonneg (alphaOf eta lam Z m (psi j)).im]

/-! ### The rescaled multiset is conjugation-invariant

The composite symmetry `rho ↦ 1 - conj rho` preserves the non-trivial zeros and their
multiplicities (`zeroMultiplicity_conj`, `zeroMultiplicity_one_sub`), and conjugating a rescaled
zero rescales the reflected conjugate: `conj (rescale T rho) = rescale T (1 - conj rho)`. -/

/-- Conjugating a rescaled point rescales the reflected conjugate. -/
private theorem conj_rescale (T : ℝ) (rho : ℂ) :
    (starRingEnd ℂ) (rescale T rho) = rescale T (1 - (starRingEnd ℂ) rho) := by
  simp only [rescale, map_mul, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal,
    map_div₀, map_ofNat]
  ring

/-- The reflected conjugate of a non-trivial zero is a non-trivial zero at the same height. -/
@[zz_tag "lem_reflect_mem"]
theorem one_sub_conj_mem_nontrivialZeros {T : ℝ} {rho : ℂ} (hrho : rho ∈ nontrivialZeros T) :
    1 - (starRingEnd ℂ) rho ∈ nontrivialZeros T := by
  obtain ⟨hzero, hre0, hre1, him0, himT⟩ := hrho
  have hzc : riemannZeta ((starRingEnd ℂ) rho) = 0 := by
    rw [riemannZeta_conj, hzero, map_zero]
  have hne1 : (starRingEnd ℂ) rho ≠ 1 := by
    intro hEq
    have : ((starRingEnd ℂ) rho).re = 1 := by rw [hEq]; simp
    rw [Complex.conj_re] at this
    linarith
  have hnen : ∀ n : ℕ, (starRingEnd ℂ) rho ≠ -(n : ℂ) := by
    intro n hEq
    have : ((starRingEnd ℂ) rho).re = -(n : ℝ) := by rw [hEq]; simp
    rw [Complex.conj_re] at this
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [riemannZeta_one_sub hnen hne1, hzc, mul_zero]
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · simpa [Complex.sub_im, Complex.conj_im] using him0
  · simpa [Complex.sub_im, Complex.conj_im] using himT

/-- The multiplicity is unchanged by the composite symmetry. -/
theorem zeroMultiplicity_one_sub_conj {rho : ℂ} (hre0 : 0 < rho.re) (hre1 : rho.re < 1) :
    zeroMultiplicity (1 - (starRingEnd ℂ) rho) = zeroMultiplicity rho := by
  have hne1 : rho ≠ 1 := fun hEq => by rw [hEq] at hre1; simp at hre1
  rw [zeroMultiplicity_one_sub (by simpa [Complex.conj_re] using hre0)
    (by simpa [Complex.conj_re] using hre1), zeroMultiplicity_conj hne1]

/-- **The rescaled multiset is conjugation-invariant.** -/
@[zz_tag "lem_Z_T_conj"]
theorem isConjInvariant_rescaledZerosFinset {T : ℝ} (hT : 1 < T) :
    IsConjInvariant (rescaledZerosFinset T) (rescaledMult T) where
  one_le := by
    classical
    intro z hz
    simp only [rescaledZerosFinset, Finset.mem_image, Set.Finite.mem_toFinset] at hz
    obtain ⟨rho, hrho, rfl⟩ := hz
    rw [rescaledMult_rescale hT]
    exact one_le_zeroMultiplicity hrho
  conj_mem := by
    classical
    intro z hz
    simp only [rescaledZerosFinset, Finset.mem_image, Set.Finite.mem_toFinset] at hz ⊢
    obtain ⟨rho, hrho, rfl⟩ := hz
    exact ⟨1 - (starRingEnd ℂ) rho, one_sub_conj_mem_nontrivialZeros hrho,
      (conj_rescale T rho).symm⟩
  mult_conj := by
    classical
    intro z hz
    simp only [rescaledZerosFinset, Finset.mem_image, Set.Finite.mem_toFinset] at hz
    obtain ⟨rho, hrho, rfl⟩ := hz
    rw [conj_rescale, rescaledMult_rescale hT, rescaledMult_rescale hT,
      zeroMultiplicity_one_sub_conj hrho.2.1 hrho.2.2.1]

/-- The tensor square of an `L²` function belongs to `L²` for the product measure. -/
private theorem memLp_tensor_square_of_memLp {lam : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioo (-lam) lam))) :
    MemLp (fun p : ℝ × ℝ => f p.1 * f p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod
        (volume.restrict (Set.Ioo (-lam) lam))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo (-lam) lam)
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 * f p.2) (μ.prod μ) :=
    hf.1.comp_fst.fun_mul hf.1.comp_snd
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    hf.integrable_norm_pow (by norm_num)
  simpa only [norm_mul, mul_pow] using hf2.mul_prod hf2

/-- Bessel's inequality for the kernel, over a symmetric adapted basis and a conjugation-invariant
multiset. -/
theorem sum_alphaOf_re_sq_le_integral_norm_bigF_sq_adapted
    {lam : ℝ} {eta : ℝ → ℝ} (h : IsAdmissible lam eta)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    {psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam}
    (hZ : IsConjInvariant Z m) (hb : IsAdaptedBasis h Z m psi)
    (hsym : ∀ j, IsSymmetricL2 (psi j)) :
    ∑ j, (alphaOf eta lam Z m (psi j)).re ^ 2
      ≤ ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          ‖bigF eta Z m u v‖ ^ 2 := by
  have hbessel := sum_sq_pairing_le_integral_norm_sq
    (lam := lam) (K := bigF eta Z m) (phi := fun j => (psi j : ℝ → ℂ))
    (memLp_bigF h Z m)
    (fun j => memLp_tensor_square_of_memLp (MeasureTheory.Lp.memLp (psi j)))
    (integral_tensor_square_pairing psi hb.orthonormal)
  have hbessel' :
      ∑ j, ‖alphaOf eta lam Z m (psi j)‖ ^ 2
        ≤ ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
            ‖bigF eta Z m u v‖ ^ 2 := by
    simpa only [alphaOf] using hbessel
  calc
    ∑ j, (alphaOf eta lam Z m (psi j)).re ^ 2 =
        ∑ j, ‖alphaOf eta lam Z m (psi j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      symm
      rw [Complex.sq_norm, Complex.normSq_apply,
        alphaOf_im_eq_zero_l2 h hZ (hsym j)]
      ring
    _ ≤ _ := hbessel'

end ZetaZeros
