/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Hilbert.AlphaExpansion.CoefficientSums

/-!
# Gram-Schmidt adapted to a flag of subspaces, and its symmetric form

Let `S` be a real subspace of a complex inner product space on which all inner products are real.
The Gram–Schmidt process applied to a finite family in `S` stays in `S`, and its initial segments
span the same subspaces as those of the family. This gives an orthonormal basis of `W` in the
symmetric subspace whose initial segments span `U` and `V`.

## Main results

* `exists_adapted_orthonormal_basis`: existence of an adapted orthonormal basis inside a real
  subspace.
* `exists_symmetric_adapted_basis`: a symmetric adapted orthonormal basis of `W` exists.
-/
@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ} {eta : ℝ → ℝ}

variable {Z : Finset ℂ} {m : ℂ → ℕ}

/-!
### The adapted orthonormal basis
-/

section AdaptedBasis

open Module InnerProductSpace Submodule Set

/-- If all inner products of elements of the real subspace `S` are real, every Gram-Schmidt vector
of a family lying in `S` stays in `S`: each projection coefficient is real. -/
private theorem gramSchmidt_mem_S
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℝ E)
    (hreal : ∀ a ∈ S, ∀ b ∈ S, (inner ℂ a b : ℂ).im = 0)
    {n : ℕ} (v : Fin n → E) (hv : ∀ i, v i ∈ S) :
    ∀ i, gramSchmidt ℂ v i ∈ S := by
  have smul_mem : ∀ (c : ℂ), c.im = 0 → ∀ x ∈ S, c • x ∈ S := by
    intro c hc x hx
    have : c = ((c.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [this, Complex.coe_smul]
    exact S.smul_mem c.re hx
  intro i
  induction hm : i.val using Nat.strong_induction_on generalizing i with
  | _ m IH =>
    subst hm
    have IH' : ∀ k : Fin n, k < i → gramSchmidt ℂ v k ∈ S := by
      intro k hk
      exact IH k.val hk k rfl
    rw [gramSchmidt_def ℂ v i]
    apply S.sub_mem (hv i)
    apply S.sum_mem
    intro k hk
    rw [Finset.mem_Iio] at hk
    rw [Submodule.starProjection_singleton ℂ (v i)]
    apply smul_mem
    · have hnum : (inner ℂ (gramSchmidt ℂ v k) (v i) : ℂ).im = 0 :=
        hreal _ (IH' k hk) _ (hv i)
      have hden : ((‖gramSchmidt ℂ v k‖ : ℂ) ^ 2).im = 0 := by
        simp [pow_two, Complex.mul_im]
      simp [Complex.div_im, hnum, hden]
    · exact IH' k hk

/-- The *normalized* Gram-Schmidt vectors also stay in `S`: `gn i = ‖g i‖⁻¹ • g i` is a real scalar
multiple of `g i ∈ S`. -/
private theorem gramSchmidtNormed_mem_S
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℝ E)
    (hreal : ∀ a ∈ S, ∀ b ∈ S, (inner ℂ a b : ℂ).im = 0)
    {n : ℕ} (v : Fin n → E) (hv : ∀ i, v i ∈ S) :
    ∀ i, gramSchmidtNormed ℂ v i ∈ S := by
  have smul_mem : ∀ (c : ℂ), c.im = 0 → ∀ x ∈ S, c • x ∈ S := by
    intro c hc x hx
    have : c = ((c.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [this, Complex.coe_smul]
    exact S.smul_mem c.re hx
  intro i
  have hmem : gramSchmidt ℂ v i ∈ S := gramSchmidt_mem_S S hreal v hv i
  unfold gramSchmidtNormed
  apply smul_mem
  · simp
  · exact hmem

open Classical in
/-- The Gram--Schmidt normalisation has exactly as many non-zero vectors as the span has
dimensions: the zero ones are precisely the vectors that were already dependent. -/
theorem card_nonzero_gramSchmidtNormed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (v : Fin n → E) :
    (Finset.univ.filter (fun i : Fin n => gramSchmidtNormed ℂ v i ≠ 0)).card
      = finrank ℂ (Submodule.span ℂ (Set.range v)) := by
  classical
  set gn : Fin n → E := gramSchmidtNormed ℂ v with hgn
  have hon : Orthonormal ℂ (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i) :=
    gramSchmidtNormed_orthonormal' v
  have hli : LinearIndependent ℂ (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i) :=
    hon.linearIndependent
  have hrange : Set.range (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i)
      = gn '' {i | gn i ≠ 0} := by
    ext x
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
  have himg : gn '' {i | gn i ≠ 0} = Set.range gn \ {0} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, rfl⟩, hi⟩
    · rintro ⟨⟨i, rfl⟩, hx⟩; exact ⟨i, hx, rfl⟩
  have hspan : Submodule.span ℂ (Set.range (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i))
      = Submodule.span ℂ (Set.range v) := by
    rw [hrange, himg, Submodule.span_sdiff_singleton_zero, hgn,
      span_gramSchmidtNormed_range, span_gramSchmidt]
  rw [← hspan]
  rw [finrank_span_eq_card hli]
  rw [Fintype.card_subtype]

/-- **Existence of an adapted orthonormal basis inside a real subspace.**

`v` is a finite ordered family spanning `W`; its initial segments of lengths `dU` and `dV` span two
nested subspaces. There is an orthonormal family spanning the same `W`, lying in `S`, whose own
initial segments (of the appropriate dimensions) span those same two subspaces. -/
theorem exists_adapted_orthonormal_basis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℝ E)
    (hreal : ∀ a ∈ S, ∀ b ∈ S, (inner ℂ a b : ℂ).im = 0)
    {n : ℕ} (v : Fin n → E) (hv : ∀ i, v i ∈ S)
    (dU dV : ℕ) (hUV : dU ≤ dV) (hVn : dV ≤ n) :
    ∃ psi : Fin (finrank ℂ (Submodule.span ℂ (Set.range v))) → E,
      Orthonormal ℂ psi ∧
      (∀ j, psi j ∈ S) ∧
      Submodule.span ℂ (Set.range psi) = Submodule.span ℂ (Set.range v) ∧
      Submodule.span ℂ
          (psi '' {j | (j : ℕ) < finrank ℂ (Submodule.span ℂ (v '' {i | (i : ℕ) < dU}))})
        = Submodule.span ℂ (v '' {i | (i : ℕ) < dU}) ∧
      Submodule.span ℂ
          (psi '' {j | (j : ℕ) < finrank ℂ (Submodule.span ℂ (v '' {i | (i : ℕ) < dV}))})
        = Submodule.span ℂ (v '' {i | (i : ℕ) < dV}) := by
  classical
  set g : Fin n → E := gramSchmidt ℂ v with hg
  set gn : Fin n → E := gramSchmidtNormed ℂ v with hgn
  set s : Finset (Fin n) := Finset.univ.filter (fun i => gn i ≠ 0) with hs
  have hcard : s.card = finrank ℂ (Submodule.span ℂ (Set.range v)) := by
    rw [hs, hgn]
    exact card_nonzero_gramSchmidtNormed v
  set r : ℕ := finrank ℂ (Submodule.span ℂ (Set.range v)) with hr
  set e : Fin r → Fin n := ⇑(s.orderEmbOfFin hcard) with he
  have e_mem : ∀ j, e j ∈ s := fun j => Finset.orderEmbOfFin_mem s hcard j
  have e_ne : ∀ j, gn (e j) ≠ 0 := by
    intro j
    have := e_mem j
    rw [hs] at this
    simpa using this
  have e_inj : Function.Injective e := (s.orderEmbOfFin hcard).injective
  have e_range : Set.range e = (s : Set (Fin n)) := Finset.range_orderEmbOfFin s hcard
  have e_mono : ∀ (x y : Fin r), y ≤ x → e y ≤ e x := by
    intro x y hxy
    exact (s.orderEmbOfFin hcard).monotone hxy
  have e_lt : ∀ (x y : Fin r), e x < e y ↔ x < y := fun x y =>
    (s.orderEmbOfFin hcard).lt_iff_lt
  have e_le : ∀ (x y : Fin r), e x ≤ e y ↔ x ≤ y := fun x y =>
    (s.orderEmbOfFin hcard).le_iff_le
  have hspanA : ∀ d0 : ℕ, d0 ≤ n →
      Submodule.span ℂ (g '' {i : Fin n | (i : ℕ) < d0})
        = Submodule.span ℂ (v '' {i : Fin n | (i : ℕ) < d0}) := by
    intro d0 hd0
    rcases eq_or_lt_of_le hd0 with h | h
    · have hset : {i : Fin n | (i : ℕ) < d0} = Set.univ := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        have := i.isLt; omega
      rw [hset, Set.image_univ, Set.image_univ, hg, span_gramSchmidt]
    · have hset : {i : Fin n | (i : ℕ) < d0} = Set.Iio (⟨d0, h⟩ : Fin n) := by
        ext i
        simp [Set.mem_Iio, Fin.lt_def]
      rw [hset, hg, span_gramSchmidt_Iio]
  have key : ∀ d0 : ℕ, d0 ≤ n →
      Submodule.span ℂ ((fun j => gn (e j)) ''
          {j : Fin r | (j : ℕ) < finrank ℂ (Submodule.span ℂ (v '' {i : Fin n | (i : ℕ) < d0}))})
        = Submodule.span ℂ (v '' {i : Fin n | (i : ℕ) < d0}) := by
    intro d0 hd0
    set A : Set (Fin n) := {i : Fin n | (i : ℕ) < d0} with hA
    set d : ℕ := finrank ℂ (Submodule.span ℂ (v '' A)) with hd
    set T : Finset (Fin n) := s.filter (fun i => (i : ℕ) < d0) with hT
    have hcountA : T.card = d := by
      have hon : Orthonormal ℂ (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i) := by
        rw [hgn]; exact gramSchmidtNormed_orthonormal' v
      have hTsub : ∀ i ∈ T, gn i ≠ 0 := by
        intro i hi
        rw [hT] at hi
        rw [Finset.mem_filter, hs, Finset.mem_filter] at hi
        exact hi.1.2
      set ι : {x : Fin n // x ∈ T} → {i : Fin n // gn i ≠ 0} :=
        fun x => ⟨x.1, hTsub x.1 x.2⟩ with hι
      have hιinj : Function.Injective ι := by
        intro a b hab
        apply Subtype.ext
        simpa [hι] using hab
      have honT : Orthonormal ℂ (fun x : {x : Fin n // x ∈ T} => gn x.1) := by
        have h := hon.comp ι hιinj
        exact h
      have hliT : LinearIndependent ℂ (fun x : {x : Fin n // x ∈ T} => gn x.1) :=
        honT.linearIndependent
      have hrangeT : Set.range (fun x : {x : Fin n // x ∈ T} => gn x.1)
          = gn '' (T : Set (Fin n)) := by
        ext y
        constructor
        · rintro ⟨⟨i, hi⟩, rfl⟩; exact ⟨i, hi, rfl⟩
        · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
      have hspanT : Submodule.span ℂ (gn '' (T : Set (Fin n))) = Submodule.span ℂ (v '' A) := by
        have hTA : (T : Set (Fin n)) ⊆ A := by
          intro i hi
          rw [Finset.mem_coe, hT, Finset.mem_filter] at hi
          exact hi.2
        have hle : Submodule.span ℂ (gn '' (T : Set (Fin n))) ≤ Submodule.span ℂ (gn '' A) :=
          Submodule.span_mono (Set.image_mono hTA)
        have hge : Submodule.span ℂ (gn '' A) ≤ Submodule.span ℂ (gn '' (T : Set (Fin n))) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, hiA, rfl⟩
          by_cases hzero : gn i = 0
          · rw [hzero]; exact Submodule.zero_mem _
          · have hiT : i ∈ T := by
              rw [hT, Finset.mem_filter, hs, Finset.mem_filter]
              exact ⟨⟨Finset.mem_univ i, hzero⟩, hiA⟩
            exact Submodule.subset_span ⟨i, hiT, rfl⟩
        have heqAT : Submodule.span ℂ (gn '' (T : Set (Fin n))) = Submodule.span ℂ (gn '' A) :=
          le_antisymm hle hge
        rw [heqAT, hgn, span_gramSchmidtNormed, ← hg, hspanA d0 hd0]
      calc T.card = Fintype.card {x : Fin n // x ∈ T} := (Fintype.card_coe T).symm
        _ = finrank ℂ (Submodule.span ℂ (Set.range (fun x : {x : Fin n // x ∈ T} => gn x.1))) :=
              (finrank_span_eq_card hliT).symm
        _ = finrank ℂ (Submodule.span ℂ (gn '' (T : Set (Fin n)))) := by rw [hrangeT]
        _ = finrank ℂ (Submodule.span ℂ (v '' A)) := by rw [hspanT]
        _ = d := rfl
    set P : Finset (Fin r) := Finset.univ.filter (fun k => (e k : ℕ) < d0) with hP
    have hPcard : P.card = d := by
      have himg : P.image e = T := by
        ext x
        simp only [hP, hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨k, hk, rfl⟩
          refine ⟨?_, hk⟩
          have := e_mem k
          rw [hs, Finset.mem_filter] at this
          rw [hs, Finset.mem_filter]
          exact this
        · rintro ⟨hxs, hxd0⟩
          have hxr : x ∈ Set.range e := by rw [e_range]; exact Finset.mem_coe.mpr hxs
          obtain ⟨k, rfl⟩ := hxr
          exact ⟨k, hxd0, rfl⟩
      have := Finset.card_image_of_injective P e_inj
      rw [himg] at this
      rw [← this, hcountA]
    have echar : ∀ j : Fin r, ((j : ℕ) < d ↔ (e j : ℕ) < d0) := by
      intro j
      constructor
      · intro hjd
        by_contra hcon
        push Not at hcon
        have hsub : P ⊆ Finset.Iio j := by
          intro k hk
          rw [hP, Finset.mem_filter] at hk
          have hlt : (e k : ℕ) < (e j : ℕ) := lt_of_lt_of_le hk.2 hcon
          have : e k < e j := hlt
          rw [Finset.mem_Iio]
          exact (e_lt k j).mp this
        have hcardle : P.card ≤ (Finset.Iio j).card := Finset.card_le_card hsub
        rw [hPcard, Fin.card_Iio] at hcardle
        omega
      · intro hej
        have hsub : Finset.Iic j ⊆ P := by
          intro k hk
          rw [Finset.mem_Iic] at hk
          rw [hP, Finset.mem_filter]
          refine ⟨Finset.mem_univ k, ?_⟩
          have hkle : e k ≤ e j := (e_le k j).mpr hk
          have : (e k : ℕ) ≤ (e j : ℕ) := hkle
          omega
        have hcardle : (Finset.Iic j).card ≤ P.card := Finset.card_le_card hsub
        rw [hPcard, Fin.card_Iic] at hcardle
        omega
    have hseteq : e '' {j : Fin r | (j : ℕ) < d} = (T : Set (Fin n)) := by
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨j, hj, rfl⟩
        rw [hT, Finset.mem_coe, Finset.mem_filter]
        have hej : e j ∈ s := e_mem j
        refine ⟨hej, ?_⟩
        exact (echar j).mp hj
      · intro hx
        rw [hT, Finset.mem_coe, Finset.mem_filter] at hx
        obtain ⟨hxs, hxd0⟩ := hx
        have hxr : x ∈ Set.range e := by rw [e_range]; exact Finset.mem_coe.mpr hxs
        obtain ⟨j, rfl⟩ := hxr
        exact ⟨j, (echar j).mpr hxd0, rfl⟩
    have himage : (fun j => gn (e j)) '' {j : Fin r | (j : ℕ) < d}
        = gn '' (e '' {j : Fin r | (j : ℕ) < d}) := by
      rw [Set.image_image]
    change Submodule.span ℂ ((fun j => gn (e j)) '' {j : Fin r | (j : ℕ) < d})
        = Submodule.span ℂ (v '' A)
    rw [himage, hseteq]
    have hTsub : ∀ i ∈ T, gn i ≠ 0 := by
      intro i hi
      rw [hT, Finset.mem_filter, hs, Finset.mem_filter] at hi
      exact hi.1.2
    have hTA : (T : Set (Fin n)) ⊆ A := by
      intro i hi
      rw [Finset.mem_coe, hT, Finset.mem_filter] at hi
      exact hi.2
    have hle : Submodule.span ℂ (gn '' (T : Set (Fin n))) ≤ Submodule.span ℂ (gn '' A) :=
      Submodule.span_mono (Set.image_mono hTA)
    have hge : Submodule.span ℂ (gn '' A) ≤ Submodule.span ℂ (gn '' (T : Set (Fin n))) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hiA, rfl⟩
      by_cases hzero : gn i = 0
      · rw [hzero]; exact Submodule.zero_mem _
      · have hiT : i ∈ T := by
          rw [hT, Finset.mem_filter, hs, Finset.mem_filter]
          exact ⟨⟨Finset.mem_univ i, hzero⟩, hiA⟩
        exact Submodule.subset_span ⟨i, hiT, rfl⟩
    have heqAT : Submodule.span ℂ (gn '' (T : Set (Fin n))) = Submodule.span ℂ (gn '' A) :=
      le_antisymm hle hge
    rw [heqAT, hgn, span_gramSchmidtNormed, ← hg, hspanA d0 hd0]
  refine ⟨fun j => gn (e j), ?_, ?_, ?_, ?_, ?_⟩
  · have hon : Orthonormal ℂ (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i) := by
      rw [hgn]; exact gramSchmidtNormed_orthonormal' v
    set φ : Fin r → {i : Fin n // gn i ≠ 0} := fun j => ⟨e j, e_ne j⟩ with hφ
    have hφinj : Function.Injective φ := by
      intro a b hab
      apply e_inj
      simpa [hφ] using hab
    have h := hon.comp φ hφinj
    exact h
  · intro j
    have : gramSchmidtNormed ℂ v (e j) ∈ S := gramSchmidtNormed_mem_S S hreal v hv (e j)
    rw [hgn]
    exact this
  · have hrange : Set.range (fun j => gn (e j)) = gn '' s := by
      rw [Set.range_comp' gn e, e_range]
    rw [hrange]
    have himg : gn '' (s : Set (Fin n)) = Set.range gn \ {0} := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        rw [hs] at hi; simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi
        exact ⟨⟨i, rfl⟩, hi.2⟩
      · rintro ⟨⟨i, rfl⟩, hx⟩
        refine ⟨i, ?_, rfl⟩
        rw [hs]
        simp only [Finset.coe_filter, Set.mem_ofPred_eq]
        exact ⟨Finset.mem_univ i, hx⟩
    rw [himg, Submodule.span_sdiff_singleton_zero, hgn,
      span_gramSchmidtNormed_range, span_gramSchmidt]
  · exact key dU (le_trans hUV hVn)
  · exact key dV hVn

end AdaptedBasis

/-! ### A symmetric adapted basis for the three Hilbert subspaces -/

/-- Enumerating a finset through its canonical equivalence with `Fin` has precisely the
finset as its range. -/
private theorem range_finset_enum {E : Type*} (s : Finset E) :
    Set.range (fun i : Fin s.card => ((s.equivFin.symm i : s) : E)) = (s : Set E) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  · intro hx
    exact ⟨s.equivFin ⟨x, hx⟩, by simp⟩

/-- The range of two finite families appended together is the union of their ranges. -/
private theorem range_fin_append {E : Type*} {a b : ℕ} (f : Fin a → E) (g : Fin b → E) :
    Set.range (Fin.append f g) = Set.range f ∪ Set.range g := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.addCases (fun j => Or.inl ⟨j, (Fin.append_left f g j).symm⟩)
      (fun j => Or.inr ⟨j, (Fin.append_right f g j).symm⟩) i
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd b i, Fin.append_left f g i⟩
    · exact ⟨Fin.natAdd a j, Fin.append_right f g j⟩

/-- The first block in an appended finite family has the expected image. -/
private theorem image_append_lt_left {E : Type*} {a b : ℕ} (f : Fin a → E) (g : Fin b → E) :
    Fin.append f g '' {i : Fin (a + b) | (i : ℕ) < a} = Set.range f := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    let j : Fin a := ⟨i, hi⟩
    have hij : i = Fin.castAdd b j := Fin.ext rfl
    exact ⟨j, by rw [hij, Fin.append_left]⟩
  · rintro ⟨j, rfl⟩
    refine ⟨Fin.castAdd b j, ?_, ?_⟩
    · exact j.isLt
    · exact Fin.append_left f g j

/-- An initial segment lying in the left block of an appended family is computed in that block. -/
private theorem image_append_lt_of_le {E : Type*} {a b d : ℕ} (f : Fin a → E) (g : Fin b → E)
    (hd : d ≤ a) :
    Fin.append f g '' {i : Fin (a + b) | (i : ℕ) < d}
      = f '' {i : Fin a | (i : ℕ) < d} := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hia : (i : ℕ) < a := lt_of_lt_of_le hi hd
    let j : Fin a := ⟨i, hia⟩
    have hij : i = Fin.castAdd b j := Fin.ext rfl
    exact ⟨j, hi, by rw [hij, Fin.append_left]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.castAdd b j, hj, Fin.append_left f g j⟩

/-- **A symmetric adapted basis exists.** Gram–Schmidt applied to the generators of `U`, then
the further generators of `V`, then those of `W`, gives an adapted orthonormal basis of symmetric
`L²` elements. -/
theorem exists_symmetric_adapted_basis
    (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    ∃ psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam,
      IsAdaptedBasis h Z m psi ∧ ∀ j, IsSymmetricL2 (psi j) := by
  classical
  let A : Finset (L2Interval lam) :=
    (multipleRealPart Z m).image (fzL2 h) ∪ (nonRealPart Z).image (gzL2 h)
  let B : Finset (L2Interval lam) := (simpleRealPart Z m).image (fzL2 h)
  let C : Finset (L2Interval lam) := (nonRealPart Z).image (hzL2 h)
  let enumA : Fin A.card → L2Interval lam :=
    fun i => ((A.equivFin.symm i : A) : L2Interval lam)
  let enumB : Fin B.card → L2Interval lam :=
    fun i => ((B.equivFin.symm i : B) : L2Interval lam)
  let enumC : Fin C.card → L2Interval lam :=
    fun i => ((C.equivFin.symm i : C) : L2Interval lam)
  let v : Fin (A.card + B.card + C.card) → L2Interval lam :=
    Fin.append (Fin.append enumA enumB) enumC
  have hrA : Set.range enumA = (A : Set (L2Interval lam)) := range_finset_enum A
  have hrB : Set.range enumB = (B : Set (L2Interval lam)) := range_finset_enum B
  have hrC : Set.range enumC = (C : Set (L2Interval lam)) := range_finset_enum C
  have himgA : v '' {i | (i : ℕ) < A.card} = (A : Set (L2Interval lam)) := by
    rw [show v = Fin.append (Fin.append enumA enumB) enumC from rfl,
      image_append_lt_of_le _ _ (Nat.le_add_right A.card B.card),
      image_append_lt_left, hrA]
  have himgAB : v '' {i | (i : ℕ) < A.card + B.card}
      = (A : Set (L2Interval lam)) ∪ (B : Set (L2Interval lam)) := by
    rw [show v = Fin.append (Fin.append enumA enumB) enumC from rfl,
      image_append_lt_left, range_fin_append, hrA, hrB]
  have hrange : Set.range v = (A : Set (L2Interval lam)) ∪ (B : Set (L2Interval lam)) ∪
      (C : Set (L2Interval lam)) := by
    rw [show v = Fin.append (Fin.append enumA enumB) enumC from rfl,
      range_fin_append, range_fin_append, hrA, hrB, hrC]
  have hA : Submodule.span ℂ (A : Set (L2Interval lam)) = subspaceU h Z m := by
    simp only [A, Finset.coe_union, Finset.coe_image, subspaceU]
  have hAB : Submodule.span ℂ
      ((A : Set (L2Interval lam)) ∪ (B : Set (L2Interval lam))) = subspaceV h Z m := by
    simp only [A, B, Finset.coe_union, Finset.coe_image, subspaceV]
    rw [show fzL2 h '' (multipleRealPart Z m : Set ℂ) ∪
        gzL2 h '' (nonRealPart Z : Set ℂ) ∪ fzL2 h '' (simpleRealPart Z m : Set ℂ)
      = fzL2 h '' ((simpleRealPart Z m ∪ multipleRealPart Z m : Finset ℂ) : Set ℂ) ∪
        gzL2 h '' (nonRealPart Z : Set ℂ) by
          rw [Finset.coe_union, Set.image_union]
          ac_rfl]
    rw [Finset.coe_union, Set.image_union]
  have hABC : Submodule.span ℂ
      ((A : Set (L2Interval lam)) ∪ (B : Set (L2Interval lam)) ∪
        (C : Set (L2Interval lam))) = subspaceW h Z m := by
    simp only [A, B, C, Finset.coe_union, Finset.coe_image, subspaceW]
    rw [show (fzL2 h '' (multipleRealPart Z m : Set ℂ) ∪
          gzL2 h '' (nonRealPart Z : Set ℂ)) ∪ fzL2 h '' (simpleRealPart Z m : Set ℂ) ∪
          hzL2 h '' (nonRealPart Z : Set ℂ)
      = (fzL2 h '' ((simpleRealPart Z m ∪ multipleRealPart Z m : Finset ℂ) : Set ℂ) ∪
          gzL2 h '' (nonRealPart Z : Set ℂ)) ∪ hzL2 h '' (nonRealPart Z : Set ℂ) by
          rw [Finset.coe_union, Set.image_union]
          ac_rfl]
    rw [Finset.coe_union, Set.image_union]
  have hv : ∀ i, v i ∈ symmetricSubspace lam := by
    intro i
    have hi : v i ∈ (A : Set (L2Interval lam)) ∪ (B : Set (L2Interval lam)) ∪
        (C : Set (L2Interval lam)) := by
      rw [← hrange]
      exact ⟨i, rfl⟩
    rcases hi with (hi | hi) | hi
    · simp only [A, Finset.coe_union, Finset.coe_image] at hi
      rcases hi with ⟨x, hx, hxi⟩ | ⟨z, hz, hzi⟩
      · rw [← hxi]
        exact fzL2_mem_symmetricSubspace h ((Finset.mem_filter.mp hx).2).1
      · rw [← hzi]
        exact gzL2_mem_symmetricSubspace h z
    · simp only [B, Finset.coe_image] at hi
      rcases hi with ⟨x, hx, hxi⟩
      rw [← hxi]
      exact fzL2_mem_symmetricSubspace h ((Finset.mem_filter.mp hx).2).1
    · simp only [C, Finset.coe_image] at hi
      rcases hi with ⟨z, hz, hzi⟩
      rw [← hzi]
      exact hzL2_mem_symmetricSubspace h z
  have hW : Submodule.span ℂ (Set.range v) = subspaceW h Z m := by
    rw [hrange, hABC]
  have hU : Submodule.span ℂ (v '' {i | (i : ℕ) < A.card}) = subspaceU h Z m := by
    rw [himgA, hA]
  have hV : Submodule.span ℂ (v '' {i | (i : ℕ) < A.card + B.card}) = subspaceV h Z m := by
    rw [himgAB, hAB]
  have hex :=
    exists_adapted_orthonormal_basis (symmetricSubspace lam)
      (fun a ha b hb => inner_symmetricL2_im_eq_zero ha hb) v hv
      A.card (A.card + B.card) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  rw [hW, hU, hV] at hex
  obtain ⟨psi, horth, hsym, hspanW, hspanU, hspanV⟩ := hex
  refine ⟨psi, ?_, hsym⟩
  exact ⟨horth, hspanW, hspanU, hspanV⟩

end ZetaZeros
