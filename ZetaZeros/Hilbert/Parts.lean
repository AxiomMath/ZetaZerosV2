/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Hilbert.AlphaExpansion
public import ZetaZeros.Hilbert.Support

/-!
# Splitting the support

Two facts the key proposition rests on: a conjugation-stable set of non-real points has even
cardinality, and the support splits into its simple real, multiple real and non-real parts.

The evenness argument is stated over the hypotheses it actually consumes -- closed under
conjugation, no real point -- so that `nonRealPart`, `𝒮₁` and `𝒮₂` all go through it once.
-/

@[expose] public section

namespace ZetaZeros

variable {Z : Finset ℂ} {m : ℂ → ℕ}

/-- The lower half of a conjugation-stable set of non-real points is the conjugate image of its
upper half; conjugation has no fixed point there. -/
theorem filter_not_pos_eq_image_filter_pos_of_conj_stable {E : Finset ℂ}
    (hre : ∀ z ∈ E, z.im ≠ 0) (hconj : ∀ z ∈ E, (starRingEnd ℂ) z ∈ E) :
    (E.filter fun z => ¬ 0 < z.im) = (E.filter fun z => 0 < z.im).image (starRingEnd ℂ) := by
  classical
  ext w
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨hwE, hwle⟩
    have hwim : w.im ≠ 0 := hre w hwE
    refine ⟨(starRingEnd ℂ) w, ⟨hconj w hwE, ?_⟩, Complex.conj_conj w⟩
    rw [Complex.conj_im]
    have hneg : w.im < 0 := lt_of_le_of_ne (not_lt.mp hwle) hwim
    linarith
  · rintro ⟨z, ⟨hzE, hzpos⟩, rfl⟩
    refine ⟨hconj z hzE, ?_⟩
    rw [Complex.conj_im, not_lt]
    linarith

/-- **A conjugation-stable set of non-real points has even cardinality**
(`lem_conj_stable_even`). Conjugation restricts to a fixed-point-free involution of it, so its
orbits all have two elements and they partition it. -/
@[zz_tag "lem_conj_stable_even"]
theorem two_dvd_card_of_conj_stable {E : Finset ℂ}
    (hre : ∀ z ∈ E, z.im ≠ 0) (hconj : ∀ z ∈ E, (starRingEnd ℂ) z ∈ E) :
    2 ∣ E.card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := E) (p := fun z : ℂ => 0 < z.im)
  rw [filter_not_pos_eq_image_filter_pos_of_conj_stable hre hconj,
    Finset.card_image_of_injective _ conj_injective] at hsplit
  omega

/-- The real part of the support splits by multiplicity into the simple and the multiple real
parts. Multiplicities are at least one on the support, which is what rules out a third case. -/
theorem allRealPart_filter_mult_eq (hZ : IsConjInvariant Z m) :
    ((allRealPart Z).filter fun z => m z = 1) = simpleRealPart Z m ∧
      ((allRealPart Z).filter fun z => ¬ m z = 1) = multipleRealPart Z m := by
  classical
  constructor
  · ext z
    simp only [allRealPart, simpleRealPart, Finset.mem_filter]
    tauto
  · ext z
    simp only [allRealPart, multipleRealPart, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hz, him⟩, hne⟩
      exact ⟨hz, him, by have := hZ.one_le z hz; omega⟩
    · rintro ⟨hz, him, hle⟩
      exact ⟨⟨hz, him⟩, by omega⟩

/-- **The support splits into its real and non-real parts** (`lem_Z_partition`). Stated as the
decomposition of a sum, which is the form every consumer needs: the three parts are pairwise
disjoint and cover `Z`. -/
@[zz_tag "lem_Z_partition"]
theorem sum_eq_sum_simpleRealPart_add_sum_multipleRealPart_add_sum_nonRealPart
    {M : Type*} [AddCommMonoid M] (hZ : IsConjInvariant Z m) (f : ℂ → M) :
    ∑ z ∈ Z, f z = ∑ z ∈ simpleRealPart Z m, f z + ∑ z ∈ multipleRealPart Z m, f z
      + ∑ z ∈ nonRealPart Z, f z := by
  classical
  have hre : ∑ z ∈ Z with z.im = 0, f z + ∑ z ∈ Z with ¬ z.im = 0, f z = ∑ z ∈ Z, f z :=
    Finset.sum_filter_add_sum_filter_not Z (fun z : ℂ => z.im = 0) f
  have hsplit :
      ∑ z ∈ allRealPart Z with m z = 1, f z + ∑ z ∈ allRealPart Z with ¬ m z = 1, f z
        = ∑ z ∈ allRealPart Z, f z :=
    Finset.sum_filter_add_sum_filter_not (allRealPart Z) (fun z : ℂ => m z = 1) f
  obtain ⟨h1, h2⟩ := allRealPart_filter_mult_eq hZ
  rw [h1, h2] at hsplit
  simp only [allRealPart, nonRealPart] at *
  rw [← hre, ← hsplit]

/-- The simple non-real part is conjugation-stable. -/
theorem conj_mem_simpleNonRealPart (hZ : IsConjInvariant Z m) {z : ℂ}
    (hz : z ∈ simpleNonRealPart Z m) : (starRingEnd ℂ) z ∈ simpleNonRealPart Z m := by
  simp only [simpleNonRealPart, Finset.mem_filter] at hz ⊢
  obtain ⟨hzZ, him, hone⟩ := hz
  refine ⟨hZ.conj_mem z hzZ, ?_, ?_⟩
  · rw [Complex.conj_im]; exact neg_ne_zero.mpr him
  · rw [hZ.mult_conj z hzZ]; exact hone

/-- The multiple non-real part is conjugation-stable. -/
theorem conj_mem_multipleNonRealPart (hZ : IsConjInvariant Z m) {z : ℂ}
    (hz : z ∈ multipleNonRealPart Z m) : (starRingEnd ℂ) z ∈ multipleNonRealPart Z m := by
  simp only [multipleNonRealPart, Finset.mem_filter] at hz ⊢
  obtain ⟨hzZ, him, htwo⟩ := hz
  refine ⟨hZ.conj_mem z hzZ, ?_, ?_⟩
  · rw [Complex.conj_im]; exact neg_ne_zero.mpr him
  · rw [hZ.mult_conj z hzZ]; exact htwo

/-- **The simple non-real part has even cardinality** (`lem_S1_even`). -/
@[zz_tag "lem_S1_even"]
theorem two_dvd_card_simpleNonRealPart (hZ : IsConjInvariant Z m) :
    2 ∣ (simpleNonRealPart Z m).card :=
  two_dvd_card_of_conj_stable
    (fun _z hz => (Finset.mem_filter.mp hz).2.1)
    (fun _ hz => conj_mem_simpleNonRealPart hZ hz)

/-- **The multiple non-real part has even cardinality** (`lem_S2_even`). -/
@[zz_tag "lem_S2_even"]
theorem two_dvd_card_multipleNonRealPart (hZ : IsConjInvariant Z m) :
    2 ∣ (multipleNonRealPart Z m).card :=
  two_dvd_card_of_conj_stable
    (fun _z hz => (Finset.mem_filter.mp hz).2.1)
    (fun _ hz => conj_mem_multipleNonRealPart hZ hz)

/-- **The non-real part splits by multiplicity** (`lem_S1_S2_partition`). Stated as the
decomposition of a sum, which gives the cardinality identity by taking `f = 1`. -/
@[zz_tag "lem_S1_S2_partition"]
theorem sum_nonRealPart_eq_sum_simpleNonRealPart_add_sum_multipleNonRealPart
    {M : Type*} [AddCommMonoid M] (hZ : IsConjInvariant Z m) (f : ℂ → M) :
    ∑ z ∈ nonRealPart Z, f z
      = ∑ z ∈ simpleNonRealPart Z m, f z + ∑ z ∈ multipleNonRealPart Z m, f z := by
  classical
  have hsplit :
      ∑ z ∈ nonRealPart Z with m z = 1, f z + ∑ z ∈ nonRealPart Z with ¬ m z = 1, f z
        = ∑ z ∈ nonRealPart Z, f z :=
    Finset.sum_filter_add_sum_filter_not (nonRealPart Z) (fun z : ℂ => m z = 1) f
  have h1 : ((nonRealPart Z).filter fun z => m z = 1) = simpleNonRealPart Z m := by
    ext z; simp only [nonRealPart, simpleNonRealPart, Finset.mem_filter]; tauto
  have h2 : ((nonRealPart Z).filter fun z => ¬ m z = 1) = multipleNonRealPart Z m := by
    ext z
    simp only [nonRealPart, multipleNonRealPart, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hz, him⟩, hne⟩
      exact ⟨hz, him, by have := hZ.one_le z hz; omega⟩
    · rintro ⟨hz, him, hle⟩
      exact ⟨⟨hz, him⟩, by omega⟩
  rw [h1, h2] at hsplit
  exact hsplit.symm

/-- **The simple part counts the simple real and simple non-real points**
(`lem_card_simple_part`). Needs no hypothesis on `m`: splitting the simple part by whether the
point is real is unconditional. -/
@[zz_tag "lem_card_simple_part"]
theorem card_simplePart_eq :
    (simplePart Z m).card = (simpleRealPart Z m).card + (simpleNonRealPart Z m).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := simplePart Z m) (p := fun z : ℂ => z.im = 0)
  have h1 : ((simplePart Z m).filter fun z => z.im = 0) = simpleRealPart Z m := by
    ext z; simp only [simplePart, simpleRealPart, Finset.mem_filter]; tauto
  have h2 : ((simplePart Z m).filter fun z => ¬ z.im = 0) = simpleNonRealPart Z m := by
    ext z; simp only [simplePart, simpleNonRealPart, Finset.mem_filter]; tauto
  rw [h1, h2] at hsplit
  omega

/-- **The real part carries mass at least `n + 2r`** (`lem_real_mass_lower`). Multiplicity is one
on the simple real part and at least two on the multiple real part. -/
@[zz_tag "lem_real_mass_lower"]
theorem le_sum_allRealPart (hZ : IsConjInvariant Z m) :
    ((simpleRealPart Z m).card : ℝ) + 2 * ((multipleRealPart Z m).card : ℝ)
      ≤ ∑ z ∈ allRealPart Z, (m z : ℝ) := by
  classical
  have hsplit :
      ∑ z ∈ allRealPart Z with m z = 1, (m z : ℝ)
        + ∑ z ∈ allRealPart Z with ¬ m z = 1, (m z : ℝ)
        = ∑ z ∈ allRealPart Z, (m z : ℝ) :=
    Finset.sum_filter_add_sum_filter_not (allRealPart Z) (fun z : ℂ => m z = 1) _
  obtain ⟨h1, h2⟩ := allRealPart_filter_mult_eq hZ
  rw [h1, h2] at hsplit
  have e1 : ∑ z ∈ simpleRealPart Z m, (m z : ℝ) = ((simpleRealPart Z m).card : ℝ) := by
    have hone : ∀ z ∈ simpleRealPart Z m, (m z : ℝ) = 1 := by
      intro z hz
      simp only [simpleRealPart, Finset.mem_filter] at hz
      rw [hz.2.2]; norm_num
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  have e2 : 2 * ((multipleRealPart Z m).card : ℝ) ≤ ∑ z ∈ multipleRealPart Z m, (m z : ℝ) := by
    have htwo : ∀ z ∈ multipleRealPart Z m, (2 : ℝ) ≤ (m z : ℝ) := by
      intro z hz
      simp only [multipleRealPart, Finset.mem_filter] at hz
      exact_mod_cast hz.2.2
    calc 2 * ((multipleRealPart Z m).card : ℝ)
        = ∑ _z ∈ multipleRealPart Z m, (2 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ z ∈ multipleRealPart Z m, (m z : ℝ) := Finset.sum_le_sum htwo
  linarith

/-- **The simple-or-real part carries mass at least `n + 2r + 2p`**
(`lem_simple_or_real_mass_lower`). It is the real part together with the simple non-real part. -/
@[zz_tag "lem_simple_or_real_mass_lower"]
theorem le_sum_simpleOrRealPart (hZ : IsConjInvariant Z m) :
    ((simpleRealPart Z m).card : ℝ) + 2 * ((multipleRealPart Z m).card : ℝ)
        + ((simpleNonRealPart Z m).card : ℝ)
      ≤ ∑ z ∈ simpleOrRealPart Z m, (m z : ℝ) := by
  classical
  have hsplit :
      ∑ z ∈ simpleOrRealPart Z m with z.im = 0, (m z : ℝ)
        + ∑ z ∈ simpleOrRealPart Z m with ¬ z.im = 0, (m z : ℝ)
        = ∑ z ∈ simpleOrRealPart Z m, (m z : ℝ) :=
    Finset.sum_filter_add_sum_filter_not (simpleOrRealPart Z m) (fun z : ℂ => z.im = 0) _
  have h1 : ((simpleOrRealPart Z m).filter fun z => z.im = 0) = allRealPart Z := by
    ext z; simp only [simpleOrRealPart, allRealPart, Finset.mem_filter]; tauto
  have h2 : ((simpleOrRealPart Z m).filter fun z => ¬ z.im = 0) = simpleNonRealPart Z m := by
    ext z; simp only [simpleOrRealPart, simpleNonRealPart, Finset.mem_filter]; tauto
  rw [h1, h2] at hsplit
  have e2 : ∑ z ∈ simpleNonRealPart Z m, (m z : ℝ) = ((simpleNonRealPart Z m).card : ℝ) := by
    have hone : ∀ z ∈ simpleNonRealPart Z m, (m z : ℝ) = 1 := by
      intro z hz
      simp only [simpleNonRealPart, Finset.mem_filter] at hz
      rw [hz.2.2]; norm_num
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  have := le_sum_allRealPart (m := m) hZ
  linarith

end ZetaZeros
