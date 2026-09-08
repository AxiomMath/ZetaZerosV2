/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Hilbert.RefinedRange
public import ZetaZeros.Hilbert.Support

/-!
# The two further conclusions of the key proposition

Equations (2.5) and (2.6) of the source. Each is a three-range estimate over the Bessel
coefficients, carrying its own A/B/C disjoint cover of the basis, followed by the same assembly
`card_simpleRealPart_lower` performs.

(2.6) is the only place a parameter is chosen: `t = 2 + √2`, forced by `t² - 4t + 2 = 0`, which is
what makes the multiple-non-real contribution cancel. It is substituted from the start rather than
carried as a variable, and the three weights it determines are `b₁ = 5/2 + √2 - A`,
`b₂ = 3/2 + √2`, `b₃ = 1/2 + √2`, satisfying `t² = 4b₂`, `b₁ + b₂ = 2t - A`, `b₁ - b₃ = 2 - A` and
`b₃ + 1 = b₂`.
-/

@[expose] public section

namespace ZetaZeros

variable {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}

/-- The three-range estimate behind (2.5). First range `a² + 4 ≥ 4a`, middle `a² + 1 ≥ 2a`, last
`a ≤ 0 ⟹ a² ≥ 3a`. -/
theorem three_range_simple_plus_real {N dU dV R1 R2 S1 S2 : ℕ} (a : Fin N → ℝ)
    (hdUV : dU ≤ dV) (hdVN : dV ≤ N)
    (hdU : dU ≤ R2 + S1 / 2 + S2 / 2) (hdGap : dV ≤ dU + R1)
    (hfirst : 2 * (R2 : ℝ) + (S1 : ℝ) + 2 * (S2 : ℝ) ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU), a j)
    (hsecond : ∑ j ∈ Finset.univ.filter
        (fun j : Fin N => dU ≤ (j : ℕ) ∧ (j : ℕ) < dV), a j ≤ (R1 : ℝ))
    (hthird : ∀ j : Fin N, dV ≤ (j : ℕ) → a j ≤ 0) :
    3 * ∑ j, a j - (2 * (R1 : ℝ) + 2 * (R2 : ℝ) + (S1 : ℝ)) ≤ ∑ j, a j ^ 2 := by
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
  have hdim_nat : 4 * dU ≤ 4 * R2 + 2 * S1 + 2 * S2 := by omega
  have hdim : 4 * (dU : ℝ) ≤ 4 * (R2 : ℝ) + 2 * (S1 : ℝ) + 2 * (S2 : ℝ) := by
    exact_mod_cast hdim_nat
  have hcardB_real : (B.card : ℝ) ≤ (R1 : ℝ) := by exact_mod_cast hcardB_le
  have hfirstA : 2 * (R2 : ℝ) + (S1 : ℝ) + 2 * (S2 : ℝ) ≤ ∑ j ∈ A, a j := hfirst
  have hsecondB : ∑ j ∈ B, a j ≤ (R1 : ℝ) := hsecond
  have hsqA : 4 * (∑ j ∈ A, a j) - 4 * (A.card : ℝ) ≤ ∑ j ∈ A, a j ^ 2 := by
    calc 4 * (∑ j ∈ A, a j) - 4 * (A.card : ℝ)
        = ∑ j ∈ A, (4 * a j - 4) := by simp [Finset.mul_sum]; ring
      _ ≤ ∑ j ∈ A, a j ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        nlinarith [sq_nonneg (a j - 2)]
  have hsqB : 2 * (∑ j ∈ B, a j) - (B.card : ℝ) ≤ ∑ j ∈ B, a j ^ 2 := by
    calc 2 * (∑ j ∈ B, a j) - (B.card : ℝ)
        = ∑ j ∈ B, (2 * a j - 1) := by simp [Finset.mul_sum]
      _ ≤ ∑ j ∈ B, a j ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        nlinarith [sq_nonneg (a j - 1)]
  have hsqC : 3 * (∑ j ∈ C, a j) ≤ ∑ j ∈ C, a j ^ 2 := by
    calc 3 * (∑ j ∈ C, a j) = ∑ j ∈ C, 3 * a j := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ C, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : dV ≤ (j : ℕ) := by simpa [C] using hj
        nlinarith [sq_nonneg (a j), hthird j hj']
  rw [hcardA] at hsqA
  have hsum (f : Fin N → ℝ) :
      ∑ j, f j = (∑ j ∈ A, f j) + (∑ j ∈ B, f j) + ∑ j ∈ C, f j := by
    rw [← hcover, Finset.sum_union hABC, Finset.sum_union hAB]
  rw [hsum a, hsum (fun j => a j ^ 2)]
  linarith

/-- The three-range estimate behind (2.6). First range `a² ≥ 2at - t²` with `t = 2 + √2`, middle
`a² + 1 ≥ 2a`, last `a ≤ 0` and `A > 0` giving `a² ≥ A a`. The choice of `t` is forced by
`t² - 4t + 2 = 0`, which is what cancels the multiple-non-real contribution. -/
theorem three_range_simple_or_real {N dU dV R1 R2 S1 S2 : ℕ} {Ac : ℝ} (a : Fin N → ℝ)
    (hdUV : dU ≤ dV) (hdVN : dV ≤ N)
    (hdU : dU ≤ R2 + S1 / 2 + S2 / 2) (hdGap : dV ≤ dU + R1)
    (hA1 : 1 ≤ Ac) (hA2 : Ac < 2)
    (hfirst : 2 * (R2 : ℝ) + (S1 : ℝ) + 2 * (S2 : ℝ) ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU), a j)
    (hsecond : ∑ j ∈ Finset.univ.filter
        (fun j : Fin N => dU ≤ (j : ℕ) ∧ (j : ℕ) < dV), a j ≤ (R1 : ℝ))
    (hthird : ∀ j : Fin N, dV ≤ (j : ℕ) → a j ≤ 0)
    (hsq : ∑ j, a j ^ 2 ≤ Ac * ∑ j, a j) :
    (5 + 2 * Real.sqrt 2 - 2 * Ac) / (3 + 2 * Real.sqrt 2) * (∑ j, a j)
      ≤ (R1 : ℝ) + 2 * (R2 : ℝ) + (S1 : ℝ) := by
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
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hdimr : (dU : ℝ) ≤ (R2 : ℝ) + (S1 : ℝ) / 2 + (S2 : ℝ) / 2 := by
    have h2 : 2 * dU ≤ 2 * R2 + S1 + S2 := by omega
    have : (2 : ℝ) * (dU : ℝ) ≤ 2 * (R2 : ℝ) + (S1 : ℝ) + (S2 : ℝ) := by exact_mod_cast h2
    linarith
  have hcardB_real : (B.card : ℝ) ≤ (R1 : ℝ) := by exact_mod_cast hcardB_le
  have hfirstA : 2 * (R2 : ℝ) + (S1 : ℝ) + 2 * (S2 : ℝ) ≤ ∑ j ∈ A, a j := hfirst
  have hsecondB : ∑ j ∈ B, a j ≤ (R1 : ℝ) := hsecond
  have hCle : ∑ j ∈ C, a j ≤ 0 := by
    refine Finset.sum_nonpos fun j hj => ?_
    have hj' : dV ≤ (j : ℕ) := by simpa [C] using hj
    exact hthird j hj'
  -- first range: (a - t)^2 >= 0 with t = 2 + sqrt 2
  have hsqA : 2 * (2 + Real.sqrt 2) * (∑ j ∈ A, a j)
      - (6 + 4 * Real.sqrt 2) * (A.card : ℝ) ≤ ∑ j ∈ A, a j ^ 2 := by
    calc 2 * (2 + Real.sqrt 2) * (∑ j ∈ A, a j) - (6 + 4 * Real.sqrt 2) * (A.card : ℝ)
        = ∑ j ∈ A, (2 * (2 + Real.sqrt 2) * a j - (6 + 4 * Real.sqrt 2)) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ j ∈ A, a j ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        nlinarith [sq_nonneg (a j - (2 + Real.sqrt 2)), hs2]
  have hsqB : 2 * (∑ j ∈ B, a j) - (B.card : ℝ) ≤ ∑ j ∈ B, a j ^ 2 := by
    calc 2 * (∑ j ∈ B, a j) - (B.card : ℝ)
        = ∑ j ∈ B, (2 * a j - 1) := by simp [Finset.mul_sum]
      _ ≤ ∑ j ∈ B, a j ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        nlinarith [sq_nonneg (a j - 1)]
  have hsqC : Ac * (∑ j ∈ C, a j) ≤ ∑ j ∈ C, a j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' : dV ≤ (j : ℕ) := by simpa [C] using hj
    nlinarith [sq_nonneg (a j), hthird j hj']
  rw [hcardA] at hsqA
  have hsum (f : Fin N → ℝ) :
      ∑ j, f j = (∑ j ∈ A, f j) + (∑ j ∈ B, f j) + ∑ j ∈ C, f j := by
    rw [← hcover, Finset.sum_union hABC, Finset.sum_union hAB]
  rw [hsum a, hsum (fun j => a j ^ 2)] at hsq
  -- the four products linarith cannot form for itself
  have hb2 : (0:ℝ) ≤ 3 / 2 + Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2]
  have hb3 : (0:ℝ) ≤ 1 / 2 + Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2]
  have hb1 : (0:ℝ) < 5 / 2 + Real.sqrt 2 - Ac := by linarith [Real.sqrt_nonneg 2]
  have p1 : 0 ≤ (3 / 2 + Real.sqrt 2) *
      ((∑ j ∈ A, a j) - (2 * (R2 : ℝ) + (S1 : ℝ) + 2 * (S2 : ℝ))) :=
    mul_nonneg hb2 (by linarith)
  have p2 : 0 ≤ (1 / 2 + Real.sqrt 2) * ((R1 : ℝ) - ∑ j ∈ B, a j) :=
    mul_nonneg hb3 (by linarith)
  have p3 : 0 ≤ (6 + 4 * Real.sqrt 2) *
      (((R2 : ℝ) + (S1 : ℝ) / 2 + (S2 : ℝ) / 2) - (dU : ℝ)) :=
    mul_nonneg (by linarith [Real.sqrt_nonneg 2]) (by linarith)
  have p4 : 0 ≤ (5 / 2 + Real.sqrt 2 - Ac) * (-(∑ j ∈ C, a j)) :=
    mul_nonneg (le_of_lt hb1) (by linarith)
  have hden : (0:ℝ) < 3 + 2 * Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2]
  rw [div_mul_eq_mul_div, div_le_iff₀ hden, hsum a]
  linarith [p1, p2, p3, p4, hsqA, hsqB, hsqC, hsq, hCle]

/-- **Lower bound for the simple part plus the real mass** (`prop_simple_plus_real_lower`),
equation (2.5). -/
@[zz_tag "prop_simple_plus_real_lower"]
theorem card_simplePart_add_realMass_lower (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m) (_hZne : Z.Nonempty) :
    3 * (∑ z ∈ Z, (m z : ℝ))
        - (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ ((simplePart Z m).card : ℝ) + ∑ z ∈ allRealPart Z, (m z : ℝ) := by
  classical
  obtain ⟨psi, hb, hsym⟩ := exists_symmetric_adapted_basis h Z m
  let a : Fin (Module.finrank ℂ (subspaceW h Z m)) → ℝ :=
    fun j => (alphaOf eta lam Z m (psi j)).re
  have hdUV : Module.finrank ℂ (subspaceU h Z m) ≤ Module.finrank ℂ (subspaceV h Z m) :=
    Submodule.finrank_mono (subspaceU_le_subspaceV h Z m)
  have hdVN : Module.finrank ℂ (subspaceV h Z m) ≤ Module.finrank ℂ (subspaceW h Z m) :=
    Submodule.finrank_mono (subspaceV_le_subspaceW h Z m)
  have hdU : Module.finrank ℂ (subspaceU h Z m)
      ≤ (multipleRealPart Z m).card + (simpleNonRealPart Z m).card / 2
        + (multipleNonRealPart Z m).card / 2 := by
    have hU := finrank_subspaceU_le h hZ
    have hcard : (nonRealPart Z).card
        = (simpleNonRealPart Z m).card + (multipleNonRealPart Z m).card := by
      simpa using sum_nonRealPart_eq_sum_simpleNonRealPart_add_sum_multipleNonRealPart
        (m := m) hZ (fun _ => (1 : ℕ))
    have h1 := two_dvd_card_simpleNonRealPart (m := m) hZ
    have h2 := two_dvd_card_multipleNonRealPart (m := m) hZ
    omega
  have hrange := three_range_simple_plus_real a hdUV hdVN hdU
    (finrank_subspaceV_le h Z m)
    (sum_alphaOf_re_first_lower_refined h hZ hb hsym)
    (sum_alphaOf_re_le_card_simpleRealPart h hZ hb hsym)
    (fun j hj => alphaOf_re_nonpos h hZ hb (hsym j) hj)
  have htotal := sum_alphaOf_re_eq_sum_mult h hZ hb hsym
  have hbessel := sum_alphaOf_re_sq_le_integral_norm_bigF_sq_adapted h Z m hZ hb hsym
  have hmoment := sum_testKernel_sq_re_eq_integral_norm_bigF_sq h hZ
  change 3 * (∑ j, a j) - _ ≤ ∑ j, a j ^ 2 at hrange
  change ∑ j, a j = ∑ z ∈ Z, (m z : ℝ) at htotal
  change ∑ j, a j ^ 2 ≤ _ at hbessel
  rw [← hmoment] at hbessel
  have hsimple := card_simplePart_eq (Z := Z) (m := m)
  have hmass := le_sum_allRealPart (m := m) hZ
  rw [hsimple]
  push_cast
  linarith

/-- **Lower bound for the simple-or-real mass** (`prop_simple_or_real_lower`), equation (2.6). -/
@[zz_tag "prop_simple_or_real_lower"]
theorem simpleOrRealMass_lower {Ac : ℝ} (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m) (_hZne : Z.Nonempty) (hA1 : 1 ≤ Ac) (hA2 : Ac < 2)
    (hbound : (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ Ac * ∑ z ∈ Z, (m z : ℝ)) :
    (5 + 2 * Real.sqrt 2 - 2 * Ac) / (3 + 2 * Real.sqrt 2) * (∑ z ∈ Z, (m z : ℝ))
      ≤ ∑ z ∈ simpleOrRealPart Z m, (m z : ℝ) := by
  classical
  obtain ⟨psi, hb, hsym⟩ := exists_symmetric_adapted_basis h Z m
  let a : Fin (Module.finrank ℂ (subspaceW h Z m)) → ℝ :=
    fun j => (alphaOf eta lam Z m (psi j)).re
  have hdUV : Module.finrank ℂ (subspaceU h Z m) ≤ Module.finrank ℂ (subspaceV h Z m) :=
    Submodule.finrank_mono (subspaceU_le_subspaceV h Z m)
  have hdVN : Module.finrank ℂ (subspaceV h Z m) ≤ Module.finrank ℂ (subspaceW h Z m) :=
    Submodule.finrank_mono (subspaceV_le_subspaceW h Z m)
  have hdU : Module.finrank ℂ (subspaceU h Z m)
      ≤ (multipleRealPart Z m).card + (simpleNonRealPart Z m).card / 2
        + (multipleNonRealPart Z m).card / 2 := by
    have hU := finrank_subspaceU_le h hZ
    have hcard : (nonRealPart Z).card
        = (simpleNonRealPart Z m).card + (multipleNonRealPart Z m).card := by
      simpa using sum_nonRealPart_eq_sum_simpleNonRealPart_add_sum_multipleNonRealPart
        (m := m) hZ (fun _ => (1 : ℕ))
    have h1 := two_dvd_card_simpleNonRealPart (m := m) hZ
    have h2 := two_dvd_card_multipleNonRealPart (m := m) hZ
    omega
  have htotal := sum_alphaOf_re_eq_sum_mult h hZ hb hsym
  have hbessel := sum_alphaOf_re_sq_le_integral_norm_bigF_sq_adapted h Z m hZ hb hsym
  have hmoment := sum_testKernel_sq_re_eq_integral_norm_bigF_sq h hZ
  change ∑ j, a j = ∑ z ∈ Z, (m z : ℝ) at htotal
  change ∑ j, a j ^ 2 ≤ _ at hbessel
  rw [← hmoment] at hbessel
  have hsq : ∑ j, a j ^ 2 ≤ Ac * ∑ j, a j := by rw [htotal]; linarith
  have hrange := three_range_simple_or_real a hdUV hdVN hdU
    (finrank_subspaceV_le h Z m) hA1 hA2
    (sum_alphaOf_re_first_lower_refined h hZ hb hsym)
    (sum_alphaOf_re_le_card_simpleRealPart h hZ hb hsym)
    (fun j hj => alphaOf_re_nonpos h hZ hb (hsym j) hj) hsq
  rw [htotal] at hrange
  have hmass := le_sum_simpleOrRealPart (m := m) hZ
  linarith

end ZetaZeros
