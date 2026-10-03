/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.PSeries
public import ZetaZeros.Zeta.AllZeros
public import ZetaZeros.PairCorrelation.DenominatorBound
public import ZetaZeros.ZeroCount.LocalCount
public import ZetaZeros.Zeta.OrderConj

/-!
# Sums over the zeros, weighted by the local count

Sums over the zeros of `ζ` whose terms decay quadratically in the distance from the ordinate of the
zero to a real height `t`, controlled by the local count `N (t + 1) - N t = O(log (|t| + 3))`. The
local count, a statement about the zeros of positive ordinate, gives a bound `O(log (|t| + 3))` for
the total multiplicity of the zeros of `𝒩*` in a unit window around an arbitrary real height `t`;
grouping the zeros by the integer part of `|im ρ - t|` turns this into the Poisson-weighted bound
`∑_ρ m_ρ / (1 + (t - im ρ)²) = O(log (|t| + 3))`. In particular the series defining `ℓ (x, t)`
converges absolutely.

## Main definitions

* `ZetaZeros.zeroSide`: the sum over zeros `ℓ (x, t)`.

## Main results

* `ZetaZeros.exists_finsum_zeroMultiplicity_window_le`: the zeros of `𝒩*` within `1` of a height
  `t` have total multiplicity `O(log (|t| + 3))`.
* `ZetaZeros.exists_summable_poissonWeight_tsum_le`: the Poisson-weighted count
  `∑_{ρ ∈ 𝒩*} m_ρ / (1 + (t - im ρ)²)` converges and is `O(log (|t| + 3))`.
* `ZetaZeros.exists_finsum_poissonWeight_nontrivialZeros_le`: for `t` outside `[0, T]` the same
  weight summed over `𝒩 (T)` is `O(log T / (1 + dist (t, [0, T])))`.
* `ZetaZeros.exists_summable_norm_zeroSideTerm_tsum_le`, `ZetaZeros.summable_zeroSideTerm`: the
  terms of `ℓ (x, t)` are absolutely summable, with
  `∑_ρ m_ρ |2 x^{ρ - 1/2 - it} / (1 - (ρ - (1/2 + it))²)| = O(√x log (|t| + 3))`.
* `ZetaZeros.exists_summable_poissonIntegral_outside_tsum_le`: the same weight *integrated* over
  `t ∈ [0, T]` and summed over the zeros of ordinate outside `(0, T]` is `O(log² T)`.
-/

@[expose] public section

namespace ZetaZeros

open Complex

/-! ### Elementary bookkeeping for sums of multiplicities -/

/-- `log (|t| + 3) ≥ 1` for every real `t`. -/
private lemma one_le_log_abs_add_three (t : ℝ) : (1 : ℝ) ≤ Real.log (|t| + 3) := by
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
  exact hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))

/-- Enlarging the index set of a sum of multiplicities can only increase it. -/
private lemma finsum_mult_le_of_subset {A B : Set ℂ} (hB : B.Finite) (hAB : A ⊆ B) :
    ∑ᶠ ρ ∈ A, zeroMultiplicity ρ ≤ ∑ᶠ ρ ∈ B, zeroMultiplicity ρ := by
  classical
  have hA := hB.subset hAB
  rw [finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hB]
  exact Finset.sum_le_sum_of_subset (Set.Finite.toFinset_subset_toFinset.mpr hAB)

/-- A sum of multiplicities over a set covered by two finite sets is at most the sum of the two
sums. -/
private lemma finsum_mult_le_add {A B C : Set ℂ} (hB : B.Finite) (hC : C.Finite)
    (h : A ⊆ B ∪ C) :
    ∑ᶠ ρ ∈ A, zeroMultiplicity ρ
      ≤ (∑ᶠ ρ ∈ B, zeroMultiplicity ρ) + ∑ᶠ ρ ∈ C, zeroMultiplicity ρ := by
  classical
  have hBC : (B ∪ C).Finite := hB.union hC
  refine (finsum_mult_le_of_subset hBC h).trans ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hBC, finsum_mem_eq_finite_toFinset_sum _ hB,
    finsum_mem_eq_finite_toFinset_sum _ hC, hB.toFinset_union hC hBC]
  have := Finset.sum_union_inter (s₁ := hB.toFinset) (s₂ := hC.toFinset) (f := zeroMultiplicity)
  omega

/-- The zeros of `𝒩*` whose ordinate lies within `1` of `t` form a finite set. -/
private lemma window_finite (t : ℝ) : {ρ ∈ allZeros | |ρ.im - t| ≤ 1}.Finite := by
  refine ((isCompact_closedBall (0 : ℂ) (2 + |t|)).inter_riemannZetaZeros_finite).subset
    fun ρ hρ => ?_
  obtain ⟨⟨hζ, h₀, h₁⟩, him⟩ := hρ
  refine ⟨?_, mem_riemannZetaZeros.mpr hζ⟩
  have h : |ρ.im| ≤ 1 + |t| := by
    have h1 := (abs_le.1 him).1
    have h2 := (abs_le.1 him).2
    have h3 := le_abs_self t
    have h4 := neg_abs_le t
    rw [abs_le]
    constructor <;> linarith
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    _ ≤ 2 + |t| := by rw [abs_of_pos h₀]; linarith

/-! ### From the local count to a unit window at an arbitrary height -/

/-- For `a ≤ b`, `N b` is `N a` plus the total multiplicity of the zeros with `a < im ρ ≤ b`. -/
private lemma zeroCount_eq_add_finsum {a b : ℝ} (hab : a ≤ b) :
    zeroCount b
      = zeroCount a + ∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros b | a < ρ.im}, zeroMultiplicity ρ := by
  classical
  have hB : (nontrivialZeros b).Finite := nontrivialZeros_finite _
  have hA : (nontrivialZeros a).Finite := nontrivialZeros_finite _
  have hW : {ρ ∈ nontrivialZeros b | a < ρ.im}.Finite := hB.subset fun _ h => h.1
  rw [zeroCount, zeroCount, finsum_mem_eq_finite_toFinset_sum _ hB,
    finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hW]
  have hdisj : Disjoint hA.toFinset hW.toFinset := by
    rw [Finset.disjoint_left]
    intro ρ hρA hρW
    exact absurd (hW.mem_toFinset.1 hρW).2 (not_lt.2 (hA.mem_toFinset.1 hρA).2.2.2.2)
  have hunion : hB.toFinset = hA.toFinset ∪ hW.toFinset := by
    ext ρ
    simp only [Finset.mem_union, Set.Finite.mem_toFinset]
    constructor
    · intro h
      rcases le_or_gt ρ.im a with hle | hlt
      · exact Or.inl ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hle⟩
      · exact Or.inr ⟨h, hlt⟩
    · rintro (h | h)
      · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, le_trans h.2.2.2.2 hab⟩
      · exact h.1
  rw [hunion, Finset.sum_union hdisj]

/-- The local count with a nonnegative constant. -/
private lemma exists_zeroCount_sub_le_nonneg :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, (zeroCount (t + 1) : ℝ) - zeroCount t ≤ C * Real.log (|t| + 3) := by
  obtain ⟨C, hC⟩ := exists_zeroCount_sub_le
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  refine (hC t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact le_trans zero_le_one (one_le_log_abs_add_three t)

/-- **A window of length three.** `N b - N a ≤ C log (a + 3)` whenever `0 ≤ a` and
`b ≤ a + 3`. -/
private lemma exists_zeroCount_sub_le_of_le_add_three :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 0 ≤ a → b ≤ a + 3 →
      (zeroCount b : ℝ) - zeroCount a ≤ C * Real.log (a + 3) := by
  obtain ⟨C, hC0, hC⟩ := exists_zeroCount_sub_le_nonneg
  refine ⟨5 * C, by linarith, fun a b ha hb => ?_⟩
  have hmono : (zeroCount b : ℝ) ≤ (zeroCount (a + 3) : ℝ) := Nat.cast_le.2 (zeroCount_mono hb)
  have h0 := hC a
  have h1 := hC (a + 1)
  have h2 := hC (a + 2)
  rw [abs_of_nonneg ha] at h0
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a + 1), show a + 1 + 1 = a + 2 by ring] at h1
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a + 2), show a + 2 + 1 = a + 3 by ring] at h2
  have hlog0 : (0 : ℝ) ≤ Real.log (a + 3) := Real.log_nonneg (by linarith)
  have h4 : Real.log (a + 1 + 3) ≤ 2 * Real.log (a + 3) := by
    have h := Real.log_le_log (by linarith) (by nlinarith : a + 1 + 3 ≤ (a + 3) ^ 2)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have h5 : Real.log (a + 2 + 3) ≤ 2 * Real.log (a + 3) := by
    have h := Real.log_le_log (by linarith) (by nlinarith : a + 2 + 3 ≤ (a + 3) ^ 2)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have p1 : C * Real.log (a + 1 + 3) ≤ C * (2 * Real.log (a + 3)) :=
    mul_le_mul_of_nonneg_left h4 hC0
  have p2 : C * Real.log (a + 2 + 3) ≤ C * (2 * Real.log (a + 3)) :=
    mul_le_mul_of_nonneg_left h5 hC0
  linarith

/-- The zeros of `𝒩*` within `1` of `t` that lie above the real axis have total multiplicity
`O(log (|t| + 3))`. -/
private lemma exists_finsum_mult_upper_window_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ((∑ᶠ ρ ∈ {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ 0 < ρ.im}, zeroMultiplicity ρ : ℕ) : ℝ)
        ≤ C * Real.log (|t| + 3) := by
  obtain ⟨C, hC0, hC⟩ := exists_zeroCount_sub_le_of_le_add_three
  refine ⟨C, hC0, fun t => ?_⟩
  have hlog0 : (0 : ℝ) ≤ Real.log (|t| + 3) :=
    le_trans zero_le_one (one_le_log_abs_add_three t)
  rcases le_or_gt (t + 1) 0 with ht | ht
  · have hempty : {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ 0 < ρ.im} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun ρ hρ => ?_
      have h1 := (abs_le.1 hρ.2.1).2
      have h2 := hρ.2.2
      linarith
    rw [hempty, finsum_mem_empty]
    exact_mod_cast mul_nonneg hC0 hlog0
  · obtain ⟨a, ha0, hale', hab, hale, halt⟩ :
        ∃ a : ℝ, 0 ≤ a ∧ a ≤ t + 1 ∧ t + 1 ≤ a + 3 ∧ a ≤ |t| ∧
          ∀ u : ℝ, 0 < u → t - 1 ≤ u → a < u := by
      rcases le_or_gt t 2 with h | h
      · exact ⟨0, le_rfl, by linarith, by linarith, abs_nonneg t, fun u hu _ => hu⟩
      · refine ⟨t - 2, by linarith, by linarith, by linarith, ?_, fun u _ hu => by linarith⟩
        rw [abs_of_pos (by linarith : (0 : ℝ) < t)]
        linarith
    have hsub : {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ 0 < ρ.im}
        ⊆ {ρ ∈ nontrivialZeros (t + 1) | a < ρ.im} := by
      intro ρ hρ
      obtain ⟨⟨hζ, h0, h1⟩, hw, hpos⟩ := hρ
      have hup := (abs_le.1 hw).2
      have hlo := (abs_le.1 hw).1
      exact ⟨⟨hζ, h0, h1, hpos, by linarith⟩, halt ρ.im hpos (by linarith)⟩
    have hfin : {ρ ∈ nontrivialZeros (t + 1) | a < ρ.im}.Finite :=
      (nontrivialZeros_finite _).subset fun _ h => h.1
    have hle := finsum_mult_le_of_subset hfin hsub
    have heq : ((∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | a < ρ.im}, zeroMultiplicity ρ : ℕ) : ℝ)
        = (zeroCount (t + 1) : ℝ) - zeroCount a := by
      rw [zeroCount_eq_add_finsum (a := a) (b := t + 1) (by linarith)]
      push_cast
      ring
    have hcast : ((∑ᶠ ρ ∈ {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ 0 < ρ.im},
        zeroMultiplicity ρ : ℕ) : ℝ)
        ≤ ((∑ᶠ ρ ∈ {ρ ∈ nontrivialZeros (t + 1) | a < ρ.im}, zeroMultiplicity ρ : ℕ) : ℝ) :=
      Nat.cast_le.2 hle
    rw [heq] at hcast
    refine hcast.trans ((hC a (t + 1) ha0 hab).trans ?_)
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith) (by linarith)) hC0

/-- Conjugation is a multiplicity-preserving bijection from the zeros of `𝒩*` in the window around
`t` that lie below the real axis onto those in the window around `-t` that lie above it. -/
private lemma finsum_mult_lower_window_eq (t : ℝ) :
    ∑ᶠ ρ ∈ {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ ρ.im < 0}, zeroMultiplicity ρ
      = ∑ᶠ ρ ∈ {ρ ∈ allZeros | |ρ.im - -t| ≤ 1 ∧ 0 < ρ.im}, zeroMultiplicity ρ := by
  have hzeta : ∀ σ : ℂ, riemannZeta σ = 0 → riemannZeta ((starRingEnd ℂ) σ) = 0 := by
    intro σ hσ
    rw [riemannZeta_conj, hσ, map_zero]
  have himage : (starRingEnd ℂ) '' {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ ρ.im < 0}
      = {ρ ∈ allZeros | |ρ.im - -t| ≤ 1 ∧ 0 < ρ.im} := by
    ext ρ
    constructor
    · rintro ⟨σ, ⟨⟨hζ, h0, h1⟩, hw, hneg⟩, rfl⟩
      refine ⟨⟨hzeta σ hζ, by simpa using h0, by simpa using h1⟩, ?_, by simpa using hneg⟩
      have : ((starRingEnd ℂ) σ).im - -t = -(σ.im - t) := by simp; ring
      rw [this, abs_neg]
      exact hw
    · rintro ⟨⟨hζ, h0, h1⟩, hw, hpos⟩
      refine ⟨(starRingEnd ℂ) ρ, ⟨⟨hzeta ρ hζ, by simpa using h0, by simpa using h1⟩, ?_,
        by simpa using hpos⟩, by simp⟩
      have : ((starRingEnd ℂ) ρ).im - t = -(ρ.im - -t) := by simp; ring
      rw [this, abs_neg]
      exact hw
  have hinj : Set.InjOn (starRingEnd ℂ) {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ ρ.im < 0} :=
    fun _ _ _ _ h => (starRingEnd ℂ).injective h
  rw [← himage, finsum_mem_image hinj]
  refine finsum_mem_congr rfl fun ρ hρ => ?_
  have hne : ρ ≠ 1 := by
    intro h
    have := hρ.2.2
    rw [h] at this
    simp at this
  exact (zeroMultiplicity_conj hne).symm

/-- **Zeros in a unit window.** There is an absolute constant `C > 0` such that for every real `t`
the zeros of `𝒩*` whose ordinate lies within `1` of `t` have total multiplicity at most
`C log (|t| + 3)`. -/
@[zz_tag "lem_strip_count"]
theorem exists_finsum_zeroMultiplicity_window_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ((∑ᶠ ρ ∈ {ρ ∈ allZeros | |ρ.im - t| ≤ 1}, zeroMultiplicity ρ : ℕ) : ℝ)
        ≤ C * Real.log (|t| + 3) := by
  obtain ⟨C, hC0, hC⟩ := exists_finsum_mult_upper_window_le
  have hA0 : (0 : ℝ) ≤ ((∑ᶠ ρ ∈ {ρ ∈ allZeros | ρ.im = 0}, zeroMultiplicity ρ : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  refine ⟨2 * C + (∑ᶠ ρ ∈ {ρ ∈ allZeros | ρ.im = 0}, zeroMultiplicity ρ : ℕ) + 1,
    by linarith, fun t => ?_⟩
  have hlog := one_le_log_abs_add_three t
  have hfinP : {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ 0 < ρ.im}.Finite :=
    (window_finite t).subset fun _ h => ⟨h.1, h.2.1⟩
  have hfinM : {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ ρ.im < 0}.Finite :=
    (window_finite t).subset fun _ h => ⟨h.1, h.2.1⟩
  have hfinR : {ρ ∈ allZeros | ρ.im = 0}.Finite := allZeros_im_eq_zero_finite
  have hcover : {ρ ∈ allZeros | |ρ.im - t| ≤ 1}
      ⊆ {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ 0 < ρ.im}
        ∪ ({ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ ρ.im < 0} ∪ {ρ ∈ allZeros | ρ.im = 0}) := by
    intro ρ hρ
    rcases lt_trichotomy ρ.im 0 with h | h | h
    · exact Or.inr (Or.inl ⟨hρ.1, hρ.2, h⟩)
    · exact Or.inr (Or.inr ⟨hρ.1, h⟩)
    · exact Or.inl ⟨hρ.1, hρ.2, h⟩
  have h1 := finsum_mult_le_add hfinP (hfinM.union hfinR) hcover
  have h2 := finsum_mult_le_add hfinM hfinR
    (subset_refl ({ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ ρ.im < 0} ∪ {ρ ∈ allZeros | ρ.im = 0}))
  have hnat : ∑ᶠ ρ ∈ {ρ ∈ allZeros | |ρ.im - t| ≤ 1}, zeroMultiplicity ρ
      ≤ (∑ᶠ ρ ∈ {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ 0 < ρ.im}, zeroMultiplicity ρ)
        + (∑ᶠ ρ ∈ {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ ρ.im < 0}, zeroMultiplicity ρ)
        + ∑ᶠ ρ ∈ {ρ ∈ allZeros | ρ.im = 0}, zeroMultiplicity ρ := by omega
  have hcast := (Nat.cast_le (α := ℝ)).2 hnat
  push_cast at hcast
  have hP := hC t
  have hM : ((∑ᶠ ρ ∈ {ρ ∈ allZeros | |ρ.im - t| ≤ 1 ∧ ρ.im < 0}, zeroMultiplicity ρ : ℕ) : ℝ)
      ≤ C * Real.log (|t| + 3) := by
    rw [finsum_mult_lower_window_eq t]
    have h := hC (-t)
    rwa [abs_neg] at h
  have hA1 : ((∑ᶠ ρ ∈ {ρ ∈ allZeros | ρ.im = 0}, zeroMultiplicity ρ : ℕ) : ℝ)
      ≤ ((∑ᶠ ρ ∈ {ρ ∈ allZeros | ρ.im = 0}, zeroMultiplicity ρ : ℕ) : ℝ)
        * Real.log (|t| + 3) := le_mul_of_one_le_right hA0 hlog
  have hexp : (2 * C + ((∑ᶠ ρ ∈ {ρ ∈ allZeros | ρ.im = 0}, zeroMultiplicity ρ : ℕ) : ℝ) + 1)
      * Real.log (|t| + 3)
      = 2 * (C * Real.log (|t| + 3))
        + ((∑ᶠ ρ ∈ {ρ ∈ allZeros | ρ.im = 0}, zeroMultiplicity ρ : ℕ) : ℝ)
          * Real.log (|t| + 3) + Real.log (|t| + 3) := by ring
  rw [hexp]
  linarith

/-! ### The Poisson-weighted count -/

/-- The unit-window count for a finite set of zeros: a `Finset` of zeros of `𝒩*` within `1` of
`c` has total multiplicity at most `C log (|c| + 3)`. -/
private lemma exists_finset_mult_window_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (S : Finset ℂ), (∀ ρ ∈ S, ρ ∈ allZeros) →
      (∀ ρ ∈ S, |ρ.im - c| ≤ 1) →
      ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) ≤ C * Real.log (|c| + 3) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_finsum_zeroMultiplicity_window_le
  refine ⟨C, hC0.le, fun c S hS hw => ?_⟩
  have hfin := window_finite c
  have hsub : S ⊆ hfin.toFinset := fun ρ hρ => hfin.mem_toFinset.2 ⟨hS ρ hρ, hw ρ hρ⟩
  calc ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ)
      ≤ ∑ ρ ∈ hfin.toFinset, (zeroMultiplicity ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
    _ = ((∑ᶠ ρ ∈ {ρ ∈ allZeros | |ρ.im - c| ≤ 1}, zeroMultiplicity ρ : ℕ) : ℝ) := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
    _ ≤ C * Real.log (|c| + 3) := hC c

/-- If `|c| ≤ |t| + k + 1/2` then `log (|c| + 3) ≤ log (|t| + 3) + log (k + 2)`. -/
private lemma log_abs_add_three_le {c t : ℝ} {k : ℕ} (hc : |c| ≤ |t| + (k : ℝ) + 1 / 2) :
    Real.log (|c| + 3) ≤ Real.log (|t| + 3) + Real.log ((k : ℝ) + 2) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hprod : |c| + 3 ≤ (|t| + 3) * ((k : ℝ) + 2) := by nlinarith [mul_nonneg ht0 hk0]
  calc Real.log (|c| + 3) ≤ Real.log ((|t| + 3) * ((k : ℝ) + 2)) :=
        Real.log_le_log (by linarith [abs_nonneg c]) hprod
    _ = Real.log (|t| + 3) + Real.log ((k : ℝ) + 2) := Real.log_mul (by linarith) (by linarith)

/-- The weight carried by the group of zeros at distance `k` from `t` is nonnegative. -/
private lemma groupWeight_nonneg (k : ℕ) :
    0 ≤ (1 + Real.log ((k : ℝ) + 2)) / (1 + (k : ℝ) ^ 2) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have h : (0 : ℝ) ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
  exact div_nonneg (by linarith) (by positivity)

/-- `(1 + log x) / (1 + y) ≤ 10 x^{-3/2}` when `x ≥ 2` and `x² ≤ 5 (1 + y)`. -/
private lemma one_add_log_div_le {x y : ℝ} (hx : 2 ≤ x) (hy : x ^ 2 ≤ 5 * (1 + y)) :
    (1 + Real.log x) / (1 + y) ≤ 10 * (1 / |x| ^ (3 / 2 : ℝ)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < 1 + y := by nlinarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hlog : Real.log x ≤ 2 * Real.sqrt x - 2 := by
    have h := Real.log_le_sub_one_of_pos hs0
    rw [Real.log_sqrt hx0.le] at h
    linarith
  have hrpow : |x| ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [abs_of_pos hx0, Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hx0, Real.rpow_one]
  rw [hrpow, mul_one_div, div_le_div_iff₀ hy0 (by positivity)]
  have h1 : 1 + Real.log x ≤ 2 * Real.sqrt x := by linarith
  have h3 : 2 * Real.sqrt x * (x * Real.sqrt x) = 2 * x ^ 2 := by
    rw [show 2 * Real.sqrt x * (x * Real.sqrt x) = 2 * x * (Real.sqrt x * Real.sqrt x) by ring,
      hss]
    ring
  nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ x * Real.sqrt x)]

/-- **The grouping weights are summable.** `∑_k (1 + log (k + 2)) / (1 + k²)` converges. -/
private lemma summable_groupWeight :
    Summable fun k : ℕ => (1 + Real.log ((k : ℝ) + 2)) / (1 + (k : ℝ) ^ 2) := by
  have hmaj : Summable fun k : ℕ => 10 * (1 / |(k : ℝ) + 2| ^ (3 / 2 : ℝ)) :=
    ((Real.summable_one_div_nat_add_rpow 2 (3 / 2)).2 (by norm_num)).mul_left 10
  refine Summable.of_nonneg_of_le groupWeight_nonneg (fun k => ?_) hmaj
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  exact one_add_log_div_le (by linarith) (by nlinarith [sq_nonneg (2 * (k : ℝ) - 1)])

/-- **The Poisson-weighted count, for a finite set of zeros.** For every finite set `F` of zeros
of `𝒩*` and every real `t`, `∑_{ρ ∈ F} m_ρ / (1 + (t - im ρ)²) ≤ C log (|t| + 3)` with `C`
absolute. -/
private lemma exists_finset_poisson_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (S : Finset ℂ), (∀ ρ ∈ S, ρ ∈ allZeros) →
      ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) ≤ C * Real.log (|t| + 3) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_finset_mult_window_le
  have hW0 : (0 : ℝ) ≤ ∑' k : ℕ, (1 + Real.log ((k : ℝ) + 2)) / (1 + (k : ℝ) ^ 2) :=
    tsum_nonneg groupWeight_nonneg
  refine ⟨2 * C * ∑' k : ℕ, (1 + Real.log ((k : ℝ) + 2)) / (1 + (k : ℝ) ^ 2),
    mul_nonneg (mul_nonneg (by norm_num) hC0) hW0, fun t S hS => ?_⟩
  have hlog1 := one_le_log_abs_add_three t
  have hlog0 : (0 : ℝ) ≤ Real.log (|t| + 3) := by linarith
  have hmaps : ∀ ρ ∈ S, ⌊|ρ.im - t|⌋₊ ∈ Finset.range (S.sup (fun ρ => ⌊|ρ.im - t|⌋₊) + 1) :=
    fun ρ hρ => Finset.mem_range_succ_iff.2
      (Finset.le_sup (f := fun ρ : ℂ => ⌊|ρ.im - t|⌋₊) hρ)
  have hfiber : ∀ j : ℕ,
      ∑ ρ ∈ S with ⌊|ρ.im - t|⌋₊ = j, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
        ≤ 2 * C * Real.log (|t| + 3) * ((1 + Real.log ((j : ℝ) + 2)) / (1 + (j : ℝ) ^ 2)) := by
    intro j
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    have hjpos : (0 : ℝ) < 1 + (j : ℝ) ^ 2 := by positivity
    have hlogj : (0 : ℝ) ≤ Real.log ((j : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hstep : ∀ ρ ∈ S.filter (fun ρ => ⌊|ρ.im - t|⌋₊ = j),
        (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
          ≤ (zeroMultiplicity ρ : ℝ) / (1 + (j : ℝ) ^ 2) := by
      intro ρ hρ
      have hj : ⌊|ρ.im - t|⌋₊ = j := (Finset.mem_filter.1 hρ).2
      have hle : (j : ℝ) ≤ |ρ.im - t| := by rw [← hj]; exact Nat.floor_le (abs_nonneg _)
      have hsq : (j : ℝ) ^ 2 ≤ (t - ρ.im) ^ 2 := by
        have h1 : (t - ρ.im) ^ 2 = |ρ.im - t| ^ 2 := by rw [sq_abs]; ring
        rw [h1]
        exact pow_le_pow_left₀ hj0 hle 2
      have hm0 : (0 : ℝ) ≤ (zeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
      gcongr
    have hsum1 : ∑ ρ ∈ S with ⌊|ρ.im - t|⌋₊ = j, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
        ≤ (∑ ρ ∈ S with ⌊|ρ.im - t|⌋₊ = j, (zeroMultiplicity ρ : ℝ)) / (1 + (j : ℝ) ^ 2) := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum hstep
    have hup : ∑ ρ ∈ S.filter (fun ρ => ⌊|ρ.im - t|⌋₊ = j) with t ≤ ρ.im,
          (zeroMultiplicity ρ : ℝ) ≤ C * (Real.log (|t| + 3) + Real.log ((j : ℝ) + 2)) := by
      refine (hC (t + (j : ℝ) + 1 / 2) _ ?_ ?_).trans ?_
      · exact fun ρ hρ => hS ρ (Finset.mem_filter.1 (Finset.mem_filter.1 hρ).1).1
      · intro ρ hρ
        have hj : ⌊|ρ.im - t|⌋₊ = j := (Finset.mem_filter.1 (Finset.mem_filter.1 hρ).1).2
        have ht : t ≤ ρ.im := (Finset.mem_filter.1 hρ).2
        have h1 : (j : ℝ) ≤ |ρ.im - t| := by rw [← hj]; exact Nat.floor_le (abs_nonneg _)
        have h2 : |ρ.im - t| < (j : ℝ) + 1 := by rw [← hj]; exact Nat.lt_floor_add_one _
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ.im - t)] at h1 h2
        rw [abs_le]
        constructor <;> linarith
      · refine mul_le_mul_of_nonneg_left (log_abs_add_three_le ?_) hC0
        rw [abs_le]
        constructor <;> linarith [le_abs_self t, neg_abs_le t]
    have hdown : ∑ ρ ∈ S.filter (fun ρ => ⌊|ρ.im - t|⌋₊ = j) with ¬ t ≤ ρ.im,
          (zeroMultiplicity ρ : ℝ) ≤ C * (Real.log (|t| + 3) + Real.log ((j : ℝ) + 2)) := by
      refine (hC (t - (j : ℝ) - 1 / 2) _ ?_ ?_).trans ?_
      · exact fun ρ hρ => hS ρ (Finset.mem_filter.1 (Finset.mem_filter.1 hρ).1).1
      · intro ρ hρ
        have hj : ⌊|ρ.im - t|⌋₊ = j := (Finset.mem_filter.1 (Finset.mem_filter.1 hρ).1).2
        have ht : ¬ t ≤ ρ.im := (Finset.mem_filter.1 hρ).2
        have h1 : (j : ℝ) ≤ |ρ.im - t| := by rw [← hj]; exact Nat.floor_le (abs_nonneg _)
        have h2 : |ρ.im - t| < (j : ℝ) + 1 := by rw [← hj]; exact Nat.lt_floor_add_one _
        rw [abs_of_neg (by linarith [not_le.1 ht] : ρ.im - t < 0)] at h1 h2
        rw [abs_le]
        constructor <;> linarith
      · refine mul_le_mul_of_nonneg_left (log_abs_add_three_le ?_) hC0
        rw [abs_le]
        constructor <;> linarith [le_abs_self t, neg_abs_le t]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (S.filter (fun ρ => ⌊|ρ.im - t|⌋₊ = j)) (fun ρ => t ≤ ρ.im)
      (fun ρ => (zeroMultiplicity ρ : ℝ))
    have hmult : ∑ ρ ∈ S with ⌊|ρ.im - t|⌋₊ = j, (zeroMultiplicity ρ : ℝ)
        ≤ 2 * C * (Real.log (|t| + 3) + Real.log ((j : ℝ) + 2)) := by linarith
    calc ∑ ρ ∈ S with ⌊|ρ.im - t|⌋₊ = j, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
        ≤ (∑ ρ ∈ S with ⌊|ρ.im - t|⌋₊ = j, (zeroMultiplicity ρ : ℝ)) / (1 + (j : ℝ) ^ 2) := hsum1
      _ ≤ (2 * C * Real.log (|t| + 3) * (1 + Real.log ((j : ℝ) + 2))) / (1 + (j : ℝ) ^ 2) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [mul_nonneg (mul_nonneg hC0 hlogj) (sub_nonneg.2 hlog1)]
      _ = 2 * C * Real.log (|t| + 3) * ((1 + Real.log ((j : ℝ) + 2)) / (1 + (j : ℝ) ^ 2)) := by
          ring
  calc ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
      = ∑ j ∈ Finset.range (S.sup (fun ρ => ⌊|ρ.im - t|⌋₊) + 1),
          ∑ ρ ∈ S with ⌊|ρ.im - t|⌋₊ = j, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ j ∈ Finset.range (S.sup (fun ρ => ⌊|ρ.im - t|⌋₊) + 1),
          2 * C * Real.log (|t| + 3) * ((1 + Real.log ((j : ℝ) + 2)) / (1 + (j : ℝ) ^ 2)) :=
        Finset.sum_le_sum fun j _ => hfiber j
    _ = 2 * C * Real.log (|t| + 3) * ∑ j ∈ Finset.range (S.sup (fun ρ => ⌊|ρ.im - t|⌋₊) + 1),
          (1 + Real.log ((j : ℝ) + 2)) / (1 + (j : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 2 * C * Real.log (|t| + 3)
          * ∑' k : ℕ, (1 + Real.log ((k : ℝ) + 2)) / (1 + (k : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (by norm_num) hC0) hlog0)
        exact summable_groupWeight.sum_le_tsum _ fun i _ => groupWeight_nonneg i
    _ = 2 * C * (∑' k : ℕ, (1 + Real.log ((k : ℝ) + 2)) / (1 + (k : ℝ) ^ 2))
          * Real.log (|t| + 3) := by ring

/-- **The Poisson-weighted count of zeros.** There is an absolute constant `C > 0` such that for
every real `t` the series `∑_{ρ ∈ 𝒩*} m_ρ / (1 + (t - im ρ)²)` converges, with sum at most
`C log (|t| + 3)`. -/
@[zz_tag "lem_local_mult_sum"]
theorem exists_summable_poissonWeight_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      Summable (fun ρ : allZeros => (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)) ∧
        ∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)
          ≤ C * Real.log (|t| + 3) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_finset_poisson_le
  refine ⟨C + 1, by linarith, fun t => ?_⟩
  have hlog1 := one_le_log_abs_add_three t
  have hf0 : ∀ ρ : allZeros,
      (0 : ℝ) ≤ (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) := by
    intro ρ
    positivity
  have hbound : ∀ u : Finset allZeros,
      ∑ ρ ∈ u, (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)
        ≤ (C + 1) * Real.log (|t| + 3) := by
    intro u
    have himg : ∑ ρ ∈ u, (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)
        = ∑ ρ ∈ u.image Subtype.val, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) :=
      (Finset.sum_image (f := fun ρ : ℂ => (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2))
        (g := Subtype.val) (s := u) fun _ _ _ _ h => Subtype.ext h).symm
    rw [himg]
    refine (hC t _ ?_).trans ?_
    · intro ρ hρ
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hρ
      exact σ.2
    · exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  exact ⟨summable_of_sum_le hf0 hbound, Real.tsum_le_of_sum_le hf0 hbound⟩

/-! ### The sum over zeros -/

/-- **The complete sum over zeros.** For `x ≥ 1` and real `t`,
`ℓ (x, t) = ∑_{ρ ∈ 𝒩*} m_ρ ⬝ 2 x^{ρ - 1/2 - it} / (1 - (ρ - (1/2 + it))²)`, the zero side of
Montgomery's explicit-formula lemma. -/
@[zz_tag "def_zero_side"]
noncomputable def zeroSide (x t : ℝ) : ℂ :=
  ∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℂ) *
    (2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
      / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2))

/-- For `m ≥ 0`, `0 ≤ v ≤ w` and a denominator `N ≥ 3/4 (1 + s²)`,
`m ⬝ 2 v / N ≤ 8/3 ⬝ w ⬝ m / (1 + s²)`. -/
private lemma mul_two_div_le {m s N v w : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) (hvw : v ≤ w)
    (hN : 3 / 4 * (1 + s ^ 2) ≤ N) :
    m * (2 * v / N) ≤ 8 / 3 * w * (m / (1 + s ^ 2)) := by
  have hs : (0 : ℝ) < 1 + s ^ 2 := by positivity
  have hNpos : (0 : ℝ) < N := by nlinarith
  have hstep : 2 * v / N ≤ 2 * w / (3 / 4 * (1 + s ^ 2)) := by
    rw [div_le_div_iff₀ hNpos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hvw (by positivity : (0 : ℝ) ≤ 3 / 4 * (1 + s ^ 2)),
      mul_le_mul_of_nonneg_left hN (by linarith : (0 : ℝ) ≤ 2 * w)]
  refine (mul_le_mul_of_nonneg_left hstep hm).trans_eq ?_
  field_simp
  ring

/-- For `x ≥ 1` and `ρ ∈ 𝒩*`, the term of `ℓ (x, t)` at `ρ` has absolute value at most
`8/3 ⬝ √x ⬝ m_ρ / (1 + (t - im ρ)²)`. -/
private lemma mul_norm_zeroSideTerm_le {x t : ℝ} (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ ∈ allZeros) :
    (zeroMultiplicity ρ : ℝ) * ‖2 * (x : ℂ) ^ (ρ - 1 / 2 - (t : ℂ) * I)
        / (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2)‖
      ≤ 8 / 3 * Real.sqrt x * ((zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) := by
  obtain ⟨-, h0, h1⟩ := hρ
  have hx0 : (0 : ℝ) < x := by linarith
  have hre : (ρ - 1 / 2 - (t : ℂ) * I).re = ρ.re - 1 / 2 := by simp
  have hnorm : ‖2 * (x : ℂ) ^ (ρ - 1 / 2 - (t : ℂ) * I)
      / (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2)‖
      = 2 * x ^ (ρ.re - 1 / 2) / ‖1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2‖ := by
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
    norm_num
  rw [hnorm]
  refine mul_two_div_le (Nat.cast_nonneg _) (Real.rpow_nonneg hx0.le _) ?_ ?_
  · rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  · have hden := three_quarters_add_sq_le_norm_one_sub_sq h0 h1 t
    nlinarith [sq_nonneg (t - ρ.im)]

/-- **The trivial bound for the sum over zeros.** There is an absolute constant `C > 0` such that
for all `x ≥ 1` and all real `t` the series of absolute values of the terms of `ℓ (x, t)`
converges, with sum at most `C √x log (|t| + 3)`. -/
@[zz_tag "lem_l_bound"]
theorem exists_summable_norm_zeroSideTerm_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x t : ℝ, 1 ≤ x →
      Summable (fun ρ : allZeros => (zeroMultiplicity (ρ : ℂ) : ℝ) *
          ‖2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
            / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2)‖) ∧
        ∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℝ) *
            ‖2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
              / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2)‖
          ≤ C * Real.sqrt x * Real.log (|t| + 3) := by
  obtain ⟨C, hC0, hC⟩ := exists_summable_poissonWeight_tsum_le
  refine ⟨3 * C, by linarith, fun x t hx => ?_⟩
  obtain ⟨hsum, hle⟩ := hC t
  have hsqrt : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hlog0 : (0 : ℝ) ≤ Real.log (|t| + 3) :=
    le_trans zero_le_one (one_le_log_abs_add_three t)
  have hmaj : Summable fun ρ : allZeros =>
      8 / 3 * Real.sqrt x * ((zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)) :=
    hsum.mul_left _
  have hptwise : ∀ ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℝ) *
      ‖2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
        / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2)‖
      ≤ 8 / 3 * Real.sqrt x
        * ((zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)) :=
    fun ρ => mul_norm_zeroSideTerm_le hx ρ.2
  have hnonneg : ∀ ρ : allZeros, (0 : ℝ) ≤ (zeroMultiplicity (ρ : ℂ) : ℝ) *
      ‖2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
        / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2)‖ := by
    intro ρ
    positivity
  have hsummable := Summable.of_nonneg_of_le hnonneg hptwise hmaj
  refine ⟨hsummable, ?_⟩
  calc ∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℝ) *
        ‖2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
          / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2)‖
      ≤ ∑' ρ : allZeros, 8 / 3 * Real.sqrt x
          * ((zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)) :=
        hsummable.tsum_le_tsum hptwise hmaj
    _ = 8 / 3 * Real.sqrt x
          * ∑' ρ : allZeros, (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) :=
        tsum_mul_left
    _ ≤ 8 / 3 * Real.sqrt x * (C * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ 3 * C * Real.sqrt x * Real.log (|t| + 3) := by
        nlinarith [mul_nonneg (mul_nonneg hC0.le hsqrt) hlog0]

/-- The series defining `ℓ (x, t)` converges absolutely for `x ≥ 1`. -/
theorem summable_zeroSideTerm {x t : ℝ} (hx : 1 ≤ x) :
    Summable fun ρ : allZeros => (zeroMultiplicity (ρ : ℂ) : ℂ) *
      (2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
        / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2)) := by
  obtain ⟨C, -, hC⟩ := exists_summable_norm_zeroSideTerm_tsum_le
  refine Summable.of_norm ((hC x t hx).1.congr fun ρ => ?_)
  simp

/-! ### The zeros seen from outside the range -/

/-- `1 / (1 + u²) ≤ 5 (1/(1 + u) - 1/(2 + u))` for `u ≥ 0`. -/
private lemma inv_one_add_sq_le_telescope {u : ℝ} (hu : 0 ≤ u) :
    1 / (1 + u ^ 2) ≤ 5 * (1 / (1 + u) - 1 / (2 + u)) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : (0 : ℝ) < 2 + u := by linarith
  have h3 : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have heq : 1 / (1 + u) - 1 / (2 + u) = 1 / ((1 + u) * (2 + u)) := by field_simp; ring
  rw [heq, mul_one_div, div_le_div_iff₀ h3 (by positivity)]
  nlinarith [sq_nonneg (8 * u - 3)]

/-- The telescoping sum itself: `∑_{j < n} (1/(1 + d + j) - 1/(2 + d + j)) ≤ 1/(1 + d)`. -/
private lemma sum_telescope_le {d : ℝ} (hd : 0 ≤ d) (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 / (1 + (d + (j : ℝ))) - 1 / (2 + (d + (j : ℝ)))) ≤ 1 / (1 + d) := by
  have key : ∀ m : ℕ, ∑ j ∈ Finset.range m,
      (1 / (1 + (d + (j : ℝ))) - 1 / (2 + (d + (j : ℝ))))
        = 1 / (1 + d) - 1 / (1 + (d + (m : ℝ))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  rw [key n]
  have h : (0 : ℝ) ≤ 1 / (1 + (d + (n : ℝ))) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    positivity
  linarith

/-- **The count seen from outside the range.** There is an absolute constant `C > 0` such that for
every `T ≥ 3` and every real `t` outside `[0, T]`,
`∑_{ρ ∈ 𝒩 (T)} m_ρ / (1 + (t - im ρ)²) ≤ C log T / (1 + d)`, where `d = min {|t|, |t - T|}` is the
distance from `t` to the range. -/
@[zz_tag "lem_outside_sum_bound"]
theorem exists_finsum_poissonWeight_nontrivialZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T t : ℝ, 3 ≤ T → t ∉ Set.Icc (0 : ℝ) T →
      ∑ᶠ ρ ∈ nontrivialZeros T, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
        ≤ C * Real.log T / (1 + min |t| |t - T|) := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_finset_mult_window_le
  refine ⟨20 * C₁ + 1, by linarith, fun T t hT ht => ?_⟩
  have hlogT : (1 : ℝ) ≤ Real.log T := by
    have h : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
    exact h.le.trans (Real.log_le_log (by norm_num) hT)
  have hfin := nontrivialZeros_finite T
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  set d := min |t| |t - T| with hdef
  have hd0 : (0 : ℝ) ≤ d := by rw [hdef]; exact le_min (abs_nonneg t) (abs_nonneg _)
  have hdpos : (0 : ℝ) < 1 + d := by linarith
  have hmem : ∀ ρ ∈ hfin.toFinset, ρ ∈ allZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
    intro ρ hρ
    have h := hfin.mem_toFinset.1 hρ
    exact ⟨nontrivialZeros_subset_allZeros T h, h.2.2.2.1, h.2.2.2.2⟩
  have hbdd : ∀ ρ ∈ hfin.toFinset, |ρ.im| ≤ T := by
    intro ρ hρ
    obtain ⟨-, hpos, hle⟩ := hmem ρ hρ
    rw [abs_of_pos hpos]
    exact hle
  have hdist : ∀ ρ ∈ hfin.toFinset, d ≤ |ρ.im - t| := by
    intro ρ hρ
    obtain ⟨-, hpos, hle⟩ := hmem ρ hρ
    rcases lt_or_ge t 0 with h | h
    · have h1 : d ≤ |t| := by rw [hdef]; exact min_le_left _ _
      rw [abs_of_neg h] at h1
      rw [abs_of_pos (by linarith : (0 : ℝ) < ρ.im - t)]
      linarith
    · have hTt : T < t := by
        by_contra hc
        exact ht (Set.mem_Icc.2 ⟨h, not_lt.1 hc⟩)
      have h1 : d ≤ |t - T| := by rw [hdef]; exact min_le_right _ _
      rw [abs_of_pos (by linarith : (0 : ℝ) < t - T)] at h1
      rw [abs_of_neg (by linarith : ρ.im - t < 0)]
      linarith
  have hwin : ∀ (c : ℝ) (F : Finset ℂ), (∀ ρ ∈ F, ρ ∈ allZeros) → (∀ ρ ∈ F, |ρ.im - c| ≤ 1) →
      (∀ ρ ∈ F, |ρ.im| ≤ T) → ∑ ρ ∈ F, (zeroMultiplicity ρ : ℝ) ≤ 2 * C₁ * Real.log T := by
    intro c F hF hw hb
    rcases F.eq_empty_or_nonempty with hE | hne
    · rw [hE, Finset.sum_empty]
      exact mul_nonneg (mul_nonneg (by norm_num) hC₁0) (by linarith)
    · obtain ⟨ρ₀, hρ₀⟩ := hne
      have hc : |c| ≤ T + 1 := by
        have h1 := abs_le.1 (hw ρ₀ hρ₀)
        have h2 := abs_le.1 (hb ρ₀ hρ₀)
        rw [abs_le]
        constructor <;> linarith
      have hlog : Real.log (|c| + 3) ≤ 2 * Real.log T := by
        have hle : |c| + 3 ≤ T ^ 2 := by nlinarith
        calc Real.log (|c| + 3) ≤ Real.log (T ^ 2) :=
              Real.log_le_log (by linarith [abs_nonneg c]) hle
          _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
      refine (hC₁ c F hF hw).trans ?_
      calc C₁ * Real.log (|c| + 3) ≤ C₁ * (2 * Real.log T) :=
            mul_le_mul_of_nonneg_left hlog hC₁0
        _ = 2 * C₁ * Real.log T := by ring
  have hmaps : ∀ ρ ∈ hfin.toFinset, ⌊|ρ.im - t| - d⌋₊
      ∈ Finset.range (hfin.toFinset.sup (fun ρ => ⌊|ρ.im - t| - d⌋₊) + 1) :=
    fun ρ hρ => Finset.mem_range_succ_iff.2
      (Finset.le_sup (f := fun ρ : ℂ => ⌊|ρ.im - t| - d⌋₊) hρ)
  have hfiber : ∀ j : ℕ,
      ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im - t| - d⌋₊ = j,
          (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
        ≤ 20 * C₁ * Real.log T
            * (1 / (1 + (d + (j : ℝ))) - 1 / (2 + (d + (j : ℝ)))) := by
    intro j
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    have hu0 : (0 : ℝ) ≤ d + (j : ℝ) := by linarith
    have hmemF : ∀ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im - t| - d⌋₊ = j),
        d + (j : ℝ) ≤ |ρ.im - t| ∧ |ρ.im - t| < d + (j : ℝ) + 1 := by
      intro ρ hρ
      have hρS := (Finset.mem_filter.1 hρ).1
      have hj : ⌊|ρ.im - t| - d⌋₊ = j := (Finset.mem_filter.1 hρ).2
      have hnn : (0 : ℝ) ≤ |ρ.im - t| - d := by linarith [hdist ρ hρS]
      refine ⟨?_, ?_⟩
      · have h := Nat.floor_le hnn
        rw [hj] at h
        linarith
      · have h := Nat.lt_floor_add_one (|ρ.im - t| - d)
        rw [hj] at h
        linarith
    have hstep : ∀ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im - t| - d⌋₊ = j),
        (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
          ≤ (zeroMultiplicity ρ : ℝ) / (1 + (d + (j : ℝ)) ^ 2) := by
      intro ρ hρ
      have h1 := (hmemF ρ hρ).1
      have hsq : (d + (j : ℝ)) ^ 2 ≤ (t - ρ.im) ^ 2 := by
        have he : (t - ρ.im) ^ 2 = |ρ.im - t| ^ 2 := by rw [sq_abs]; ring
        rw [he]
        exact pow_le_pow_left₀ hu0 h1 2
      have hm0 : (0 : ℝ) ≤ (zeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
      have hjpos : (0 : ℝ) < 1 + (d + (j : ℝ)) ^ 2 := by positivity
      gcongr
    have hsum1 : ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im - t| - d⌋₊ = j,
          (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
        ≤ (∑ ρ ∈ hfin.toFinset with ⌊|ρ.im - t| - d⌋₊ = j, (zeroMultiplicity ρ : ℝ))
            / (1 + (d + (j : ℝ)) ^ 2) := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum hstep
    have hFall : ∀ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im - t| - d⌋₊ = j), ρ ∈ allZeros :=
      fun ρ hρ => (hmem ρ (Finset.mem_filter.1 hρ).1).1
    have hFbd : ∀ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im - t| - d⌋₊ = j), |ρ.im| ≤ T :=
      fun ρ hρ => hbdd ρ (Finset.mem_filter.1 hρ).1
    have hup : ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im - t| - d⌋₊ = j) with t ≤ ρ.im,
        (zeroMultiplicity ρ : ℝ) ≤ 2 * C₁ * Real.log T := by
      refine hwin (t + d + (j : ℝ) + 1 / 2) _
        (fun ρ hρ => hFall ρ (Finset.mem_filter.1 hρ).1) ?_
        (fun ρ hρ => hFbd ρ (Finset.mem_filter.1 hρ).1)
      intro ρ hρ
      have h := hmemF ρ (Finset.mem_filter.1 hρ).1
      have ht' : t ≤ ρ.im := (Finset.mem_filter.1 hρ).2
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ.im - t)] at h
      rw [abs_le]
      constructor <;> linarith [h.1, h.2]
    have hdown : ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ⌊|ρ.im - t| - d⌋₊ = j) with ¬ t ≤ ρ.im,
        (zeroMultiplicity ρ : ℝ) ≤ 2 * C₁ * Real.log T := by
      refine hwin (t - d - (j : ℝ) - 1 / 2) _
        (fun ρ hρ => hFall ρ (Finset.mem_filter.1 hρ).1) ?_
        (fun ρ hρ => hFbd ρ (Finset.mem_filter.1 hρ).1)
      intro ρ hρ
      have h := hmemF ρ (Finset.mem_filter.1 hρ).1
      have ht' : ¬ t ≤ ρ.im := (Finset.mem_filter.1 hρ).2
      rw [abs_of_neg (by linarith [not_le.1 ht'] : ρ.im - t < 0)] at h
      rw [abs_le]
      constructor <;> linarith [h.1, h.2]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (hfin.toFinset.filter (fun ρ => ⌊|ρ.im - t| - d⌋₊ = j)) (fun ρ => t ≤ ρ.im)
      (fun ρ => (zeroMultiplicity ρ : ℝ))
    have hmult : ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im - t| - d⌋₊ = j, (zeroMultiplicity ρ : ℝ)
        ≤ 4 * C₁ * Real.log T := by linarith
    calc ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im - t| - d⌋₊ = j,
          (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
        ≤ (∑ ρ ∈ hfin.toFinset with ⌊|ρ.im - t| - d⌋₊ = j, (zeroMultiplicity ρ : ℝ))
            / (1 + (d + (j : ℝ)) ^ 2) := hsum1
      _ = (∑ ρ ∈ hfin.toFinset with ⌊|ρ.im - t| - d⌋₊ = j, (zeroMultiplicity ρ : ℝ))
            * (1 / (1 + (d + (j : ℝ)) ^ 2)) := by rw [mul_one_div]
      _ ≤ 4 * C₁ * Real.log T
            * (5 * (1 / (1 + (d + (j : ℝ))) - 1 / (2 + (d + (j : ℝ))))) :=
          mul_le_mul hmult (inv_one_add_sq_le_telescope hu0) (by positivity)
            (mul_nonneg (mul_nonneg (by norm_num) hC₁0) (by linarith))
      _ = 20 * C₁ * Real.log T
            * (1 / (1 + (d + (j : ℝ))) - 1 / (2 + (d + (j : ℝ)))) := by ring
  have hcoef : (0 : ℝ) ≤ 20 * C₁ * Real.log T :=
    mul_nonneg (mul_nonneg (by norm_num) hC₁0) (by linarith)
  calc ∑ ρ ∈ hfin.toFinset, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
      = ∑ j ∈ Finset.range (hfin.toFinset.sup (fun ρ => ⌊|ρ.im - t| - d⌋₊) + 1),
          ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im - t| - d⌋₊ = j,
            (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ j ∈ Finset.range (hfin.toFinset.sup (fun ρ => ⌊|ρ.im - t| - d⌋₊) + 1),
          20 * C₁ * Real.log T * (1 / (1 + (d + (j : ℝ))) - 1 / (2 + (d + (j : ℝ)))) :=
        Finset.sum_le_sum fun j _ => hfiber j
    _ = 20 * C₁ * Real.log T
          * ∑ j ∈ Finset.range (hfin.toFinset.sup (fun ρ => ⌊|ρ.im - t| - d⌋₊) + 1),
              (1 / (1 + (d + (j : ℝ))) - 1 / (2 + (d + (j : ℝ)))) := by rw [Finset.mul_sum]
    _ ≤ 20 * C₁ * Real.log T * (1 / (1 + d)) :=
        mul_le_mul_of_nonneg_left (sum_telescope_le hd0 _) hcoef
    _ = 20 * C₁ * Real.log T / (1 + d) := by rw [mul_one_div]
    _ ≤ (20 * C₁ + 1) * Real.log T / (1 + d) := by
        have hL : (0 : ℝ) ≤ Real.log T := by linarith
        gcongr
        linarith

/-! ### The zeros outside the range, integrated

For the zeros whose ordinate lies at distance `h` from `[0, T]`, the Poisson weight integrated over
`t ∈ [0, T]` is `arctan (h + T) - arctan h`, which is `O(T / ((1 + h)(1 + h + T)))`; summed over
these zeros with multiplicity, the total is `O(log² T)`. -/

/-- A telescoping comparison. If `f k ≤ g k - g (k + 1)` for every `k` and `g` is nonnegative, then
every partial sum of `f` over a block `[N, M)` is at most `g N`. -/
private lemma sum_Ico_le_of_le_sub {f g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k)
    (h : ∀ k, f k ≤ g k - g (k + 1)) (N M : ℕ) :
    ∑ k ∈ Finset.Ico N M, f k ≤ g N := by
  calc ∑ k ∈ Finset.Ico N M, f k
      ≤ ∑ k ∈ Finset.Ico N M, (g k - g (k + 1)) := Finset.sum_le_sum fun k _ => h k
    _ = ∑ i ∈ Finset.range (M - N), (g (N + i) - g (N + i + 1)) := by
        rw [Finset.sum_Ico_eq_sum_range]
    _ = g (N + 0) - g (N + (M - N)) := Finset.sum_range_sub' (fun i => g (N + i)) (M - N)
    _ ≤ g N := by simpa using hg (N + (M - N))

/-- `1 / (a + 1) ≤ log (a + 1) - log a` for `a > 0`. -/
private lemma inv_le_log_sub_log {a : ℝ} (ha : 0 < a) :
    1 / (a + 1) ≤ Real.log (a + 1) - Real.log a := by
  have h := Real.log_le_sub_one_of_pos (x := a / (a + 1)) (by positivity)
  rw [Real.log_div ha.ne' (by positivity)] at h
  have he : a / (a + 1) - 1 = -(1 / (a + 1)) := by field_simp; ring
  rw [he] at h
  linarith

/-- `log (a + 1) - log a ≤ 1 / a` for `a > 0`. -/
private lemma log_sub_log_le_inv {a : ℝ} (ha : 0 < a) :
    Real.log (a + 1) - Real.log a ≤ 1 / a := by
  have h := Real.log_le_sub_one_of_pos (x := (a + 1) / a) (by positivity)
  rw [Real.log_div (by positivity) ha.ne'] at h
  have he : (a + 1) / a - 1 = 1 / a := by field_simp; ring
  rw [he] at h
  linarith

/-- **The harmonic head.** `∑_{k < n} 1 / (1 + k) ≤ 2 log (n + 1)`. -/
private lemma sum_range_inv_one_add_le_log (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / (1 + (k : ℝ)) ≤ 2 * Real.log ((n : ℝ) + 1) := by
  have key : ∀ k : ℕ, 1 / (1 + (k : ℝ))
      ≤ 2 * (Real.log (((k + 1 : ℕ) : ℝ) + 1) - Real.log ((k : ℝ) + 1)) := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h := inv_le_log_sub_log (a := (k : ℝ) + 1) (by linarith)
    have hc : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 1 + 1 := by push_cast; ring
    rw [hc]
    calc 1 / (1 + (k : ℝ)) ≤ 2 / ((k : ℝ) + 1 + 1) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
      _ = 2 * (1 / ((k : ℝ) + 1 + 1)) := by ring
      _ ≤ 2 * (Real.log ((k : ℝ) + 1 + 1) - Real.log ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
  calc ∑ k ∈ Finset.range n, 1 / (1 + (k : ℝ))
      ≤ ∑ k ∈ Finset.range n,
          2 * (Real.log (((k + 1 : ℕ) : ℝ) + 1) - Real.log ((k : ℝ) + 1)) :=
        Finset.sum_le_sum fun k _ => key k
    _ = 2 * ∑ k ∈ Finset.range n,
          (Real.log (((k + 1 : ℕ) : ℝ) + 1) - Real.log ((k : ℝ) + 1)) := by rw [Finset.mul_sum]
    _ = 2 * (Real.log ((n : ℝ) + 1) - Real.log (((0 : ℕ) : ℝ) + 1)) := by
        rw [Finset.sum_range_sub (fun k : ℕ => Real.log ((k : ℝ) + 1)) n]
    _ = 2 * Real.log ((n : ℝ) + 1) := by norm_num
/-- **The quadratic tail.** `∑_{N ≤ k < M} (1 + k)^{-2} ≤ 2 / (1 + N)`. -/
private lemma sum_Ico_inv_one_add_sq_le (N M : ℕ) :
    ∑ k ∈ Finset.Ico N M, 1 / (1 + (k : ℝ)) ^ 2 ≤ 2 / (1 + (N : ℝ)) := by
  refine sum_Ico_le_of_le_sub (g := fun k : ℕ => 2 / (1 + (k : ℝ))) (fun k => ?_) (fun k => ?_) N M
  · have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    positivity
  · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : (0 : ℝ) < 1 + (k : ℝ) := by linarith
    have h2 : (0 : ℝ) < 1 + ((k : ℝ) + 1) := by linarith
    push_cast
    rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (k : ℝ)]

/-- **The log-weighted quadratic tail.** `∑_{N ≤ k < M} log (k + 2) / (1 + k)² ≤
2 (log (N + 2) + 1) / (1 + N)`. -/
private lemma sum_Ico_log_div_one_add_sq_le (N M : ℕ) :
    ∑ k ∈ Finset.Ico N M, Real.log ((k : ℝ) + 2) / (1 + (k : ℝ)) ^ 2
      ≤ 2 * (Real.log ((N : ℝ) + 2) + 1) / (1 + (N : ℝ)) := by
  refine sum_Ico_le_of_le_sub
    (g := fun k : ℕ => 2 * (Real.log ((k : ℝ) + 2) + 1) / (1 + (k : ℝ))) (fun k => ?_)
    (fun k => ?_) N M
  · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have : (0 : ℝ) ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
    exact div_nonneg (by linarith) (by linarith)
  · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    set a : ℝ := 1 + (k : ℝ) with hadef
    have ha1 : (1 : ℝ) ≤ a := by rw [hadef]; linarith
    have ha0 : (0 : ℝ) < a := by linarith
    have hL : (0 : ℝ) ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hLa : Real.log ((k : ℝ) + 2) = Real.log (a + 1) := by rw [hadef]; ring_nf
    have hdiff : Real.log (a + 2) - Real.log (a + 1) ≤ 1 / (a + 1) := by
      have h := log_sub_log_le_inv (a := a + 1) (by linarith)
      have he : a + 1 + 1 = a + 2 := by ring
      rwa [he] at h
    have hX : -1 ≤ a * (Real.log (a + 1) - Real.log (a + 2)) := by
      have h2 : a * (Real.log (a + 2) - Real.log (a + 1)) ≤ a * (1 / (a + 1)) :=
        mul_le_mul_of_nonneg_left hdiff ha0.le
      have h3 : a * (1 / (a + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by linarith)]; linarith
      nlinarith
    have hL2 : (0 : ℝ) ≤ Real.log (a + 1) := by rw [← hLa]; exact hL
    push_cast
    have e1 : (k : ℝ) + 2 = a + 1 := by rw [hadef]; ring
    have e2 : (k : ℝ) + 1 + 2 = a + 2 := by rw [hadef]; ring
    have e3 : 1 + ((k : ℝ) + 1) = a + 1 := by rw [hadef]; ring
    rw [e1, e2, e3, div_sub_div _ _ ha0.ne' (by positivity : (a + 1) ≠ 0),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg ha0.le ha0.le)
        (by linarith : (0 : ℝ) ≤ a * (Real.log (a + 1) - Real.log (a + 2)) + 1),
      mul_nonneg hL2 (by nlinarith : (0 : ℝ) ≤ a ^ 2 - a)]

/-- **The weighted series over the groups of zeros is `O(log² T)`.** For `T ≥ 3` and every `M`,
`∑_{k < M} (2 log T + log (k + 2)) ⬝ T / ((1 + k)(1 + k + T)) ≤ 26 log² T`. -/
private lemma sum_range_logWeight_le {T : ℝ} (hT : 3 ≤ T) (M : ℕ) :
    ∑ k ∈ Finset.range M, (2 * Real.log T + Real.log ((k : ℝ) + 2))
        * (T / ((1 + (k : ℝ)) * (1 + (k : ℝ) + T))) ≤ 26 * Real.log T ^ 2 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (1 : ℝ) ≤ Real.log T := by
    have h : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
    exact h.le.trans (Real.log_le_log (by norm_num) hT)
  have hlogsq : Real.log T ≤ Real.log T ^ 2 := by nlinarith
  set f : ℕ → ℝ := fun k => (2 * Real.log T + Real.log ((k : ℝ) + 2))
    * (T / ((1 + (k : ℝ)) * (1 + (k : ℝ) + T))) with hf
  have hf0 : ∀ k : ℕ, 0 ≤ f k := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hL : (0 : ℝ) ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
    rw [hf]
    exact mul_nonneg (by linarith) (by positivity)
  set N : ℕ := ⌈T⌉₊ with hN
  have hNT : T ≤ (N : ℝ) := Nat.le_ceil T
  have hNT1 : (N : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0.le
  have hhead : ∀ k : ℕ, k < N → f k ≤ 4 * Real.log T * (1 / (1 + (k : ℝ))) := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hkT : (k : ℝ) < T := by
      have : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
      linarith
    have hL : Real.log ((k : ℝ) + 2) ≤ 2 * Real.log T := by
      have hle : (k : ℝ) + 2 ≤ T ^ 2 := by nlinarith
      calc Real.log ((k : ℝ) + 2) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hle
        _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
    have hden : T / ((1 + (k : ℝ)) * (1 + (k : ℝ) + T)) ≤ 1 / (1 + (k : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hk0 hT0.le]
    rw [hf]
    calc (2 * Real.log T + Real.log ((k : ℝ) + 2)) * (T / ((1 + (k : ℝ)) * (1 + (k : ℝ) + T)))
        ≤ (2 * Real.log T + Real.log ((k : ℝ) + 2)) * (1 / (1 + (k : ℝ))) := by
          refine mul_le_mul_of_nonneg_left hden ?_
          have : (0 : ℝ) ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
          linarith
      _ ≤ 4 * Real.log T * (1 / (1 + (k : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hheadsum : ∑ k ∈ Finset.Ico 0 N, f k ≤ 16 * Real.log T ^ 2 := by
    rw [← Finset.range_eq_Ico]
    calc ∑ k ∈ Finset.range N, f k
        ≤ ∑ k ∈ Finset.range N, 4 * Real.log T * (1 / (1 + (k : ℝ))) :=
          Finset.sum_le_sum fun k hk => hhead k (Finset.mem_range.1 hk)
      _ = 4 * Real.log T * ∑ k ∈ Finset.range N, 1 / (1 + (k : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ 4 * Real.log T * (2 * Real.log ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_one_add_le_log N) (by linarith)
      _ ≤ 16 * Real.log T ^ 2 := by
          have hle : (N : ℝ) + 1 ≤ T ^ 2 := by nlinarith
          have h1 : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log T := by
            calc Real.log ((N : ℝ) + 1) ≤ Real.log (T ^ 2) :=
                  Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) N]) hle
              _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
          nlinarith
  have htail : ∀ k : ℕ, f k ≤ 2 * T * Real.log T * (1 / (1 + (k : ℝ)) ^ 2)
      + T * (Real.log ((k : ℝ) + 2) / (1 + (k : ℝ)) ^ 2) := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hL : (0 : ℝ) ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hden : T / ((1 + (k : ℝ)) * (1 + (k : ℝ) + T)) ≤ T / (1 + (k : ℝ)) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hT0.le hT0.le) hk0]
    rw [hf]
    calc (2 * Real.log T + Real.log ((k : ℝ) + 2)) * (T / ((1 + (k : ℝ)) * (1 + (k : ℝ) + T)))
        ≤ (2 * Real.log T + Real.log ((k : ℝ) + 2)) * (T / (1 + (k : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hden (by linarith)
      _ = 2 * T * Real.log T * (1 / (1 + (k : ℝ)) ^ 2)
            + T * (Real.log ((k : ℝ) + 2) / (1 + (k : ℝ)) ^ 2) := by field_simp
  have htailsum : ∀ P : ℕ, ∑ k ∈ Finset.Ico N P, f k ≤ 10 * Real.log T ^ 2 := by
    intro P
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hNpos : (0 : ℝ) < 1 + (N : ℝ) := by positivity
    have hTN : T / (1 + (N : ℝ)) ≤ 1 := by rw [div_le_one hNpos]; linarith
    have hlogN0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hlogN : Real.log ((N : ℝ) + 2) ≤ 2 * Real.log T := by
      have hle : (N : ℝ) + 2 ≤ T ^ 2 := by nlinarith
      calc Real.log ((N : ℝ) + 2) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hle
        _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
    calc ∑ k ∈ Finset.Ico N P, f k
        ≤ ∑ k ∈ Finset.Ico N P, (2 * T * Real.log T * (1 / (1 + (k : ℝ)) ^ 2)
            + T * (Real.log ((k : ℝ) + 2) / (1 + (k : ℝ)) ^ 2)) :=
          Finset.sum_le_sum fun k _ => htail k
      _ = 2 * T * Real.log T * ∑ k ∈ Finset.Ico N P, 1 / (1 + (k : ℝ)) ^ 2
            + T * ∑ k ∈ Finset.Ico N P, Real.log ((k : ℝ) + 2) / (1 + (k : ℝ)) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * T * Real.log T * (2 / (1 + (N : ℝ)))
            + T * (2 * (Real.log ((N : ℝ) + 2) + 1) / (1 + (N : ℝ))) := by
          have h1 := mul_le_mul_of_nonneg_left (sum_Ico_inv_one_add_sq_le N P)
            (by positivity : (0 : ℝ) ≤ 2 * T * Real.log T)
          have h2 := mul_le_mul_of_nonneg_left (sum_Ico_log_div_one_add_sq_le N P) hT0.le
          linarith
      _ ≤ 10 * Real.log T ^ 2 := by
          have e1 : 2 * T * Real.log T * (2 / (1 + (N : ℝ)))
              = 4 * Real.log T * (T / (1 + (N : ℝ))) := by ring
          have e2 : T * (2 * (Real.log ((N : ℝ) + 2) + 1) / (1 + (N : ℝ)))
              = 2 * (Real.log ((N : ℝ) + 2) + 1) * (T / (1 + (N : ℝ))) := by ring
          rw [e1, e2]
          have hb1 : 4 * Real.log T * (T / (1 + (N : ℝ))) ≤ 4 * Real.log T := by
            calc 4 * Real.log T * (T / (1 + (N : ℝ))) ≤ 4 * Real.log T * 1 :=
                  mul_le_mul_of_nonneg_left hTN (by linarith)
              _ = 4 * Real.log T := by ring
          have hb2 : 2 * (Real.log ((N : ℝ) + 2) + 1) * (T / (1 + (N : ℝ)))
              ≤ 2 * (Real.log ((N : ℝ) + 2) + 1) := by
            calc 2 * (Real.log ((N : ℝ) + 2) + 1) * (T / (1 + (N : ℝ)))
                ≤ 2 * (Real.log ((N : ℝ) + 2) + 1) * 1 :=
                  mul_le_mul_of_nonneg_left hTN (by linarith)
              _ = 2 * (Real.log ((N : ℝ) + 2) + 1) := by ring
          linarith
  calc ∑ k ∈ Finset.range M, f k
      ≤ ∑ k ∈ Finset.range (max M N), f k :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun i hi => Finset.mem_range.2
            (lt_of_lt_of_le (Finset.mem_range.1 hi) (le_max_left M N))) fun i _ _ => hf0 i
    _ = ∑ k ∈ Finset.Ico 0 N, f k + ∑ k ∈ Finset.Ico N (max M N), f k := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive f (Nat.zero_le N) (le_max_right M N)]
    _ ≤ 16 * Real.log T ^ 2 + 10 * Real.log T ^ 2 := by
        linarith [htailsum (max M N)]
    _ = 26 * Real.log T ^ 2 := by ring

/-- `arctan x ≤ x` for `x > 0`. -/
private lemma arctan_le_self {x : ℝ} (hx : 0 < x) : Real.arctan x ≤ x := by
  have h1 : 0 < Real.arctan x := Real.arctan_pos.2 hx
  have h2 : Real.arctan x < Real.pi / 2 := Real.arctan_lt_pi_div_two x
  have h3 := Real.lt_tan h1 h2
  rw [Real.tan_arctan] at h3
  exact h3.le

/-- **The saturating bound.** `arctan (h + T) - arctan h ≤ 4 / (1 + h)` for `h ≥ 0`, whatever
`T`. -/
private lemma arctan_add_sub_arctan_le {h T : ℝ} (hh : 0 ≤ h) :
    Real.arctan (h + T) - Real.arctan h ≤ 4 / (1 + h) := by
  rcases le_or_gt h 1 with hle | hgt
  · have h1 : Real.arctan (h + T) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have h2 : (0 : ℝ) ≤ Real.arctan h := Real.arctan_nonneg.2 hh
    have h4 : (2 : ℝ) ≤ 4 / (1 + h) := by rw [le_div_iff₀ (by linarith)]; linarith
    linarith [Real.pi_le_four]
  · have hpos : (0 : ℝ) < h := by linarith
    have hinv : Real.arctan h⁻¹ = Real.pi / 2 - Real.arctan h := Real.arctan_inv_of_pos hpos
    have h1 : Real.arctan (h + T) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have h2 : Real.arctan h⁻¹ ≤ h⁻¹ := arctan_le_self (by positivity)
    have h3 : h⁻¹ ≤ 4 / (1 + h) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    linarith

/-- The Poisson integral over the range, in closed form. If the ordinate `γ` sits at distance `h`
below `0` or above `T`, then `∫_0^T dt / (1 + (t - γ)²) = arctan (h + T) - arctan h`. -/
private lemma integral_poisson_eq {γ T h : ℝ} (hγ : γ = -h ∨ γ = T + h) :
    (∫ t in (0 : ℝ)..T, 1 / (1 + (t - γ) ^ 2)) = Real.arctan (h + T) - Real.arctan h := by
  rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => 1 / (1 + u ^ 2)) γ,
    integral_one_div_one_add_sq]
  rcases hγ with rfl | rfl
  · rw [show T - -h = h + T by ring, show (0 : ℝ) - -h = h by ring]
  · rw [show T - (T + h) = -h by ring, show (0 : ℝ) - (T + h) = -(h + T) by ring,
      Real.arctan_neg, Real.arctan_neg]
    ring

/-- The pointwise bound for the Poisson integral: if every `t` of the range is at distance at least
`h` from `γ`, then `∫_0^T dt / (1 + (t - γ)²) ≤ T / (1 + h²)`. -/
private lemma integral_poisson_le_const {γ T h : ℝ} (hT : 0 ≤ T) (hh : 0 ≤ h)
    (hdist : ∀ t ∈ Set.Icc (0 : ℝ) T, h ≤ |t - γ|) :
    (∫ t in (0 : ℝ)..T, 1 / (1 + (t - γ) ^ 2)) ≤ T / (1 + h ^ 2) := by
  have hcont : Continuous fun t : ℝ => 1 / (1 + (t - γ) ^ 2) :=
    continuous_const.div (by fun_prop) fun t => by positivity
  have hle : (∫ t in (0 : ℝ)..T, 1 / (1 + (t - γ) ^ 2))
      ≤ ∫ _t in (0 : ℝ)..T, 1 / (1 + h ^ 2) := by
    refine intervalIntegral.integral_mono_on hT (hcont.intervalIntegrable 0 T)
      (continuous_const.intervalIntegrable 0 T) fun t ht => ?_
    have h2 : h ^ 2 ≤ (t - γ) ^ 2 := by
      rw [show (t - γ) ^ 2 = |t - γ| ^ 2 from (sq_abs _).symm]
      exact pow_le_pow_left₀ hh (hdist t ht) 2
    have h3 : (0 : ℝ) < 1 + h ^ 2 := by positivity
    gcongr
  refine hle.trans_eq ?_
  rw [intervalIntegral.integral_const]
  simp [div_eq_mul_inv]

/-- **The integral over the range, for one zero outside it.** For `T ≥ 3` and an ordinate at
distance `h` from `[0, T]`, `∫_0^T dt / (1 + (t - γ)²) ≤ 10 T / ((1 + h)(1 + h + T))`. -/
private lemma integral_poisson_le {T h γ : ℝ} (hT : 3 ≤ T) (hh : 0 ≤ h)
    (hγ : γ = -h ∨ γ = T + h) :
    (∫ t in (0 : ℝ)..T, 1 / (1 + (t - γ) ^ 2)) ≤ 10 * T / ((1 + h) * (1 + h + T)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  rcases le_or_gt h T with hle | hgt
  · rw [integral_poisson_eq hγ]
    refine (arctan_add_sub_arctan_le hh).trans ?_
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith
  · refine (integral_poisson_le_const hT0.le hh ?_).trans ?_
    · intro t ht
      obtain ⟨ht0, htT⟩ := ht
      rcases hγ with rfl | rfl
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (h - 1), mul_nonneg hT0.le (sq_nonneg (h - 1))]

/-- The same bound with `h` replaced by a natural number `j ≤ h`:
`∫_0^T dt / (1 + (t - γ)²) ≤ 10 T / ((1 + j)(1 + j + T))`. -/
private lemma integral_poisson_le_floor {T h γ : ℝ} (hT : 3 ≤ T) (hh : 0 ≤ h) {j : ℕ}
    (hj : (j : ℝ) ≤ h) (hγ : γ = -h ∨ γ = T + h) :
    (∫ t in (0 : ℝ)..T, 1 / (1 + (t - γ) ^ 2))
      ≤ 10 * T / ((1 + (j : ℝ)) * (1 + (j : ℝ) + T)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  refine (integral_poisson_le hT hh hγ).trans ?_
  have hmono : (1 + (j : ℝ)) * (1 + (j : ℝ) + T) ≤ (1 + h) * (1 + h + T) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 10 * T)]

/-- The unit-window count at a centre `c` with `|c| ≤ T + j + 1`, for `T ≥ 3`: the zeros of `𝒩*`
within `1` of `c` have total multiplicity `O(2 log T + log (j + 2))`. -/
private lemma exists_finset_mult_outside_window_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 3 ≤ T → ∀ (j : ℕ) (c : ℝ), |c| ≤ T + (j : ℝ) + 1 →
      ∀ F : Finset ℂ, (∀ ρ ∈ F, ρ ∈ allZeros) → (∀ ρ ∈ F, |ρ.im - c| ≤ 1) →
      ∑ ρ ∈ F, (zeroMultiplicity ρ : ℝ) ≤ C * (2 * Real.log T + Real.log ((j : ℝ) + 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_finset_mult_window_le
  refine ⟨C, hC0, fun T hT j c hc F hF hw => ?_⟩
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  refine (hC c F hF hw).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  have hprod : |c| + 3 ≤ (T + 3) * ((j : ℝ) + 2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ T) hj0]
  have hlogT3 : Real.log (T + 3) ≤ 2 * Real.log T := by
    have hle : T + 3 ≤ T ^ 2 := by nlinarith
    calc Real.log (T + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hle
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  calc Real.log (|c| + 3) ≤ Real.log ((T + 3) * ((j : ℝ) + 2)) :=
        Real.log_le_log (by linarith [abs_nonneg c]) hprod
    _ = Real.log (T + 3) + Real.log ((j : ℝ) + 2) :=
        Real.log_mul (by linarith) (by linarith)
    _ ≤ 2 * Real.log T + Real.log ((j : ℝ) + 2) := by linarith

/-- **The integrated count, for a finite set of zeros outside the range.** For `T ≥ 3` and a finite
set of zeros of `𝒩*` whose ordinates lie outside `(0, T]`, the sum of
`m_ρ ∫_0^T dt / (1 + (t - im ρ)²)` is at most `C log² T` with `C` absolute. -/
private lemma exists_finset_poissonIntegral_outside_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 3 ≤ T → ∀ S : Finset ℂ, (∀ ρ ∈ S, ρ ∈ allZeros) →
      (∀ ρ ∈ S, ρ.im ∉ Set.Ioc (0 : ℝ) T) →
      ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2)
        ≤ C * Real.log T ^ 2 := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_finset_mult_outside_window_le
  refine ⟨520 * C₁, by linarith, fun T hT S hS hout => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (1 : ℝ) ≤ Real.log T := by
    have h : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
    exact h.le.trans (Real.log_le_log (by norm_num) hT)
  set d : ℂ → ℝ := fun ρ : ℂ => if ρ.im ≤ 0 then -ρ.im else ρ.im - T with hd
  have hcase : ∀ ρ ∈ S, (ρ.im ≤ 0 ∧ d ρ = -ρ.im) ∨ (T < ρ.im ∧ d ρ = ρ.im - T) := by
    intro ρ hρ
    rcases le_or_gt ρ.im 0 with him | him
    · exact Or.inl ⟨him, by simp [hd, him]⟩
    · have hTim : T < ρ.im := by
        by_contra hc
        exact hout ρ hρ (Set.mem_Ioc.2 ⟨him, not_lt.1 hc⟩)
      exact Or.inr ⟨hTim, by simp [hd, not_le.2 him]⟩
  have hd0 : ∀ ρ ∈ S, 0 ≤ d ρ := by
    intro ρ hρ
    rcases hcase ρ hρ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> linarith
  have hdim : ∀ ρ ∈ S, ρ.im = -(d ρ) ∨ ρ.im = T + d ρ := by
    intro ρ hρ
    rcases hcase ρ hρ with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inl (by rw [h2]; ring)
    · exact Or.inr (by rw [h2]; ring)
  have hmaps : ∀ ρ ∈ S, ⌊d ρ⌋₊ ∈ Finset.range (S.sup (fun ρ => ⌊d ρ⌋₊) + 1) :=
    fun ρ hρ => Finset.mem_range_succ_iff.2 (Finset.le_sup (f := fun ρ : ℂ => ⌊d ρ⌋₊) hρ)
  have hfiber : ∀ j : ℕ,
      ∑ ρ ∈ S with ⌊d ρ⌋₊ = j,
          (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2)
        ≤ 20 * C₁ * ((2 * Real.log T + Real.log ((j : ℝ) + 2))
            * (T / ((1 + (j : ℝ)) * (1 + (j : ℝ) + T)))) := by
    intro j
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hB0 : (0 : ℝ) ≤ 10 * T / ((1 + (j : ℝ)) * (1 + (j : ℝ) + T)) := by positivity
    have hmemF : ∀ ρ ∈ S.filter (fun ρ => ⌊d ρ⌋₊ = j),
        ρ ∈ S ∧ (j : ℝ) ≤ d ρ ∧ d ρ < (j : ℝ) + 1 := by
      intro ρ hρ
      have hρS := (Finset.mem_filter.1 hρ).1
      have hj : ⌊d ρ⌋₊ = j := (Finset.mem_filter.1 hρ).2
      refine ⟨hρS, ?_, ?_⟩
      · have h := Nat.floor_le (hd0 ρ hρS)
        rw [hj] at h
        exact h
      · have h := Nat.lt_floor_add_one (d ρ)
        rw [hj] at h
        exact h
    have hstep : ∀ ρ ∈ S.filter (fun ρ => ⌊d ρ⌋₊ = j),
        (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2)
          ≤ (zeroMultiplicity ρ : ℝ) * (10 * T / ((1 + (j : ℝ)) * (1 + (j : ℝ) + T))) := by
      intro ρ hρ
      obtain ⟨hρS, hjle, -⟩ := hmemF ρ hρ
      exact mul_le_mul_of_nonneg_left
        (integral_poisson_le_floor hT (hd0 ρ hρS) hjle (hdim ρ hρS)) (Nat.cast_nonneg _)
    have hsum1 : ∑ ρ ∈ S with ⌊d ρ⌋₊ = j,
          (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2)
        ≤ (∑ ρ ∈ S with ⌊d ρ⌋₊ = j, (zeroMultiplicity ρ : ℝ))
            * (10 * T / ((1 + (j : ℝ)) * (1 + (j : ℝ) + T))) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hstep
    have hlow : ∑ ρ ∈ S.filter (fun ρ => ⌊d ρ⌋₊ = j) with ρ.im ≤ 0,
        (zeroMultiplicity ρ : ℝ) ≤ C₁ * (2 * Real.log T + Real.log ((j : ℝ) + 2)) := by
      refine hC₁ T hT j (-((j : ℝ) + 1 / 2)) ?_ _ ?_ ?_
      · rw [abs_le]
        constructor <;> linarith
      · exact fun ρ hρ => hS ρ (hmemF ρ (Finset.mem_filter.1 hρ).1).1
      · intro ρ hρ
        obtain ⟨hρS, h1, h2⟩ := hmemF ρ (Finset.mem_filter.1 hρ).1
        have him : ρ.im ≤ 0 := (Finset.mem_filter.1 hρ).2
        have hval : ρ.im = -(d ρ) := by
          rcases hdim ρ hρS with h | h
          · exact h
          · exfalso
            rw [h] at him
            linarith [hd0 ρ hρS]
        rw [hval, abs_le]
        constructor <;> linarith
    have hhigh : ∑ ρ ∈ S.filter (fun ρ => ⌊d ρ⌋₊ = j) with ¬ ρ.im ≤ 0,
        (zeroMultiplicity ρ : ℝ) ≤ C₁ * (2 * Real.log T + Real.log ((j : ℝ) + 2)) := by
      refine hC₁ T hT j (T + (j : ℝ) + 1 / 2) ?_ _ ?_ ?_
      · rw [abs_le]
        constructor <;> linarith
      · exact fun ρ hρ => hS ρ (hmemF ρ (Finset.mem_filter.1 hρ).1).1
      · intro ρ hρ
        obtain ⟨hρS, h1, h2⟩ := hmemF ρ (Finset.mem_filter.1 hρ).1
        have him : ¬ ρ.im ≤ 0 := (Finset.mem_filter.1 hρ).2
        have hval : ρ.im = T + d ρ := by
          rcases hdim ρ hρS with h | h
          · exact absurd (by rw [h]; linarith [hd0 ρ hρS] : ρ.im ≤ 0) him
          · exact h
        rw [hval, abs_le]
        constructor <;> linarith
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (S.filter (fun ρ => ⌊d ρ⌋₊ = j)) (fun ρ => ρ.im ≤ 0)
      (fun ρ => (zeroMultiplicity ρ : ℝ))
    have hmult : ∑ ρ ∈ S with ⌊d ρ⌋₊ = j, (zeroMultiplicity ρ : ℝ)
        ≤ 2 * C₁ * (2 * Real.log T + Real.log ((j : ℝ) + 2)) := by linarith
    calc ∑ ρ ∈ S with ⌊d ρ⌋₊ = j,
          (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2)
        ≤ (∑ ρ ∈ S with ⌊d ρ⌋₊ = j, (zeroMultiplicity ρ : ℝ))
            * (10 * T / ((1 + (j : ℝ)) * (1 + (j : ℝ) + T))) := hsum1
      _ ≤ 2 * C₁ * (2 * Real.log T + Real.log ((j : ℝ) + 2))
            * (10 * T / ((1 + (j : ℝ)) * (1 + (j : ℝ) + T))) :=
          mul_le_mul_of_nonneg_right hmult hB0
      _ = 20 * C₁ * ((2 * Real.log T + Real.log ((j : ℝ) + 2))
            * (T / ((1 + (j : ℝ)) * (1 + (j : ℝ) + T)))) := by ring
  calc ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2)
      = ∑ j ∈ Finset.range (S.sup (fun ρ => ⌊d ρ⌋₊) + 1),
          ∑ ρ ∈ S with ⌊d ρ⌋₊ = j,
            (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ j ∈ Finset.range (S.sup (fun ρ => ⌊d ρ⌋₊) + 1),
          20 * C₁ * ((2 * Real.log T + Real.log ((j : ℝ) + 2))
            * (T / ((1 + (j : ℝ)) * (1 + (j : ℝ) + T)))) :=
        Finset.sum_le_sum fun j _ => hfiber j
    _ = 20 * C₁ * ∑ j ∈ Finset.range (S.sup (fun ρ => ⌊d ρ⌋₊) + 1),
          (2 * Real.log T + Real.log ((j : ℝ) + 2))
            * (T / ((1 + (j : ℝ)) * (1 + (j : ℝ) + T))) := by rw [Finset.mul_sum]
    _ ≤ 20 * C₁ * (26 * Real.log T ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_range_logWeight_le hT _) (by linarith)
    _ = 520 * C₁ * Real.log T ^ 2 := by ring

/-- **The zeros outside the range, integrated.** There is an absolute constant `C > 0` such that
for every `T ≥ 3` the family indexed by the zeros `ρ ∈ 𝒩*` whose ordinate lies outside `(0, T]`,
with term `m_ρ ∫_0^T dt / (1 + (t - im ρ)²)`, is summable with sum at most `C log² T`. -/
@[zz_tag "lem_one_sided_integral"]
theorem exists_summable_poissonIntegral_outside_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
      Summable (fun ρ : {ρ ∈ allZeros | ρ.im ∉ Set.Ioc (0 : ℝ) T} =>
          (zeroMultiplicity (ρ : ℂ) : ℝ)
            * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - (ρ : ℂ).im) ^ 2)) ∧
        ∑' ρ : {ρ ∈ allZeros | ρ.im ∉ Set.Ioc (0 : ℝ) T},
            (zeroMultiplicity (ρ : ℂ) : ℝ)
              * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - (ρ : ℂ).im) ^ 2)
          ≤ C * Real.log T ^ 2 := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_finset_poissonIntegral_outside_le
  refine ⟨C + 1, by linarith, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hf0 : ∀ ρ : {ρ ∈ allZeros | ρ.im ∉ Set.Ioc (0 : ℝ) T},
      (0 : ℝ) ≤ (zeroMultiplicity (ρ : ℂ) : ℝ)
        * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - (ρ : ℂ).im) ^ 2) := by
    intro ρ
    refine mul_nonneg (Nat.cast_nonneg _)
      (intervalIntegral.integral_nonneg hT0.le fun t _ => by positivity)
  have hbound : ∀ u : Finset {ρ ∈ allZeros | ρ.im ∉ Set.Ioc (0 : ℝ) T},
      ∑ ρ ∈ u, (zeroMultiplicity (ρ : ℂ) : ℝ)
          * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - (ρ : ℂ).im) ^ 2)
        ≤ (C + 1) * Real.log T ^ 2 := by
    intro u
    have himg : ∑ ρ ∈ u, (zeroMultiplicity (ρ : ℂ) : ℝ)
          * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - (ρ : ℂ).im) ^ 2)
        = ∑ ρ ∈ u.image Subtype.val, (zeroMultiplicity ρ : ℝ)
            * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) :=
      (Finset.sum_image (f := fun ρ : ℂ => (zeroMultiplicity ρ : ℝ)
        * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2))
        (g := Subtype.val) (s := u) fun _ _ _ _ h => Subtype.ext h).symm
    rw [himg]
    refine (hC T hT _ ?_ ?_).trans ?_
    · intro ρ hρ
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hρ
      exact σ.2.1
    · intro ρ hρ
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hρ
      exact σ.2.2
    · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  exact ⟨summable_of_sum_le hf0 hbound, Real.tsum_le_of_sum_le hf0 hbound⟩

end ZetaZeros
