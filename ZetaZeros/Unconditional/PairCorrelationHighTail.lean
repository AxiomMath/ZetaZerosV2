/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationTailComparison
import ZetaZeros.Unconditional.PairCorrelationFullZeroMoment
import ZetaZeros.Unconditional.PairCorrelationIntegratedAssembly
import ZetaZeros.Unconditional.PairCorrelationIntegratedEndpoint

/-!
# High-ordinate tails for Montgomery's full zero sum

The Riemann--von Mangoldt local zero count controls both tails of the multiplicity-weighted
Lorentzian zero series.  Combining this with the pointwise bound for the complex explicit-formula
summand gives a uniform `sqrt x * log Z / Z` estimate outside `|gamma| <= Z` for `t in [0,T]`
when `Z >= 2T`.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex Finset MeasureTheory Set

lemma sum_inv_mul_sqrt_finset_le (F : Finset ℕ) {D : ℝ} (hD : 1 ≤ D) :
    ∑ i ∈ F, 1 / ((D + i) * Real.sqrt (D + i)) ≤
      3 / Real.sqrt D := by
  classical
  set N : ℕ := F.sup id + 1
  have hsub : F ⊆ Finset.range N := by
    intro i hi
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  calc
    ∑ i ∈ F, 1 / ((D + i) * Real.sqrt (D + i)) ≤
        ∑ i ∈ Finset.range N, 1 / ((D + i) * Real.sqrt (D + i)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 3 / Real.sqrt D := sum_inv_mul_sqrt_le hD N

lemma log_div_sq_le_inv_mul_sqrt {D y : ℝ}
    (hD : Real.exp 1 ≤ D) (hy : D ≤ y) :
    Real.log y / y ^ 2 ≤
      (3 * Real.log D / Real.sqrt D) *
        (1 / (y * Real.sqrt y)) := by
  have hDpos : 0 < D := (Real.exp_pos 1).trans_le hD
  have hypos : 0 < y := hDpos.trans_le hy
  have hlog := log_le_three_mul_log_mul_sqrt_ratio hD hy
  rw [Real.sqrt_div (show 0 ≤ y from hypos.le)] at hlog
  calc
    Real.log y / y ^ 2 ≤
        (3 * Real.log D * (Real.sqrt y / Real.sqrt D)) / y ^ 2 :=
      div_le_div_of_nonneg_right hlog (sq_nonneg y)
    _ = (3 * Real.log D / Real.sqrt D) *
          (1 / (y * Real.sqrt y)) := by
      have hsD : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
      have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
      field_simp [ne_of_gt hsD, ne_of_gt hsy, ne_of_gt hypos]
      ring_nf
      rw [Real.sq_sqrt hypos.le]

lemma log_add_three_div_le_two_log_div {D : ℝ} (hD : 3 ≤ D) :
    Real.log (D + 3) / (D + 3) ≤ 2 * Real.log D / D := by
  have hDpos : 0 < D := by linarith
  have hBpos : 0 < D + 3 := by linarith
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
  have hlogtwo : Real.log 2 ≤ Real.log D :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogB : Real.log (D + 3) ≤ 2 * Real.log D := by
    calc
      Real.log (D + 3) ≤ Real.log (2 * D) :=
        Real.log_le_log hBpos (by linarith)
      _ = Real.log 2 + Real.log D := by rw [Real.log_mul (by norm_num) hDpos.ne']
      _ ≤ 2 * Real.log D := by linarith
  rw [div_le_div_iff₀ hBpos hDpos]
  calc
    Real.log (D + 3) * D ≤ (2 * Real.log D) * D :=
      mul_le_mul_of_nonneg_right hlogB hDpos.le
    _ ≤ (2 * Real.log D) * (D + 3) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

lemma one_side_inv_sq_sum_le {ι : Type*}
    (s : Finset ι) (y : ι → ℝ) (m : ι → ℕ)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 3 ≤ D)
    (hy : ∀ ρ ∈ s, D < y ρ)
    (hcount : ∀ j : ℕ,
      ∑ ρ ∈ s with ⌈y ρ - D⌉₊ - 1 = j, (m ρ : ℝ) ≤
        A * Real.log (D + j + 3)) :
    ∑ ρ ∈ s, (m ρ : ℝ) / (y ρ) ^ 2 ≤
      72 * A * Real.log D / D := by
  classical
  let key : ι → ℕ := fun ρ => ⌈y ρ - D⌉₊ - 1
  let B : ℝ := D + 3
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hexpB : Real.exp 1 ≤ B := by
    dsimp [B]
    linarith [Real.exp_one_lt_d9]
  rw [← Finset.sum_fiberwise_of_maps_to (g := key) (t := s.image key)
    (fun ρ hρ => Finset.mem_image_of_mem key hρ)]
  have hfiber : ∀ j ∈ s.image key,
      ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) / (y ρ) ^ 2 ≤
        (12 * A * Real.log B / Real.sqrt B) *
          (1 / ((B + j) * Real.sqrt (B + j))) := by
    intro j hj
    have hpoint : ∀ ρ ∈ s.filter (fun ρ => key ρ = j),
        (m ρ : ℝ) / (y ρ) ^ 2 ≤
          (4 / (B + j) ^ 2) * (m ρ : ℝ) := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have hceil1 : 1 ≤ ⌈y ρ - D⌉₊ :=
        Nat.one_le_ceil_iff.mpr (by linarith [hy ρ hρ.1])
      have hc : ⌈y ρ - D⌉₊ = j + 1 := by
        dsimp [key] at hρ
        omega
      have hinter := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
      push_cast at hinter
      have hypos : 0 < y ρ := by linarith [hy ρ hρ.1]
      have hqpos : 0 < B + j := by dsimp [B]; positivity
      have hq : B + j < 2 * y ρ := by
        dsimp [B]
        nlinarith [hinter.1, hD]
      have hinv : 1 / (y ρ) ^ 2 ≤ 4 / (B + j) ^ 2 := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hypos) (sq_pos_of_pos hqpos)]
        nlinarith [sq_nonneg (B + j), sq_nonneg (y ρ)]
      calc
        (m ρ : ℝ) / (y ρ) ^ 2 =
            (m ρ : ℝ) * (1 / (y ρ) ^ 2) := by ring
        _ ≤ (m ρ : ℝ) * (4 / (B + j) ^ 2) :=
          mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
        _ = (4 / (B + j) ^ 2) * (m ρ : ℝ) := by ring
    have hlogweight := log_div_sq_le_inv_mul_sqrt hexpB
      (show B ≤ B + (j : ℝ) by
        exact le_add_of_nonneg_right (Nat.cast_nonneg j))
    calc
      ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) / (y ρ) ^ 2 ≤
          ∑ ρ ∈ s with key ρ = j,
            (4 / (B + j) ^ 2) * (m ρ : ℝ) :=
        Finset.sum_le_sum hpoint
      _ = (4 / (B + j) ^ 2) *
            ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ (4 / (B + j) ^ 2) *
            (A * Real.log (D + j + 3)) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [key] using hcount j
        · positivity
      _ = 4 * A * (Real.log (B + j) / (B + j) ^ 2) := by
        dsimp [B]
        ring
      _ ≤ 4 * A *
            ((3 * Real.log B / Real.sqrt B) *
              (1 / ((B + j) * Real.sqrt (B + j)))) := by
        exact mul_le_mul_of_nonneg_left hlogweight (mul_nonneg (by norm_num) hA)
      _ = (12 * A * Real.log B / Real.sqrt B) *
            (1 / ((B + j) * Real.sqrt (B + j))) := by ring
  calc
    ∑ j ∈ s.image key,
        ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) / (y ρ) ^ 2 ≤
        ∑ j ∈ s.image key,
          (12 * A * Real.log B / Real.sqrt B) *
            (1 / ((B + j) * Real.sqrt (B + j))) :=
      Finset.sum_le_sum hfiber
    _ = (12 * A * Real.log B / Real.sqrt B) *
          ∑ j ∈ s.image key, 1 / ((B + j) * Real.sqrt (B + j)) := by
      rw [Finset.mul_sum]
    _ ≤ (12 * A * Real.log B / Real.sqrt B) *
          (3 / Real.sqrt B) := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_inv_mul_sqrt_finset_le (s.image key) hB
      · have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
        have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
        positivity
    _ = 36 * A * (Real.log B / B) := by
      have hBpos : 0 < B := by linarith
      have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
      field_simp [ne_of_gt hBpos, ne_of_gt hsB]
      ring_nf
      rw [Real.sq_sqrt hBpos.le]
    _ ≤ 36 * A * (2 * Real.log D / D) := by
      exact mul_le_mul_of_nonneg_left (log_add_three_div_le_two_log_div hD)
        (mul_nonneg (by norm_num) hA)
    _ = 72 * A * Real.log D / D := by ring

/-- A local unit-window count controls the positive high-ordinate inverse-square tail. -/
lemma positive_inv_sq_sum_le_of_localCount {ι : Type*}
    {γ : ι → ℝ} {m : ι → ℕ} {A D : ℝ}
    (hLC : Zeta23.Tail.LocalCount γ m A) (hD : 3 ≤ D)
    (s : Finset ι) (hpos : ∀ ρ ∈ s, D < γ ρ) :
    ∑ ρ ∈ s, (m ρ : ℝ) / (γ ρ) ^ 2 ≤
      72 * A * Real.log D / D := by
  apply one_side_inv_sq_sum_le s γ m (le_trans (by norm_num) hLC.one_le) hD hpos
  intro j
  have hw := hLC.window (D + j)
    (s.filter fun ρ => ⌈γ ρ - D⌉₊ - 1 = j) (by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have hceil1 : 1 ≤ ⌈γ ρ - D⌉₊ :=
        Nat.one_le_ceil_iff.mpr (by linarith [hpos ρ hρ.1])
      have hc : ⌈γ ρ - D⌉₊ = j + 1 := by omega
      have hinter := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
      push_cast at hinter
      constructor <;> linarith)
  simpa [abs_of_nonneg (show 0 ≤ D + (j : ℝ) by positivity)] using hw

/-- A local unit-window count also controls the negative high-ordinate inverse-square tail.
The harmless factor four comes from covering a reflected half-open unit interval by two of the
half-open windows in `LocalCount`. -/
lemma negative_inv_sq_sum_le_of_localCount {ι : Type*}
    {γ : ι → ℝ} {m : ι → ℕ} {A D : ℝ}
    (hLC : Zeta23.Tail.LocalCount γ m A) (hD : 3 ≤ D)
    (s : Finset ι) (hneg : ∀ ρ ∈ s, D < -γ ρ) :
    ∑ ρ ∈ s, (m ρ : ℝ) / (γ ρ) ^ 2 ≤
      288 * A * Real.log D / D := by
  have hA : 0 ≤ A := le_trans (by norm_num) hLC.one_le
  have hone : ∀ j : ℕ,
      ∑ ρ ∈ s with ⌈-γ ρ - D⌉₊ - 1 = j, (m ρ : ℝ) ≤
        (4 * A) * Real.log (D + j + 3) := by
    intro j
    let f : Finset ι := s.filter (fun ρ => ⌈-γ ρ - D⌉₊ - 1 = j)
    let a : ℝ := -(D + j + 1)
    have hf_bounds : ∀ ρ ∈ f, a ≤ γ ρ ∧ γ ρ < a + 1 := by
      intro ρ hρ
      simp only [f, Finset.mem_filter] at hρ
      have hceil1 : 1 ≤ ⌈-γ ρ - D⌉₊ :=
        Nat.one_le_ceil_iff.mpr (by linarith [hneg ρ hρ.1])
      have hc : ⌈-γ ρ - D⌉₊ = j + 1 := by omega
      have hinter := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
      push_cast at hinter
      dsimp [a]
      constructor <;> linarith
    have hleft := hLC.window (a - 1) (f.filter fun ρ => γ ρ ≤ a) (by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have hb := hf_bounds ρ hρ.1
      constructor <;> linarith)
    have hright := hLC.window a (f.filter fun ρ => ¬ γ ρ ≤ a) (by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have hb := hf_bounds ρ hρ.1
      constructor <;> linarith)
    have ha_abs : |a| = D + j + 1 := by
      rw [abs_of_nonpos]
      · dsimp [a]
        ring
      · dsimp [a]
        linarith [hD, (show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j)]
    have ha1_abs : |a - 1| = D + j + 2 := by
      rw [abs_of_nonpos]
      · dsimp [a]
        ring
      · dsimp [a]
        linarith
    rw [ha_abs] at hright
    rw [ha1_abs] at hleft
    have hbasepos : 0 < D + (j : ℝ) + 3 := by positivity
    have hbigpos : 0 < D + (j : ℝ) + 5 := by positivity
    have harg : D + (j : ℝ) + 5 ≤
        (D + (j : ℝ) + 3) * (D + (j : ℝ) + 3) := by
      nlinarith [hD, (show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j)]
    have hlogbig : Real.log (D + (j : ℝ) + 5) ≤
        2 * Real.log (D + (j : ℝ) + 3) := by
      calc
        Real.log (D + (j : ℝ) + 5) ≤
            Real.log ((D + (j : ℝ) + 3) * (D + (j : ℝ) + 3)) :=
          Real.log_le_log hbigpos harg
        _ = Real.log (D + (j : ℝ) + 3) +
              Real.log (D + (j : ℝ) + 3) := by
          rw [Real.log_mul hbasepos.ne' hbasepos.ne']
        _ = 2 * Real.log (D + (j : ℝ) + 3) := by ring
    have hleft' :
        ∑ ρ ∈ f with γ ρ ≤ a, (m ρ : ℝ) ≤
          A * Real.log (D + (j : ℝ) + 5) := by
      convert hleft using 1; ring
    have hright' :
        ∑ ρ ∈ f with ¬ γ ρ ≤ a, (m ρ : ℝ) ≤
          A * Real.log (D + (j : ℝ) + 5) := by
      exact hright.trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity) (by linarith)) hA)
    change ∑ ρ ∈ f, (m ρ : ℝ) ≤ _
    rw [← Finset.sum_filter_add_sum_filter_not f (fun ρ => γ ρ ≤ a)]
    calc
      (∑ ρ ∈ f with γ ρ ≤ a, (m ρ : ℝ)) +
          ∑ ρ ∈ f with ¬ γ ρ ≤ a, (m ρ : ℝ) ≤
          A * Real.log (D + (j : ℝ) + 5) +
            A * Real.log (D + (j : ℝ) + 5) := add_le_add hleft' hright'
      _ ≤ (4 * A) * Real.log (D + (j : ℝ) + 3) := by
        have := mul_le_mul_of_nonneg_left hlogbig hA
        nlinarith
  have h := one_side_inv_sq_sum_le s (fun ρ => -γ ρ) m
    (mul_nonneg (by norm_num) hA) hD hneg hone
  calc
    ∑ ρ ∈ s, (m ρ : ℝ) / γ ρ ^ 2 =
        ∑ ρ ∈ s, (m ρ : ℝ) / (-γ ρ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro ρ _
      rw [neg_sq]
    _ ≤ 72 * (4 * A) * Real.log D / D := h
    _ = 288 * A * Real.log D / D := by ring

/-- The two-sided finite high-ordinate inverse-square tail follows from the local count. -/
lemma abs_inv_sq_sum_le_of_localCount {ι : Type*}
    {γ : ι → ℝ} {m : ι → ℕ} {A D : ℝ}
    (hLC : Zeta23.Tail.LocalCount γ m A) (hD : 3 ≤ D)
    (s : Finset ι) (htail : ∀ ρ ∈ s, D < |γ ρ|) :
    ∑ ρ ∈ s, (m ρ : ℝ) / (γ ρ) ^ 2 ≤
      360 * A * Real.log D / D := by
  classical
  have hp := positive_inv_sq_sum_le_of_localCount hLC hD
    (s.filter fun ρ => 0 ≤ γ ρ) (by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      simpa [abs_of_nonneg hρ.2] using htail ρ hρ.1)
  have hn := negative_inv_sq_sum_le_of_localCount hLC hD
    (s.filter fun ρ => ¬ 0 ≤ γ ρ) (by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      simpa [abs_of_neg (lt_of_not_ge hρ.2)] using htail ρ hρ.1)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => 0 ≤ γ ρ)]
  calc
    (∑ ρ ∈ s with 0 ≤ γ ρ, (m ρ : ℝ) / γ ρ ^ 2) +
        ∑ ρ ∈ s with ¬ 0 ≤ γ ρ, (m ρ : ℝ) / γ ρ ^ 2 ≤
        72 * A * Real.log D / D + 288 * A * Real.log D / D :=
      add_le_add hp hn
    _ = 360 * A * Real.log D / D := by ring

/-- Far from the integration window, translating a zero ordinate by `t ∈ [0,T]` loses at
most a factor four in the inverse-square majorant. -/
lemma abs_shifted_lorentzian_sum_le_of_localCount {ι : Type*}
    {γ : ι → ℝ} {m : ι → ℕ} {A T Z t : ℝ}
    (hLC : Zeta23.Tail.LocalCount γ m A) (hZ : 3 ≤ Z)
    (ht0 : 0 ≤ t) (htT : t ≤ T) (hTZ : 2 * T ≤ Z)
    (s : Finset ι) (htail : ∀ ρ ∈ s, Z < |γ ρ|) :
    ∑ ρ ∈ s, (m ρ : ℝ) / (1 + (t - γ ρ) ^ 2) ≤
      1440 * A * Real.log Z / Z := by
  have hA : 0 ≤ A := le_trans (by norm_num) hLC.one_le
  have hinv := abs_inv_sq_sum_le_of_localCount hLC hZ s htail
  have hpoint : ∀ ρ ∈ s,
      (m ρ : ℝ) / (1 + (t - γ ρ) ^ 2) ≤
        4 * ((m ρ : ℝ) / (γ ρ) ^ 2) := by
    intro ρ hρ
    have htailρ := htail ρ hρ
    have hZ0 : 0 ≤ Z := by linarith
    have hγne : γ ρ ≠ 0 := by
      intro h
      rw [h, abs_zero] at htailρ
      linarith
    have hsq : (γ ρ) ^ 2 ≤ 4 * (t - γ ρ) ^ 2 := by
      by_cases hγ : 0 ≤ γ ρ
      · have hZγ : Z < γ ρ := by simpa [abs_of_nonneg hγ] using htailρ
        have hfirst : 0 ≤ γ ρ - 2 * t := by linarith
        have hsecond : 0 ≤ 3 * γ ρ - 2 * t := by linarith
        have hprod := mul_nonneg hfirst hsecond
        nlinarith
      · have hγ' : γ ρ < 0 := lt_of_not_ge hγ
        have hprod : 0 ≤ t * (-γ ρ) :=
          mul_nonneg ht0 (neg_nonneg.mpr hγ'.le)
        nlinarith [sq_nonneg t]
    have hden : 0 < 1 + (t - γ ρ) ^ 2 := by positivity
    have hγsq : 0 < (γ ρ) ^ 2 := sq_pos_of_ne_zero hγne
    have hweight : 1 / (1 + (t - γ ρ) ^ 2) ≤ 4 / (γ ρ) ^ 2 := by
      rw [div_le_div_iff₀ hden hγsq]
      nlinarith
    calc
      (m ρ : ℝ) / (1 + (t - γ ρ) ^ 2) =
          (m ρ : ℝ) * (1 / (1 + (t - γ ρ) ^ 2)) := by ring
      _ ≤ (m ρ : ℝ) * (4 / (γ ρ) ^ 2) :=
        mul_le_mul_of_nonneg_left hweight (Nat.cast_nonneg _)
      _ = 4 * ((m ρ : ℝ) / (γ ρ) ^ 2) := by ring
  calc
    ∑ ρ ∈ s, (m ρ : ℝ) / (1 + (t - γ ρ) ^ 2) ≤
        ∑ ρ ∈ s, 4 * ((m ρ : ℝ) / (γ ρ) ^ 2) :=
      Finset.sum_le_sum hpoint
    _ = 4 * ∑ ρ ∈ s, (m ρ : ℝ) / (γ ρ) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (360 * A * Real.log Z / Z) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 1440 * A * Real.log Z / Z := by ring

/-- Uniform shifted Lorentzian tail for the actual Riemann-zeta zero multiset. -/
theorem zetaZero_high_shiftedLorentzian_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (T Z t : ℝ), 3 ≤ Z → 0 ≤ t → t ≤ T → 2 * T ≤ Z →
      (∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        if Z < |(ρ : ℂ).im| then
          (Zeta23.zeroMult ρ : ℝ) /
            (1 + (t - (ρ : ℂ).im) ^ 2)
        else 0) ≤ C * Real.log Z / Z := by
  classical
  obtain ⟨A, hA, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount
    (Zeta23.zetaZeros Zeta23.zetaSeam) hA (fun u => by
      rw [Zeta23.zetaZeros_N]
      exact hloc u)
  refine ⟨1440 * A, mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hA), ?_⟩
  intro T Z t hZ ht0 htT hTZ
  apply Real.tsum_le_of_sum_le (fun ρ => by
    split_ifs <;> positivity)
  intro s
  have hs := abs_shifted_lorentzian_sum_le_of_localCount hLC hZ ht0 htT hTZ
    (s.filter fun ρ => Z < |(ρ : ℂ).im|) (by
      intro ρ hρ
      exact (Finset.mem_filter.mp hρ).2)
  rw [← Finset.sum_filter]
  exact hs

/-- The complex high-ordinate tail of Montgomery's full zero series is uniformly controlled
by the shifted Lorentzian tail. -/
theorem zetaZero_high_fullZeroLorentzian_tsum_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (x T Z t : ℝ), 1 ≤ x → 3 ≤ Z →
      0 ≤ t → t ≤ T → 2 * T ≤ Z →
      ‖∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        if Z < |(ρ : ℂ).im| then fullZeroLorentzianSummand x t ρ else 0‖ ≤
        C * Real.sqrt x * Real.log Z / Z := by
  classical
  obtain ⟨C, hC, hbound⟩ := zetaZero_high_shiftedLorentzian_tsum_le
  refine ⟨(8 / 3 : ℝ) * C, mul_pos (by norm_num) hC, ?_⟩
  intro x T Z t hx hZ ht0 htT hTZ
  let S : Set (Zeta23.zetaZeros Zeta23.zetaSeam).carrier :=
    {ρ | Z < |(ρ : ℂ).im|}
  have hfull : Summable (fullZeroLorentzianSummand x t) := by
    apply (zeroLorentzianSummand_summable x hx t).congr
    intro ρ
    rw [fullZeroLorentzianSummand]
  have htail : Summable (fun ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
      if Z < |(ρ : ℂ).im| then fullZeroLorentzianSummand x t ρ else 0) := by
    apply (hfull.indicator S).congr
    intro ρ
    simp only [Set.indicator_apply, S, Set.mem_ofPred_eq]
  have hshift : Summable (fun ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
      if Z < |(ρ : ℂ).im| then
        (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)
      else 0) := by
    apply ((shiftedZeroLorentzian_summable t).indicator S).congr
    intro ρ
    simp only [Set.indicator_apply, S, Set.mem_ofPred_eq]
  have hpoint : ∀ ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
      ‖if Z < |(ρ : ℂ).im| then fullZeroLorentzianSummand x t ρ else 0‖ ≤
        (8 / 3 : ℝ) * Real.sqrt x *
          (if Z < |(ρ : ℂ).im| then
            (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)
          else 0) := by
    intro ρ
    split_ifs with hρ
    · simpa only [fullZeroLorentzianSummand, mul_div_assoc] using
        zeroLorentzianSummand_norm_le x hx t ρ
    · simp
  calc
    ‖∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        if Z < |(ρ : ℂ).im| then fullZeroLorentzianSummand x t ρ else 0‖ ≤
        ∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
          ‖if Z < |(ρ : ℂ).im| then fullZeroLorentzianSummand x t ρ else 0‖ :=
      norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
          (8 / 3 : ℝ) * Real.sqrt x *
            (if Z < |(ρ : ℂ).im| then
              (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)
            else 0) := by
      exact Summable.tsum_le_tsum hpoint htail.norm
        (hshift.mul_left ((8 / 3 : ℝ) * Real.sqrt x))
    _ = (8 / 3 : ℝ) * Real.sqrt x *
          (∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
            if Z < |(ρ : ℂ).im| then
              (Zeta23.zeroMult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2)
            else 0) := by rw [tsum_mul_left]
    _ ≤ (8 / 3 : ℝ) * Real.sqrt x * (C * Real.log Z / Z) := by
      exact mul_le_mul_of_nonneg_left (hbound T Z t hZ ht0 htT hTZ) (by positivity)
    _ = ((8 / 3 : ℝ) * C) * Real.sqrt x * Real.log Z / Z := by ring

private theorem zetaZero_carrier_countable :
    (Zeta23.zetaZeros Zeta23.zetaSeam).carrier.Countable := by
  let windows : ℕ → Set ℂ := fun n =>
    (Zeta23.zetaZeros Zeta23.zetaSeam).carrier ∩
      {rho | -(n : ℝ) < rho.im ∧ rho.im ≤ (n : ℝ)}
  have hwindow : ∀ n : ℕ, (windows n).Countable := by
    intro n
    exact ((Zeta23.zetaZeros Zeta23.zetaSeam).finite_window
      (-(n : ℝ)) (n : ℝ)).countable
  have hunion : (⋃ n : ℕ, windows n).Countable :=
    Set.countable_iUnion hwindow
  apply hunion.mono
  intro rho hrho
  obtain ⟨n, hn⟩ := exists_nat_gt |rho.im|
  rw [Set.mem_iUnion]
  refine ⟨n, ?_⟩
  dsimp only [windows]
  exact ⟨hrho, (abs_lt.mp hn).1, (abs_lt.mp hn).2.le⟩

/-- The part of Montgomery's full zero series above ordinate height `Z`. -/
noncomputable def highFullZeroLorentzianTail (x Z t : ℝ) : ℂ :=
  ∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
    if Z < |(rho : ℂ).im| then fullZeroLorentzianSummand x t rho else 0

/-- The finite-height part of the complementary zero sum.  This is exactly the pair of
ordinate ranges `[-Z, 0]` and `(T, Z]`; unlike the high tail, estimating this term at the
closed endpoint requires the Vinogradov--Korobov input. -/
noncomputable def finiteMediumFullZeroLorentzianTail
    (x T Z t : ℝ) : ℂ :=
  ∑' rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
    if rho ∉ finiteZeroCarrierWindow T ∧ |(rho : ℂ).im| ≤ Z then
      fullZeroLorentzianSummand x t rho
    else 0

/-- Once `Z ≥ T`, the complementary zero series splits exactly into its finite-height
part and the already-controlled high-ordinate tail. -/
theorem fullWindowComplement_eq_finiteMedium_add_high
    (x : ℝ) (hx : 1 ≤ x) (T Z t : ℝ) (hTZ : T ≤ Z) :
    (∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
        rho ∉ finiteZeroCarrierWindow T},
      fullZeroLorentzianSummand x t rho) =
      finiteMediumFullZeroLorentzianTail x T Z t +
        highFullZeroLorentzianTail x Z t := by
  classical
  let f : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier → ℂ :=
    fullZeroLorentzianSummand x t
  let mediumSet : Set (Zeta23.zetaZeros Zeta23.zetaSeam).carrier :=
    {rho | rho ∉ finiteZeroCarrierWindow T ∧ |(rho : ℂ).im| ≤ Z}
  let highSet : Set (Zeta23.zetaZeros Zeta23.zetaSeam).carrier :=
    {rho | Z < |(rho : ℂ).im|}
  have hfull : Summable f := by
    apply (zeroLorentzianSummand_summable x hx t).congr
    intro rho
    simp only [f, fullZeroLorentzianSummand]
  have hmedium : Summable (mediumSet.indicator f) := hfull.indicator mediumSet
  have hhigh : Summable (highSet.indicator f) := hfull.indicator highSet
  change (∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
      rho ∉ finiteZeroCarrierWindow T}, f rho) = _
  calc
    (∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
        rho ∉ finiteZeroCarrierWindow T}, f rho) =
        ∑' rho, ({rho |
          rho ∉ finiteZeroCarrierWindow T}.indicator f) rho := by
      exact _root_.tsum_subtype _ _
    _ =
        ∑' rho, (mediumSet.indicator f rho + highSet.indicator f rho) := by
      apply tsum_congr
      intro rho
      simp only [Set.indicator_apply]
      change (if rho ∉ finiteZeroCarrierWindow T then f rho else 0) =
        (if rho ∉ finiteZeroCarrierWindow T ∧ |(rho : ℂ).im| ≤ Z then f rho else 0) +
          if Z < |(rho : ℂ).im| then f rho else 0
      by_cases hwindow : rho ∈ finiteZeroCarrierWindow T
      · have hrange := (mem_finiteZeroWindow.mp
          (mem_finiteZeroCarrierWindow.mp hwindow)).2
        have habs : |(rho : ℂ).im| ≤ Z := by
          rw [abs_of_pos hrange.1]
          exact hrange.2.trans hTZ
        rw [ite_eq_right (fun hn => hn hwindow),
          ite_eq_right (fun hm => hm.1 hwindow),
          ite_eq_right (not_lt_of_ge habs)]
        simp
      · by_cases hheight : |(rho : ℂ).im| ≤ Z
        · rw [ite_eq_left hwindow, ite_eq_left ⟨hwindow, hheight⟩,
            ite_eq_right (not_lt_of_ge hheight)]
          simp
        · have hhigh' : Z < |(rho : ℂ).im| := lt_of_not_ge hheight
          rw [ite_eq_left hwindow, ite_eq_right (fun hm => hheight hm.2), ite_eq_left hhigh']
          simp
    _ = (∑' rho, mediumSet.indicator f rho) +
          ∑' rho, highSet.indicator f rho :=
      Summable.tsum_add hmedium hhigh
    _ = finiteMediumFullZeroLorentzianTail x T Z t +
          highFullZeroLorentzianTail x Z t := by
      apply congrArg₂ (· + ·)
      · apply tsum_congr
        intro rho
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, mediumSet, f]
      · apply tsum_congr
        intro rho
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, highSet, f]

private theorem measurable_fullZeroLorentzianSummand_fixed
    (x : ℝ) (hx : 1 ≤ x)
    (rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier) :
    Measurable (fun t : ℝ => fullZeroLorentzianSummand x t rho) := by
  rw [show (fun t : ℝ => fullZeroLorentzianSummand x t rho) =
      (fun t : ℝ =>
        (x : ℂ) ^ (-Complex.I * t) *
          ((2 * Zeta23.zeroMult rho : ℂ) *
            pairPower x ((rho : ℂ) - 1 / 2) * zeroLorentzian rho t)) by
    funext t
    exact fullZeroLorentzianSummand_eq_phase_mul x
      (zero_lt_one.trans_le hx) t rho]
  apply Measurable.mul
  · rw [show (fun t : ℝ => (x : ℂ) ^ (-Complex.I * t)) =
        (fun t : ℝ => Complex.exp
          (Complex.log (x : ℂ) * (-Complex.I * (t : ℂ)))) by
      funext t
      rw [Complex.cpow_def_of_ne_zero]
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (zero_lt_one.trans_le hx))]
    fun_prop
  · apply Measurable.const_mul
    unfold zeroLorentzian
    fun_prop

private theorem continuous_fullZeroLorentzianSummand_fixed
    (x : ℝ) (hx : 1 ≤ x)
    (rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier) :
    Continuous (fun t : ℝ => fullZeroLorentzianSummand x t rho) := by
  rw [show (fun t : ℝ => fullZeroLorentzianSummand x t rho) =
      (fun t : ℝ =>
        (x : ℂ) ^ (-Complex.I * t) *
          ((2 * Zeta23.zeroMult rho : ℂ) *
            pairPower x ((rho : ℂ) - 1 / 2) * zeroLorentzian rho t)) by
    funext t
    exact fullZeroLorentzianSummand_eq_phase_mul x
      (zero_lt_one.trans_le hx) t rho]
  apply Continuous.mul
  · rw [show (fun t : ℝ => (x : ℂ) ^ (-Complex.I * t)) =
        (fun t : ℝ => Complex.exp
          (Complex.log (x : ℂ) * (-Complex.I * (t : ℂ)))) by
      funext t
      rw [Complex.cpow_def_of_ne_zero]
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (zero_lt_one.trans_le hx))]
    fun_prop
  · apply Continuous.const_mul
    unfold zeroLorentzian
    apply Continuous.div₀ continuous_const (by fun_prop)
    intro t
    have hstrip := (Zeta23.zetaZeros Zeta23.zetaSeam).strip
      (rho : ℂ) rho.property
    have hdelta : |(rho : ℂ).re - 1 / 2| ≤ (1 / 2 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith [hstrip.1, hstrip.2]
    have hlower := shiftedLorentzian_norm_lower
      (t - (rho : ℂ).im) ((rho : ℂ).re - 1 / 2) hdelta
    have hden :
        (1 : ℂ) + ((t : ℂ) + Complex.I * ((rho : ℂ) - 1 / 2)) ^ 2 =
          1 + (((t - (rho : ℂ).im : ℝ) : ℂ) +
            Complex.I * (((rho : ℂ).re - 1 / 2 : ℝ) : ℂ)) ^ 2 := by
      congr 2
      apply Complex.ext
      · simp [sub_eq_add_neg]
      · simp [sub_eq_add_neg]
    rw [← hden] at hlower
    intro hzero
    rw [hzero, norm_zero] at hlower
    nlinarith [sq_nonneg (t - (rho : ℂ).im)]

private theorem finite_zeroCarrier_abs_im_le (Z : ℝ) :
    {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier |
      |(rho : ℂ).im| ≤ Z}.Finite := by
  let B : ℝ := |Z| + 1
  have hfinite :
      ((fun rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier => (rho : ℂ)) ⁻¹'
        ((Zeta23.zetaZeros Zeta23.zetaSeam).carrier ∩
          {rho : ℂ | -B < rho.im ∧ rho.im ≤ B})).Finite :=
    ((Zeta23.zetaZeros Zeta23.zetaSeam).finite_window (-B) B).preimage
      Subtype.val_injective.injOn
  refine Set.Finite.subset hfinite ?_
  intro rho hrho
  change |(rho : ℂ).im| ≤ Z at hrho
  have hrange := abs_le.mp hrho
  have hZabs : Z ≤ |Z| := le_abs_self Z
  exact ⟨rho.property, by
    dsimp only [B]
    constructor <;> linarith⟩

/-- The finite-height complementary zero sum is continuous in the height variable. -/
theorem continuous_finiteMediumFullZeroLorentzianTail
    (x : ℝ) (hx : 1 ≤ x) (T Z : ℝ) :
    Continuous (finiteMediumFullZeroLorentzianTail x T Z) := by
  classical
  let S : Finset (Zeta23.zetaZeros Zeta23.zetaSeam).carrier :=
    (finite_zeroCarrier_abs_im_le Z).toFinset
  have hrepr : finiteMediumFullZeroLorentzianTail x T Z =
      fun t : ℝ => ∑ rho ∈ S,
        if rho ∉ finiteZeroCarrierWindow T ∧ |(rho : ℂ).im| ≤ Z then
          fullZeroLorentzianSummand x t rho
        else 0 := by
    funext t
    unfold finiteMediumFullZeroLorentzianTail
    rw [tsum_eq_sum (s := S)]
    intro rho hrho
    have habs : ¬ |(rho : ℂ).im| ≤ Z := by
      intro habs
      exact hrho (by
        simp only [S, Set.Finite.mem_toFinset]
        change |(rho : ℂ).im| ≤ Z
        exact habs)
    simp only [habs, and_false, ↓reduceIte]
  rw [hrepr]
  apply continuous_finsetSum
  intro rho _hrho
  by_cases hmedium :
      rho ∉ finiteZeroCarrierWindow T ∧ |(rho : ℂ).im| ≤ Z
  · have heq :
        (fun t : ℝ =>
          if rho ∉ finiteZeroCarrierWindow T ∧ |(rho : ℂ).im| ≤ Z then
            fullZeroLorentzianSummand x t rho
          else 0) =
          fun t : ℝ => fullZeroLorentzianSummand x t rho := by
        funext t
        exact ite_eq_left hmedium
    rw [heq]
    exact continuous_fullZeroLorentzianSummand_fixed x hx rho
  · have heq :
        (fun t : ℝ =>
          if rho ∉ finiteZeroCarrierWindow T ∧ |(rho : ℂ).im| ≤ Z then
            fullZeroLorentzianSummand x t rho
          else 0) =
          fun _t : ℝ => 0 := by
        funext t
        exact ite_eq_right hmedium
    rw [heq]
    exact continuous_const

/-- The squared norm of the finite-height complementary zero sum is integrable on every
bounded height window. -/
theorem finiteMediumFullZeroLorentzianTail_norm_sq_integrableOn
    (x : ℝ) (hx : 1 ≤ x) (T Z : ℝ) :
    IntegrableOn (fun t : ℝ =>
      ‖finiteMediumFullZeroLorentzianTail x T Z t‖ ^ 2) (Set.Ioc 0 T) := by
  exact ((continuous_finiteMediumFullZeroLorentzianTail x hx T Z).norm.pow 2)
    |>.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

theorem measurable_highFullZeroLorentzianTail
    (x : ℝ) (hx : 1 ≤ x) (Z : ℝ) :
    Measurable (highFullZeroLorentzianTail x Z) := by
  let : Countable (Zeta23.zetaZeros Zeta23.zetaSeam).carrier :=
    zetaZero_carrier_countable.to_subtype
  unfold highFullZeroLorentzianTail
  apply Measurable.tsum
  intro rho
  by_cases hrho : Z < |(rho : ℂ).im|
  · simp only [hrho, ↓reduceIte]
    exact measurable_fullZeroLorentzianSummand_fixed x hx rho
  · simp only [hrho, ↓reduceIte]
    exact measurable_const

/-- The full zero sum outside Montgomery's finite window is measurable after splitting it
into the continuous finite-height part and the measurable high-ordinate tail. -/
theorem measurable_fullWindowComplement
    (x : ℝ) (hx : 1 ≤ x) (T Z : ℝ) (hTZ : T ≤ Z) :
    Measurable (fun t : ℝ =>
      ∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
          rho ∉ finiteZeroCarrierWindow T},
        fullZeroLorentzianSummand x t rho) := by
  have heq :
      (fun t : ℝ =>
        ∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
            rho ∉ finiteZeroCarrierWindow T},
          fullZeroLorentzianSummand x t rho) =
        fun t : ℝ => finiteMediumFullZeroLorentzianTail x T Z t +
          highFullZeroLorentzianTail x Z t := by
    funext t
    exact fullWindowComplement_eq_finiteMedium_add_high x hx T Z t hTZ
  rw [heq]
  exact (continuous_finiteMediumFullZeroLorentzianTail x hx T Z).measurable.add
    (measurable_highFullZeroLorentzianTail x hx Z)

/-- Squaring the exact medium-plus-high decomposition costs at most a factor two on each
piece. -/
theorem fullWindowComplement_norm_sq_le
    (x : ℝ) (hx : 1 ≤ x) (T Z t : ℝ) (hTZ : T ≤ Z) :
    ‖(∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
        rho ∉ finiteZeroCarrierWindow T},
      fullZeroLorentzianSummand x t rho)‖ ^ 2 ≤
      2 * ‖finiteMediumFullZeroLorentzianTail x T Z t‖ ^ 2 +
        2 * ‖highFullZeroLorentzianTail x Z t‖ ^ 2 := by
  rw [fullWindowComplement_eq_finiteMedium_add_high x hx T Z t hTZ]
  have htriangle := norm_add_le
    (finiteMediumFullZeroLorentzianTail x T Z t)
    (highFullZeroLorentzianTail x Z t)
  have hleft : 0 ≤ ‖finiteMediumFullZeroLorentzianTail x T Z t +
      highFullZeroLorentzianTail x Z t‖ := norm_nonneg _
  have hmedium : 0 ≤ ‖finiteMediumFullZeroLorentzianTail x T Z t‖ := norm_nonneg _
  have hhigh : 0 ≤ ‖highFullZeroLorentzianTail x Z t‖ := norm_nonneg _
  nlinarith [sq_nonneg
    (‖finiteMediumFullZeroLorentzianTail x T Z t‖ -
      ‖highFullZeroLorentzianTail x Z t‖)]

theorem highFullZeroLorentzianTail_norm_sq_integrableOn
    (x T Z : ℝ) (hx : 1 ≤ x) (_hT : 0 ≤ T)
    (hZ : 3 ≤ Z) (hTZ : 2 * T ≤ Z) :
    IntegrableOn (fun t : ℝ => ‖highFullZeroLorentzianTail x Z t‖ ^ 2)
      (Set.Ioc 0 T) := by
  obtain ⟨C, hC, htail⟩ := zetaZero_high_fullZeroLorentzian_tsum_norm_le
  apply IntegrableOn.of_bound measure_Ioc_lt_top
    ((measurable_highFullZeroLorentzianTail x hx Z).norm.pow_const 2).aestronglyMeasurable
    ((C * Real.sqrt x * Real.log Z / Z) ^ 2)
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hbound_nonneg : 0 ≤ C * Real.sqrt x * Real.log Z / Z := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg hC.le (Real.sqrt_nonneg x))
        (Real.log_nonneg (by linarith)))
      (by linarith)
  exact sq_le_sq' ((neg_nonpos.mpr hbound_nonneg).trans (norm_nonneg _))
    (htail x T Z t hx hZ ht.1.le ht.2 hTZ)

/-- The squared norm of the complete complementary zero sum is integrable whenever the
high-ordinate tail estimate applies. -/
theorem fullWindowComplement_norm_sq_integrableOn
    (x T Z : ℝ) (hx : 1 ≤ x) (hT : 0 ≤ T)
    (hZ : 3 ≤ Z) (hTZ : 2 * T ≤ Z) :
    IntegrableOn (fun t : ℝ =>
      ‖(∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
          rho ∉ finiteZeroCarrierWindow T},
        fullZeroLorentzianSummand x t rho)‖ ^ 2) (Set.Ioc 0 T) := by
  have hTZ' : T ≤ Z := by linarith
  have hmedium := finiteMediumFullZeroLorentzianTail_norm_sq_integrableOn x hx T Z
  have hhigh := highFullZeroLorentzianTail_norm_sq_integrableOn x T Z hx hT hZ hTZ
  have hmajor : IntegrableOn (fun t : ℝ =>
      2 * ‖finiteMediumFullZeroLorentzianTail x T Z t‖ ^ 2 +
        2 * ‖highFullZeroLorentzianTail x Z t‖ ^ 2) (Set.Ioc 0 T) := by
    exact (hmedium.const_mul 2).add (hhigh.const_mul 2)
  apply hmajor.mono'
  · exact ((measurable_fullWindowComplement x hx T Z hTZ').norm.pow_const 2)
      |>.aestronglyMeasurable
  · apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t _ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact fullWindowComplement_norm_sq_le x hx T Z t hTZ'

/-- Integrating the exact complement split leaves the finite-height medium range as the
only term not already estimated by the high-tail argument. -/
theorem fullWindowComplement_norm_sq_setIntegral_le
    (x T Z : ℝ) (hx : 1 ≤ x) (hT : 0 ≤ T)
    (hZ : 3 ≤ Z) (hTZ : 2 * T ≤ Z) :
    (∫ t in Set.Ioc 0 T,
      ‖(∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
          rho ∉ finiteZeroCarrierWindow T},
        fullZeroLorentzianSummand x t rho)‖ ^ 2) ≤
      2 * (∫ t in Set.Ioc 0 T,
        ‖finiteMediumFullZeroLorentzianTail x T Z t‖ ^ 2) +
      2 * (∫ t in Set.Ioc 0 T,
        ‖highFullZeroLorentzianTail x Z t‖ ^ 2) := by
  have hTZ' : T ≤ Z := by linarith
  have hleft := fullWindowComplement_norm_sq_integrableOn x T Z hx hT hZ hTZ
  have hmedium := finiteMediumFullZeroLorentzianTail_norm_sq_integrableOn x hx T Z
  have hhigh := highFullZeroLorentzianTail_norm_sq_integrableOn x T Z hx hT hZ hTZ
  have hmajor : IntegrableOn (fun t : ℝ =>
      2 * ‖finiteMediumFullZeroLorentzianTail x T Z t‖ ^ 2 +
        2 * ‖highFullZeroLorentzianTail x Z t‖ ^ 2) (Set.Ioc 0 T) := by
    exact (hmedium.const_mul 2).add (hhigh.const_mul 2)
  calc
    (∫ t in Set.Ioc 0 T,
        ‖(∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
            rho ∉ finiteZeroCarrierWindow T},
          fullZeroLorentzianSummand x t rho)‖ ^ 2) ≤
        ∫ t in Set.Ioc 0 T,
          (2 * ‖finiteMediumFullZeroLorentzianTail x T Z t‖ ^ 2 +
            2 * ‖highFullZeroLorentzianTail x Z t‖ ^ 2) := by
      apply MeasureTheory.integral_mono_ae hleft hmajor
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro t _ht
      exact fullWindowComplement_norm_sq_le x hx T Z t hTZ'
    _ = 2 * (∫ t in Set.Ioc 0 T,
          ‖finiteMediumFullZeroLorentzianTail x T Z t‖ ^ 2) +
        2 * (∫ t in Set.Ioc 0 T,
          ‖highFullZeroLorentzianTail x Z t‖ ^ 2) := by
      rw [MeasureTheory.integral_add (hmedium.const_mul 2) (hhigh.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- The squared high-ordinate tail has the integrated bound obtained by squaring the
uniform pointwise estimate. -/
theorem highFullZeroLorentzianTail_norm_sq_setIntegral_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (x T Z : ℝ),
      1 ≤ x → 0 ≤ T → 3 ≤ Z → 2 * T ≤ Z →
      ∫ t in Set.Ioc 0 T, ‖highFullZeroLorentzianTail x Z t‖ ^ 2 ≤
        T * (C * Real.sqrt x * Real.log Z / Z) ^ 2 := by
  obtain ⟨C, hC, htail⟩ := zetaZero_high_fullZeroLorentzian_tsum_norm_le
  refine ⟨C, hC, ?_⟩
  intro x T Z hx hT hZ hTZ
  have hf := highFullZeroLorentzianTail_norm_sq_integrableOn x T Z hx hT hZ hTZ
  have hg : IntegrableOn
      (fun _ : ℝ => (C * Real.sqrt x * Real.log Z / Z) ^ 2)
      (Set.Ioc 0 T) := by
    rw [integrableOn_const_iff]
    exact Or.inr measure_Ioc_lt_top
  calc
    (∫ t in Set.Ioc 0 T, ‖highFullZeroLorentzianTail x Z t‖ ^ 2) ≤
        ∫ _t in Set.Ioc 0 T, (C * Real.sqrt x * Real.log Z / Z) ^ 2 := by
      apply MeasureTheory.integral_mono_ae hf hg
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro t ht
      have hbound_nonneg : 0 ≤ C * Real.sqrt x * Real.log Z / Z := by
        exact div_nonneg
          (mul_nonneg (mul_nonneg hC.le (Real.sqrt_nonneg x))
            (Real.log_nonneg (by linarith)))
          (by linarith)
      exact sq_le_sq' ((neg_nonpos.mpr hbound_nonneg).trans (norm_nonneg _))
        (htail x T Z t hx hZ ht.1.le ht.2 hTZ)
    _ = T * (C * Real.sqrt x * Real.log Z / Z) ^ 2 := by
      rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hT]
      simp

/-- At the logarithmically enlarged cutoff `Z = T * (log T)^2`, the integrated squared
far tail is `O((log T)^{-2})`, uniformly for `1 ≤ x ≤ T`. -/
theorem highFullZeroLorentzianTail_logSquaredCutoff_norm_sq_setIntegral_le :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ x : ℝ,
      1 ≤ x → x ≤ T →
      ∫ t in Set.Ioc 0 T,
        ‖highFullZeroLorentzianTail x
          (T * (Real.log T) ^ 2) t‖ ^ 2 ≤
        K / (Real.log T) ^ 2 := by
  obtain ⟨C, hC, htail⟩ :=
    highFullZeroLorentzianTail_norm_sq_setIntegral_le
  refine ⟨9 * C ^ 2, by positivity, Real.exp 2, ?_⟩
  intro T hT x hx hxT
  have hTpos : 0 < T := (Real.exp_pos 2).trans_le hT
  have hTone : 1 ≤ T :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hT
  have hlogtwo : 2 ≤ Real.log T :=
    (Real.le_log_iff_exp_le hTpos).2 hT
  have hlogpos : 0 < Real.log T := by linarith
  have hlogSqFour : 4 ≤ (Real.log T) ^ 2 := by nlinarith
  have hZthree : 3 ≤ T * (Real.log T) ^ 2 := by
    calc
      (3 : ℝ) ≤ 1 * 4 := by norm_num
      _ ≤ T * (Real.log T) ^ 2 :=
        mul_le_mul hTone hlogSqFour (by norm_num) hTpos.le
  have hTZ : 2 * T ≤ T * (Real.log T) ^ 2 := by
    have htwoSq : (2 : ℝ) ≤ (Real.log T) ^ 2 := by linarith
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left htwoSq hTpos.le)
  have hlogZ :
      Real.log (T * (Real.log T) ^ 2) ≤ 3 * Real.log T := by
    rw [Real.log_mul hTpos.ne' (pow_ne_zero 2 hlogpos.ne'),
      Real.log_pow]
    have hloglog := Real.log_le_sub_one_of_pos hlogpos
    norm_num at hloglog ⊢
    nlinarith
  have hlogZnonneg : 0 ≤ Real.log (T * (Real.log T) ^ 2) :=
    Real.log_nonneg (by linarith [hZthree])
  have hsqrt : Real.sqrt x ≤ Real.sqrt T := Real.sqrt_le_sqrt hxT
  have hnumerator :
      C * Real.sqrt x * Real.log (T * (Real.log T) ^ 2) ≤
        C * Real.sqrt T * (3 * Real.log T) := by
    calc
      C * Real.sqrt x * Real.log (T * (Real.log T) ^ 2) ≤
          C * Real.sqrt T * Real.log (T * (Real.log T) ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt hC.le) hlogZnonneg
      _ ≤ C * Real.sqrt T * (3 * Real.log T) := by
        exact mul_le_mul_of_nonneg_left hlogZ
          (mul_nonneg hC.le (Real.sqrt_nonneg T))
  have hsqrtTpos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hinside :
      C * Real.sqrt x * Real.log (T * (Real.log T) ^ 2) /
          (T * (Real.log T) ^ 2) ≤
        3 * C / (Real.sqrt T * Real.log T) := by
    calc
      C * Real.sqrt x * Real.log (T * (Real.log T) ^ 2) /
          (T * (Real.log T) ^ 2) ≤
          C * Real.sqrt T * (3 * Real.log T) /
            (T * (Real.log T) ^ 2) :=
        (div_le_div_iff_of_pos_right (by positivity)).2 hnumerator
      _ = 3 * C / (Real.sqrt T * Real.log T) := by
        field_simp [hlogpos.ne', hsqrtTpos.ne']
        rw [Real.sq_sqrt hTpos.le]
  have hinsideNonneg :
      0 ≤ C * Real.sqrt x * Real.log (T * (Real.log T) ^ 2) /
        (T * (Real.log T) ^ 2) := by positivity
  have hmajorNonneg :
      0 ≤ 3 * C / (Real.sqrt T * Real.log T) := by positivity
  have hsquare :
      (C * Real.sqrt x * Real.log (T * (Real.log T) ^ 2) /
          (T * (Real.log T) ^ 2)) ^ 2 ≤
        (3 * C / (Real.sqrt T * Real.log T)) ^ 2 :=
    sq_le_sq' ((neg_nonpos.mpr hmajorNonneg).trans hinsideNonneg) hinside
  calc
    (∫ t in Set.Ioc 0 T,
        ‖highFullZeroLorentzianTail x
          (T * (Real.log T) ^ 2) t‖ ^ 2) ≤
        T * (C * Real.sqrt x *
          Real.log (T * (Real.log T) ^ 2) /
            (T * (Real.log T) ^ 2)) ^ 2 :=
      htail x T (T * (Real.log T) ^ 2) hx hTpos.le hZthree hTZ
    _ ≤ T * (3 * C / (Real.sqrt T * Real.log T)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hTpos.le
    _ = 9 * C ^ 2 / (Real.log T) ^ 2 := by
      field_simp [hlogpos.ne', hsqrtTpos.ne']
      rw [Real.sq_sqrt hTpos.le]
      ring

/-- At the logarithmically enlarged cutoff, the complete complement is reduced to the
finite-height medium range, up to an explicit `O((log T)⁻²)` far-tail error.  Controlling
the remaining medium integral at the closed Fourier endpoint is precisely where the
Vinogradov--Korobov-strength input is still required. -/
theorem fullWindowComplement_logSquaredCutoff_norm_sq_setIntegral_le :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ x : ℝ,
      1 ≤ x → x ≤ T →
      (∫ t in Set.Ioc 0 T,
        ‖(∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
            rho ∉ finiteZeroCarrierWindow T},
          fullZeroLorentzianSummand x t rho)‖ ^ 2) ≤
        2 * (∫ t in Set.Ioc 0 T,
          ‖finiteMediumFullZeroLorentzianTail x T
            (T * (Real.log T) ^ 2) t‖ ^ 2) +
        K / (Real.log T) ^ 2 := by
  obtain ⟨K, hK, T₀, hhigh⟩ :=
    highFullZeroLorentzianTail_logSquaredCutoff_norm_sq_setIntegral_le
  refine ⟨2 * K, by positivity, max T₀ (Real.exp 2), ?_⟩
  intro T hT x hx hxT
  have hT₀ : T₀ ≤ T := (le_max_left T₀ (Real.exp 2)).trans hT
  have hTexp : Real.exp 2 ≤ T := (le_max_right T₀ (Real.exp 2)).trans hT
  have hTpos : 0 < T := (Real.exp_pos 2).trans_le hTexp
  have hTone : 1 ≤ T :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hTexp
  have hlogtwo : 2 ≤ Real.log T :=
    (Real.le_log_iff_exp_le hTpos).2 hTexp
  have hZthree : 3 ≤ T * (Real.log T) ^ 2 := by
    have hlogSqFour : 4 ≤ (Real.log T) ^ 2 := by nlinarith
    calc
      (3 : ℝ) ≤ 1 * 4 := by norm_num
      _ ≤ T * (Real.log T) ^ 2 :=
        mul_le_mul hTone hlogSqFour (by norm_num) hTpos.le
  have hTZ : 2 * T ≤ T * (Real.log T) ^ 2 := by
    have htwoSq : (2 : ℝ) ≤ (Real.log T) ^ 2 := by nlinarith
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left htwoSq hTpos.le)
  have hsplit := fullWindowComplement_norm_sq_setIntegral_le
    x T (T * (Real.log T) ^ 2) hx hTpos.le hZthree hTZ
  have hfar := hhigh T hT₀ x hx hxT
  calc
    (∫ t in Set.Ioc 0 T,
        ‖(∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
            rho ∉ finiteZeroCarrierWindow T},
          fullZeroLorentzianSummand x t rho)‖ ^ 2) ≤
        2 * (∫ t in Set.Ioc 0 T,
          ‖finiteMediumFullZeroLorentzianTail x T
            (T * (Real.log T) ^ 2) t‖ ^ 2) +
        2 * (∫ t in Set.Ioc 0 T,
          ‖highFullZeroLorentzianTail x
            (T * (Real.log T) ^ 2) t‖ ^ 2) := hsplit
    _ ≤ 2 * (∫ t in Set.Ioc 0 T,
          ‖finiteMediumFullZeroLorentzianTail x T
            (T * (Real.log T) ^ 2) t‖ ^ 2) +
        2 * (K / (Real.log T) ^ 2) := by
      linarith
    _ = 2 * (∫ t in Set.Ioc 0 T,
          ‖finiteMediumFullZeroLorentzianTail x T
            (T * (Real.log T) ^ 2) t‖ ^ 2) +
        (2 * K) / (Real.log T) ^ 2 := by ring

/-- Cauchy--Schwarz for the product of two norm functions on a measurable set.  The
square-integrability hypotheses are phrased exactly as they occur in the endpoint energy
comparison below. -/
lemma setIntegral_norm_mul_norm_le_sqrt
    {f g : ℝ → ℂ} {s : Set ℝ}
    (hf : IntegrableOn (fun t => ‖f t‖ ^ 2) s)
    (hg : IntegrableOn (fun t => ‖g t‖ ^ 2) s) :
    (∫ t in s, ‖f t‖ * ‖g t‖) ≤
      Real.sqrt ((∫ t in s, ‖f t‖ ^ 2) *
        (∫ t in s, ‖g t‖ ^ 2)) := by
  let μ : Measure ℝ := volume.restrict s
  let F : ℝ → ℝ := fun t => ‖f t‖
  let G : ℝ → ℝ := fun t => ‖g t‖
  have hf' : Integrable (fun t => ‖f t‖ ^ 2) μ := by
    change IntegrableOn (fun t => ‖f t‖ ^ 2) s
    exact hf
  have hg' : Integrable (fun t => ‖g t‖ ^ 2) μ := by
    change IntegrableOn (fun t => ‖g t‖ ^ 2) s
    exact hg
  have hFmeas : AEStronglyMeasurable F μ := by
    have hsqrt := hf'.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
    simpa only [F, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hGmeas : AEStronglyMeasurable G μ := by
    have hsqrt := hg'.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
    simpa only [G, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hFsq : Integrable (fun t => ‖F t‖ ^ 2) μ := by
    simpa only [F, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hf'
  have hGsq : Integrable (fun t => ‖G t‖ ^ 2) μ := by
    simpa only [G, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hg'
  have hF : MemLp F 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hFmeas).2 hFsq
  have hG : MemLp G 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hGmeas).2 hGsq
  have hcs := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (f := F) (g := G) Real.HolderConjugate.two_two
      (by simpa using hF) (by simpa using hG)
  have hFnonneg : 0 ≤ ∫ t in s, ‖f t‖ ^ 2 :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  have hGnonneg : 0 ≤ ∫ t in s, ‖g t‖ ^ 2 :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  calc
    (∫ t in s, ‖f t‖ * ‖g t‖) ≤
        Real.sqrt (∫ t in s, ‖f t‖ ^ 2) *
          Real.sqrt (∫ t in s, ‖g t‖ ^ 2) := by
      simpa only [μ, F, G, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), abs_mul,
        Real.sqrt_eq_rpow, Real.rpow_two] using hcs
    _ = Real.sqrt ((∫ t in s, ‖f t‖ ^ 2) *
          (∫ t in s, ‖g t‖ ^ 2)) :=
      (Real.sqrt_mul hFnonneg _).symm

/-- The abstract energy identity behind the endpoint comparison.  If `B` is supported on
`s`, the difference of the global second moments is controlled by the exterior energy of
`A`, the interior discrepancy energy, and the Cauchy--Schwarz cross term. -/
lemma norm_secondMoment_sub_secondMoment_le_exterior_add_discrepancy
    {A B : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    (hA : Integrable (fun t => A t * (starRingEnd ℂ) (A t)))
    (hB : Integrable (fun t => B t * (starRingEnd ℂ) (B t)))
    (hBzero : ∀ t ∉ s, B t = 0)
    (hD : IntegrableOn (fun t => ‖A t - B t‖ ^ 2) s) :
    ‖(∫ t, A t * (starRingEnd ℂ) (A t)) -
        ∫ t, B t * (starRingEnd ℂ) (B t)‖ ≤
      (∫ t in sᶜ, ‖A t‖ ^ 2) +
        (∫ t in s, ‖A t - B t‖ ^ 2) +
          2 * Real.sqrt ((∫ t in s, ‖A t - B t‖ ^ 2) *
            (∫ t in s, ‖B t‖ ^ 2)) := by
  have hAsq : Integrable (fun t => ‖A t‖ ^ 2) := by
    have h := hA.norm
    simpa only [norm_mul, Complex.norm_conj, pow_two] using h
  have hBsq : Integrable (fun t => ‖B t‖ ^ 2) := by
    have h := hB.norm
    simpa only [norm_mul, Complex.norm_conj, pow_two] using h
  have hBsqOn : IntegrableOn (fun t => ‖B t‖ ^ 2) s :=
    hBsq.integrableOn
  have hDnorm_meas : AEStronglyMeasurable (fun t => ‖A t - B t‖)
      (volume.restrict s) := by
    have hsqrt := hD.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hBnorm_meas : AEStronglyMeasurable (fun t => ‖B t‖)
      (volume.restrict s) := by
    have hsqrt := hBsqOn.aestronglyMeasurable.aemeasurable.sqrt
      |>.aestronglyMeasurable
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hprod : IntegrableOn (fun t => ‖A t - B t‖ * ‖B t‖) s := by
    apply (hD.add hBsqOn).mono'
    · exact hDnorm_meas.mul hBnorm_meas
    · filter_upwards with t
      simp only [Pi.add_apply, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      nlinarith [sq_nonneg (‖A t - B t‖ - ‖B t‖),
        norm_nonneg (A t - B t), norm_nonneg (B t)]
  have hmajor : IntegrableOn (fun t =>
      ‖A t - B t‖ ^ 2 + 2 * (‖A t - B t‖ * ‖B t‖)) s :=
    hD.add (hprod.const_mul 2)
  have hpoint : ∀ t,
      ‖A t * (starRingEnd ℂ) (A t) -
          B t * (starRingEnd ℂ) (B t)‖ ≤
        ‖A t - B t‖ ^ 2 + 2 * (‖A t - B t‖ * ‖B t‖) := by
    intro t
    have htriangle : ‖A t‖ ≤ ‖A t - B t‖ + ‖B t‖ := by
      simpa only [sub_add_cancel] using norm_add_le (A t - B t) (B t)
    calc
      ‖A t * (starRingEnd ℂ) (A t) -
          B t * (starRingEnd ℂ) (B t)‖ ≤
          ‖A t - B t‖ * (‖A t‖ + ‖B t‖) :=
        norm_mul_conj_sub_mul_conj_le (A t) (B t)
      _ ≤ ‖A t - B t‖ *
          ((‖A t - B t‖ + ‖B t‖) + ‖B t‖) := by
        gcongr
      _ = ‖A t - B t‖ ^ 2 +
          2 * (‖A t - B t‖ * ‖B t‖) := by ring
  have hBcompl : ∫ t in sᶜ,
      B t * (starRingEnd ℂ) (B t) = 0 := by
    apply integral_eq_zero_of_ae
    apply ae_restrict_of_forall_mem hs.compl
    intro t ht
    simp only [Pi.zero_apply]
    rw [hBzero t ht, map_zero, zero_mul]
  have hdecomp :
      (∫ t, A t * (starRingEnd ℂ) (A t)) -
          ∫ t, B t * (starRingEnd ℂ) (B t) =
        (∫ t in s, (A t * (starRingEnd ℂ) (A t) -
          B t * (starRingEnd ℂ) (B t))) +
          ∫ t in sᶜ, A t * (starRingEnd ℂ) (A t) := by
    rw [← integral_add_compl hs hA, ← integral_add_compl hs hB, hBcompl]
    rw [integral_sub hA.integrableOn hB.integrableOn]
    ring
  rw [hdecomp]
  calc
    ‖(∫ t in s, (A t * (starRingEnd ℂ) (A t) -
        B t * (starRingEnd ℂ) (B t))) +
        ∫ t in sᶜ, A t * (starRingEnd ℂ) (A t)‖ ≤
        ‖∫ t in s, (A t * (starRingEnd ℂ) (A t) -
          B t * (starRingEnd ℂ) (B t))‖ +
          ‖∫ t in sᶜ, A t * (starRingEnd ℂ) (A t)‖ := norm_add_le _ _
    _ ≤ (∫ t in s,
          (‖A t - B t‖ ^ 2 + 2 * (‖A t - B t‖ * ‖B t‖))) +
        (∫ t in sᶜ, ‖A t‖ ^ 2) := by
      gcongr
      · apply norm_integral_le_of_norm_le hmajor
        filter_upwards with t
        exact hpoint t
      · calc
          ‖∫ t in sᶜ, A t * (starRingEnd ℂ) (A t)‖ ≤
              ∫ t in sᶜ, ‖A t * (starRingEnd ℂ) (A t)‖ :=
            norm_integral_le_integral_norm _
          _ = ∫ t in sᶜ, ‖A t‖ ^ 2 := by
            congr 1
            funext t
            rw [norm_mul, Complex.norm_conj, pow_two]
    _ = (∫ t in sᶜ, ‖A t‖ ^ 2) +
        (∫ t in s, ‖A t - B t‖ ^ 2) +
          2 * (∫ t in s, ‖A t - B t‖ * ‖B t‖) := by
      rw [MeasureTheory.integral_add hD (hprod.const_mul 2),
        MeasureTheory.integral_const_mul]
      ring
    _ ≤ (∫ t in sᶜ, ‖A t‖ ^ 2) +
        (∫ t in s, ‖A t - B t‖ ^ 2) +
          2 * Real.sqrt ((∫ t in s, ‖A t - B t‖ ^ 2) *
            (∫ t in s, ‖B t‖ ^ 2)) := by
      gcongr
      exact setIntegral_norm_mul_norm_le_sqrt hD hBsqOn

/-- Exact specialization of the abstract energy bridge to Montgomery's finite window and
the phase-corrected full-zero model.  The interior discrepancy is rewritten as the
complementary zero energy by the exact zero-sum identity; no pointwise majorant is used. -/
theorem norm_finiteWindowSecondMoment_sub_windowedFullZeroSecondMoment_le_energy
    (x T Z : ℝ) (hx : 1 ≤ x) (hT : 0 ≤ T)
    (hZ : 3 ≤ Z) (hTZ : 2 * T ≤ Z) :
    ‖finiteWindowSecondMoment x T - windowedFullZeroSecondMoment x T‖ ≤
      (∫ t in (Set.Ioc 0 T)ᶜ, ‖finiteWindowLorentzianSum x T t‖ ^ 2) +
        (∫ t in Set.Ioc 0 T,
          ‖(∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
              rho ∉ finiteZeroCarrierWindow T},
            fullZeroLorentzianSummand x t rho)‖ ^ 2) +
          2 * Real.sqrt
            ((∫ t in Set.Ioc 0 T,
                ‖(∑' rho : {rho :
                    (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
                    rho ∉ finiteZeroCarrierWindow T},
                  fullZeroLorentzianSummand x t rho)‖ ^ 2) *
              (∫ t in Set.Ioc 0 T, ‖windowedFullZeroSum x T t‖ ^ 2)) := by
  have hA := finiteWindowLorentzianSum_mul_conj_integrable x T
  have hB := integrable_windowedFullZeroSum_mul_conj x T hx
  have hcomplement :=
    fullWindowComplement_norm_sq_integrableOn x T Z hx hT hZ hTZ
  have hD : IntegrableOn (fun t =>
      ‖finiteWindowLorentzianSum x T t - windowedFullZeroSum x T t‖ ^ 2)
      (Set.Ioc 0 T) := by
    refine hcomplement.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_finiteWindowLorentzianSum_sub_windowedFullZeroSum_of_mem
      x hx T t ht]
  have hzero : ∀ t ∉ Set.Ioc (0 : ℝ) T,
      windowedFullZeroSum x T t = 0 := by
    intro t ht
    rw [windowedFullZeroSum, Set.indicator_of_notMem ht]
  have hbridge :=
    norm_secondMoment_sub_secondMoment_le_exterior_add_discrepancy
      measurableSet_Ioc hA hB hzero hD
  have henergy :
      (∫ t in Set.Ioc 0 T,
          ‖finiteWindowLorentzianSum x T t - windowedFullZeroSum x T t‖ ^ 2) =
        ∫ t in Set.Ioc 0 T,
          ‖(∑' rho : {rho :
              (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
              rho ∉ finiteZeroCarrierWindow T},
            fullZeroLorentzianSummand x t rho)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_finiteWindowLorentzianSum_sub_windowedFullZeroSum_of_mem
      x hx T t ht]
  rw [henergy] at hbridge
  simpa only [finiteWindowSecondMoment, windowedFullZeroSecondMoment] using hbridge

/-- The genuine finite-medium endpoint input.  At `x = T`, proving this uniform
`O(T / log T)` estimate requires principal-zeta Vinogradov--Korobov strength (or an
equivalent integrated endpoint theorem); the high-ordinate part has already been proved
above. -/
def FiniteMediumFullZeroEndpointEnergyBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ x : ℝ, 1 ≤ x → x ≤ T →
    (∫ t in Set.Ioc 0 T,
      ‖finiteMediumFullZeroLorentzianTail x T
        (T * (Real.log T) ^ 2) t‖ ^ 2) ≤ C * T / Real.log T

/-- Exterior leakage of the finite positive-height window.  This contract is separated
from the interior complementary-zero estimate because it is a distinct boundary term in
the exact energy identity. -/
def FiniteWindowExteriorEnergyBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ x : ℝ, 1 ≤ x → x ≤ T →
    (∫ t in (Set.Ioc 0 T)ᶜ,
      ‖finiteWindowLorentzianSum x T t‖ ^ 2) ≤ C * (T + x)

/-- The proved high-ordinate estimate upgrades the finite-medium endpoint contract to a
bound for the entire complementary zero energy. -/
theorem fullWindowComplement_endpointEnergyBound_of_finiteMedium
    (hmedium : FiniteMediumFullZeroEndpointEnergyBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ x : ℝ, 1 ≤ x → x ≤ T →
      (∫ t in Set.Ioc 0 T,
        ‖(∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
            rho ∉ finiteZeroCarrierWindow T},
          fullZeroLorentzianSummand x t rho)‖ ^ 2) ≤ C * T / Real.log T := by
  rcases hmedium with ⟨Cm, hCm, Tm, hmedium⟩
  rcases fullWindowComplement_logSquaredCutoff_norm_sq_setIntegral_le with
    ⟨Kh, hKh, Th, hhigh⟩
  refine ⟨2 * Cm + Kh, by positivity,
    max (max Tm Th) (Real.exp 2), ?_⟩
  intro T hT x hx hxT
  have hTm : Tm ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTh : Th ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTexp : Real.exp 2 ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := (Real.exp_pos 2).trans_le hTexp
  have hTone : 1 ≤ T :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hTexp
  have hlogtwo : 2 ≤ Real.log T :=
    (Real.le_log_iff_exp_le hTpos).2 hTexp
  have hlogpos : 0 < Real.log T := by linarith
  have hinv : 1 / (Real.log T) ^ 2 ≤ T / Real.log T := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hlogpos) hlogpos).2
    calc
      1 * Real.log T ≤ (Real.log T) ^ 2 := by nlinarith
      _ ≤ T * (Real.log T) ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg (Real.log T)) hTone
  have hsplit := hhigh T hTh x hx hxT
  have hmed := hmedium T hTm x hx hxT
  calc
    (∫ t in Set.Ioc 0 T,
        ‖(∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
            rho ∉ finiteZeroCarrierWindow T},
          fullZeroLorentzianSummand x t rho)‖ ^ 2) ≤
        2 * (∫ t in Set.Ioc 0 T,
          ‖finiteMediumFullZeroLorentzianTail x T
            (T * (Real.log T) ^ 2) t‖ ^ 2) +
          Kh / (Real.log T) ^ 2 := hsplit
    _ ≤ 2 * (Cm * T / Real.log T) + Kh / (Real.log T) ^ 2 := by
      gcongr
    _ ≤ 2 * (Cm * T / Real.log T) + Kh * (T / Real.log T) := by
      exact add_le_add (le_refl _)
        (by
          calc
            Kh / (Real.log T) ^ 2 = Kh * (1 / (Real.log T) ^ 2) := by ring
            _ ≤ Kh * (T / Real.log T) :=
              mul_le_mul_of_nonneg_left hinv hKh.le)
    _ = (2 * Cm + Kh) * T / Real.log T := by ring

end ZetaZeros.Unconditional.PairCorrelationProof
