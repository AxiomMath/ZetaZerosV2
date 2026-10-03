/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.PairCorrelation.Function

/-!
# From the mean square to the pair-correlation function

The relation between the mean square `L (x, T) = ∫₀^T |ℓ (x, t)|² dt` of the zero side of the
explicit formula and the pair-correlation function `F (x, T)`.

## Main results

* `ZetaZeros.allZeros_countable`: the set `𝒩*` of all non-trivial zeros is countable.
* `ZetaZeros.zeroSideMeanSquare_eq_tsum_pairKernel_integral`: expanding the square,
  `L (x, T) = 4 ∑_{ρ, ρ' ∈ 𝒩*} m_ρ m_ρ' x^{ρ + conj ρ' - 1} ∫₀^T κ_{ρ,ρ'} (t) dt`, the family
  being absolutely summable.
* `ZetaZeros.exists_norm_pairCorrelation_sub_zeroSideMeanSquare_div_le`: the truncation lemma
  `|F (x, T) - L (x, T) / (2π)| ≤ C x log³T`.

## Implementation notes

The whole error of the truncation lemma is controlled with the single bound
`|x^{ρ + conj ρ' - 1}| ≤ x`, which uses nothing about the two zeros beyond `0 < re < 1`. That is
`norm_cpow_pair_le`, whose only hypotheses are `1 ≤ x`, `re ρ < 1` and `re ρ' < 1`; no zero-free
region enters.

Absolute summability over `𝒩* × 𝒩*` is proved throughout by bounding *finite* partial sums: the
double sum of the majorant over two finite sets of zeros is the integral of the product of the two
Poisson-weighted counts (`sum_sum_pairIntegral_eq`), so each imported estimate is applied to a
`Finset` and the summability then comes from `summable_of_sum_le`.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory

/-! ### The zeros form a countable set -/

/-- **The non-trivial zeros are countable.** Every bounded region contains finitely many of them,
and the plane is a countable union of closed balls of integer radius. -/
theorem allZeros_countable : allZeros.Countable := by
  refine Set.Countable.mono (fun ρ hρ => ?_)
    (Set.countable_iUnion fun n : ℕ =>
      ((isCompact_closedBall (0 : ℂ) n).inter_riemannZetaZeros_finite).countable)
  obtain ⟨n, hn⟩ := exists_nat_ge ‖ρ‖
  refine Set.mem_iUnion.2 ⟨n, ?_, mem_riemannZetaZeros.mpr hρ.1⟩
  simpa [Metric.mem_closedBall] using hn

instance : Countable (allZeros : Set ℂ) := allZeros_countable.to_subtype

/-! ### Elementary facts about the pair kernel -/

/-- The second factor of the pair kernel is the conjugate of the denominator of the sum over
zeros: conjugation fixes `1/2` and negates `it`. -/
theorem conj_denom (ρ : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2)
      = 1 - ((starRingEnd ℂ) ρ - (1 / 2 - (t : ℂ) * I)) ^ 2 := by
  simp only [map_sub, map_pow, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal,
    map_div₀, map_ofNat]
  ring

/-- The denominator of the sum over zeros is at least `3/4 (1 + (t - im ρ)²)`. -/
private lemma norm_denom_ge {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (t : ℝ) :
    3 / 4 * (1 + (t - ρ.im) ^ 2) ≤ ‖1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2‖ := by
  have h := three_quarters_add_sq_le_norm_one_sub_sq h0 h1 t
  nlinarith [sq_nonneg (t - ρ.im)]

/-- The same for the conjugated factor, whose modulus is unchanged. -/
private lemma norm_denom_conj_ge {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (t : ℝ) :
    3 / 4 * (1 + (t - ρ.im) ^ 2)
      ≤ ‖1 - ((starRingEnd ℂ) ρ - (1 / 2 - (t : ℂ) * I)) ^ 2‖ := by
  rw [← conj_denom, Complex.norm_conj]
  exact norm_denom_ge h0 h1 t

/-- **The pair kernel is dominated by the product of two Poisson weights.** -/
private lemma norm_pairKernel_le {ρ ρ' : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (h0' : 0 < ρ'.re)
    (h1' : ρ'.re < 1) (t : ℝ) :
    ‖pairKernel ρ ρ' t‖
      ≤ 16 / 9 * (1 / (1 + (t - ρ.im) ^ 2)) * (1 / (1 + (t - ρ'.im) ^ 2)) := by
  have ha : (0 : ℝ) < 1 + (t - ρ.im) ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 + (t - ρ'.im) ^ 2 := by positivity
  have hA := norm_denom_ge h0 h1 t
  have hB := norm_denom_conj_ge h0' h1' t
  have hkey : 9 / 16 * ((1 + (t - ρ.im) ^ 2) * (1 + (t - ρ'.im) ^ 2))
      ≤ ‖1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2‖ *
        ‖1 - ((starRingEnd ℂ) ρ' - (1 / 2 - (t : ℂ) * I)) ^ 2‖ :=
    calc 9 / 16 * ((1 + (t - ρ.im) ^ 2) * (1 + (t - ρ'.im) ^ 2))
        = 3 / 4 * (1 + (t - ρ.im) ^ 2) * (3 / 4 * (1 + (t - ρ'.im) ^ 2)) := by ring
      _ ≤ _ := mul_le_mul hA hB (by positivity) (norm_nonneg _)
  rw [pairKernel, norm_inv, norm_mul, inv_eq_one_div,
    show (16 : ℝ) / 9 * (1 / (1 + (t - ρ.im) ^ 2)) * (1 / (1 + (t - ρ'.im) ^ 2))
      = 1 / (9 / 16 * ((1 + (t - ρ.im) ^ 2) * (1 + (t - ρ'.im) ^ 2))) from by
        field_simp]
  exact one_div_le_one_div_of_le (by positivity) hkey

/-- Neither factor of the pair kernel vanishes, for zeros of the open critical strip. -/
private lemma pairKernel_denom_ne_zero {ρ ρ' : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (h0' : 0 < ρ'.re) (h1' : ρ'.re < 1) (t : ℝ) :
    (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2) *
      (1 - ((starRingEnd ℂ) ρ' - (1 / 2 - (t : ℂ) * I)) ^ 2) ≠ 0 := by
  have hA := norm_denom_ge h0 h1 t
  have hB := norm_denom_conj_ge h0' h1' t
  have ha : (0 : ℝ) < 1 + (t - ρ.im) ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 + (t - ρ'.im) ^ 2 := by positivity
  refine mul_ne_zero (fun h => ?_) (fun h => ?_)
  · rw [h, norm_zero] at hA; nlinarith
  · rw [h, norm_zero] at hB; nlinarith

/-- The pair kernel is continuous in `t`. -/
theorem continuous_pairKernel {ρ ρ' : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (h0' : 0 < ρ'.re)
    (h1' : ρ'.re < 1) : Continuous (pairKernel ρ ρ') := by
  refine Continuous.inv₀ ?_ (pairKernel_denom_ne_zero h0 h1 h0' h1')
  fun_prop

/-- The Poisson weight of a single zero is continuous. -/
private lemma continuous_poisson (γ : ℝ) :
    Continuous fun t : ℝ => 1 / (1 + (t - γ) ^ 2) :=
  continuous_const.div (by fun_prop) fun t => by positivity

/-- The Poisson weight of a single zero is integrable on the line. -/
private lemma integrable_poisson (γ : ℝ) :
    Integrable (fun t : ℝ => 1 / (1 + (t - γ) ^ 2)) := by
  simpa [one_div] using integrable_inv_one_add_sq.comp_sub_right γ

/-! ### The Poisson-weighted count over a finite set of zeros -/

/-- **The Poisson-weighted count, for a finite set of zeros.** The bound of
`exists_summable_poissonWeight_tsum_le` for a finite sum over zeros. -/
private lemma exists_finset_poissonWeight_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (A : Finset ℂ), (∀ ρ ∈ A, ρ ∈ allZeros) →
      ∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) ≤ C * Real.log (|t| + 3) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_summable_poissonWeight_tsum_le
  refine ⟨C, hC0, fun t A hA => ?_⟩
  obtain ⟨hsum, hle⟩ := hC t
  have h1 := Finset.sum_subtype_eq_sum_filter
    (fun ρ : ℂ => (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) (p := (· ∈ allZeros)) (s := A)
  rw [Finset.filter_true_of_mem hA] at h1
  rw [← h1]
  exact (hsum.sum_le_tsum _ fun i _ => by positivity).trans hle

/-- **The one-sided integral estimate, for a finite set of zeros.** The bound of
`exists_summable_poissonIntegral_outside_tsum_le` for a finite sum over zeros. -/
private lemma exists_finset_poissonIntegral_outside_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T → ∀ A : Finset ℂ,
      (∀ ρ ∈ A, ρ ∈ allZeros ∧ ρ.im ∉ Set.Ioc (0 : ℝ) T) →
      ∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2)
        ≤ C * Real.log T ^ 2 := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_summable_poissonIntegral_outside_tsum_le
  refine ⟨C, hC0, fun T hT A hA => ?_⟩
  obtain ⟨hsum, hle⟩ := hC T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have h1 := Finset.sum_subtype_eq_sum_filter
    (fun ρ : ℂ => (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2))
    (p := fun ρ : ℂ => ρ ∈ allZeros ∧ ρ.im ∉ Set.Ioc (0 : ℝ) T) (s := A)
  rw [Finset.filter_true_of_mem hA] at h1
  rw [← h1]
  refine (hsum.sum_le_tsum _ fun i _ => ?_).trans hle
  exact mul_nonneg (Nat.cast_nonneg _)
    (intervalIntegral.integral_nonneg hT0.le fun t _ => by positivity)

/-! ### The majorant of a pair of zeros -/

/-- The integral over `[0, T]` of the product of the Poisson weights of two zeros, each carrying
its multiplicity: the majorant of the pair term of the expansion of the mean square. -/
private noncomputable def pairIntegral (T : ℝ) (ρ ρ' : ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..T, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) *
    ((zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2))

/-- The integrand of `pairIntegral` is continuous. -/
private lemma continuous_pairSummand (ρ ρ' : ℂ) :
    Continuous fun t : ℝ => (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) *
      ((zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2)) :=
  Continuous.mul (continuous_const.div (by fun_prop) fun t => by positivity)
    (continuous_const.div (by fun_prop) fun t => by positivity)

/-- The integrand of `pairIntegral` is interval integrable. -/
private lemma intervalIntegrable_pair (ρ ρ' : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) *
      ((zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2))) volume a b :=
  (continuous_pairSummand ρ ρ').intervalIntegrable a b

/-- `pairIntegral` is nonnegative for `0 ≤ T`. -/
private lemma pairIntegral_nonneg {T : ℝ} (hT : 0 ≤ T) (ρ ρ' : ℂ) : 0 ≤ pairIntegral T ρ ρ' :=
  intervalIntegral.integral_nonneg hT fun t _ => by positivity

/-- `pairIntegral` is symmetric. -/
private lemma pairIntegral_comm (T : ℝ) (ρ ρ' : ℂ) :
    pairIntegral T ρ ρ' = pairIntegral T ρ' ρ := by
  rw [pairIntegral, pairIntegral]
  exact intervalIntegral.integral_congr fun t _ => mul_comm _ _

/-- **The double sum of the majorant is the integral of the product of the two Poisson sums.** -/
private lemma sum_sum_pairIntegral_eq (T : ℝ) (A B : Finset ℂ) :
    ∑ ρ ∈ A, ∑ ρ' ∈ B, pairIntegral T ρ ρ'
      = ∫ t in (0 : ℝ)..T, (∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) *
          ∑ ρ' ∈ B, (zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2) := by
  have hint : ∀ ρ : ℂ, IntervalIntegrable (fun t : ℝ => ∑ ρ' ∈ B,
      (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) *
        ((zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2))) volume 0 T := fun ρ =>
    Continuous.intervalIntegrable
      (continuous_finsetSum B fun ρ' _ => continuous_pairSummand ρ ρ') 0 T
  have h1 : ∀ ρ : ℂ, ∑ ρ' ∈ B, pairIntegral T ρ ρ'
      = ∫ t in (0 : ℝ)..T, ∑ ρ' ∈ B, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) *
          ((zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2)) := fun ρ =>
    (intervalIntegral.integral_finsetSum fun ρ' _ => intervalIntegrable_pair ρ ρ' 0 T).symm
  rw [Finset.sum_congr rfl fun ρ _ => h1 ρ,
    ← intervalIntegral.integral_finsetSum fun ρ _ => hint ρ]
  exact intervalIntegral.integral_congr fun t _ => (Finset.sum_mul_sum _ _ _ _).symm

/-- `pairIntegral` with the two multiplicities pulled out of the integral. -/
private lemma pairIntegral_eq (T : ℝ) (ρ ρ' : ℂ) :
    pairIntegral T ρ ρ' = (zeroMultiplicity ρ : ℝ) * (zeroMultiplicity ρ' : ℝ) *
      ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) * (1 / (1 + (t - ρ'.im) ^ 2)) := by
  rw [pairIntegral, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun t _ => by ring

/-- A finite Poisson sum is continuous. -/
private lemma continuous_poissonSum (A : Finset ℂ) :
    Continuous fun t : ℝ => ∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) :=
  continuous_finsetSum A fun ρ _ => continuous_const.div (by fun_prop) fun t => by positivity

/-! ### The uniform bound over finite sets of pairs of zeros -/

/-- **The majorant is uniformly bounded over finite sets of pairs.** The double sum is the
integral over `[0, T]` of the square of the Poisson-weighted count, which is `O(log (T + 3))` on
the range; the interval has length `T`. -/
private lemma exists_sum_pairIntegral_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ u : Finset (allZeros × allZeros),
      ∑ p ∈ u, pairIntegral T (p.1 : ℂ) (p.2 : ℂ) ≤ C * T * Real.log (T + 3) ^ 2 := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_finset_poissonWeight_le
  refine ⟨C ^ 2, by positivity, fun T hT u => ?_⟩
  set S : Finset allZeros := u.image Prod.fst ∪ u.image Prod.snd with hSdef
  set A : Finset ℂ := S.image Subtype.val with hAdef
  have hAmem : ∀ ρ ∈ A, ρ ∈ allZeros := fun ρ hρ => by
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hρ
    exact σ.2
  have hsub : u ⊆ S ×ˢ S := fun p hp => by
    rw [Finset.mem_product, hSdef]
    exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  have hconv : ∑ ρ ∈ A, ∑ ρ' ∈ A, pairIntegral T ρ ρ'
      = ∑ ρ ∈ S, ∑ ρ' ∈ S, pairIntegral T (ρ : ℂ) (ρ' : ℂ) := by
    rw [hAdef, Finset.sum_image fun _ _ _ _ h => Subtype.ext h]
    exact Finset.sum_congr rfl fun ρ _ => Finset.sum_image fun _ _ _ _ h => Subtype.ext h
  calc ∑ p ∈ u, pairIntegral T (p.1 : ℂ) (p.2 : ℂ)
      ≤ ∑ p ∈ S ×ˢ S, pairIntegral T (p.1 : ℂ) (p.2 : ℂ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => pairIntegral_nonneg hT _ _
    _ = ∑ ρ ∈ A, ∑ ρ' ∈ A, pairIntegral T ρ ρ' := by rw [Finset.sum_product, hconv]
    _ = ∫ t in (0 : ℝ)..T, (∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) *
          ∑ ρ' ∈ A, (zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2) :=
        sum_sum_pairIntegral_eq _ _ _
    _ ≤ ∫ t in (0 : ℝ)..T, C * Real.log (T + 3) * (C * Real.log (T + 3)) := by
        refine intervalIntegral.integral_mono_on hT
          (((continuous_poissonSum A).mul (continuous_poissonSum A)).intervalIntegrable 0 T)
          intervalIntegrable_const fun t ht => ?_
        have hnn : (0 : ℝ) ≤ ∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) :=
          Finset.sum_nonneg fun ρ _ => by positivity
        have h2 : ∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
            ≤ C * Real.log (T + 3) := by
          obtain ⟨ht0, htT⟩ := ht
          refine (hC t A hAmem).trans (mul_le_mul_of_nonneg_left ?_ hC0.le)
          rw [abs_of_nonneg ht0]
          exact Real.log_le_log (by linarith) (by linarith)
        exact mul_le_mul h2 h2 hnn (hnn.trans h2)
    _ = C ^ 2 * T * Real.log (T + 3) ^ 2 := by
        rw [intervalIntegral.integral_const]; simp; ring

/-- The pair majorant is summable over pairs of zeros. -/
private lemma summable_pairIntegral {T : ℝ} (hT : 0 ≤ T) :
    Summable fun p : allZeros × allZeros => pairIntegral T (p.1 : ℂ) (p.2 : ℂ) := by
  obtain ⟨C, -, hC⟩ := exists_sum_pairIntegral_le
  exact summable_of_sum_le (fun p => pairIntegral_nonneg hT _ _) (hC T hT)

/-! ### Expanding the square -/

/-- A power of a positive real base commutes with conjugation of the exponent. -/
private lemma conj_ofReal_cpow' {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ z) = (x : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : ((x : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact fun h => Real.pi_ne_zero h.symm
  have h := Complex.conj_cpow ((x : ℝ) : ℂ) ((starRingEnd ℂ) z) harg
  simp only [Complex.conj_ofReal, Complex.conj_conj] at h
  exact h.symm

/-- **The product of a term of `ℓ (x, t)` with the conjugate of another.** The two factors
`x^{-it}` cancel, leaving `x^{ρ + conj ρ' - 1}` times the pair kernel. -/
private lemma zeroSideTerm_mul_conj {x : ℝ} (hx : 0 < x) (t : ℝ) (ρ ρ' : ℂ) :
    (zeroMultiplicity ρ : ℂ) * (2 * (x : ℂ) ^ (ρ - 1 / 2 - (t : ℂ) * I)
        / (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2)) *
      (starRingEnd ℂ) ((zeroMultiplicity ρ' : ℂ) * (2 * (x : ℂ) ^ (ρ' - 1 / 2 - (t : ℂ) * I)
        / (1 - (ρ' - (1 / 2 + (t : ℂ) * I)) ^ 2)))
      = 4 * ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
        (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1) * pairKernel ρ ρ' t := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hconj : (starRingEnd ℂ) (ρ' - 1 / 2 - (t : ℂ) * I)
      = (starRingEnd ℂ) ρ' - 1 / 2 + (t : ℂ) * I := by
    simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hadd : ρ - 1 / 2 - (t : ℂ) * I + ((starRingEnd ℂ) ρ' - 1 / 2 + (t : ℂ) * I)
      = ρ + (starRingEnd ℂ) ρ' - 1 := by ring
  rw [pairKernel, ← conj_denom, mul_inv, ← hadd, Complex.cpow_add _ _ hxne, map_mul, map_div₀,
    map_mul, map_ofNat, Complex.conj_natCast, conj_ofReal_cpow' hx, hconj]
  push_cast
  ring

/-- **The square of the modulus of the sum over zeros, expanded over pairs.** For `x ≥ 1` the
series defining `ℓ (x, t)` converges absolutely, so the product of the series with its conjugate is
the sum over ordered pairs of zeros. -/
private lemma norm_zeroSide_sq_eq_tsum {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    ((‖zeroSide x t‖ ^ 2 : ℝ) : ℂ) = ∑' p : allZeros × allZeros,
      4 * ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
        (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
        pairKernel (p.1 : ℂ) (p.2 : ℂ) t := by
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨C, -, hC⟩ := exists_summable_norm_zeroSideTerm_tsum_le
  have hsn : Summable fun ρ : allZeros => ‖(zeroMultiplicity (ρ : ℂ) : ℂ) *
      (2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
        / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2))‖ :=
    ((hC x t hx).1).congr fun ρ => by simp
  have hsc : Summable fun ρ : allZeros => ‖(starRingEnd ℂ) ((zeroMultiplicity (ρ : ℂ) : ℂ) *
      (2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
        / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2)))‖ :=
    hsn.congr fun ρ => (Complex.norm_conj _).symm
  have h1 : ((‖zeroSide x t‖ ^ 2 : ℝ) : ℂ) = zeroSide x t * (starRingEnd ℂ) (zeroSide x t) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  have hstar : ∀ f : allZeros → ℂ,
      (starRingEnd ℂ) (∑' ρ : allZeros, f ρ) = ∑' ρ : allZeros, (starRingEnd ℂ) (f ρ) :=
    fun _ => tsum_star
  rw [h1, zeroSide, hstar, tsum_mul_tsum_of_summable_norm hsn hsc]
  exact tsum_congr fun p => zeroSideTerm_mul_conj hx0 t _ _

/-! ### The pair expansion of the mean square -/

/-- The modulus of `x^{ρ + conj ρ' - 1}` is at most `x`: the exponent has real part
`(re ρ - 1/2) + (re ρ' - 1/2) < 1`, and `x ≥ 1`. This uses *only* that the two zeros lie in the
open critical strip. -/
private lemma norm_cpow_pair_le {x : ℝ} (hx : 1 ≤ x) {ρ ρ' : ℂ} (h1 : ρ.re < 1)
    (h1' : ρ'.re < 1) : ‖(x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1)‖ ≤ x := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0,
    show (ρ + (starRingEnd ℂ) ρ' - 1).re = ρ.re + ρ'.re - 1 by simp]
  calc x ^ (ρ.re + ρ'.re - 1) ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    _ = x := Real.rpow_one x

/-- The integral over `[0, T]` of the modulus of the pair kernel is at most `16/9` times the
integral of the product of the two Poisson weights. -/
private lemma integral_norm_pairKernel_le {T : ℝ} (hT : 0 ≤ T) {ρ ρ' : ℂ} (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (h0' : 0 < ρ'.re) (h1' : ρ'.re < 1) :
    ∫ t in (0 : ℝ)..T, ‖pairKernel ρ ρ' t‖
      ≤ 16 / 9 * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) * (1 / (1 + (t - ρ'.im) ^ 2)) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hT
    ((continuous_pairKernel h0 h1 h0' h1').norm.intervalIntegrable 0 T) ?_ fun t _ => ?_
  · refine Continuous.intervalIntegrable (Continuous.mul continuous_const ?_) 0 T
    exact Continuous.mul (continuous_const.div (by fun_prop) fun t => by positivity)
      (continuous_const.div (by fun_prop) fun t => by positivity)
  · have h := norm_pairKernel_le h0 h1 h0' h1' t
    calc ‖pairKernel ρ ρ' t‖ ≤ 16 / 9 * (1 / (1 + (t - ρ.im) ^ 2)) *
          (1 / (1 + (t - ρ'.im) ^ 2)) := h
      _ = 16 / 9 * (1 / (1 + (t - ρ.im) ^ 2) * (1 / (1 + (t - ρ'.im) ^ 2))) := by ring

/-- **The pair term of the expansion of the mean square is dominated by the majorant.** The factor
`x` is the trivial strip bound `x^{δ + δ'} ≤ x`. -/
private lemma norm_pairTerm_le {x T : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T) {ρ ρ' : ℂ}
    (hρ : ρ ∈ allZeros) (hρ' : ρ' ∈ allZeros) :
    ‖((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
        (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1) * ∫ t in (0 : ℝ)..T, pairKernel ρ ρ' t‖
      ≤ 16 / 9 * x * pairIntegral T ρ ρ' := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hm : (0 : ℝ) ≤ (zeroMultiplicity ρ : ℝ) * (zeroMultiplicity ρ' : ℝ) := by positivity
  have hk := (intervalIntegral.norm_integral_le_integral_norm hT).trans
    (integral_norm_pairKernel_le hT hρ.2.1 hρ.2.2 hρ'.2.1 hρ'.2.2)
  have hknn : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) *
      (1 / (1 + (t - ρ'.im) ^ 2)) :=
    intervalIntegral.integral_nonneg hT fun t _ => by positivity
  calc ‖((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
        (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1) * ∫ t in (0 : ℝ)..T, pairKernel ρ ρ' t‖
      = (zeroMultiplicity ρ : ℝ) * (zeroMultiplicity ρ' : ℝ) *
          ‖(x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1)‖ *
          ‖∫ t in (0 : ℝ)..T, pairKernel ρ ρ' t‖ := by
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        push_cast
        ring
    _ ≤ (zeroMultiplicity ρ : ℝ) * (zeroMultiplicity ρ' : ℝ) * x *
          (16 / 9 * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) *
            (1 / (1 + (t - ρ'.im) ^ 2))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (norm_cpow_pair_le hx hρ.2.2 hρ'.2.2) hm) hk
          (norm_nonneg _) (by positivity)
    _ = 16 / 9 * x * pairIntegral T ρ ρ' := by rw [pairIntegral_eq]; ring

/-- The integral over `[0, T]` of the modulus of the summand of the expansion. -/
private lemma integral_norm_pairSummand_le {x T : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T)
    {ρ ρ' : ℂ} (hρ : ρ ∈ allZeros) (hρ' : ρ' ∈ allZeros) :
    ∫ t in (0 : ℝ)..T, ‖4 * ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
        (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1) * pairKernel ρ ρ' t‖
      ≤ 64 / 9 * x * pairIntegral T ρ ρ' := by
  have hm : (0 : ℝ) ≤ (zeroMultiplicity ρ : ℝ) * (zeroMultiplicity ρ' : ℝ) := by positivity
  have hknn : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) *
      (1 / (1 + (t - ρ'.im) ^ 2)) :=
    intervalIntegral.integral_nonneg hT fun t _ => by positivity
  have hsplit : ∫ t in (0 : ℝ)..T, ‖4 * ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
        (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1) * pairKernel ρ ρ' t‖
      = ‖4 * ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
          (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1)‖ *
        ∫ t in (0 : ℝ)..T, ‖pairKernel ρ ρ' t‖ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => norm_mul _ _
  rw [hsplit]
  calc ‖4 * ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
        (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1)‖ * ∫ t in (0 : ℝ)..T, ‖pairKernel ρ ρ' t‖
      = 4 * ((zeroMultiplicity ρ : ℝ) * (zeroMultiplicity ρ' : ℝ)) *
          ‖(x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1)‖ *
          ∫ t in (0 : ℝ)..T, ‖pairKernel ρ ρ' t‖ := by
        rw [norm_mul, norm_mul, Complex.norm_natCast,
          show ‖(4 : ℂ)‖ = (4 : ℝ) from by norm_num]
        push_cast
        ring
    _ ≤ 4 * ((zeroMultiplicity ρ : ℝ) * (zeroMultiplicity ρ' : ℝ)) * x *
          (16 / 9 * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) *
            (1 / (1 + (t - ρ'.im) ^ 2))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (norm_cpow_pair_le hx hρ.2.2 hρ'.2.2)
          (by positivity))
          (integral_norm_pairKernel_le hT hρ.2.1 hρ.2.2 hρ'.2.1 hρ'.2.2)
          (intervalIntegral.integral_nonneg hT fun t _ => norm_nonneg _) (by positivity)
    _ = 64 / 9 * x * pairIntegral T ρ ρ' := by rw [pairIntegral_eq]; ring

/-- **The mean square expanded over pairs of zeros.** For `x ≥ 1` and `T ≥ 3` the family indexed
by ordered pairs of non-trivial zeros, with term
`m_ρ m_ρ' x^{ρ + conj ρ' - 1} ∫₀^T κ_{ρ,ρ'} (t) dt`, is absolutely summable and
`L (x, T) = 4 ∑_{ρ, ρ' ∈ 𝒩*} m_ρ m_ρ' x^{ρ + conj ρ' - 1} ∫₀^T κ_{ρ,ρ'} (t) dt`.

For fixed `t` the factors `x^{-it}` of the term at `ρ` and of the conjugate of the term at `ρ'`
cancel, leaving `4 m_ρ m_ρ' x^{ρ + conj ρ' - 1} κ_{ρ,ρ'} (t)`. Absolute summability comes from the
trivial bound `|x^{ρ + conj ρ' - 1}| ≤ x` and the fact that the double sum of the majorant is the
integral over `[0, T]` of the square of the Poisson-weighted count, which is bounded there; Fubini
then integrates the expansion term by term. -/
@[zz_tag "lem_L_pair_expansion"]
theorem zeroSideMeanSquare_eq_tsum_pairKernel_integral {x T : ℝ} (hx : 1 ≤ x) (hT : 3 ≤ T) :
    Summable (fun p : allZeros × allZeros =>
        ‖((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
            (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
            ∫ t in (0 : ℝ)..T, pairKernel (p.1 : ℂ) (p.2 : ℂ) t‖) ∧
      (zeroSideMeanSquare x T : ℂ) = 4 * ∑' p : allZeros × allZeros,
        ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
          (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
          ∫ t in (0 : ℝ)..T, pairKernel (p.1 : ℂ) (p.2 : ℂ) t := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hmaj := (summable_pairIntegral hT0).mul_left (64 / 9 * x)
  refine ⟨Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_pairTerm_le hx hT0 p.1.2 p.2.2)
      ((summable_pairIntegral hT0).mul_left (16 / 9 * x)), ?_⟩
  have hint : ∀ p : allZeros × allZeros, Integrable
      (fun t : ℝ => 4 * ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
        (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) * pairKernel (p.1 : ℂ) (p.2 : ℂ) t)
      (volume.restrict (Set.Ioc (0 : ℝ) T)) := fun p =>
    Continuous.integrableOn_Ioc (continuous_const.mul
      (continuous_pairKernel p.1.2.2.1 p.1.2.2.2 p.2.2.2.1 p.2.2.2.2))
  have hnorm : ∀ p : allZeros × allZeros,
      ∫ t, ‖4 * ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
          (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
          pairKernel (p.1 : ℂ) (p.2 : ℂ) t‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) T))
        = ∫ t in (0 : ℝ)..T, ‖4 * ((zeroMultiplicity (p.1 : ℂ) *
            zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
            (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
            pairKernel (p.1 : ℂ) (p.2 : ℂ) t‖ := fun p =>
    (intervalIntegral.integral_of_le hT0).symm
  have hsummable : Summable fun p : allZeros × allZeros =>
      ∫ t, ‖4 * ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
        (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
        pairKernel (p.1 : ℂ) (p.2 : ℂ) t‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) T)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmaj
    · rw [hnorm p]
      exact intervalIntegral.integral_nonneg hT0 fun t _ => norm_nonneg _
    · rw [hnorm p]
      exact integral_norm_pairSummand_le hx hT0 p.1.2 p.2.2
  have heq := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsummable
  have hterm : ∀ p : allZeros × allZeros,
      ∫ t, 4 * ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
          (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
          pairKernel (p.1 : ℂ) (p.2 : ℂ) t ∂(volume.restrict (Set.Ioc (0 : ℝ) T))
        = 4 * (((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
            (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
            ∫ t in (0 : ℝ)..T, pairKernel (p.1 : ℂ) (p.2 : ℂ) t) := by
    intro p
    rw [← intervalIntegral.integral_of_le hT0, intervalIntegral.integral_const_mul]
    ring
  have hRHS : ∫ t, (∑' p : allZeros × allZeros,
      4 * ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
        (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
        pairKernel (p.1 : ℂ) (p.2 : ℂ) t) ∂(volume.restrict (Set.Ioc (0 : ℝ) T))
      = (zeroSideMeanSquare x T : ℂ) := by
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t => (norm_zeroSide_sq_eq_tsum hx t).symm),
      ← intervalIntegral.integral_of_le hT0, intervalIntegral.integral_ofReal,
      zeroSideMeanSquare]
  rw [← hRHS, ← heq, tsum_congr hterm, tsum_mul_left]

/-! ### Elementary logarithm bookkeeping -/

/-- `log T ≥ 1` for `T ≥ 3`. -/
private lemma one_le_log {T : ℝ} (hT : 3 ≤ T) : (1 : ℝ) ≤ Real.log T := by
  have h : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
  exact h.le.trans (Real.log_le_log (by norm_num) hT)

/-- `log (T + 3) ≤ 2 log T` for `T ≥ 3`: the argument is at most `2T`, and `log 2 ≤ log T`. -/
private lemma log_add_three_le {T : ℝ} (hT : 3 ≤ T) : Real.log (T + 3) ≤ 2 * Real.log T := by
  have h1 := one_le_log hT
  have h2 : Real.log (T + 3) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul (by norm_num) (by linarith)] at h2
  linarith [Real.log_two_lt_d9]

/-! ### The pairs with a zero outside the range -/

/-- Pulling the multiplicity out of the integral of a single Poisson weight. -/
private lemma integral_poissonWeight (T : ℝ) (ρ : ℂ) :
    ∫ t in (0 : ℝ)..T, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
      = (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) := by
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun t _ => by ring

/-- The integral of a finite Poisson sum, term by term. -/
private lemma integral_poissonSum (T : ℝ) (A : Finset ℂ) :
    ∫ t in (0 : ℝ)..T, ∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
      = ∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) := by
  rw [intervalIntegral.integral_finsetSum (s := A) (f := fun (ρ : ℂ) (t : ℝ) =>
      (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2))
    fun ρ _ => (continuous_const.div (by fun_prop) fun t => by positivity).intervalIntegrable 0 T]
  exact Finset.sum_congr rfl fun ρ _ => integral_poissonWeight T ρ

/-- **The majorant of a finite set of pairs whose first zero has ordinate outside `(0, T]`.**
The second bracket is `O(log T)` on the range by the Poisson-weighted count, and the integral of
the first is `O(log² T)` by the one-sided integral estimate. -/
private lemma sum_pairIntegral_fst_outside_le {T : ℝ} (hT : 3 ≤ T) {C C' : ℝ} (hC0 : 0 < C)
    (hC : ∀ (t : ℝ) (A : Finset ℂ), (∀ ρ ∈ A, ρ ∈ allZeros) →
      ∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) ≤ C * Real.log (|t| + 3))
    (hC' : ∀ A : Finset ℂ, (∀ ρ ∈ A, ρ ∈ allZeros ∧ ρ.im ∉ Set.Ioc (0 : ℝ) T) →
      ∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) * ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2)
        ≤ C' * Real.log T ^ 2)
    (u : Finset (allZeros × allZeros))
    (hu : ∀ p ∈ u, (p.1 : ℂ).im ∉ Set.Ioc (0 : ℝ) T) :
    ∑ p ∈ u, pairIntegral T (p.1 : ℂ) (p.2 : ℂ)
      ≤ C * Real.log (T + 3) * (C' * Real.log T ^ 2) := by
  classical
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set A : Finset ℂ := (u.image Prod.fst).image Subtype.val with hAdef
  set B : Finset ℂ := (u.image Prod.snd).image Subtype.val with hBdef
  have hAmem : ∀ ρ ∈ A, ρ ∈ allZeros ∧ ρ.im ∉ Set.Ioc (0 : ℝ) T := by
    intro ρ hρ
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hρ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hσ
    exact ⟨p.1.2, hu p hp⟩
  have hBmem : ∀ ρ ∈ B, ρ ∈ allZeros := by
    intro ρ hρ
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hρ
    exact σ.2
  have hsub : u ⊆ u.image Prod.fst ×ˢ u.image Prod.snd := fun p hp => by
    rw [Finset.mem_product]
    exact ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hconv : ∑ ρ ∈ A, ∑ ρ' ∈ B, pairIntegral T ρ ρ'
      = ∑ ρ ∈ u.image Prod.fst, ∑ ρ' ∈ u.image Prod.snd,
          pairIntegral T (ρ : ℂ) (ρ' : ℂ) := by
    rw [hAdef, Finset.sum_image fun _ _ _ _ h => Subtype.ext h]
    exact Finset.sum_congr rfl fun ρ _ => by
      rw [hBdef, Finset.sum_image fun _ _ _ _ h => Subtype.ext h]
  calc ∑ p ∈ u, pairIntegral T (p.1 : ℂ) (p.2 : ℂ)
      ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd, pairIntegral T (p.1 : ℂ) (p.2 : ℂ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => pairIntegral_nonneg hT0 _ _
    _ = ∑ ρ ∈ A, ∑ ρ' ∈ B, pairIntegral T ρ ρ' := by rw [Finset.sum_product, hconv]
    _ = ∫ t in (0 : ℝ)..T, (∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) *
          ∑ ρ' ∈ B, (zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2) :=
        sum_sum_pairIntegral_eq _ _ _
    _ ≤ ∫ t in (0 : ℝ)..T, (∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) *
          (C * Real.log (T + 3)) := by
        refine intervalIntegral.integral_mono_on hT0
          (((continuous_poissonSum A).mul (continuous_poissonSum B)).intervalIntegrable 0 T)
          (((continuous_poissonSum A).mul continuous_const).intervalIntegrable 0 T)
          fun t ht => ?_
        obtain ⟨ht0, htT⟩ := ht
        refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun ρ _ => by positivity)
        refine (hC t B hBmem).trans (mul_le_mul_of_nonneg_left ?_ hC0.le)
        rw [abs_of_nonneg ht0]
        exact Real.log_le_log (by linarith) (by linarith)
    _ = C * Real.log (T + 3) * ∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) *
          ∫ t in (0 : ℝ)..T, 1 / (1 + (t - ρ.im) ^ 2) := by
        rw [intervalIntegral.integral_mul_const, integral_poissonSum]
        ring
    _ ≤ C * Real.log (T + 3) * (C' * Real.log T ^ 2) :=
        mul_le_mul_of_nonneg_left (hC' A hAmem)
          (mul_nonneg hC0.le (Real.log_nonneg (by linarith)))

/-- **The majorant of a finite set of pairs with at least one zero outside the range.** By
symmetry it is twice the one-sided bound. -/
private lemma exists_sum_pairIntegral_outside_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T → ∀ u : Finset (allZeros × allZeros),
      (∀ p ∈ u, (p.1 : ℂ).im ∉ Set.Ioc (0 : ℝ) T ∨ (p.2 : ℂ).im ∉ Set.Ioc (0 : ℝ) T) →
      ∑ p ∈ u, pairIntegral T (p.1 : ℂ) (p.2 : ℂ)
        ≤ C * Real.log (T + 3) * Real.log T ^ 2 := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_finset_poissonWeight_le
  obtain ⟨C', hC'0, hC'⟩ := exists_finset_poissonIntegral_outside_le
  refine ⟨2 * (C * C'), by positivity, fun T hT u hu => ?_⟩
  set v : Finset (allZeros × allZeros) := u.filter fun p => (p.1 : ℂ).im ∉ Set.Ioc (0 : ℝ) T
    with hvdef
  set w : Finset (allZeros × allZeros) := u.filter fun p => ¬ (p.1 : ℂ).im ∉ Set.Ioc (0 : ℝ) T
    with hwdef
  have h1 := sum_pairIntegral_fst_outside_le hT hC0 hC (hC' T hT) v fun p hp =>
    (Finset.mem_filter.1 hp).2
  have hswap : ∀ p ∈ w.image Prod.swap, (p.1 : ℂ).im ∉ Set.Ioc (0 : ℝ) T := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hqu, hq1⟩ := Finset.mem_filter.1 hq
    exact (hu q hqu).resolve_left hq1
  have h2 := sum_pairIntegral_fst_outside_le hT hC0 hC (hC' T hT) (w.image Prod.swap) hswap
  have hw : ∑ p ∈ w.image Prod.swap, pairIntegral T (p.1 : ℂ) (p.2 : ℂ)
      = ∑ p ∈ w, pairIntegral T (p.1 : ℂ) (p.2 : ℂ) := by
    rw [Finset.sum_image fun _ _ _ _ h => Prod.swap_injective h]
    exact Finset.sum_congr rfl fun p _ => (pairIntegral_comm T _ _).symm
  rw [hw] at h2
  have hsplit : ∑ p ∈ v, pairIntegral T (p.1 : ℂ) (p.2 : ℂ)
      + ∑ p ∈ w, pairIntegral T (p.1 : ℂ) (p.2 : ℂ)
      = ∑ p ∈ u, pairIntegral T (p.1 : ℂ) (p.2 : ℂ) := by
    rw [hvdef, hwdef]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [← hsplit]
  nlinarith [h1, h2]

/-! ### The zeros up to a height, as finite sets -/

/-- The zeros of `𝒩 (T)`, seen inside the subtype of all zeros, form a finite set. -/
private lemma nontrivialZeros_preimage_finite (T : ℝ) :
    (Subtype.val ⁻¹' nontrivialZeros T : Set allZeros).Finite :=
  Set.Finite.preimage Subtype.val_injective.injOn (nontrivialZeros_finite T)

/-- `𝒩 (T)` as a `Finset` of the subtype `𝒩*`. -/
private noncomputable def zerosUpTo (T : ℝ) : Finset allZeros :=
  (nontrivialZeros_preimage_finite T).toFinset

/-- `𝒩 (T)` as a `Finset` of `ℂ`. -/
private noncomputable def zerosUpToC (T : ℝ) : Finset ℂ := (nontrivialZeros_finite T).toFinset

private lemma mem_zerosUpTo {T : ℝ} {ρ : allZeros} :
    ρ ∈ zerosUpTo T ↔ (ρ : ℂ) ∈ nontrivialZeros T := by
  simp [zerosUpTo]

private lemma mem_zerosUpToC {T : ℝ} {ρ : ℂ} : ρ ∈ zerosUpToC T ↔ ρ ∈ nontrivialZeros T := by
  simp [zerosUpToC]

private lemma zerosUpToC_eq_image (T : ℝ) :
    zerosUpToC T = (zerosUpTo T).image Subtype.val := by
  ext ρ
  simp only [mem_zerosUpToC, Finset.mem_image, mem_zerosUpTo]
  refine ⟨fun hρ => ⟨⟨ρ, nontrivialZeros_subset_allZeros T hρ⟩, hρ, rfl⟩, ?_⟩
  rintro ⟨σ, hσ, rfl⟩
  exact hσ

private lemma finsum_nontrivialZeros_eq {M : Type*} [AddCommMonoid M] (T : ℝ) (g : ℂ → M) :
    ∑ᶠ ρ ∈ nontrivialZeros T, g ρ = ∑ ρ ∈ zerosUpToC T, g ρ :=
  finsum_mem_eq_finite_toFinset_sum g (nontrivialZeros_finite T)

private lemma sum_zerosUpToC {M : Type*} [AddCommMonoid M] (T : ℝ) (h : ℂ → M) :
    ∑ ρ ∈ zerosUpToC T, h ρ = ∑ ρ ∈ zerosUpTo T, h (ρ : ℂ) := by
  rw [zerosUpToC_eq_image]
  exact Finset.sum_image fun _ _ _ _ hh => Subtype.ext hh

private lemma sum_product_zerosUpTo {M : Type*} [AddCommMonoid M] (T : ℝ) (g : ℂ → ℂ → M) :
    ∑ p ∈ zerosUpTo T ×ˢ zerosUpTo T, g (p.1 : ℂ) (p.2 : ℂ)
      = ∑ ρ ∈ zerosUpToC T, ∑ ρ' ∈ zerosUpToC T, g ρ ρ' := by
  rw [Finset.sum_product, sum_zerosUpToC]
  exact Finset.sum_congr rfl fun ρ _ => (sum_zerosUpToC T fun ρ' => g (ρ : ℂ) ρ').symm

/-- For a zero of `𝒩*`, membership in `𝒩 (T)` is exactly a condition on the ordinate. -/
private lemma mem_nontrivialZeros_iff {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ allZeros) :
    ρ ∈ nontrivialZeros T ↔ ρ.im ∈ Set.Ioc (0 : ℝ) T :=
  ⟨fun h => ⟨h.2.2.2.1, h.2.2.2.2⟩, fun h => ⟨hρ.1, hρ.2.1, hρ.2.2, h.1, h.2⟩⟩

/-! ### Extending the range of integration -/

/-- The product of two Poisson weights is integrable on the line: the second factor is bounded. -/
private lemma integrable_poissonProd (γ γ' : ℝ) :
    Integrable fun t : ℝ => 1 / (1 + (t - γ) ^ 2) * (1 / (1 + (t - γ') ^ 2)) := by
  refine Integrable.mono' (integrable_poisson γ)
    ((continuous_poisson γ).mul (continuous_poisson γ')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hb : 1 / (1 + (t - γ') ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (t - γ')]
  rw [Real.norm_of_nonneg (by positivity)]
  calc 1 / (1 + (t - γ) ^ 2) * (1 / (1 + (t - γ') ^ 2))
      ≤ 1 / (1 + (t - γ) ^ 2) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 / (1 + (t - γ) ^ 2) := by ring

private lemma integrable_poissonPair (ρ ρ' : ℂ) :
    Integrable fun t : ℝ => (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) *
      ((zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2)) :=
  ((integrable_poissonProd ρ.im ρ'.im).const_mul
    ((zeroMultiplicity ρ : ℝ) * (zeroMultiplicity ρ' : ℝ))).congr
    (Filter.Eventually.of_forall fun t => by ring)

/-- The pair kernel is integrable on the line. -/
theorem integrable_pairKernel {ρ ρ' : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (h0' : 0 < ρ'.re)
    (h1' : ρ'.re < 1) : Integrable (pairKernel ρ ρ') := by
  refine Integrable.mono' ((integrable_poisson ρ.im).const_mul (16 / 9))
    (continuous_pairKernel h0 h1 h0' h1').aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hb : 1 / (1 + (t - ρ'.im) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (t - ρ'.im)]
  calc ‖pairKernel ρ ρ' t‖
      ≤ 16 / 9 * (1 / (1 + (t - ρ.im) ^ 2)) * (1 / (1 + (t - ρ'.im) ^ 2)) :=
        norm_pairKernel_le h0 h1 h0' h1' t
    _ ≤ 16 / 9 * (1 / (1 + (t - ρ.im) ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 16 / 9 * (1 / (1 + (t - ρ.im) ^ 2)) := by ring

/-- The integral of the product of the two Poisson weights over the complement of the range: the
majorant of the error made by integrating the pair kernel over the whole line. -/
private noncomputable def pairComplIntegral (T : ℝ) (ρ ρ' : ℂ) : ℝ :=
  ∫ t in (Set.Icc (0 : ℝ) T)ᶜ, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) *
    ((zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2))

private lemma pairComplIntegral_nonneg (T : ℝ) (ρ ρ' : ℂ) : 0 ≤ pairComplIntegral T ρ ρ' :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc.compl fun t _ => by positivity

private lemma sum_sum_pairComplIntegral_eq (T : ℝ) (A B : Finset ℂ) :
    ∑ ρ ∈ A, ∑ ρ' ∈ B, pairComplIntegral T ρ ρ'
      = ∫ t in (Set.Icc (0 : ℝ) T)ᶜ,
          (∑ ρ ∈ A, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) *
            ∑ ρ' ∈ B, (zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2) := by
  have h1 : ∀ ρ : ℂ, ∑ ρ' ∈ B, pairComplIntegral T ρ ρ'
      = ∫ t in (Set.Icc (0 : ℝ) T)ᶜ, ∑ ρ' ∈ B,
          (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) *
            ((zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2)) := fun ρ =>
    (MeasureTheory.integral_finsetSum B fun ρ' _ => (integrable_poissonPair ρ ρ').restrict).symm
  rw [Finset.sum_congr rfl fun ρ _ => h1 ρ,
    ← MeasureTheory.integral_finsetSum A fun ρ _ =>
      MeasureTheory.integrable_finsetSum B fun ρ' _ => (integrable_poissonPair ρ ρ').restrict]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun t => (Finset.sum_mul_sum _ _ _ _).symm)

/-- `(1 + d)^{-2} ≤ (1 + t²)^{-1} + (1 + (t - T)²)^{-1}` for `d = min {|t|, |t - T|}`: the minimum
is attained at one of the two, and `(1 + d)² ≥ 1 + d²`. -/
private lemma inv_one_add_min_sq_le (t T : ℝ) :
    1 / (1 + min |t| |t - T|) ^ 2 ≤ (1 + t ^ 2)⁻¹ + (1 + (t - T) ^ 2)⁻¹ := by
  have h0 : (0 : ℝ) ≤ min |t| |t - T| := le_min (abs_nonneg t) (abs_nonneg _)
  have hkey : 1 / (1 + min |t| |t - T|) ^ 2 ≤ 1 / (1 + min |t| |t - T| ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hA : (0 : ℝ) < 1 / (1 + t ^ 2) := by positivity
  have hB : (0 : ℝ) < 1 / (1 + (t - T) ^ 2) := by positivity
  rw [inv_eq_one_div, inv_eq_one_div]
  rcases le_total |t| |t - T| with h | h
  · rw [min_eq_left h] at hkey ⊢
    rw [sq_abs] at hkey
    linarith
  · rw [min_eq_right h] at hkey ⊢
    rw [sq_abs] at hkey
    linarith

private lemma integral_inv_one_add_sub_sq (γ : ℝ) : ∫ t : ℝ, (1 + (t - γ) ^ 2)⁻¹ = Real.pi := by
  have h : ∫ t : ℝ, (1 + (t + -γ) ^ 2)⁻¹ = ∫ t : ℝ, (1 + t ^ 2)⁻¹ :=
    integral_add_right_eq_self (fun t : ℝ => (1 + t ^ 2)⁻¹) (-γ)
  simp only [← sub_eq_add_neg] at h
  rw [h]
  exact integral_univ_inv_one_add_sq

/-- **The total error made by extending the range of integration.** For the pairs of `𝒩 (T)` the
Poisson-weighted count seen from outside the range is `O(log T / (1 + d))`, and the integral of
`(1 + d)^{-2}` over the complement of the range is `O(1)`. -/
private lemma exists_sum_pairComplIntegral_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
      ∑ ρ ∈ zerosUpToC T, ∑ ρ' ∈ zerosUpToC T, pairComplIntegral T ρ ρ'
        ≤ C * Real.log T ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_finsum_poissonWeight_nontrivialZeros_le
  refine ⟨2 * Real.pi * C ^ 2, by positivity, fun T hT => ?_⟩
  have hmaj : Integrable fun t : ℝ =>
      (C * Real.log T) ^ 2 * ((1 + t ^ 2)⁻¹ + (1 + (t - T) ^ 2)⁻¹) :=
    Integrable.const_mul (integrable_inv_one_add_sq.add
      (by simpa [one_div] using integrable_poisson T)) _
  have hprod : Integrable fun t : ℝ =>
      (∑ ρ ∈ zerosUpToC T, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) *
        ∑ ρ' ∈ zerosUpToC T, (zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2) :=
    (MeasureTheory.integrable_finsetSum (zerosUpToC T) fun ρ _ =>
      MeasureTheory.integrable_finsetSum (zerosUpToC T) fun ρ' _ =>
        integrable_poissonPair ρ ρ').congr
      (Filter.Eventually.of_forall fun t => (Finset.sum_mul_sum _ _ _ _).symm)
  rw [sum_sum_pairComplIntegral_eq]
  calc ∫ t in (Set.Icc (0 : ℝ) T)ᶜ,
        (∑ ρ ∈ zerosUpToC T, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) *
          ∑ ρ' ∈ zerosUpToC T, (zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2)
      ≤ ∫ t in (Set.Icc (0 : ℝ) T)ᶜ,
          (C * Real.log T) ^ 2 * ((1 + t ^ 2)⁻¹ + (1 + (t - T) ^ 2)⁻¹) := by
        refine MeasureTheory.setIntegral_mono_on hprod.integrableOn hmaj.integrableOn
          measurableSet_Icc.compl fun t ht => ?_
        have hb : ∑ ρ ∈ zerosUpToC T, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)
            ≤ C * Real.log T / (1 + min |t| |t - T|) := by
          rw [← finsum_nontrivialZeros_eq]
          exact hC T t hT ht
        have hnn : (0 : ℝ) ≤ ∑ ρ ∈ zerosUpToC T, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2) :=
          Finset.sum_nonneg fun ρ _ => by positivity
        have hd : (0 : ℝ) ≤ min |t| |t - T| := le_min (abs_nonneg t) (abs_nonneg _)
        calc (∑ ρ ∈ zerosUpToC T, (zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) *
              ∑ ρ' ∈ zerosUpToC T, (zeroMultiplicity ρ' : ℝ) / (1 + (t - ρ'.im) ^ 2)
            ≤ C * Real.log T / (1 + min |t| |t - T|) *
                (C * Real.log T / (1 + min |t| |t - T|)) := mul_le_mul hb hb hnn (hnn.trans hb)
          _ = (C * Real.log T) ^ 2 * (1 / (1 + min |t| |t - T|) ^ 2) := by
              field_simp
          _ ≤ (C * Real.log T) ^ 2 * ((1 + t ^ 2)⁻¹ + (1 + (t - T) ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left (inv_one_add_min_sq_le t T) (by positivity)
    _ ≤ ∫ t : ℝ, (C * Real.log T) ^ 2 * ((1 + t ^ 2)⁻¹ + (1 + (t - T) ^ 2)⁻¹) :=
        MeasureTheory.setIntegral_le_integral hmaj
          (Filter.Eventually.of_forall fun t => by positivity)
    _ = 2 * Real.pi * C ^ 2 * Real.log T ^ 2 := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add
          integrable_inv_one_add_sq (by simpa [one_div] using integrable_poisson T),
          integral_univ_inv_one_add_sq, integral_inv_one_add_sub_sq]
        ring

/-! ### The truncation lemma -/

/-- The term of the pair expansion of the mean square: the kernel integrated over `[0, T]`. -/
private noncomputable def pairTermTrunc (x T : ℝ) (p : allZeros × allZeros) : ℂ :=
  ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
    (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
    ∫ t in (0 : ℝ)..T, pairKernel (p.1 : ℂ) (p.2 : ℂ) t

/-- The term of the pair expansion of `2π F (x, T)`: the kernel integrated over the whole line. -/
private noncomputable def pairTermFull (x : ℝ) (p : allZeros × allZeros) : ℂ :=
  ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
    (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
    ∫ t : ℝ, pairKernel (p.1 : ℂ) (p.2 : ℂ) t

/-- The pair expansion of the mean square, in the vocabulary of `pairTermTrunc`. -/
private lemma zeroSideMeanSquare_eq' {x T : ℝ} (hx : 1 ≤ x) (hT : 3 ≤ T) :
    Summable (fun p : allZeros × allZeros => ‖pairTermTrunc x T p‖) ∧
      (zeroSideMeanSquare x T : ℂ) = 4 * ∑' p : allZeros × allZeros, pairTermTrunc x T p :=
  zeroSideMeanSquare_eq_tsum_pairKernel_integral hx hT

private lemma norm_pairTermTrunc_le {x T : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T)
    (p : allZeros × allZeros) :
    ‖pairTermTrunc x T p‖ ≤ 16 / 9 * x * pairIntegral T (p.1 : ℂ) (p.2 : ℂ) :=
  norm_pairTerm_le hx hT p.1.2 p.2.2

/-- Pulling the multiplicities out of `pairComplIntegral`. -/
private lemma pairComplIntegral_eq (T : ℝ) (ρ ρ' : ℂ) :
    pairComplIntegral T ρ ρ' = (zeroMultiplicity ρ : ℝ) * (zeroMultiplicity ρ' : ℝ) *
      ∫ t in (Set.Icc (0 : ℝ) T)ᶜ, 1 / (1 + (t - ρ.im) ^ 2) * (1 / (1 + (t - ρ'.im) ^ 2)) := by
  rw [pairComplIntegral, ← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)

/-- The modulus of the pair kernel, integrated over the complement of the range. -/
private lemma setIntegral_norm_pairKernel_le (_T : ℝ) {ρ ρ' : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (h0' : 0 < ρ'.re) (h1' : ρ'.re < 1) :
    ∫ t in (Set.Icc (0 : ℝ) T)ᶜ, ‖pairKernel ρ ρ' t‖
      ≤ 16 / 9 * ∫ t in (Set.Icc (0 : ℝ) T)ᶜ,
          1 / (1 + (t - ρ.im) ^ 2) * (1 / (1 + (t - ρ'.im) ^ 2)) := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_mono_on
    (integrable_pairKernel h0 h1 h0' h1').norm.integrableOn
    ((integrable_poissonProd ρ.im ρ'.im).const_mul _).integrableOn
    measurableSet_Icc.compl fun t _ => ?_
  calc ‖pairKernel ρ ρ' t‖
      ≤ 16 / 9 * (1 / (1 + (t - ρ.im) ^ 2)) * (1 / (1 + (t - ρ'.im) ^ 2)) :=
        norm_pairKernel_le h0 h1 h0' h1' t
    _ = 16 / 9 * (1 / (1 + (t - ρ.im) ^ 2) * (1 / (1 + (t - ρ'.im) ^ 2))) := by ring

/-- Integrating the pair kernel over the whole line rather than over `[0, T]` costs the integral
over the complement of the range. -/
private lemma integral_pairKernel_sub {T : ℝ} (hT : 0 ≤ T) {ρ ρ' : ℂ} (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (h0' : 0 < ρ'.re) (h1' : ρ'.re < 1) :
    (∫ t in (0 : ℝ)..T, pairKernel ρ ρ' t) - ∫ t : ℝ, pairKernel ρ ρ' t
      = -∫ t in (Set.Icc (0 : ℝ) T)ᶜ, pairKernel ρ ρ' t := by
  have h := MeasureTheory.integral_add_compl (μ := volume) (s := Set.Icc (0 : ℝ) T)
    measurableSet_Icc (integrable_pairKernel h0 h1 h0' h1')
  rw [← h, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  ring

/-- **The error of one pair from extending the range of integration.** The factor `x` is again the
trivial strip bound `x^{δ + δ'} ≤ x`. -/
private lemma norm_pairTermTrunc_sub_full_le {x T : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T)
    (p : allZeros × allZeros) :
    ‖pairTermTrunc x T p - pairTermFull x p‖
      ≤ 16 / 9 * x * pairComplIntegral T (p.1 : ℂ) (p.2 : ℂ) := by
  have hm : (0 : ℝ) ≤ (zeroMultiplicity (p.1 : ℂ) : ℝ) * (zeroMultiplicity (p.2 : ℂ) : ℝ) := by
    positivity
  have hnn : (0 : ℝ) ≤ ∫ t in (Set.Icc (0 : ℝ) T)ᶜ,
      1 / (1 + (t - (p.1 : ℂ).im) ^ 2) * (1 / (1 + (t - (p.2 : ℂ).im) ^ 2)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc.compl fun t _ => by positivity
  have hfac : pairTermTrunc x T p - pairTermFull x p
      = -(((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
          (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
          ∫ t in (Set.Icc (0 : ℝ) T)ᶜ, pairKernel (p.1 : ℂ) (p.2 : ℂ) t) := by
    rw [pairTermTrunc, pairTermFull, ← mul_sub,
      integral_pairKernel_sub hT p.1.2.2.1 p.1.2.2.2 p.2.2.2.1 p.2.2.2.2]
    ring
  rw [hfac, norm_neg, norm_mul, norm_mul, Complex.norm_natCast]
  calc ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℝ) *
        ‖(x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1)‖ *
        ‖∫ t in (Set.Icc (0 : ℝ) T)ᶜ, pairKernel (p.1 : ℂ) (p.2 : ℂ) t‖
      ≤ (zeroMultiplicity (p.1 : ℂ) : ℝ) * (zeroMultiplicity (p.2 : ℂ) : ℝ) * x *
          (16 / 9 * ∫ t in (Set.Icc (0 : ℝ) T)ᶜ,
            1 / (1 + (t - (p.1 : ℂ).im) ^ 2) * (1 / (1 + (t - (p.2 : ℂ).im) ^ 2))) := by
        refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
        · rw [Nat.cast_mul]
          exact mul_le_mul_of_nonneg_left
            (norm_cpow_pair_le hx p.1.2.2.2 p.2.2.2.2) hm
        · exact (MeasureTheory.norm_integral_le_integral_norm _).trans
            (setIntegral_norm_pairKernel_le T p.1.2.2.1 p.1.2.2.2 p.2.2.2.1 p.2.2.2.2)
    _ = 16 / 9 * x * pairComplIntegral T (p.1 : ℂ) (p.2 : ℂ) := by
        rw [pairComplIntegral_eq]; ring

/-- **The pair-correlation function through the kernel integral over the line.** The residue
evaluation of the pair kernel turns the weight into `(2/π) ∫_ℝ κ`. -/
private lemma two_pi_pairCorrelation_eq (x T : ℝ) :
    2 * (Real.pi : ℂ) * pairCorrelation x T
      = 4 * ∑ p ∈ zerosUpTo T ×ˢ zerosUpTo T, pairTermFull x p := by
  have hfull : ∀ p : allZeros × allZeros, pairTermFull x p
      = ((zeroMultiplicity (p.1 : ℂ) * zeroMultiplicity (p.2 : ℂ) : ℕ) : ℂ) *
        (x : ℂ) ^ ((p.1 : ℂ) + (starRingEnd ℂ) (p.2 : ℂ) - 1) *
        ∫ t : ℝ, pairKernel (p.1 : ℂ) (p.2 : ℂ) t := fun _ => rfl
  rw [pairCorrelation_eq_reflected, Finset.sum_congr rfl fun p _ => hfull p]
  simp only [finsum_nontrivialZeros_eq]
  rw [sum_product_zerosUpTo T fun ρ ρ' =>
      ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
        (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1) * ∫ t : ℝ, pairKernel ρ ρ' t,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ' hρ' => ?_
  have h := mem_zerosUpToC.1 hρ
  have h' := mem_zerosUpToC.1 hρ'
  rw [integral_pairKernel h.2.1 h.2.2.1 h'.2.1 h'.2.2.1]
  ring

/-- A pair not both of whose zeros lie in `𝒩 (T)` has a zero with ordinate outside `(0, T]`. -/
private lemma not_mem_product_imp {T : ℝ} {p : allZeros × allZeros}
    (hp : p ∉ zerosUpTo T ×ˢ zerosUpTo T) :
    (p.1 : ℂ).im ∉ Set.Ioc (0 : ℝ) T ∨ (p.2 : ℂ).im ∉ Set.Ioc (0 : ℝ) T := by
  rw [Finset.mem_product] at hp
  rcases not_and_or.1 hp with h | h
  · exact Or.inl fun hc => h (mem_zerosUpTo.2 ((mem_nontrivialZeros_iff p.1.2).2 hc))
  · exact Or.inr fun hc => h (mem_zerosUpTo.2 ((mem_nontrivialZeros_iff p.2.2).2 hc))

/-- **The truncation lemma.** There is an absolute constant `C > 0` such that for all `x ≥ 1` and
`T ≥ 3`, `|F (x, T) - L (x, T) / (2π)| ≤ C x log³T`.

The reflected form of `F (x, T)` and the residue evaluation of the pair kernel give
`2π F (x, T) = 4 ∑_{ρ, ρ' ∈ 𝒩 (T)} m_ρ m_ρ' x^{ρ + conj ρ' - 1} ∫_ℝ κ_{ρ,ρ'}`, which differs from
the pair expansion of `L (x, T)` in two ways: the pairs with a zero outside `𝒩 (T)` are absent, and
the remaining ones are integrated over the whole line rather than over `[0, T]`.

In *both* error terms the only bound used on the two zeros is
`|x^{ρ + conj ρ' - 1}| = x^{δ + δ'} ≤ x`, valid because `|δ|, |δ'| < 1/2` for a zero of the open
critical strip and `x ≥ 1`; no zero-free region is used.

The first error is `O(x log³T)` by the Poisson-weighted count on the range together with the
one-sided integral estimate for the zeros outside it; the second is `O(x log²T)` by the count seen
from outside the range, whose square integrates to `O(1)` over the complement of `[0, T]`. -/
@[zz_tag "lem_F_L_truncation"]
theorem exists_norm_pairCorrelation_sub_zeroSideMeanSquare_div_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x T : ℝ, 1 ≤ x → 3 ≤ T →
      ‖pairCorrelation x T - ((zeroSideMeanSquare x T / (2 * Real.pi) : ℝ) : ℂ)‖
        ≤ C * x * Real.log T ^ 3 := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_sum_pairIntegral_outside_le
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_sum_pairComplIntegral_le
  refine ⟨4 * (32 / 9 * C₁ + 16 / 9 * C₂), by positivity, fun x T hx hT => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog1 := one_le_log hT
  obtain ⟨hsum1, hL⟩ := zeroSideMeanSquare_eq' hx hT
  have hsummable : Summable (pairTermTrunc x T) := Summable.of_norm hsum1
  have hsplit := hsummable.sum_add_tsum_compl (s := zerosUpTo T ×ˢ zerosUpTo T)
  have hdecomp : (zeroSideMeanSquare x T : ℂ) - 2 * (Real.pi : ℂ) * pairCorrelation x T
      = 4 * (∑' q : ↥((↑(zerosUpTo T ×ˢ zerosUpTo T) : Set (allZeros × allZeros))ᶜ),
          pairTermTrunc x T (q : allZeros × allZeros))
        + 4 * ∑ p ∈ zerosUpTo T ×ˢ zerosUpTo T,
            (pairTermTrunc x T p - pairTermFull x p) := by
    rw [hL, two_pi_pairCorrelation_eq, ← hsplit, Finset.sum_sub_distrib]
    ring
  have hb1 : ‖∑' q : ↥((↑(zerosUpTo T ×ˢ zerosUpTo T) : Set (allZeros × allZeros))ᶜ),
        pairTermTrunc x T (q : allZeros × allZeros)‖
      ≤ 16 / 9 * x * (C₁ * Real.log (T + 3) * Real.log T ^ 2) := by
    refine (norm_tsum_le_tsum_norm (hsum1.subtype _)).trans ?_
    refine Real.tsum_le_of_sum_le (fun q => norm_nonneg _) fun v => ?_
    calc ∑ q ∈ v, ‖pairTermTrunc x T (q : allZeros × allZeros)‖
        ≤ ∑ q ∈ v, 16 / 9 * x * pairIntegral T
            ((q : allZeros × allZeros).1 : ℂ) ((q : allZeros × allZeros).2 : ℂ) :=
          Finset.sum_le_sum fun q _ => norm_pairTermTrunc_le hx hT0 _
      _ = 16 / 9 * x * ∑ q ∈ v, pairIntegral T
            ((q : allZeros × allZeros).1 : ℂ) ((q : allZeros × allZeros).2 : ℂ) := by
          rw [Finset.mul_sum]
      _ = 16 / 9 * x * ∑ p ∈ v.image Subtype.val,
            pairIntegral T (p.1 : ℂ) (p.2 : ℂ) := by
          rw [Finset.sum_image fun _ _ _ _ h => Subtype.ext h]
      _ ≤ 16 / 9 * x * (C₁ * Real.log (T + 3) * Real.log T ^ 2) := by
          refine mul_le_mul_of_nonneg_left (hC₁ T hT _ fun p hp => ?_) (by positivity)
          obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hp
          exact not_mem_product_imp q.2
  have hb2 : ∑ p ∈ zerosUpTo T ×ˢ zerosUpTo T, ‖pairTermTrunc x T p - pairTermFull x p‖
      ≤ 16 / 9 * x * (C₂ * Real.log T ^ 2) := by
    calc ∑ p ∈ zerosUpTo T ×ˢ zerosUpTo T, ‖pairTermTrunc x T p - pairTermFull x p‖
        ≤ ∑ p ∈ zerosUpTo T ×ˢ zerosUpTo T,
            16 / 9 * x * pairComplIntegral T (p.1 : ℂ) (p.2 : ℂ) :=
          Finset.sum_le_sum fun p _ => norm_pairTermTrunc_sub_full_le hx hT0 p
      _ = 16 / 9 * x * ∑ p ∈ zerosUpTo T ×ˢ zerosUpTo T,
            pairComplIntegral T (p.1 : ℂ) (p.2 : ℂ) := by rw [Finset.mul_sum]
      _ = 16 / 9 * x * ∑ ρ ∈ zerosUpToC T, ∑ ρ' ∈ zerosUpToC T, pairComplIntegral T ρ ρ' := by
          rw [sum_product_zerosUpTo]
      _ ≤ 16 / 9 * x * (C₂ * Real.log T ^ 2) :=
          mul_le_mul_of_nonneg_left (hC₂ T hT) (by positivity)
  have hkey : ‖(zeroSideMeanSquare x T : ℂ) - 2 * (Real.pi : ℂ) * pairCorrelation x T‖
      ≤ 4 * (16 / 9 * x * (C₁ * Real.log (T + 3) * Real.log T ^ 2))
        + 4 * (16 / 9 * x * (C₂ * Real.log T ^ 2)) := by
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = (4 : ℝ) from by norm_num]
    exact add_le_add (mul_le_mul_of_nonneg_left hb1 (by norm_num))
      (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans hb2) (by norm_num))
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have heq : pairCorrelation x T - ((zeroSideMeanSquare x T / (2 * Real.pi) : ℝ) : ℂ)
      = -(((2 * Real.pi : ℝ) : ℂ))⁻¹ *
        ((zeroSideMeanSquare x T : ℂ) - 2 * (Real.pi : ℂ) * pairCorrelation x T) := by
    have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
    push_cast at hne ⊢
    field_simp
    ring
  have hnormpi : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
    simp [Real.pi_nonneg]
  rw [heq, norm_mul, norm_neg, norm_inv, hnormpi]
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have ha : C₁ * Real.log (T + 3) * Real.log T ^ 2 ≤ 2 * C₁ * Real.log T ^ 3 :=
    calc C₁ * Real.log (T + 3) * Real.log T ^ 2
        = C₁ * Real.log T ^ 2 * Real.log (T + 3) := by ring
      _ ≤ C₁ * Real.log T ^ 2 * (2 * Real.log T) :=
          mul_le_mul_of_nonneg_left (log_add_three_le hT) (by positivity)
      _ = 2 * C₁ * Real.log T ^ 3 := by ring
  have hb : C₂ * Real.log T ^ 2 ≤ C₂ * Real.log T ^ 3 := by
    refine mul_le_mul_of_nonneg_left ?_ hC₂0.le
    nlinarith [mul_nonneg (sq_nonneg (Real.log T)) (by linarith : (0 : ℝ) ≤ Real.log T - 1)]
  calc (2 * Real.pi)⁻¹ *
        ‖(zeroSideMeanSquare x T : ℂ) - 2 * (Real.pi : ℂ) * pairCorrelation x T‖
      ≤ 1 * ‖(zeroSideMeanSquare x T : ℂ) - 2 * (Real.pi : ℂ) * pairCorrelation x T‖ :=
        mul_le_mul_of_nonneg_right (by rw [inv_le_one_iff₀]; right; exact h2pi) (norm_nonneg _)
    _ = ‖(zeroSideMeanSquare x T : ℂ) - 2 * (Real.pi : ℂ) * pairCorrelation x T‖ := one_mul _
    _ ≤ 4 * (16 / 9 * x * (C₁ * Real.log (T + 3) * Real.log T ^ 2))
        + 4 * (16 / 9 * x * (C₂ * Real.log T ^ 2)) := hkey
    _ ≤ 4 * (32 / 9 * C₁ + 16 / 9 * C₂) * x * Real.log T ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left ha hx0.le, mul_le_mul_of_nonneg_left hb hx0.le]

end ZetaZeros
