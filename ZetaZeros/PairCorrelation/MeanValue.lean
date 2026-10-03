/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.PairCorrelation.Elementary

/-!
# The mean value theorem for Dirichlet polynomials

The second moment of a Dirichlet polynomial `∑ aₙ n^{-it}` on `[0, T]`: the diagonal contributes
`T ∑ |aₙ|²`, and the off-diagonal is controlled by the multiplicative gaps `|log n - log m|`.

Expanding the square and integrating gives, for `m ≠ n`,
`∫_0^T (n/m)^{it} dt = (n^{iT} m^{-iT} - 1) / (i (log n - log m))`, whose modulus is at most
`2 / |log n - log m|`, and this bound is summed over the off-diagonal pairs.

## Main results

* `ZetaZeros.abs_integral_norm_sq_sub_le_sum_div_abs_log_sub_log`: the mean value theorem with the
  off-diagonal error left as the sum `2 ∑_{m ≠ n} |aₙ| |aₘ| / |log m - log n|`.
* `ZetaZeros.abs_integral_norm_sq_sub_le_sq_sum_sqrt`: the off-diagonal error bounded by
  `2 (∑ √(n + 1) |aₙ|)²`, from the multiplicative gap `|log n - log m| ≥ (min m n + 1)⁻¹`.
* `ZetaZeros.abs_integral_norm_sq_sub_le_tsum_div_abs_log_sub_log`: the first bound for an `ℓ¹`
  coefficient sequence over all `n ≥ 1`.

## Implementation notes

The error term is the off-diagonal sum `2 ∑_{m ≠ n} |aₙ| |aₘ| / |log m - log n|` rather than the
sharp Montgomery--Vaughan error `O(∑ n |aₙ|²)`, which would follow from the weighted Hilbert
inequality `|∑_{r ≠ s} a_r conj a_s / (t_r - t_s)| ≤ C ∑_r |a_r|² / δ_r` applied to the
frequencies `log n`. For the coefficients `aₙ = Λ(n) n^{-1/2} min {n/x, x/n}` the off-diagonal sum
can be estimated directly from the support of `Λ` on prime powers.

The passage from a finitely supported coefficient sequence to an `ℓ¹` sequence over all `n ≥ 1`
is taken along the net of finite subsets of `ℕ`. It needs `Summable (fun n ↦ ‖aₙ‖)`, which makes
the partial sums converge uniformly in `t`, and summability of the off-diagonal double sum,
without which the right-hand side is `0` by the `tsum` convention and the statement is false.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory intervalIntegral

/-- The regularising integral of the off-diagonal expansion: `∫_0^T e^{i c t} dt`, which for
`c = log m - log n` is the integral `∫_0^T (m/n)^{it} dt` produced by one off-diagonal pair. -/
private noncomputable def oscIntegral (c T : ℝ) : ℂ := ∫ t in (0:ℝ)..T, Complex.exp (c * t * I)

/-- A diagonal pair contributes the full length of the interval. -/
private lemma oscIntegral_zero (T : ℝ) : oscIntegral 0 T = (T : ℂ) := by
  simp [oscIntegral]

/-- The off-diagonal cancellation: `|∫_0^T e^{i c t} dt| ≤ 2 / |c|`, since the primitive
`e^{i c t} / (i c)` has modulus `1 / |c|` at both endpoints. -/
private lemma norm_oscIntegral_le (c T : ℝ) (hc : c ≠ 0) : ‖oscIntegral c T‖ ≤ 2 / |c| := by
  have hcI : (c : ℂ) * I ≠ 0 := by simp [Complex.ext_iff, hc]
  have h : oscIntegral c T = ∫ t in (0:ℝ)..T, Complex.exp (((c : ℂ) * I) * t) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring_nf
  rw [h, integral_exp_mul_complex hcI, norm_div, show ‖(c : ℂ) * I‖ = |c| by simp]
  have hnum : ‖Complex.exp ((c : ℂ) * I * T) - Complex.exp ((c : ℂ) * I * 0)‖ ≤ 2 := by
    have h1 : ‖Complex.exp ((c : ℂ) * I * T)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have h2 : ‖Complex.exp ((c : ℂ) * I * 0)‖ = 1 := by simp
    calc ‖Complex.exp ((c : ℂ) * I * T) - Complex.exp ((c : ℂ) * I * 0)‖
        ≤ ‖Complex.exp ((c : ℂ) * I * T)‖ + ‖Complex.exp ((c : ℂ) * I * 0)‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  have hpos : (0:ℝ) < |c| := abs_pos.mpr hc
  gcongr
  simpa using hnum

/-- Expanding `|∑ aₙ e^{-i t Lₙ}|²` as `∑_n ∑_m aₙ conj aₘ e^{i (Lₘ - Lₙ) t}`. -/
private lemma ofReal_norm_sq_sum_exp {ι : Type*} (s : Finset ι) (a : ι → ℂ) (L : ι → ℝ) (t : ℝ) :
    ((‖∑ n ∈ s, a n * Complex.exp (-(t * L n) * I)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, a n * (starRingEnd ℂ) (a m) * Complex.exp ((L m - L n) * t * I) := by
  push_cast
  rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  have hconj : (starRingEnd ℂ) (-((t : ℂ) * (L m : ℂ)) * I) = ((L m : ℂ) * (t : ℂ)) * I := by
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [map_mul, ← Complex.exp_conj, mul_mul_mul_comm, ← Complex.exp_add, hconj]
  ring_nf

/-- The same expansion after integration over `[0, T]`: the integral of the square is the sum of
the `oscIntegral`s of the pairwise frequency differences. -/
private lemma ofReal_integral_norm_sq_sum_exp {ι : Type*} (s : Finset ι) (a : ι → ℂ) (L : ι → ℝ)
    (T : ℝ) :
    ((∫ t in (0:ℝ)..T, ‖∑ n ∈ s, a n * Complex.exp (-(t * L n) * I)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, a n * (starRingEnd ℂ) (a m) * oscIntegral (L m - L n) T := by
  rw [← intervalIntegral.integral_ofReal,
    intervalIntegral.integral_congr (g := fun t => ∑ n ∈ s, ∑ m ∈ s,
      a n * (starRingEnd ℂ) (a m) * Complex.exp ((L m - L n) * t * I))
      (fun t _ => ofReal_norm_sq_sum_exp s a L t),
    intervalIntegral.integral_finsetSum
      (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_finsetSum
    (fun m _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [oscIntegral, Complex.ofReal_sub]
  exact intervalIntegral.integral_const_mul (μ := volume) _ _

/-- The mean value theorem for an exponential sum with arbitrary distinct real frequencies:
`∫_0^T |∑ aₙ e^{-i t Lₙ}|² dt = T ∑ |aₙ|²` up to twice the sum of `|aₙ| |aₘ|` over the
off-diagonal pairs, weighted by the reciprocal frequency gaps. -/
private lemma abs_integral_norm_sq_sub_le_of_frequencies {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (L : ι → ℝ) (hL : ∀ n ∈ s, ∀ m ∈ s, m ≠ n → L m ≠ L n) (T : ℝ) :
    |(∫ t in (0:ℝ)..T, ‖∑ n ∈ s, a n * Complex.exp (-(t * L n) * I)‖ ^ 2)
        - T * ∑ n ∈ s, ‖a n‖ ^ 2|
      ≤ 2 * ∑ n ∈ s, ∑ m ∈ s.erase n, ‖a n‖ * ‖a m‖ / |L m - L n| := by
  have key : ((∫ t in (0:ℝ)..T, ‖∑ n ∈ s, a n * Complex.exp (-(t * L n) * I)‖ ^ 2 : ℝ) : ℂ)
        - ((T : ℂ) * ∑ n ∈ s, ((‖a n‖ ^ 2 : ℝ) : ℂ))
      = ∑ n ∈ s, ∑ m ∈ s.erase n, a n * (starRingEnd ℂ) (a m) * oscIntegral (L m - L n) T := by
    rw [ofReal_integral_norm_sq_sum_exp s a L T, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Finset.add_sum_erase _ _ hn, sub_self, oscIntegral_zero, Complex.mul_conj']
    push_cast
    ring
  have hbound : ‖∑ n ∈ s, ∑ m ∈ s.erase n,
        a n * (starRingEnd ℂ) (a m) * oscIntegral (L m - L n) T‖
      ≤ ∑ n ∈ s, ∑ m ∈ s.erase n, ‖a n‖ * ‖a m‖ * (2 / |L m - L n|) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    have hne : L m - L n ≠ 0 :=
      sub_ne_zero_of_ne (hL n hn m (Finset.mem_of_mem_erase hm) (Finset.ne_of_mem_erase hm))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (norm_oscIntegral_le _ T hne) (by positivity)
  have hcast : ‖((∫ t in (0:ℝ)..T, ‖∑ n ∈ s, a n * Complex.exp (-(t * L n) * I)‖ ^ 2 : ℝ) : ℂ)
        - ((T : ℂ) * ∑ n ∈ s, ((‖a n‖ ^ 2 : ℝ) : ℂ))‖
      = |(∫ t in (0:ℝ)..T, ‖∑ n ∈ s, a n * Complex.exp (-(t * L n) * I)‖ ^ 2)
        - T * ∑ n ∈ s, ‖a n‖ ^ 2| := by
    rw [← Complex.ofReal_sum, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    exact Complex.norm_real _
  have hfin : ∑ n ∈ s, ∑ m ∈ s.erase n, ‖a n‖ * ‖a m‖ * (2 / |L m - L n|)
      = 2 * ∑ n ∈ s, ∑ m ∈ s.erase n, ‖a n‖ * ‖a m‖ / |L m - L n| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [← hcast, key, ← hfin]
  exact hbound

/-- `n^{-it} = e^{-i t log n}` for a positive integer `n`. -/
private lemma natCast_cpow_neg_ofReal_mul_I {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (-(t : ℂ) * I) = Complex.exp (-(t * Real.log n) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- **The mean value theorem for Dirichlet polynomials.** For a finite set `A` of positive
integers,
`∫_0^T |∑_{n ∈ A} aₙ n^{-it}|² dt = T ∑_{n ∈ A} |aₙ|²`
up to an error of at most `2 ∑_{m ≠ n} |aₙ| |aₘ| / |log m - log n|`.

The diagonal pairs give `T ∑ |aₙ|²` exactly; each off-diagonal pair contributes
`aₙ conj aₘ ∫_0^T (m/n)^{it} dt`, of modulus at most `2 |aₙ| |aₘ| / |log m - log n|`. -/
@[zz_tag "lem_mean_value"]
theorem abs_integral_norm_sq_sub_le_sum_div_abs_log_sub_log (A : Finset ℕ) (hA : 0 ∉ A)
    (a : ℕ → ℂ) (T : ℝ) :
    |(∫ t in (0:ℝ)..T, ‖∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2) - T * ∑ n ∈ A, ‖a n‖ ^ 2|
      ≤ 2 * ∑ n ∈ A, ∑ m ∈ A.erase n, ‖a n‖ * ‖a m‖ / |Real.log m - Real.log n| := by
  have hpos : ∀ n ∈ A, 0 < (n : ℝ) := fun n hn =>
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h => hA (h ▸ hn))
  have hint : ∀ t : ℝ, (∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I))
      = ∑ n ∈ A, a n * Complex.exp (-(t * Real.log n) * I) := fun t =>
    Finset.sum_congr rfl fun n hn => by
      rw [natCast_cpow_neg_ofReal_mul_I (fun h => hA (h ▸ hn)) t]
  simp only [hint]
  refine abs_integral_norm_sq_sub_le_of_frequencies A a (fun n : ℕ => Real.log n)
    (fun n hn m hm hmn h => ?_) T
  have hcast : (m : ℝ) = n := by
    rw [← Real.exp_log (hpos m hm), h, Real.exp_log (hpos n hn)]
  exact hmn (by exact_mod_cast hcast)

/-- The mean value theorem for Dirichlet polynomials with the off-diagonal error at most
`2 (∑_{n ∈ A} √(n + 1) |aₙ|)²`: the multiplicative gap `|log n - log m| ≥ (n + 1)⁻¹`, applied in
both orders, gives `|log n - log m|⁻¹ ≤ √(n + 1) √(m + 1)`. -/
theorem abs_integral_norm_sq_sub_le_sq_sum_sqrt (A : Finset ℕ) (hA : 0 ∉ A) (a : ℕ → ℂ) (T :
    ℝ) :
    |(∫ t in (0:ℝ)..T, ‖∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2) - T * ∑ n ∈ A, ‖a n‖ ^ 2|
      ≤ 2 * (∑ n ∈ A, Real.sqrt (n + 1) * ‖a n‖) ^ 2 := by
  refine (abs_integral_norm_sq_sub_le_sum_div_abs_log_sub_log A hA a T).trans ?_
  have hterm : ∀ n ∈ A, ∀ m ∈ A.erase n, ‖a n‖ * ‖a m‖ / |Real.log m - Real.log n|
      ≤ (Real.sqrt (n + 1) * ‖a n‖) * (Real.sqrt (m + 1) * ‖a m‖) := by
    intro n hn m hm
    have hmA : m ∈ A := Finset.mem_of_mem_erase hm
    have hmn : m ≠ n := Finset.ne_of_mem_erase hm
    have h1n : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h => hA (h ▸ hn)
    have h1m : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => hA (h ▸ hmA)
    set d := |Real.log m - Real.log n| with hd
    have hdn : ((n : ℝ) + 1)⁻¹ ≤ d := by
      rw [hd, abs_sub_comm]
      exact inv_natCast_add_one_le_abs_log_sub_log h1m h1n hmn
    have hdm : ((m : ℝ) + 1)⁻¹ ≤ d := by
      rw [hd]
      exact inv_natCast_add_one_le_abs_log_sub_log h1n h1m (Ne.symm hmn)
    have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hdn
    have h2 : d⁻¹ ≤ (n : ℝ) + 1 := by
      rw [inv_le_comm₀ (by positivity) hdpos] at hdn
      exact hdn
    have h3 : d⁻¹ ≤ (m : ℝ) + 1 := by
      rw [inv_le_comm₀ (by positivity) hdpos] at hdm
      exact hdm
    have hinv : d⁻¹ ≤ Real.sqrt (n + 1) * Real.sqrt (m + 1) := by
      rw [← Real.sqrt_mul (by positivity),
        show d⁻¹ = Real.sqrt (d⁻¹ ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      refine Real.sqrt_le_sqrt ?_
      have h4 : (0:ℝ) ≤ d⁻¹ := by positivity
      nlinarith
    calc ‖a n‖ * ‖a m‖ / d = (‖a n‖ * ‖a m‖) * d⁻¹ := by ring
      _ ≤ (‖a n‖ * ‖a m‖) * (Real.sqrt (n + 1) * Real.sqrt (m + 1)) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (Real.sqrt (n + 1) * ‖a n‖) * (Real.sqrt (m + 1) * ‖a m‖) := by ring
  have hsum : ∑ n ∈ A, ∑ m ∈ A.erase n, ‖a n‖ * ‖a m‖ / |Real.log m - Real.log n|
      ≤ (∑ n ∈ A, Real.sqrt (n + 1) * ‖a n‖) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    refine le_trans (Finset.sum_le_sum (hterm n hn)) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      fun m _ _ => by positivity
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  gcongr

/-! ### The passage to `ℓ¹` coefficients

The limit along the net of finite subsets of `ℕ`, for an absolutely summable coefficient sequence
whose off-diagonal double sum is summable. -/

/-- `‖n^{-it}‖ ≤ 1` for every natural `n`. Equality holds for `n ≥ 1`; for `n = 0` the power is
`0` unless the exponent vanishes, when it is `1`. -/
private lemma norm_natCast_cpow_neg_mul_I_le (n : ℕ) (t : ℝ) :
    ‖(n : ℂ) ^ (-(t : ℂ) * I)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero]
    rcases eq_or_ne (-(t : ℂ) * I) 0 with h | h
    · rw [h, Complex.cpow_zero, norm_one]
    · rw [Complex.zero_cpow h, norm_zero]
      norm_num
  · rw [natCast_cpow_neg_ofReal_mul_I hn.ne' t, Complex.norm_exp]
    simp only [Complex.mul_I_re, Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, add_zero, neg_zero, Real.exp_zero]
    exact le_rfl

/-- Each term of the Dirichlet series is bounded by its coefficient: `‖aₙ n^{-it}‖ ≤ ‖aₙ‖`. -/
private lemma norm_term_le (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ≤ ‖a n‖ := by
  rw [norm_mul]
  calc ‖a n‖ * ‖(n : ℂ) ^ (-(t : ℂ) * I)‖ ≤ ‖a n‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_natCast_cpow_neg_mul_I_le n t) (norm_nonneg _)
    _ = ‖a n‖ := mul_one _

private lemma summable_term (a : ℕ → ℂ) (hsum : Summable fun n ↦ ‖a n‖) (t : ℝ) :
    Summable (fun n : ℕ ↦ a n * (n : ℂ) ^ (-(t : ℂ) * I)) :=
  Summable.of_norm_bounded hsum fun n ↦ norm_term_le a n t

/-- The uniform tail estimate: the Dirichlet series differs from its partial sum over `A` by at
most `∑_{n ∉ A} ‖aₙ‖`, *independently of `t`*. -/
private lemma norm_tsum_sub_sum_le (a : ℕ → ℂ) (hsum : Summable fun n ↦ ‖a n‖)
    (A : Finset ℕ) (t : ℝ) :
    ‖(∑' n : ℕ, a n * (n : ℂ) ^ (-(t : ℂ) * I)) - ∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖
      ≤ ∑' n : {x // x ∉ A}, ‖a n‖ := by
  have hsub : Summable (fun n : {x // x ∉ A} ↦ ‖a n‖) := hsum.subtype _
  have hnorm : Summable (fun n : {x // x ∉ A} ↦ ‖a n * ((n : ℕ) : ℂ) ^ (-(t : ℂ) * I)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ norm_term_le a n t) hsub
  have heq : (∑' n : ℕ, a n * (n : ℂ) ^ (-(t : ℂ) * I))
      - ∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I)
      = ∑' n : {x // x ∉ A}, a n * ((n : ℕ) : ℂ) ^ (-(t : ℂ) * I) := by
    rw [← (summable_term a hsum t).sum_add_tsum_subtype_compl A]
    ring
  rw [heq]
  exact le_trans (norm_tsum_le_tsum_norm hnorm)
    (hnorm.tsum_le_tsum (fun n ↦ norm_term_le a n t) hsub)

private lemma norm_sum_le_bound (a : ℕ → ℂ) (hsum : Summable fun n ↦ ‖a n‖) (A : Finset ℕ) (t : ℝ) :
    ‖∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ≤ ∑' n : ℕ, ‖a n‖ :=
  le_trans (norm_sum_le _ _)
    (le_trans (Finset.sum_le_sum fun n _ ↦ norm_term_le a n t)
      (hsum.sum_le_tsum A fun _ _ ↦ norm_nonneg _))

private lemma norm_tsum_le_bound (a : ℕ → ℂ) (hsum : Summable fun n ↦ ‖a n‖) (t : ℝ) :
    ‖∑' n : ℕ, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ≤ ∑' n : ℕ, ‖a n‖ := by
  have hnorm : Summable (fun n : ℕ ↦ ‖a n * (n : ℂ) ^ (-(t : ℂ) * I)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ norm_term_le a n t) hsum
  exact le_trans (norm_tsum_le_tsum_norm hnorm)
    (hnorm.tsum_le_tsum (fun n ↦ norm_term_le a n t) hsum)

private lemma continuous_term (a : ℕ → ℂ) (ha0 : a 0 = 0) (n : ℕ) :
    Continuous (fun t : ℝ ↦ a n * (n : ℂ) ^ (-(t : ℂ) * I)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [ha0] using continuous_const (y := (0 : ℂ))
  · exact continuous_const.mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (Nat.cast_ne_zero.mpr hn.ne')))

private lemma continuous_partialSum (a : ℕ → ℂ) (ha0 : a 0 = 0) (A : Finset ℕ) :
    Continuous (fun t : ℝ ↦ ∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I)) :=
  continuous_finsetSum A fun n _ ↦ continuous_term a ha0 n

/-- The Dirichlet series of an `ℓ¹` sequence is continuous in `t`: the partial sums converge to it
uniformly, since `‖aₙ n^{-it}‖ ≤ ‖aₙ‖` with `∑ ‖aₙ‖ < ∞`. -/
private lemma continuous_dirichlet (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (hsum : Summable fun n ↦ ‖a n‖) :
    Continuous (fun t : ℝ ↦ ∑' n : ℕ, a n * (n : ℂ) ^ (-(t : ℂ) * I)) :=
  continuous_tsum (fun n ↦ continuous_term a ha0 n) hsum fun n t ↦ norm_term_le a n t

/-- The integrals of the partial sums converge to the integral of the series, because the
convergence is uniform on the compact interval `[0, T]`. -/
private lemma tendsto_integral_norm_sq (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (hsum : Summable fun n ↦ ‖a n‖) (T : ℝ) :
    Filter.Tendsto
      (fun A : Finset ℕ ↦ ∫ t in (0 : ℝ)..T, ‖∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2)
      Filter.atTop
      (nhds (∫ t in (0 : ℝ)..T, ‖∑' n : ℕ, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2)) := by
  set B : ℝ := ∑' n : ℕ, ‖a n‖ with hBdef
  have hB0 : 0 ≤ B := tsum_nonneg fun _ ↦ norm_nonneg _
  have hIS : IntervalIntegrable
      (fun t ↦ ‖∑' n : ℕ, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2) volume 0 T :=
    (((continuous_dirichlet a ha0 hsum).norm).pow 2).intervalIntegrable 0 T
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun A ↦ ?_)
    (g := fun A : Finset ℕ ↦ 2 * B * (∑' n : {x // x ∉ A}, ‖a n‖) * |T - 0|) ?_
  · have hIA : IntervalIntegrable
        (fun t ↦ ‖∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2) volume 0 T :=
      (((continuous_partialSum a ha0 A).norm).pow 2).intervalIntegrable 0 T
    rw [← intervalIntegral.integral_sub hIA hIS]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦ ?_
    set u : ℂ := ∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I) with hu
    set v : ℂ := ∑' n : ℕ, a n * (n : ℂ) ^ (-(t : ℂ) * I) with hv
    set d : ℝ := ∑' n : {x // x ∉ A}, ‖a n‖ with hd
    have hd0 : 0 ≤ d := tsum_nonneg fun _ ↦ norm_nonneg _
    have hdiff : |‖u‖ - ‖v‖| ≤ d := by
      refine le_trans (abs_sub_comm ‖u‖ ‖v‖ ▸ abs_norm_sub_norm_le v u) ?_
      exact norm_tsum_sub_sum_le a hsum A t
    have hub : ‖u‖ ≤ B := norm_sum_le_bound a hsum A t
    have hvb : ‖v‖ ≤ B := norm_tsum_le_bound a hsum t
    have hun : (0 : ℝ) ≤ ‖u‖ := norm_nonneg _
    have hvn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
    obtain ⟨hlo, hhi⟩ := abs_le.mp hdiff
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · nlinarith [mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ 2 * B - (‖u‖ + ‖v‖))]
    · nlinarith [mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ 2 * B - (‖u‖ + ‖v‖))]
  · have h := ((tendsto_tsum_compl_atTop_zero (fun n ↦ ‖a n‖)).const_mul (2 * B)).mul_const
      |T - 0|
    simpa using h

/-- **The mean value theorem for `ℓ¹` Dirichlet series.** For an absolutely summable coefficient
sequence supported on `n ≥ 1` whose off-diagonal sum is summable,
`∫_0^T |∑_n aₙ n^{-it}|² dt = T ∑_n |aₙ|²`
up to `2 ∑_{m ≠ n} |aₙ| |aₘ| / |log m - log n|`. -/
theorem abs_integral_norm_sq_sub_le_tsum_div_abs_log_sub_log (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (hsum : Summable fun n ↦ ‖a n‖)
    (hoff : Summable fun p : ℕ × ℕ ↦
      if p.1 = p.2 then 0 else ‖a p.1‖ * ‖a p.2‖ / |Real.log p.2 - Real.log p.1|)
    (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖∑' n : ℕ, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2)
        - T * ∑' n : ℕ, ‖a n‖ ^ 2|
      ≤ 2 * ∑' p : ℕ × ℕ,
          (if p.1 = p.2 then 0 else ‖a p.1‖ * ‖a p.2‖ / |Real.log p.2 - Real.log p.1|) := by
  have hoffnn : ∀ p : ℕ × ℕ,
      0 ≤ (if p.1 = p.2 then 0 else ‖a p.1‖ * ‖a p.2‖ / |Real.log p.2 - Real.log p.1|) := by
    intro p
    split_ifs
    · exact le_rfl
    · positivity
  have hsq : Summable (fun n : ℕ ↦ ‖a n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) (fun n ↦ ?_)
      (hsum.mul_left (∑' k : ℕ, ‖a k‖))
    have hle : ‖a n‖ ≤ ∑' k : ℕ, ‖a k‖ := hsum.le_tsum n fun _ _ ↦ norm_nonneg _
    nlinarith [norm_nonneg (a n)]
  have hlim : Filter.Tendsto
      (fun A : Finset ℕ ↦ |(∫ t in (0 : ℝ)..T, ‖∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2)
        - T * ∑ n ∈ A, ‖a n‖ ^ 2|) Filter.atTop
      (nhds |(∫ t in (0 : ℝ)..T, ‖∑' n : ℕ, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2)
        - T * ∑' n : ℕ, ‖a n‖ ^ 2|) :=
    ((tendsto_integral_norm_sq a ha0 hsum T).sub
      ((hsq.hasSum : Filter.Tendsto _ _ _).const_mul T)).abs
  refine le_of_tendsto hlim (.of_forall fun A ↦ ?_)
  have h0 : (0 : ℕ) ∉ A.erase 0 := Finset.notMem_erase 0 A
  have hint : ∀ t : ℝ, (∑ n ∈ A, a n * (n : ℂ) ^ (-(t : ℂ) * I))
      = ∑ n ∈ A.erase 0, a n * (n : ℂ) ^ (-(t : ℂ) * I) := fun t ↦
    (Finset.sum_erase A (by rw [ha0, zero_mul])).symm
  have hdiag : (∑ n ∈ A, ‖a n‖ ^ 2) = ∑ n ∈ A.erase 0, ‖a n‖ ^ 2 :=
    (Finset.sum_erase A (by rw [ha0]; simp)).symm
  simp only [hint, hdiag]
  refine le_trans (abs_integral_norm_sq_sub_le_sum_div_abs_log_sub_log (A.erase 0) h0 a T) ?_
  have hrw : ∀ n ∈ A.erase 0,
      (∑ m ∈ (A.erase 0).erase n, ‖a n‖ * ‖a m‖ / |Real.log m - Real.log n|)
        = ∑ m ∈ A.erase 0,
            (if n = m then 0 else ‖a n‖ * ‖a m‖ / |Real.log m - Real.log n|) := by
    intro n _
    have hzero : ∀ m ∈ A.erase 0, m ∉ (A.erase 0).erase n →
        (if n = m then (0 : ℝ) else ‖a n‖ * ‖a m‖ / |Real.log m - Real.log n|) = 0 := by
      intro m hm hmn
      have hmeq : m = n := by
        by_contra h
        exact hmn (Finset.mem_erase.mpr ⟨h, hm⟩)
      simp [hmeq]
    rw [← Finset.sum_subset (Finset.erase_subset n (A.erase 0)) hzero]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    simp [Ne.symm (Finset.ne_of_mem_erase hm)]
  have hkey : (∑ n ∈ A.erase 0, ∑ m ∈ (A.erase 0).erase n,
        ‖a n‖ * ‖a m‖ / |Real.log m - Real.log n|)
      ≤ ∑' p : ℕ × ℕ,
          (if p.1 = p.2 then 0 else ‖a p.1‖ * ‖a p.2‖ / |Real.log p.2 - Real.log p.1|) := by
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_product']
    exact hoff.sum_le_tsum _ fun p _ ↦ hoffnn p
  linarith

end ZetaZeros
