/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
public import ZetaZeros.PairCorrelation.Function

/-!
# The trivial bound for the weighted prime sum

The pointwise estimate `|D (x, t)| ≪ x^{1/2} log (2 x)` for the prime side

`D (x, t) = ∑_{n ≥ 1} Λ (n) n^{-1/2 - it} min {n / x, x / n}`

of Montgomery's explicit-formula lemma, together with the absolute convergence of the series that
defines it. Both come from the same majorant: the sum of absolute values

`∑_{n ≥ 1} Λ (n) n^{-1/2} min {n / x, x / n}`

is bounded by `C x^{1/2} log (2 x)` uniformly in `t`, since `t` does not occur in it.

The sum is split at `n = x`. Below `x` the terms are
`Λ (n) n^{1/2} / x ≤ log (2 x) n^{1/2} / x ≤ log (2 x) x^{-1/2}`, and there are at most `2 x` of
them. Above `x` the terms are `x Λ (n) n^{-3/2} ≤ x log n ⬝ n^{-3/2}`, and the logarithm is split
as `log n = log x + log (n / x) ≤ log x + 4 (n / x)^{1/4}`, which turns the tail into a combination
of the two convergent tails `∑_{n > N} n^{-3/2}` and `∑_{n > N} n^{-5/4}`. Each of those is bounded
by the corresponding improper integral over `(N, ∞)`, giving `2 N^{-1/2}` and `4 N^{-1/4}`; with
`N = ⌊x⌋` and `N ≥ x / 2` the two contributions are `O (x^{1/2} log x)` and `O (x^{1/2})`.

## Main results

* `ZetaZeros.summable_vonMangoldt_div_sqrt_mul_min`: the majorant series converges.
* `ZetaZeros.exists_tsum_vonMangoldt_div_sqrt_mul_min_le`: the bound
  `∑_{n ≥ 1} Λ (n) n^{-1/2} min {n / x, x / n} ≤ C x^{1/2} log (2 x)` for `x ≥ 1`.
* `ZetaZeros.exists_summable_and_norm_weightedPrimeSum_le`: the series defining `D (x, t)`
  converges absolutely and `‖D (x, t)‖ ≤ C x^{1/2} log (2 x)`, uniformly in `t`.

## Implementation notes

The majorant is indexed by all of `ℕ`, matching `ZetaZeros.weightedPrimeSum`; the term at `n = 0`
vanishes because `Λ 0 = 0`, and `min (0 / x) (x / 0) = 0` as well, so nothing needs to be excluded.

Every exponent is a real `rpow`, as in `AntitoneOn.tsum_comp_add_le_integral` and
`integral_Ioi_rpow_of_lt`; the square roots in the weight `n^{-1/2}` of the summand and in the
conclusion `x^{1/2}` are converted by `Real.sqrt_eq_rpow`.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt

/-! ### Elementary estimates -/

/-- `log u ≤ 4 u^{1/4}` for `u ≥ 1`: apply `log v ≤ v - 1` to `v = u^{1/4}` and multiply by `4`. -/
private lemma log_le_four_mul_rpow {u : ℝ} (hu : 1 ≤ u) : Real.log u ≤ 4 * u ^ ((1 : ℝ) / 4) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have h1 : Real.log (u ^ ((1 : ℝ) / 4)) = 1 / 4 * Real.log u := Real.log_rpow hu0 _
  have h2 : Real.log (u ^ ((1 : ℝ) / 4)) ≤ u ^ ((1 : ℝ) / 4) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu0 _)
  rw [h1] at h2
  linarith

/-- `n^{-3/2} = (n √n)⁻¹`. -/
private lemma rpow_neg_three_half {n : ℝ} (hn : 0 < n) :
    n ^ (-(3 / 2 : ℝ)) = (n * Real.sqrt n)⁻¹ := by
  rw [Real.rpow_neg hn.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn,
    Real.rpow_one, Real.sqrt_eq_rpow]

/-- `n^{1/4} (n √n)⁻¹ = n^{-5/4}`. -/
private lemma rpow_neg_five_quarter {n : ℝ} (hn : 0 < n) :
    n ^ ((1 : ℝ) / 4) * (n * Real.sqrt n)⁻¹ = n ^ (-(5 / 4 : ℝ)) := by
  rw [← rpow_neg_three_half hn, ← Real.rpow_add hn]
  norm_num

/-- A negative power is antitone, so halving the base costs at most a factor `2^e ≤ 2`. -/
private lemma rpow_neg_le_two_mul {y N e : ℝ} (hy : 0 < y) (hN : y / 2 ≤ N) (he0 : 0 ≤ e)
    (he1 : e ≤ 1) : N ^ (-e) ≤ 2 * y ^ (-e) := by
  have hy2 : (0 : ℝ) < y / 2 := by linarith
  have h1 : N ^ (-e) ≤ (y / 2) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos hy2 hN (neg_nonpos.mpr he0)
  have h2' : (2 : ℝ) ^ (-e) = ((2 : ℝ) ^ e)⁻¹ := Real.rpow_neg (by norm_num) e
  have h2 : (y / 2) ^ (-e) = y ^ (-e) * 2 ^ e := by
    rw [Real.div_rpow hy.le (by norm_num), h2', div_eq_mul_inv, inv_inv]
  have h3 : (2 : ℝ) ^ e ≤ 2 := by
    calc (2 : ℝ) ^ e ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two he1
      _ = 2 := Real.rpow_one 2
  have h4 : (0 : ℝ) ≤ y ^ (-e) := Real.rpow_nonneg hy.le _
  rw [h2] at h1
  nlinarith

/-! ### The tails of the two comparison series -/

/-- The tail `∑_{n > N} n^{-s}` of a convergent power series is at most the improper integral
`∫_N^∞ u^{-s} du = N^{1-s} / (s - 1)`, by the comparison of a sum with the integral of an
antitone function. -/
private lemma tsum_rpow_shift_le {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    ∑' i : ℕ, ((i : ℝ) + N + 1) ^ (-s) ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : -s < -1 := by linarith
  have hanti : AntitoneOn (fun u : ℝ => u ^ (-s)) (Ici (N : ℝ)) := fun u hu v _ huv =>
    Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hN0 hu) huv (by linarith)
  have hint : IntegrableOn (fun u : ℝ => u ^ (-s)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hlt hN0
  have hnn : ∀ t ∈ Ioi (N : ℝ), (0 : ℝ) ≤ t ^ (-s) := fun t ht =>
    Real.rpow_nonneg (le_of_lt (lt_trans hN0 ht)) _
  have key := hanti.tsum_comp_add_le_integral N hint hnn
  have hcast : ∀ i : ℕ, ((i + N + 1 : ℕ) : ℝ) = (i : ℝ) + N + 1 := by
    intro i; push_cast; ring
  simp only [hcast] at key
  refine key.trans ?_
  rw [integral_Ioi_rpow_of_lt hlt hN0, show (-s + 1) = 1 - s from by ring, neg_div, ← div_neg,
    neg_sub]

/-- The shifted power series `∑_i (i + N + 1)^{-s}` converges for `s > 1`. -/
private lemma summable_rpow_shift {s : ℝ} (hs : 1 < s) (N : ℕ) :
    Summable (fun i : ℕ => ((i : ℝ) + N + 1) ^ (-s)) := by
  have hf : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  refine ((summable_nat_add_iff (N + 1)).mpr hf).congr ?_
  intro i
  push_cast
  ring_nf

/-- The tail of a summable sequence dominated term by term, above the cut `N`, by a combination of
`(i + N + 1)^{-3/2}` and `(i + N + 1)^{-5/4}`, is at most `2 B N^{-1/2} + 4 C N^{-1/4}`. -/
private lemma tsum_shift_le {a : ℕ → ℝ} (hsum : Summable a) {N : ℕ} (hN1 : 1 ≤ N)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hle : ∀ i : ℕ, a (i + (N + 1)) ≤ B * ((i : ℝ) + N + 1) ^ (-(3 / 2 : ℝ))
      + C * ((i : ℝ) + N + 1) ^ (-(5 / 4 : ℝ))) :
    ∑' i : ℕ, a (i + (N + 1))
      ≤ 2 * B * (N : ℝ) ^ (-(1 / 2 : ℝ)) + 4 * C * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hS3 : Summable (fun i : ℕ => ((i : ℝ) + N + 1) ^ (-(3 / 2 : ℝ))) :=
    summable_rpow_shift (by norm_num) N
  have hS5 : Summable (fun i : ℕ => ((i : ℝ) + N + 1) ^ (-(5 / 4 : ℝ))) :=
    summable_rpow_shift (by norm_num) N
  have htail : Summable (fun i : ℕ => a (i + (N + 1))) := (summable_nat_add_iff (N + 1)).mpr hsum
  have hFsum : Summable (fun i : ℕ => B * ((i : ℝ) + N + 1) ^ (-(3 / 2 : ℝ))
      + C * ((i : ℝ) + N + 1) ^ (-(5 / 4 : ℝ))) := (hS3.mul_left _).add (hS5.mul_left _)
  refine (htail.tsum_le_tsum hle hFsum).trans ?_
  rw [(hS3.mul_left _).tsum_add (hS5.mul_left _), tsum_mul_left, tsum_mul_left]
  have hb3 : (∑' i : ℕ, ((i : ℝ) + N + 1) ^ (-(3 / 2 : ℝ))) ≤ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have h := tsum_rpow_shift_le (s := (3 / 2 : ℝ)) (by norm_num) hN1
    rw [show (1 : ℝ) - 3 / 2 = -(1 / 2 : ℝ) by norm_num,
      show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num] at h
    linarith
  have hb5 : (∑' i : ℕ, ((i : ℝ) + N + 1) ^ (-(5 / 4 : ℝ))) ≤ 4 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have h := tsum_rpow_shift_le (s := (5 / 4 : ℝ)) (by norm_num) hN1
    rw [show (1 : ℝ) - 5 / 4 = -(1 / 4 : ℝ) by norm_num,
      show (5 : ℝ) / 4 - 1 = 1 / 4 by norm_num] at h
    linarith
  calc B * (∑' i : ℕ, ((i : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)))
        + C * (∑' i : ℕ, ((i : ℝ) + N + 1) ^ (-(5 / 4 : ℝ)))
      ≤ B * (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) + C * (4 * (N : ℝ) ^ (-(1 / 4 : ℝ))) := by gcongr
    _ = 2 * B * (N : ℝ) ^ (-(1 / 2 : ℝ)) + 4 * C * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by ring

/-! ### The summand of the majorant -/

/-- Every term of the majorant is nonnegative. -/
private lemma term_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 ≤ Λ n / Real.sqrt n * min ((n : ℝ) / x) (x / n) :=
  mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (le_min (by positivity) (by positivity))

/-- The bound of a term of the majorant obtained from `min {n / x, x / n} ≤ x / n` and
`Λ ≤ log`. -/
private lemma term_le_inv {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    Λ n / Real.sqrt n * min ((n : ℝ) / x) (x / n)
      ≤ x * Real.log n * ((n : ℝ) * Real.sqrt n)⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hLn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hmin : min ((n : ℝ) / x) (x / n) ≤ x / (n : ℝ) := min_le_right _ _
  have hmin0 : (0 : ℝ) ≤ min ((n : ℝ) / x) (x / n) := le_min (by positivity) (by positivity)
  calc Λ n / Real.sqrt n * min ((n : ℝ) / x) (x / n)
      ≤ Real.log n / Real.sqrt n * (x / (n : ℝ)) := by
        gcongr
        exact ArithmeticFunction.vonMangoldt_le_log
    _ = x * Real.log n * ((n : ℝ) * Real.sqrt n)⁻¹ := by field_simp

/-- The global majorant `4 x n^{-5/4}` of the terms, from `Λ (n) ≤ log n ≤ 4 n^{1/4}` and
`min {n / x, x / n} ≤ x / n`. -/
private lemma term_le_global {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Λ n / Real.sqrt n * min ((n : ℝ) / x) (x / n) ≤ 4 * x * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp [Real.zero_rpow]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast h
    refine (term_le_inv hx h).trans ?_
    have hinv : (0 : ℝ) < ((n : ℝ) * Real.sqrt n)⁻¹ := by positivity
    calc x * Real.log n * ((n : ℝ) * Real.sqrt n)⁻¹
        ≤ x * (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) * Real.sqrt n)⁻¹ := by
          have := log_le_four_mul_rpow (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast h)
          gcongr
      _ = 4 * x * ((n : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) * Real.sqrt n)⁻¹) := by ring
      _ = 4 * x * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by rw [rpow_neg_five_quarter hn0]

/-- Below the cut: for `n ≤ x` the term is `Λ (n) n^{1/2} / x ≤ log (2 x) x^{1/2} / x`. -/
private lemma term_le_head {x : ℝ} (hx : 1 ≤ x) (i : ℕ) (hix : (i : ℝ) ≤ x) :
    Λ i / Real.sqrt i * min ((i : ℝ) / x) (x / i) ≤ Real.log (2 * x) * Real.sqrt x / x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hL2 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hRnn : (0 : ℝ) ≤ Real.log (2 * x) * Real.sqrt x / x :=
    div_nonneg (mul_nonneg hL2 (Real.sqrt_nonneg x)) hx0.le
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    simpa using hRnn
  · have hi0 : (0 : ℝ) < i := by exact_mod_cast h
    have hsq0 : (0 : ℝ) < Real.sqrt i := Real.sqrt_pos.mpr hi0
    have hLn : (0 : ℝ) ≤ Real.log i := Real.log_nonneg (by exact_mod_cast h)
    have hLx : Real.log i ≤ Real.log (2 * x) := Real.log_le_log hi0 (by linarith)
    have hsq : Real.sqrt i ≤ Real.sqrt x := Real.sqrt_le_sqrt hix
    have hmin : min ((i : ℝ) / x) (x / i) ≤ (i : ℝ) / x := min_le_left _ _
    have hmin0 : (0 : ℝ) ≤ min ((i : ℝ) / x) (x / i) := le_min (by positivity) (by positivity)
    calc Λ i / Real.sqrt i * min ((i : ℝ) / x) (x / i)
        ≤ Real.log i / Real.sqrt i * ((i : ℝ) / x) := by
          gcongr
          exact ArithmeticFunction.vonMangoldt_le_log
      _ = Real.log i * ((i : ℝ) / Real.sqrt i) / x := by ring
      _ = Real.log i * Real.sqrt i / x := by rw [Real.div_sqrt]
      _ ≤ Real.log (2 * x) * Real.sqrt x / x := by gcongr

/-- Above the cut: for `n ≥ x` the term is at most `x log n ⬝ n^{-3/2}`, and splitting
`log n ≤ log x + 4 (n / x)^{1/4}` turns that into a combination of `n^{-3/2}` and `n^{-5/4}`. -/
private lemma term_le_tail {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : 1 ≤ n) (hxn : x ≤ (n : ℝ)) :
    Λ n / Real.sqrt n * min ((n : ℝ) / x) (x / n)
      ≤ x * Real.log x * (n : ℝ) ^ (-(3 / 2 : ℝ))
        + 4 * x ^ ((3 : ℝ) / 4) * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ex34 : x / x ^ ((1 : ℝ) / 4) = x ^ ((3 : ℝ) / 4) := by
    rw [show ((3 : ℝ) / 4) = 1 - 1 / 4 by norm_num, Real.rpow_sub hx0, Real.rpow_one]
  refine (term_le_inv hx0 hn).trans ?_
  have h2 : Real.log n ≤ Real.log x + 4 * ((n : ℝ) / x) ^ ((1 : ℝ) / 4) := by
    have hnx : 1 ≤ (n : ℝ) / x := (one_le_div hx0).mpr hxn
    have h := log_le_four_mul_rpow hnx
    rw [Real.log_div (by positivity) (by positivity)] at h
    linarith
  have hinv0 : (0 : ℝ) < ((n : ℝ) * Real.sqrt n)⁻¹ := by positivity
  calc x * Real.log n * ((n : ℝ) * Real.sqrt n)⁻¹
      ≤ x * (Real.log x + 4 * ((n : ℝ) / x) ^ ((1 : ℝ) / 4)) * ((n : ℝ) * Real.sqrt n)⁻¹ := by
        gcongr
    _ = x * Real.log x * ((n : ℝ) * Real.sqrt n)⁻¹
          + 4 * (x / x ^ ((1 : ℝ) / 4))
            * ((n : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) * Real.sqrt n)⁻¹) := by
        rw [Real.div_rpow hn0.le hx0.le]
        have hxq : x ^ ((1 : ℝ) / 4) ≠ 0 := by positivity
        field_simp
    _ = x * Real.log x * (n : ℝ) ^ (-(3 / 2 : ℝ))
          + 4 * x ^ ((3 : ℝ) / 4) * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
        rw [rpow_neg_three_half hn0, rpow_neg_five_quarter hn0, ex34]

/-! ### The trivial bound -/

/-- The series of absolute values of the weighted prime sum converges, for every `x > 0`: its
terms are at most `4 x n^{-5/4}`. -/
theorem summable_vonMangoldt_div_sqrt_mul_min {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => Λ n / Real.sqrt n * min ((n : ℝ) / x) (x / n)) :=
  Summable.of_nonneg_of_le (term_nonneg hx) (term_le_global hx)
    ((Real.summable_nat_rpow.mpr (by norm_num)).mul_left _)

/-- **The trivial bound for the weighted prime sum.** There is an absolute constant `C > 0` such
that for every `x ≥ 1`,
`∑_{n ≥ 1} Λ (n) n^{-1/2} min {n / x, x / n} ≤ C x^{1/2} log (2 x)`.

The sum is split at `n = ⌊x⌋`. The `⌊x⌋ + 1 ≤ 2 x` terms below the cut are each at most
`log (2 x) x^{1/2} / x`, contributing `2 x^{1/2} log (2 x)`. Above the cut the terms are at most
`x log x ⬝ n^{-3/2} + 4 x^{3/4} n^{-5/4}`, and the two tails are `O (x^{-1/2})` and
`O (x^{-1/4})` by comparison with the improper integrals, contributing
`4 x^{1/2} log x + 32 x^{1/2}`. -/
@[zz_tag "lem_D_pointwise"]
theorem exists_tsum_vonMangoldt_div_sqrt_mul_min_le :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      ∑' n : ℕ, Λ n / Real.sqrt n * min ((n : ℝ) / x) (x / n)
        ≤ C * Real.sqrt x * Real.log (2 * x) := by
  refine ⟨100, by norm_num, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hgsum := summable_vonMangoldt_div_sqrt_mul_min hx0
  have hN1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  set N := ⌊x⌋₊ with hNdef
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hNhalf : x / 2 ≤ (N : ℝ) := by linarith
  have hL2 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hLx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hsplit := hgsum.sum_add_tsum_nat_add (N + 1)
  have hhead : ∑ i ∈ Finset.range (N + 1), Λ i / Real.sqrt i * min ((i : ℝ) / x) (x / i)
      ≤ 2 * Real.sqrt x * Real.log (2 * x) := by
    have hb : ∀ i ∈ Finset.range (N + 1),
        Λ i / Real.sqrt i * min ((i : ℝ) / x) (x / i) ≤ Real.log (2 * x) * Real.sqrt x / x := by
      intro i hi
      have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      exact term_le_head hx i (le_trans (by exact_mod_cast hiN) hNx)
    have hs := Finset.sum_le_card_nsmul _ _ _ hb
    simp only [Finset.card_range, nsmul_eq_mul] at hs
    refine hs.trans ?_
    have hc0 : (0 : ℝ) ≤ Real.log (2 * x) * Real.sqrt x / x :=
      div_nonneg (mul_nonneg hL2 (Real.sqrt_nonneg x)) hx0.le
    have hcard : ((N + 1 : ℕ) : ℝ) ≤ 2 * x := by push_cast; linarith
    calc ((N + 1 : ℕ) : ℝ) * (Real.log (2 * x) * Real.sqrt x / x)
        ≤ (2 * x) * (Real.log (2 * x) * Real.sqrt x / x) := by gcongr
      _ = 2 * Real.sqrt x * Real.log (2 * x) := by field_simp
  have hxq : (0 : ℝ) ≤ x ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hx0.le _
  have htail := tsum_shift_le hgsum hN1 (B := x * Real.log x) (C := 4 * x ^ ((3 : ℝ) / 4))
    (mul_nonneg hx0.le hLx0) (by positivity) (fun i => by
      have hb : ((i + (N + 1) : ℕ) : ℝ) = (i : ℝ) + N + 1 := by push_cast; ring
      have hn1 : 1 ≤ i + (N + 1) := by omega
      have hxn : x ≤ ((i + (N + 1) : ℕ) : ℝ) := by rw [hb]; linarith
      rw [← hb]
      exact term_le_tail hx hn1 hxn)
  have ea : x * x ^ (-(1 / 2 : ℝ)) = Real.sqrt x := by
    have h := Real.rpow_add hx0 1 (-(1 / 2 : ℝ))
    rw [Real.rpow_one] at h
    rw [Real.sqrt_eq_rpow, ← h]
    norm_num
  have eb : x ^ ((3 : ℝ) / 4) * x ^ (-(1 / 4 : ℝ)) = Real.sqrt x := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]
    norm_num
  have hN3 : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * x ^ (-(1 / 2 : ℝ)) :=
    rpow_neg_le_two_mul hx0 hNhalf (by norm_num) (by norm_num)
  have hN5 : (N : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 2 * x ^ (-(1 / 4 : ℝ)) :=
    rpow_neg_le_two_mul hx0 hNhalf (by norm_num) (by norm_num)
  have htail' : ∑' i : ℕ,
      Λ (i + (N + 1)) / Real.sqrt ((i + (N + 1) : ℕ) : ℝ)
        * min (((i + (N + 1) : ℕ) : ℝ) / x) (x / ((i + (N + 1) : ℕ) : ℝ))
      ≤ 4 * Real.sqrt x * Real.log x + 32 * Real.sqrt x := by
    refine htail.trans ?_
    calc 2 * (x * Real.log x) * (N : ℝ) ^ (-(1 / 2 : ℝ))
          + 4 * (4 * x ^ ((3 : ℝ) / 4)) * (N : ℝ) ^ (-(1 / 4 : ℝ))
        ≤ 2 * (x * Real.log x) * (2 * x ^ (-(1 / 2 : ℝ)))
          + 4 * (4 * x ^ ((3 : ℝ) / 4)) * (2 * x ^ (-(1 / 4 : ℝ))) := by
          gcongr
      _ = 4 * (x * x ^ (-(1 / 2 : ℝ))) * Real.log x
          + 32 * (x ^ ((3 : ℝ) / 4) * x ^ (-(1 / 4 : ℝ))) := by ring
      _ = 4 * Real.sqrt x * Real.log x + 32 * Real.sqrt x := by rw [ea, eb]
  have hA : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hLL2 : Real.log x ≤ Real.log (2 * x) := Real.log_le_log hx0 (by linarith)
  have hl2 : Real.log 2 ≤ Real.log (2 * x) := Real.log_le_log two_pos (by linarith)
  have hl2' : (0.6931 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  rw [← hsplit]
  have h1 : Real.sqrt x * Real.log x ≤ Real.sqrt x * Real.log (2 * x) := by
    exact mul_le_mul_of_nonneg_left hLL2 (by linarith)
  have h2 : 32 * Real.sqrt x ≤ 47 * (Real.sqrt x * Real.log (2 * x)) := by nlinarith
  nlinarith [hhead, htail']

/-- **The trivial bound for `D (x, t)`.** There is an absolute constant `C > 0` such that for every
`x ≥ 1` and every `t`, the series defining `D (x, t)` converges absolutely and
`‖D (x, t)‖ ≤ C x^{1/2} log (2 x)`.

Both halves are the previous theorem read through `‖Λ (n) n^{-1/2 - it} min {n / x, x / n}‖
= Λ (n) n^{-1/2} min {n / x, x / n}`, which holds because `|n^{-1/2 - it}| = n^{-1/2}` and the
weight is nonnegative; in particular the bound is uniform in `t`, as `t` does not occur in the
majorant. -/
@[zz_tag "lem_D_pointwise"]
theorem exists_summable_and_norm_weightedPrimeSum_le :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x → ∀ t : ℝ,
      Summable (fun n : ℕ => (Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) *
          ((min ((n : ℝ) / x) (x / (n : ℝ)) : ℝ) : ℂ)) ∧
        ‖weightedPrimeSum x t‖ ≤ C * Real.sqrt x * Real.log (2 * x) := by
  obtain ⟨C, hC, hbound⟩ := exists_tsum_vonMangoldt_div_sqrt_mul_min_le
  refine ⟨C, hC, fun x hx t => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hnorm : ∀ n : ℕ, ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) *
      ((min ((n : ℝ) / x) (x / (n : ℝ)) : ℝ) : ℂ)‖
      = Λ n / Real.sqrt n * min ((n : ℝ) / x) (x / (n : ℝ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp
    · have hmin : (0 : ℝ) ≤ min ((n : ℝ) / x) (x / (n : ℝ)) :=
        le_min (by positivity) (by positivity)
      rw [norm_mul, norm_div, Complex.norm_natCast_cpow_of_pos h, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Real.norm_of_nonneg hmin, Real.sqrt_eq_rpow]
      norm_num
  have hsn : Summable (fun n : ℕ => ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) *
      ((min ((n : ℝ) / x) (x / (n : ℝ)) : ℝ) : ℂ)‖) :=
    (summable_vonMangoldt_div_sqrt_mul_min hx0).congr fun n => (hnorm n).symm
  refine ⟨hsn.of_norm, ?_⟩
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  rw [tsum_congr hnorm]
  exact hbound x hx

end ZetaZeros
