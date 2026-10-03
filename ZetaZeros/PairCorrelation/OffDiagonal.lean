/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.PairCorrelation.MeanValue
public import ZetaZeros.PairCorrelation.TrivialBound
public import ZetaZeros.PairCorrelation.VonMangoldtSums

/-!
# The off-diagonal estimate for the weighted prime sum

The estimate

`∑_{m ≠ n} |aₘ| |aₙ| / |log m - log n| ≤ C x log² (2x)`,  `aₙ = Λ (n) n^{-1/2} min {n / x, x / n}`,

together with the summability of that family over `ℕ × ℕ` off the diagonal, and the resulting
mean square of the weighted prime sum, through the mean value theorem
`ZetaZeros.abs_integral_norm_sq_sub_le_tsum_div_abs_log_sub_log`.

## The estimate

The multiplicative gap `1 / |log m - log n| ≤ min {m, n} + 1` is useless here: it reduces the sum
to `(∑_n n |aₙ|) (∑_m |aₘ|)`, and `∑_n n |aₙ|` diverges, its tail terms being
`≍ x log n ⬝ n^{-1/2}`. The symmetric variant `min {m, n} ≤ √(mn)` reduces it to
`(∑_n Λ(n) min {n/x, x/n})²`, whose tail `x ∑_{n > x} Λ(n) / n` diverges too. The sum is split at
`n = 2m` instead.

*Far pairs*, `max ≥ 2 min`. Here `|log m - log n| ≥ log 2` and the contribution is at most
`(∑_n |aₙ|)² / log 2`, which is `≪ x log² (2x)` by the trivial bound for the weighted prime sum.

*Close pairs*, `max < 2 min`. Here `|log n - log m| ≥ (n - m) / n` and `√(n / m) ≤ 2`, so the
`n^{-1/2}` of the two coefficients is absorbed and `2ab ≤ a² + b²` leaves the harmonic kernel
`1 / |m - n|` weighted by `Λ(m)² min {m/x, x/m}²`. For each `m` the kernel sums to `3 (1 + log m)`
over the close range -- at most `m` values of `n` on either side of `m`, contributing
`1, 1/2, 1/3, …` in each direction -- so what remains is the log-weighted second moment
`∑_m Λ(m)² min {m/x, x/m}² (1 + log m) ≪ x log² (2x)`.

In that last sum the excess splits as `1 + log n ≤ (1 + log x) + max {0, log (n/x)}`. The first
part is `1 + log x` times the plain second moment `∑_n Λ(n)² min {n/x, x/n}² ≪ x log (2x)`. The
second is obtained from that same bound by *dyadic superposition*: above `2^k x` the `x`-weight is
`4^{-k}` times the `2^k x`-weight, so

`∑_k 4^{-k} ∑_n Λ(n)² min {n/(2^k x), 2^k x/n}²`

majorises `∑_n Λ(n)² min {n/x, x/n}² ⬝ log_2 (n/x)`, each `n` being reached by `log_2 (n/x)`
scales, while its cost `∑_k 4^{-k} C 2^k x log (2^{k+1} x) ≪ x log (2x)` is summable because the
weights `4^{-k}` beat the growth `2^k` of the scales.

## Main results

* `ZetaZeros.exists_summable_and_tsum_offDiagonal_le`: the off-diagonal estimate.
* `ZetaZeros.exists_abs_integral_norm_weightedPrimeSum_sq_sub_le`: the mean square
  `∫_0^T |D (x, t)|² dt = T log x + O (T + x log² (2x))`.
-/

@[expose] public section

namespace ZetaZeros

open Finset
open scoped ArithmeticFunction.vonMangoldt

/-! ### The weight -/

/-- The weight `min {n / x, x / n}` carried by the coefficients of the weighted prime sum. -/
private noncomputable def wgt (x : ℝ) (n : ℕ) : ℝ := min ((n : ℝ) / x) (x / n)

private lemma wgt_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 ≤ wgt x n :=
  le_min (by positivity) (div_nonneg hx.le (Nat.cast_nonneg n))

private lemma wgt_le_div {x : ℝ} (n : ℕ) : wgt x n ≤ x / n := min_le_right _ _

/-- Above `x` the weight is the decreasing branch `x / n`. -/
private lemma wgt_eq_div {x : ℝ} (hx : 0 < x) {n : ℕ} (h : x ≤ (n : ℝ)) : wgt x n = x / n := by
  have hn : (0 : ℝ) < n := lt_of_lt_of_le hx h
  refine min_eq_right ?_
  rw [div_le_div_iff₀ hn hx]
  nlinarith

/-! ### A summable majorant -/

private lemma log_le_six_mul_rpow (n : ℕ) : Real.log n ≤ 6 * (n : ℝ) ^ ((1 : ℝ) / 6) := by
  calc Real.log n ≤ (n : ℝ) ^ ((1 : ℝ) / 6) / (1 / 6) := Real.log_le_rpow_div (by positivity)
        (by norm_num)
    _ = 6 * (n : ℝ) ^ ((1 : ℝ) / 6) := by ring

private lemma rpow_sixth_cube (n : ℕ) : ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 = Real.sqrt n := by
  rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 6)) 3, ← Real.rpow_mul (Nat.cast_nonneg n),
    Real.sqrt_eq_rpow]
  norm_num

private lemma rpow_sixth_sq_le {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 ≤ Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 6)) 2, ← Real.rpow_mul (by positivity),
    Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)

/-- The majorant `Λ(n)² (1 + log n) ≤ 252 √n`, from `log n ≤ 6 n^{1/6}`. -/
private lemma vonMangoldt_sq_mul_one_add_log_le (n : ℕ) :
    Λ n ^ 2 * (1 + Real.log n) ≤ 252 * Real.sqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have h0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  set q : ℝ := (n : ℝ) ^ ((1 : ℝ) / 6) with hq
  have hq0 : 0 ≤ q := by positivity
  have h2 : Real.log n ≤ 6 * q := log_le_six_mul_rpow n
  have h3 : q ^ 3 = Real.sqrt n := rpow_sixth_cube n
  have h4 : q ^ 2 ≤ Real.sqrt n := rpow_sixth_sq_le hn
  have hsq : Λ n ^ 2 ≤ Real.log n ^ 2 := by nlinarith
  have hcube : Λ n ^ 2 * Real.log n ≤ Real.log n ^ 3 := by nlinarith
  have key : Real.log n ^ 2 ≤ 36 * q ^ 2 := by nlinarith
  have key3 : Real.log n ^ 3 ≤ 216 * q ^ 3 := by nlinarith
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

private lemma summable_sqrt_div_sq : Summable (fun n : ℕ ↦ Real.sqrt n / (n : ℝ) ^ 2) := by
  have h : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ ((3 : ℝ) / 2)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  refine h.congr fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have h0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub h0, one_div,
      ← Real.rpow_neg h0.le]
    norm_num

/-- Every weight of size at most `1 + log n` gives a summable series `Λ(n)² wgt² g`. -/
private lemma summable_vonMangoldt_sq_wgt_sq_mul {x : ℝ} (hx : 0 < x) (g : ℕ → ℝ)
    (hg0 : ∀ n, 0 ≤ g n) (hg1 : ∀ n, g n ≤ 1 + Real.log n) :
    Summable (fun n : ℕ ↦ Λ n ^ 2 * wgt x n ^ 2 * g n) := by
  refine Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hg0 n)) (fun n ↦ ?_)
    (summable_sqrt_div_sq.mul_left (252 * x ^ 2))
  have hw : wgt x n ^ 2 ≤ (x / n) ^ 2 := by
    have := wgt_le_div (x := x) n
    have := wgt_nonneg hx n
    nlinarith
  have hL : (0 : ℝ) ≤ Λ n ^ 2 := sq_nonneg _
  have hmain : Λ n ^ 2 * g n ≤ 252 * Real.sqrt n := by
    refine le_trans (mul_le_mul_of_nonneg_left (hg1 n) hL) ?_
    exact vonMangoldt_sq_mul_one_add_log_le n
  calc Λ n ^ 2 * wgt x n ^ 2 * g n = (Λ n ^ 2 * g n) * wgt x n ^ 2 := by ring
    _ ≤ (252 * Real.sqrt n) * (x / n) ^ 2 := by
        refine mul_le_mul hmain hw (sq_nonneg _) (by positivity)
    _ = 252 * x ^ 2 * (Real.sqrt n / (n : ℝ) ^ 2) := by
        rw [div_pow]; ring

private lemma log_natCast_nonneg (n : ℕ) : 0 ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hn)

private lemma summable_vonMangoldt_sq_wgt_sq {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ Λ n ^ 2 * wgt x n ^ 2) := by
  have h := summable_vonMangoldt_sq_wgt_sq_mul hx (fun _ ↦ 1) (fun _ ↦ zero_le_one)
    (fun n ↦ by linarith [log_natCast_nonneg n])
  exact h.congr fun n ↦ by ring

/-- The excess `max {0, log (n / x)}` is at most `1 + log n`, for `x ≥ 1`. -/
private lemma max_log_div_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    max 0 (Real.log ((n : ℝ) / x)) ≤ 1 + Real.log n := by
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hln : 0 ≤ Real.log n := log_natCast_nonneg n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [Real.log_div hn0 (by positivity)]
    rcases le_or_gt (Real.log n - Real.log x) 0 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h.le]; linarith

/-! ### The dyadic superposition -/

/-- The dyadic count: for `0 ≤ y < 2 ^ K x`, the excess `log (y / x)` is at most `log 2` times the
number of `k < K` with `2 ^ k x ≤ y`. The powers below the last one that fits all fit. -/
private lemma max_log_div_le_card {x : ℝ} (hx : 0 < x) :
    ∀ (K : ℕ) (y : ℝ), 0 ≤ y → y < 2 ^ K * x →
      max 0 (Real.log (y / x))
        ≤ Real.log 2 * (((range K).filter (fun k ↦ (2 : ℝ) ^ k * x ≤ y)).card : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  intro K
  induction K with
  | zero =>
      intro y hy0 hy
      rw [pow_zero, one_mul] at hy
      have h : Real.log (y / x) ≤ 0 :=
        Real.log_nonpos (by positivity) ((div_le_one hx).mpr hy.le)
      rw [max_eq_left h]
      simp
  | succ K ih =>
      intro y hy0 hy
      rcases lt_or_ge y (2 ^ K * x) with h | h
      · refine le_trans (ih y hy0 h) ?_
        have hcard : (((range K).filter (fun k ↦ (2 : ℝ) ^ k * x ≤ y)).card : ℝ)
            ≤ (((range (K + 1)).filter (fun k ↦ (2 : ℝ) ^ k * x ≤ y)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card
            (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (Nat.le_succ K)))
        exact mul_le_mul_of_nonneg_left hcard hl2.le
      · have hall : ∀ k ∈ range (K + 1), (2 : ℝ) ^ k * x ≤ y := by
          intro k hk
          have hkK : k ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hk)
          have : (2 : ℝ) ^ k ≤ 2 ^ K := pow_le_pow_right₀ one_le_two hkK
          nlinarith
        rw [Finset.filter_true_of_mem hall, card_range]
        have hy0' : 0 < y := lt_of_lt_of_le (by positivity) h
        have hlt : y / x < 2 ^ (K + 1) := by
          rw [div_lt_iff₀ hx]; linarith [hy]
        have hlog : Real.log (y / x) ≤ ((K : ℝ) + 1) * Real.log 2 := by
          have := Real.log_le_log (by positivity) hlt.le
          rw [Real.log_pow] at this
          push_cast at this
          linarith
        rw [max_le_iff]
        refine ⟨by positivity, ?_⟩
        push_cast
        linarith

/-! ### Two geometric sums -/

private lemma sum_half_pow_mul_succ (N : ℕ) :
    ∑ k ∈ range N, (1 / 2 : ℝ) ^ k * ((k : ℝ) + 1) = 4 - (2 * N + 4) * (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      ring

private lemma sum_half_pow (N : ℕ) :
    ∑ k ∈ range N, (1 / 2 : ℝ) ^ k = 2 - 2 * (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- `∑_{k < N} 2^{-k} ((k + 1) a + b) ≤ 4 a + 2 b` for `a, b ≥ 0`. -/
private lemma sum_half_pow_affine_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ) :
    ∑ k ∈ range N, (1 / 2 : ℝ) ^ k * (((k : ℝ) + 1) * a + b) ≤ 4 * a + 2 * b := by
  have hsplit : ∑ k ∈ range N, (1 / 2 : ℝ) ^ k * (((k : ℝ) + 1) * a + b)
      = (∑ k ∈ range N, (1 / 2 : ℝ) ^ k * ((k : ℝ) + 1)) * a
        + (∑ k ∈ range N, (1 / 2 : ℝ) ^ k) * b := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hsplit, sum_half_pow_mul_succ, sum_half_pow]
  have h1 : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
  have h2 : (0 : ℝ) ≤ (2 * N + 4) * (1 / 2 : ℝ) ^ N := by positivity
  nlinarith

/-! ### The log-weighted second moment -/

/-- Rescaling: above `2 ^ k x` the weight for `x` is `4 ^ {-k}` times the weight for `2 ^ k x`. -/
private lemma vonMangoldt_sq_wgt_sq_scale {x : ℝ} (hx : 0 < x) (k : ℕ) {n : ℕ}
    (h : (2 : ℝ) ^ k * x ≤ (n : ℝ)) :
    Λ n ^ 2 * wgt x n ^ 2 = (1 / 4 : ℝ) ^ k * (Λ n ^ 2 * wgt ((2 : ℝ) ^ k * x) n ^ 2) := by
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have hxn : x ≤ (n : ℝ) := by nlinarith
  have h4 : ((1 : ℝ) / 4) ^ k * ((2 : ℝ) ^ k) ^ 2 = 1 := by
    have h5 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
    rw [h5, div_pow, one_pow]
    field_simp
  rw [wgt_eq_div hx hxn, wgt_eq_div (by positivity) h]
  calc Λ n ^ 2 * (x / n) ^ 2
      = Λ n ^ 2 * (x / n) ^ 2 * (((1 : ℝ) / 4) ^ k * ((2 : ℝ) ^ k) ^ 2) := by rw [h4, mul_one]
    _ = (1 / 4 : ℝ) ^ k * (Λ n ^ 2 * ((2 : ℝ) ^ k * x / n) ^ 2) := by ring

/-- **The log-weighted second moment.** Superposing the bound
`∑_n Λ(n)² min {n/y, y/n}² ≤ C y log (2y)` over the dyadic scales `y = 2 ^ k x` with the weights
`4 ^ {-k}` produces the excess factor `log (n / x)`: above `2 ^ k x` the `k`-th summand is
`4 ^ {-k}` times the one for `x`, so the scales that reach `n` each contribute the same amount and
there are `log_2 (n / x)` of them, while the cost `∑_k 4 ^ {-k} C 2 ^ k x log (2 ^ {k + 1} x)` is
still `O (x log (2x))`. -/
private lemma tsum_vonMangoldt_sq_wgt_sq_mul_max_log_le {C : ℝ} (hC : 0 < C)
    (hb : ∀ y : ℝ, 1 ≤ y → (∑' n : ℕ, Λ n ^ 2 * wgt y n ^ 2) ≤ C * y * Real.log (2 * y))
    {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, Λ n ^ 2 * wgt x n ^ 2 * max 0 (Real.log ((n : ℝ) / x)))
      ≤ 6 * C * x * Real.log (2 * x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog2x : Real.log 2 ≤ Real.log (2 * x) := Real.log_le_log two_pos (by linarith)
  have hlogxle : Real.log x ≤ Real.log (2 * x) := Real.log_le_log hx0 (by linarith)
  have hlogk : ∀ k : ℕ,
      Real.log (2 * ((2 : ℝ) ^ k * x)) = ((k : ℝ) + 1) * Real.log 2 + Real.log x :=
    fun k ↦ by
      have h1 : (2 : ℝ) * ((2 : ℝ) ^ k * x) = 2 ^ (k + 1) * x := by ring
      rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast
      ring
  have hsum := summable_vonMangoldt_sq_wgt_sq_mul hx0 (fun n ↦ max 0 (Real.log ((n : ℝ) / x)))
    (fun _ ↦ le_max_left _ _) (fun n ↦ max_log_div_le hx n)
  refine hsum.tsum_le_of_sum_range_le fun N ↦ ?_
  have step1 : ∀ n ∈ range N, Λ n ^ 2 * wgt x n ^ 2 * max 0 (Real.log ((n : ℝ) / x))
      ≤ Real.log 2 *
        ∑ k ∈ range N, (if (2 : ℝ) ^ k * x ≤ (n : ℝ) then Λ n ^ 2 * wgt x n ^ 2 else 0) := by
    intro n hn
    have hnN : (n : ℝ) < 2 ^ N * x := by
      have h1 : (n : ℝ) < (N : ℝ) := by exact_mod_cast mem_range.mp hn
      have h2 : (N : ℝ) ≤ 2 ^ N := by
        have := Nat.lt_two_pow_self (n := N)
        have : (N : ℝ) < ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this
        linarith
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) N]
    have hcard := max_log_div_le_card hx0 N (n : ℝ) (Nat.cast_nonneg n) hnN
    have hsumif : ∑ k ∈ range N, (if (2 : ℝ) ^ k * x ≤ (n : ℝ) then Λ n ^ 2 * wgt x n ^ 2 else 0)
        = ((((range N).filter (fun k ↦ (2 : ℝ) ^ k * x ≤ (n : ℝ))).card : ℕ) : ℝ) *
            (Λ n ^ 2 * wgt x n ^ 2) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hnn : (0 : ℝ) ≤ Λ n ^ 2 * wgt x n ^ 2 := by positivity
    rw [hsumif]
    calc Λ n ^ 2 * wgt x n ^ 2 * max 0 (Real.log ((n : ℝ) / x))
        ≤ Λ n ^ 2 * wgt x n ^ 2 *
            (Real.log 2 * ((((range N).filter (fun k ↦ (2 : ℝ) ^ k * x ≤ (n : ℝ))).card : ℕ) : ℝ))
          := mul_le_mul_of_nonneg_left hcard hnn
      _ = Real.log 2 *
            (((((range N).filter (fun k ↦ (2 : ℝ) ^ k * x ≤ (n : ℝ))).card : ℕ) : ℝ) *
              (Λ n ^ 2 * wgt x n ^ 2)) := by ring
  have step3 : ∀ k ∈ range N,
      (∑ n ∈ range N, (if (2 : ℝ) ^ k * x ≤ (n : ℝ) then Λ n ^ 2 * wgt x n ^ 2 else 0))
        ≤ (1 / 4 : ℝ) ^ k * (C * ((2 : ℝ) ^ k * x) * Real.log (2 * ((2 : ℝ) ^ k * x))) := by
    intro k _
    have hxk : (1 : ℝ) ≤ (2 : ℝ) ^ k * x := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
      nlinarith
    have hxk0 : (0 : ℝ) < (2 : ℝ) ^ k * x := by positivity
    have hsk := summable_vonMangoldt_sq_wgt_sq hxk0
    calc (∑ n ∈ range N, (if (2 : ℝ) ^ k * x ≤ (n : ℝ) then Λ n ^ 2 * wgt x n ^ 2 else 0))
        ≤ ∑ n ∈ range N, (1 / 4 : ℝ) ^ k * (Λ n ^ 2 * wgt ((2 : ℝ) ^ k * x) n ^ 2) := by
          refine Finset.sum_le_sum fun n _ ↦ ?_
          split_ifs with hcase
          · exact le_of_eq (vonMangoldt_sq_wgt_sq_scale hx0 k hcase)
          · positivity
      _ = (1 / 4 : ℝ) ^ k * ∑ n ∈ range N, (Λ n ^ 2 * wgt ((2 : ℝ) ^ k * x) n ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / 4 : ℝ) ^ k * ∑' n : ℕ, (Λ n ^ 2 * wgt ((2 : ℝ) ^ k * x) n ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Summable.sum_le_tsum _ (fun n _ ↦ by positivity) hsk
      _ ≤ (1 / 4 : ℝ) ^ k * (C * ((2 : ℝ) ^ k * x) * Real.log (2 * ((2 : ℝ) ^ k * x))) := by
          exact mul_le_mul_of_nonneg_left (hb _ hxk) (by positivity)
  calc (∑ n ∈ range N, Λ n ^ 2 * wgt x n ^ 2 * max 0 (Real.log ((n : ℝ) / x)))
      ≤ ∑ n ∈ range N, Real.log 2 *
          ∑ k ∈ range N, (if (2 : ℝ) ^ k * x ≤ (n : ℝ) then Λ n ^ 2 * wgt x n ^ 2 else 0) :=
        Finset.sum_le_sum step1
    _ = Real.log 2 * ∑ k ∈ range N,
          ∑ n ∈ range N, (if (2 : ℝ) ^ k * x ≤ (n : ℝ) then Λ n ^ 2 * wgt x n ^ 2 else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ Real.log 2 * ∑ k ∈ range N,
          (1 / 4 : ℝ) ^ k * (C * ((2 : ℝ) ^ k * x) * Real.log (2 * ((2 : ℝ) ^ k * x))) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum step3) hl2.le
    _ = Real.log 2 * (C * x *
          ∑ k ∈ range N, (1 / 2 : ℝ) ^ k * (((k : ℝ) + 1) * Real.log 2 + Real.log x)) := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [hlogk k]
        have h24 : (1 / 4 : ℝ) ^ k * (2 : ℝ) ^ k = (1 / 2 : ℝ) ^ k := by
          rw [← mul_pow]
          norm_num
        calc (1 / 4 : ℝ) ^ k * (C * ((2 : ℝ) ^ k * x) * (((k : ℝ) + 1) * Real.log 2 + Real.log x))
            = ((1 / 4 : ℝ) ^ k * (2 : ℝ) ^ k) *
                (C * x * (((k : ℝ) + 1) * Real.log 2 + Real.log x)) := by ring
          _ = C * x * ((1 / 2 : ℝ) ^ k * (((k : ℝ) + 1) * Real.log 2 + Real.log x)) := by
              rw [h24]; ring
    _ ≤ Real.log 2 * (C * x * (4 * Real.log 2 + 2 * Real.log x)) := by
        refine mul_le_mul_of_nonneg_left ?_ hl2.le
        exact mul_le_mul_of_nonneg_left (sum_half_pow_affine_le hl2.le hlogx N) (by positivity)
    _ ≤ 6 * C * x * Real.log (2 * x) := by
        have h1 : 4 * Real.log 2 + 2 * Real.log x ≤ 6 * Real.log (2 * x) := by linarith
        have h2 : (0 : ℝ) ≤ C * x := by positivity
        have h3 : Real.log 2 * (C * x * (4 * Real.log 2 + 2 * Real.log x))
            ≤ 1 * (C * x * (6 * Real.log (2 * x))) := by
          refine mul_le_mul hl2' (mul_le_mul_of_nonneg_left h1 h2) ?_ (by norm_num)
          positivity
        nlinarith [h3]

private lemma one_add_log_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    1 + Real.log n ≤ (1 + Real.log x) + max 0 (Real.log ((n : ℝ) / x)) := by
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.log_nonneg hx]
  · have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [Real.log_div hn0 (by positivity)]
    rcases le_or_gt (Real.log n - Real.log x) 0 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h.le]; linarith

/-- **The log-weighted second moment.** There is an absolute `C > 0` with
`∑_n Λ(n)² min {n/x, x/n}² (1 + log n) ≤ C x log² (2x)` for every `x ≥ 1`.

The excess splits as `1 + log n ≤ (1 + log x) + max {0, log (n/x)}`: the first part is the plain
second moment, scaled by `1 + log x ≪ log (2x)`, and the second is the dyadic superposition. -/
private lemma exists_tsum_vonMangoldt_sq_wgt_sq_mul_one_add_log_le :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      (∑' n : ℕ, Λ n ^ 2 * wgt x n ^ 2 * (1 + Real.log n)) ≤ C * x * Real.log (2 * x) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_tsum_vonMangoldt_sq_mul_min_sq_le
  have hb' : ∀ y : ℝ, 1 ≤ y → (∑' n : ℕ, Λ n ^ 2 * wgt y n ^ 2) ≤ C * y * Real.log (2 * y) :=
    fun y hy ↦ hb y hy
  refine ⟨15 * C, by positivity, fun x hx ↦ ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl2 : Real.log 2 ≤ Real.log (2 * x) := Real.log_le_log two_pos (by linarith)
  have hone : 1 ≤ 2 * Real.log (2 * x) := by
    have := Real.log_two_gt_d9
    linarith
  have hlogxle : Real.log x ≤ Real.log (2 * x) := Real.log_le_log hx0 (by linarith)
  have hlog2x0 : 0 ≤ Real.log (2 * x) := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2)]
  have hs1 := summable_vonMangoldt_sq_wgt_sq_mul hx0 (fun n ↦ 1 + Real.log n)
    (fun n ↦ by linarith [log_natCast_nonneg n]) (fun _ ↦ le_rfl)
  have hs2 : Summable (fun n : ℕ ↦ Λ n ^ 2 * wgt x n ^ 2 * (1 + Real.log x)) :=
    (summable_vonMangoldt_sq_wgt_sq hx0).mul_right _
  have hs3 := summable_vonMangoldt_sq_wgt_sq_mul hx0 (fun n ↦ max 0 (Real.log ((n : ℝ) / x)))
    (fun _ ↦ le_max_left _ _) (fun n ↦ max_log_div_le hx n)
  have hsplit : (∑' n : ℕ, Λ n ^ 2 * wgt x n ^ 2 * (1 + Real.log n))
      ≤ (∑' n : ℕ, Λ n ^ 2 * wgt x n ^ 2 * (1 + Real.log x))
        + ∑' n : ℕ, Λ n ^ 2 * wgt x n ^ 2 * max 0 (Real.log ((n : ℝ) / x)) := by
    rw [← hs2.tsum_add hs3]
    refine hs1.tsum_le_tsum (fun n ↦ ?_) (hs2.add hs3)
    have hnn : (0 : ℝ) ≤ Λ n ^ 2 * wgt x n ^ 2 := by positivity
    calc Λ n ^ 2 * wgt x n ^ 2 * (1 + Real.log n)
        ≤ Λ n ^ 2 * wgt x n ^ 2 * ((1 + Real.log x) + max 0 (Real.log ((n : ℝ) / x))) :=
          mul_le_mul_of_nonneg_left (one_add_log_le hx n) hnn
      _ = _ := by ring
  have hpart1 : (∑' n : ℕ, Λ n ^ 2 * wgt x n ^ 2 * (1 + Real.log x))
      ≤ (1 + Real.log x) * (C * x * Real.log (2 * x)) := by
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hb' x hx) (by linarith) |>.trans_eq (by ring)
  have hpart2 := tsum_vonMangoldt_sq_wgt_sq_mul_max_log_le hC hb' hx
  have hCx : (0 : ℝ) ≤ C * x := by positivity
  have hmain : (1 + Real.log x) * (C * x * Real.log (2 * x)) + 6 * C * x * Real.log (2 * x)
      ≤ 15 * C * x * Real.log (2 * x) ^ 2 := by
    have h1 : 1 + Real.log x ≤ 3 * Real.log (2 * x) := by linarith
    have h2 : (1 + Real.log x) * (C * x * Real.log (2 * x))
        ≤ (3 * Real.log (2 * x)) * (C * x * Real.log (2 * x)) := by
      refine mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : 6 * C * x * Real.log (2 * x) ≤ 12 * C * x * Real.log (2 * x) ^ 2 := by
      nlinarith [mul_nonneg hCx hlog2x0]
    nlinarith
  linarith

/-! ### The close-pair kernel -/

/-- The kernel `1 / |m - n|`, cut off to the multiplicatively close pairs `max < 2 min`. It
vanishes on the diagonal, where the division is by zero. -/
private noncomputable def ker (m n : ℕ) : ℝ :=
  if max m n < 2 * min m n then 1 / |(m : ℝ) - (n : ℝ)| else 0

private lemma ker_nonneg (m n : ℕ) : 0 ≤ ker m n := by
  unfold ker
  split_ifs
  · positivity
  · exact le_rfl

private lemma ker_symm (m n : ℕ) : ker m n = ker n m := by
  unfold ker
  rw [max_comm, min_comm, abs_sub_comm]

private lemma ker_eq_zero_of_le {m n : ℕ} (h : 2 * m ≤ n) : ker m n = 0 := by
  have hnot : ¬ (max m n < 2 * min m n) := by omega
  unfold ker
  simp [hnot]

/-- Off the diagonal the kernel is exactly `1 / |m - n|` on close pairs, hence at most that. -/
private lemma ker_le_inv {m n : ℕ} : ker m n ≤ 1 / |(m : ℝ) - (n : ℝ)| := by
  unfold ker
  split_ifs
  · exact le_rfl
  · positivity

private lemma summable_ker (m : ℕ) : Summable (ker m) :=
  summable_of_ne_finset_zero (s := range (2 * m)) fun n hn ↦
    ker_eq_zero_of_le (by simpa using Nat.le_of_not_lt (fun h ↦ hn (mem_range.mpr h)))

/-- The harmonic bound: for each `m` the close pairs contribute `∑_n ker m n ≤ 3 (1 + log m)`.
There are at most `m` values of `n` below `m` and at most `m` above, and in each direction the
kernel is the harmonic sequence `1, 1/2, 1/3, …`. -/
private lemma tsum_ker_le (m : ℕ) : ∑' n : ℕ, ker m n ≤ 3 * (1 + Real.log m) := by
  have hharm : ∑ j ∈ range m, (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 + Real.log m := by
    have h := harmonic_le_one_add_log m
    have hcast : ((harmonic m : ℚ) : ℝ) = ∑ j ∈ range m, (1 : ℝ) / ((j : ℝ) + 1) := by
      simp [harmonic]
    rw [← hcast]
    exact_mod_cast h
  have hzero : ∀ n ∉ range (2 * m), ker m n = 0 := fun n hn ↦
    ker_eq_zero_of_le (by simpa using Nat.le_of_not_lt (fun h ↦ hn (mem_range.mpr h)))
  rw [tsum_eq_sum hzero]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hsplit : ∑ n ∈ range (2 * m), ker m n
      = (∑ n ∈ range m, ker m n) + ∑ n ∈ Ico m (2 * m), ker m n :=
    (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  have hA : ∑ n ∈ range m, ker m n ≤ ∑ j ∈ range m, (1 : ℝ) / ((j : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect (fun j ↦ (1 : ℝ) / ((j : ℝ) + 1)) m]
    refine Finset.sum_le_sum fun n hn ↦ ?_
    have hnm : n < m := mem_range.mp hn
    have hcast : ((m - 1 - n : ℕ) : ℝ) + 1 = (m : ℝ) - (n : ℝ) := by
      have h1 : m - 1 - n + (1 + n) = m := by omega
      have h2 : ((m - 1 - n : ℕ) : ℝ) + (1 + (n : ℝ)) = (m : ℝ) := by
        have := congrArg (fun k : ℕ ↦ (k : ℝ)) h1
        push_cast at this
        linarith
      linarith
    rw [hcast]
    refine le_trans ker_le_inv ?_
    rw [abs_of_nonneg (by
      have : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith)]
  have hB : ∑ n ∈ Ico m (2 * m), ker m n ≤ ∑ j ∈ range m, 2 * ((1 : ℝ) / ((j : ℝ) + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : 2 * m - m = m := by omega
    rw [hlen]
    refine Finset.sum_le_sum fun j hj ↦ ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [show m + 0 = m from rfl]
      have : ker m m = 0 := by
        unfold ker
        split_ifs
        · simp
        · rfl
      rw [this]
      positivity
    · refine le_trans ker_le_inv ?_
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
      have hcast : |(m : ℝ) - ((m + j : ℕ) : ℝ)| = (j : ℝ) := by
        push_cast
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [hcast]
      have key : 2 * ((1 : ℝ) / ((j : ℝ) + 1)) - 1 / (j : ℝ)
          = ((j : ℝ) - 1) / ((j : ℝ) * ((j : ℝ) + 1)) := by
        have hj2 : (j : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ ((j : ℝ) - 1) / ((j : ℝ) * ((j : ℝ) + 1)) :=
        div_nonneg (by linarith) (by positivity)
      linarith
  calc ∑ n ∈ range (2 * m), ker m n
      = (∑ n ∈ range m, ker m n) + ∑ n ∈ Ico m (2 * m), ker m n := hsplit
    _ ≤ (∑ j ∈ range m, (1 : ℝ) / ((j : ℝ) + 1))
          + ∑ j ∈ range m, 2 * ((1 : ℝ) / ((j : ℝ) + 1)) := add_le_add hA hB
    _ = 3 * ∑ j ∈ range m, (1 : ℝ) / ((j : ℝ) + 1) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 3 * (1 + Real.log m) := by linarith

/-! ### The pointwise majorant for a pair -/

/-- The coefficient `aₙ = Λ(n) n^{-1/2} min {n / x, x / n}` of the weighted prime sum. -/
private noncomputable def cf (x : ℝ) (n : ℕ) : ℝ := Λ n / Real.sqrt n * wgt x n

private lemma cf_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 ≤ cf x n :=
  mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (wgt_nonneg hx n)

private lemma cf_zero {x : ℝ} : cf x 0 = 0 := by
  unfold cf
  simp

private lemma cf_eq {x : ℝ} (n : ℕ) : cf x n = (Λ n * wgt x n) / Real.sqrt n := by
  unfold cf
  ring

/-- **The majorant for an ordered pair.** For `m < n` the reciprocal gap `1 / (log n - log m)` is
at most `1 / log 2` when `n ≥ 2m`, and at most `n / (n - m)` always; in the close range `n < 2m`
the factor `n` is absorbed by `√(n/m) ≤ 2` and the product of the coefficients by
`2ab ≤ a² + b²`. -/
private lemma cf_mul_cf_div_abs_log_le {x : ℝ} (hx : 1 ≤ x) {m n : ℕ} (hmn : m < n) :
    cf x m * cf x n / |Real.log n - Real.log m|
      ≤ cf x m * cf x n / Real.log 2
        + ((Λ m * wgt x m) ^ 2 + (Λ n * wgt x n) ^ 2) * ker m n := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hkn : 0 ≤ ker m n := ker_nonneg m n
  have ha : 0 ≤ Λ m * wgt x m := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (wgt_nonneg hx0 m)
  have hb : 0 ≤ Λ n * wgt x n := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (wgt_nonneg hx0 n)
  have hsq : 0 ≤ ((Λ m * wgt x m) ^ 2 + (Λ n * wgt x n) ^ 2) * ker m n := by positivity
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [cf_zero]
    simp only [zero_mul, zero_div, zero_add]
    exact hsq
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hprod : 0 ≤ cf x m * cf x n := mul_nonneg (cf_nonneg hx0 m) (cf_nonneg hx0 n)
  have hgap : 0 < Real.log n - Real.log m :=
    sub_pos.mpr (Real.log_lt_log (by linarith) hmnR)
  rw [abs_of_nonneg hgap.le]
  rcases le_or_gt (2 * (m : ℝ)) (n : ℝ) with hfar | hclose
  · have h2 : Real.log 2 ≤ Real.log n - Real.log m := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (m : ℝ)) hfar
      rw [Real.log_mul two_ne_zero (by positivity)] at h
      linarith
    have : cf x m * cf x n / (Real.log n - Real.log m) ≤ cf x m * cf x n / Real.log 2 := by
      gcongr
    linarith
  · have hclose' : n < 2 * m := by exact_mod_cast hclose
    have hkeq : ker m n = 1 / ((n : ℝ) - (m : ℝ)) := by
      have hlt : max m n < 2 * min m n := by omega
      have habs : |(m : ℝ) - (n : ℝ)| = (n : ℝ) - (m : ℝ) := by
        rw [abs_of_nonpos (by linarith : (m : ℝ) - (n : ℝ) ≤ 0)]; ring
      unfold ker
      simp [hlt, habs]
    have hlb : ((n : ℝ) - (m : ℝ)) / (n : ℝ) ≤ Real.log n - Real.log m := by
      calc ((n : ℝ) - (m : ℝ)) / (n : ℝ) = 1 - (m : ℝ) / (n : ℝ) := by field_simp
        _ = 1 - ((n : ℝ) / (m : ℝ))⁻¹ := by rw [inv_div]
        _ ≤ Real.log ((n : ℝ) / (m : ℝ)) :=
            Real.one_sub_inv_le_log_of_pos (by positivity)
        _ = Real.log n - Real.log m := Real.log_div (by positivity) (by positivity)
    have hdpos : 0 < ((n : ℝ) - (m : ℝ)) / (n : ℝ) := by
      apply div_pos <;> linarith
    have hsm : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
    have hsqn : Real.sqrt n ≤ 2 * Real.sqrt m := by
      calc Real.sqrt n ≤ Real.sqrt (4 * (m : ℝ)) := Real.sqrt_le_sqrt (by linarith)
        _ = 2 * Real.sqrt m := by
            rw [show (4 : ℝ) * (m : ℝ) = 2 ^ 2 * (m : ℝ) by ring,
              Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have hkey : cf x m * cf x n * (n : ℝ) ≤ (Λ m * wgt x m) ^ 2 + (Λ n * wgt x n) ^ 2 := by
      have hnsq : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
      have hratio : Real.sqrt n / Real.sqrt m ≤ 2 := by
        rw [div_le_iff₀ hsm]; linarith
      have hsn : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn0)
      have hrw : cf x m * cf x n * (n : ℝ)
          = (Λ m * wgt x m) * (Λ n * wgt x n) * (Real.sqrt n / Real.sqrt m) := by
        calc cf x m * cf x n * (n : ℝ)
            = (Λ m * wgt x m) / Real.sqrt m * ((Λ n * wgt x n) / Real.sqrt n) *
                (Real.sqrt n * Real.sqrt n) := by
              rw [cf_eq, cf_eq, Real.mul_self_sqrt hn0.le]
          _ = (Λ m * wgt x m) * (Λ n * wgt x n) * (Real.sqrt n / Real.sqrt m) := by
              field_simp
      rw [hrw]
      nlinarith [sq_nonneg (Λ m * wgt x m - Λ n * wgt x n), mul_nonneg ha hb,
        mul_nonneg (mul_nonneg ha hb) (by linarith : (0 : ℝ) ≤ 2 - Real.sqrt n / Real.sqrt m)]
    have hchain : cf x m * cf x n / (Real.log n - Real.log m)
        ≤ ((Λ m * wgt x m) ^ 2 + (Λ n * wgt x n) ^ 2) * ker m n := by
      calc cf x m * cf x n / (Real.log n - Real.log m)
          ≤ cf x m * cf x n / (((n : ℝ) - (m : ℝ)) / (n : ℝ)) := by gcongr
        _ = cf x m * cf x n * (n : ℝ) / ((n : ℝ) - (m : ℝ)) := by
            rw [div_div_eq_mul_div]
        _ ≤ ((Λ m * wgt x m) ^ 2 + (Λ n * wgt x n) ^ 2) / ((n : ℝ) - (m : ℝ)) := by
            gcongr
        _ = ((Λ m * wgt x m) ^ 2 + (Λ n * wgt x n) ^ 2) * ker m n := by
            rw [hkeq]; ring
    have : 0 ≤ cf x m * cf x n / Real.log 2 := by positivity
    linarith

/-- The majorant, symmetrised: `1 / log 2` times the product of the coefficients, plus the
close-pair kernel weighted by the squares at either end. -/
private lemma offDiag_le {x : ℝ} (hx : 1 ≤ x) (p : ℕ × ℕ) :
    (if p.1 = p.2 then 0 else cf x p.1 * cf x p.2 / |Real.log p.2 - Real.log p.1|)
      ≤ cf x p.1 * cf x p.2 / Real.log 2
        + ((Λ p.1 * wgt x p.1) ^ 2 * ker p.1 p.2 + (Λ p.2 * wgt x p.2) ^ 2 * ker p.1 p.2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨m, n⟩ := p
  have hnn : 0 ≤ cf x m * cf x n / Real.log 2 +
      ((Λ m * wgt x m) ^ 2 * ker m n + (Λ n * wgt x n) ^ 2 * ker m n) := by
    have h1 : 0 ≤ cf x m * cf x n := mul_nonneg (cf_nonneg hx0 m) (cf_nonneg hx0 n)
    have h2 := ker_nonneg m n
    have : 0 ≤ cf x m * cf x n / Real.log 2 := by positivity
    nlinarith [sq_nonneg (Λ m * wgt x m), sq_nonneg (Λ n * wgt x n)]
  split_ifs with h
  · exact hnn
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact (cf_mul_cf_div_abs_log_le hx hlt).trans_eq (by ring)
    · calc cf x m * cf x n / |Real.log n - Real.log m|
          = cf x n * cf x m / |Real.log m - Real.log n| := by rw [abs_sub_comm]; ring
        _ ≤ cf x n * cf x m / Real.log 2
              + ((Λ n * wgt x n) ^ 2 + (Λ m * wgt x m) ^ 2) * ker n m :=
            cf_mul_cf_div_abs_log_le hx hgt
        _ = _ := by rw [ker_symm n m]; ring

/-! ### Summing the majorant -/

private lemma summable_cf {x : ℝ} (hx : 0 < x) : Summable (cf x) :=
  summable_vonMangoldt_div_sqrt_mul_min hx

/-- The close-pair part of the majorant is summable over `ℕ × ℕ`, because for each `m` the kernel
sums to `3 (1 + log m)` and the resulting series is the log-weighted second moment. -/
private lemma ker_weighted_nonneg {x : ℝ} (m n : ℕ) : 0 ≤ (Λ m * wgt x m) ^ 2 * ker m n :=
  mul_nonneg (sq_nonneg _) (ker_nonneg _ _)

/-- For each `m` the close pairs contribute at most `3` times the log-weighted second moment
summand. -/
private lemma tsum_ker_weighted_inner {x : ℝ} (m : ℕ) :
    (∑' n : ℕ, (Λ m * wgt x m) ^ 2 * ker m n) ≤ 3 * (Λ m ^ 2 * wgt x m ^ 2 * (1 + Real.log m)) := by
  rw [tsum_mul_left, mul_pow]
  have h := tsum_ker_le m
  have hnn : (0 : ℝ) ≤ Λ m ^ 2 * wgt x m ^ 2 := by positivity
  nlinarith

private lemma summable_ker_weighted {x : ℝ} (hx : 0 < x) :
    Summable (fun p : ℕ × ℕ ↦ (Λ p.1 * wgt x p.1) ^ 2 * ker p.1 p.2) := by
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ (Λ p.1 * wgt x p.1) ^ 2 * ker p.1 p.2 :=
    fun p ↦ ker_weighted_nonneg p.1 p.2
  have hG := summable_vonMangoldt_sq_wgt_sq_mul hx (fun m ↦ 1 + Real.log m)
    (fun m ↦ by linarith [log_natCast_nonneg m]) (fun _ ↦ le_rfl)
  refine (summable_prod_of_nonneg hnn).mpr
    ⟨fun m ↦ (summable_ker m).mul_left ((Λ m * wgt x m) ^ 2), ?_⟩
  exact Summable.of_nonneg_of_le (fun m ↦ tsum_nonneg fun n ↦ hnn (m, n))
    (fun m ↦ tsum_ker_weighted_inner m) (hG.mul_left 3)

private lemma summable_ker_weighted' {x : ℝ} (hx : 0 < x) :
    Summable (fun p : ℕ × ℕ ↦ (Λ p.2 * wgt x p.2) ^ 2 * ker p.1 p.2) := by
  have h := (summable_ker_weighted hx).prod_symm
  refine h.congr fun p ↦ ?_
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [ker_symm p.2 p.1]

private lemma tsum_ker_weighted_symm :
    (∑' p : ℕ × ℕ, (Λ p.2 * wgt x p.2) ^ 2 * ker p.1 p.2)
      = ∑' p : ℕ × ℕ, (Λ p.1 * wgt x p.1) ^ 2 * ker p.1 p.2 := by
  have h := (Equiv.prodComm ℕ ℕ).tsum_eq
    (fun p : ℕ × ℕ ↦ (Λ p.1 * wgt x p.1) ^ 2 * ker p.1 p.2)
  simp only [Equiv.coe_prodComm, Prod.fst_swap, Prod.snd_swap] at h
  rw [← h]
  exact tsum_congr fun p ↦ by rw [ker_symm p.2 p.1]

/-- The close-pair part of the majorant is at most `3 G`, where `G` is the log-weighted second
moment. -/
private lemma tsum_ker_weighted_le {C : ℝ}
    (hG : ∀ y : ℝ, 1 ≤ y →
      (∑' n : ℕ, Λ n ^ 2 * wgt y n ^ 2 * (1 + Real.log n)) ≤ C * y * Real.log (2 * y) ^ 2)
    {x : ℝ} (hx : 1 ≤ x) :
    (∑' p : ℕ × ℕ, (Λ p.1 * wgt x p.1) ^ 2 * ker p.1 p.2)
      ≤ 3 * (C * x * Real.log (2 * x) ^ 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hGsum := summable_vonMangoldt_sq_wgt_sq_mul hx0 (fun m ↦ 1 + Real.log m)
    (fun m ↦ by linarith [log_natCast_nonneg m]) (fun _ ↦ le_rfl)
  rw [(summable_ker_weighted hx0).tsum_prod'
    (fun m ↦ (summable_ker m).mul_left ((Λ m * wgt x m) ^ 2))]
  have hsummable : Summable (fun m : ℕ ↦ ∑' n : ℕ, (Λ m * wgt x m) ^ 2 * ker m n) :=
    Summable.of_nonneg_of_le (fun m ↦ tsum_nonneg fun n ↦ ker_weighted_nonneg m n)
      (fun m ↦ tsum_ker_weighted_inner m) (hGsum.mul_left 3)
  calc (∑' m : ℕ, ∑' n : ℕ, (Λ m * wgt x m) ^ 2 * ker m n)
      ≤ ∑' m : ℕ, 3 * (Λ m ^ 2 * wgt x m ^ 2 * (1 + Real.log m)) :=
        hsummable.tsum_le_tsum (fun m ↦ tsum_ker_weighted_inner m) (hGsum.mul_left 3)
    _ = 3 * ∑' m : ℕ, Λ m ^ 2 * wgt x m ^ 2 * (1 + Real.log m) := tsum_mul_left
    _ ≤ 3 * (C * x * Real.log (2 * x) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (hG x hx) (by norm_num)

/-! ### The off-diagonal estimate -/

/-- The off-diagonal estimate, in terms of the coefficient `cf`. -/
private lemma exists_summable_and_tsum_offDiagonal_cf_le :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      Summable (fun p : ℕ × ℕ ↦ if p.1 = p.2 then 0 else
          cf x p.1 * cf x p.2 / |Real.log p.2 - Real.log p.1|) ∧
        (∑' p : ℕ × ℕ, if p.1 = p.2 then 0 else
            cf x p.1 * cf x p.2 / |Real.log p.2 - Real.log p.1|)
          ≤ C * x * Real.log (2 * x) ^ 2 := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_tsum_vonMangoldt_div_sqrt_mul_min_le
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_tsum_vonMangoldt_sq_wgt_sq_mul_one_add_log_le
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨C₁ ^ 2 / Real.log 2 + 6 * C₂, by positivity, fun x hx ↦ ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hFnn : ∀ p : ℕ × ℕ, 0 ≤ (if p.1 = p.2 then 0 else
      cf x p.1 * cf x p.2 / |Real.log p.2 - Real.log p.1|) := by
    intro p
    split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (cf_nonneg hx0 _) (cf_nonneg hx0 _)) (abs_nonneg _)
  have hM1 : Summable (fun p : ℕ × ℕ ↦ cf x p.1 * cf x p.2 / Real.log 2) :=
    (Summable.mul_of_nonneg (summable_cf hx0) (summable_cf hx0) (fun n ↦ cf_nonneg hx0 n)
      (fun n ↦ cf_nonneg hx0 n)).div_const _
  have hM23 : Summable (fun p : ℕ × ℕ ↦
      (Λ p.1 * wgt x p.1) ^ 2 * ker p.1 p.2 + (Λ p.2 * wgt x p.2) ^ 2 * ker p.1 p.2) :=
    (summable_ker_weighted hx0).add (summable_ker_weighted' hx0)
  have hMsum : Summable (fun p : ℕ × ℕ ↦ cf x p.1 * cf x p.2 / Real.log 2
      + ((Λ p.1 * wgt x p.1) ^ 2 * ker p.1 p.2 + (Λ p.2 * wgt x p.2) ^ 2 * ker p.1 p.2)) :=
    hM1.add hM23
  have hFsum : Summable (fun p : ℕ × ℕ ↦ if p.1 = p.2 then 0 else
      cf x p.1 * cf x p.2 / |Real.log p.2 - Real.log p.1|) :=
    Summable.of_nonneg_of_le hFnn (fun p ↦ offDiag_le hx p) hMsum
  refine ⟨hFsum, ?_⟩
  have hprod : (∑' p : ℕ × ℕ, cf x p.1 * cf x p.2 / Real.log 2)
      = (∑' n : ℕ, cf x n) ^ 2 / Real.log 2 := by
    rw [tsum_div_const]
    congr 1
    rw [← Summable.tsum_mul_tsum (summable_cf hx0) (summable_cf hx0)
      (Summable.mul_of_nonneg (summable_cf hx0) (summable_cf hx0) (fun n ↦ cf_nonneg hx0 n)
        (fun n ↦ cf_nonneg hx0 n))]
    ring
  have hsqx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hcfnn : 0 ≤ ∑' n : ℕ, cf x n := tsum_nonneg fun n ↦ cf_nonneg hx0 n
  have hcfle : (∑' n : ℕ, cf x n) ≤ C₁ * Real.sqrt x * Real.log (2 * x) := hb₁ x hx
  have hprodle : (∑' n : ℕ, cf x n) ^ 2 / Real.log 2
      ≤ C₁ ^ 2 / Real.log 2 * x * Real.log (2 * x) ^ 2 := by
    have hsq : (∑' n : ℕ, cf x n) ^ 2 ≤ C₁ ^ 2 * x * Real.log (2 * x) ^ 2 := by
      have hrhs : 0 ≤ C₁ * Real.sqrt x * Real.log (2 * x) := by positivity
      have h2 : (∑' n : ℕ, cf x n) ^ 2 ≤ (C₁ * Real.sqrt x * Real.log (2 * x)) ^ 2 := by
        nlinarith [hcfle]
      calc (∑' n : ℕ, cf x n) ^ 2 ≤ (C₁ * Real.sqrt x * Real.log (2 * x)) ^ 2 := h2
        _ = C₁ ^ 2 * x * Real.log (2 * x) ^ 2 := by rw [mul_pow, mul_pow, hsqx]
    calc (∑' n : ℕ, cf x n) ^ 2 / Real.log 2
        ≤ (C₁ ^ 2 * x * Real.log (2 * x) ^ 2) / Real.log 2 := by gcongr
      _ = C₁ ^ 2 / Real.log 2 * x * Real.log (2 * x) ^ 2 := by ring
  have hkerle := tsum_ker_weighted_le hb₂ hx
  have hMle : (∑' p : ℕ × ℕ, (cf x p.1 * cf x p.2 / Real.log 2
        + ((Λ p.1 * wgt x p.1) ^ 2 * ker p.1 p.2 + (Λ p.2 * wgt x p.2) ^ 2 * ker p.1 p.2)))
      ≤ (C₁ ^ 2 / Real.log 2 + 6 * C₂) * x * Real.log (2 * x) ^ 2 := by
    rw [hM1.tsum_add hM23, (summable_ker_weighted hx0).tsum_add (summable_ker_weighted' hx0),
      tsum_ker_weighted_symm, hprod]
    have hfin : (C₁ ^ 2 / Real.log 2 + 6 * C₂) * x * Real.log (2 * x) ^ 2
        = C₁ ^ 2 / Real.log 2 * x * Real.log (2 * x) ^ 2
          + 6 * C₂ * x * Real.log (2 * x) ^ 2 := by ring
    rw [hfin]
    linarith
  exact le_trans (hFsum.tsum_le_tsum (fun p ↦ offDiag_le hx p) hMsum) hMle

/-- **The off-diagonal estimate for the weighted prime sum.** There is an absolute constant `C > 0`
such that for every `x ≥ 1` the family indexed by the pairs `(m, n)` with `m ≠ n` of
`|aₘ| |aₙ| / |log m - log n|`, for `aₙ = Λ(n) n^{-1/2} min {n / x, x / n}`, is summable with
`∑_{m ≠ n} |aₘ| |aₙ| / |log m - log n| ≤ C x log² (2x)`. -/
@[zz_tag "lem_off_diagonal"]
theorem exists_summable_and_tsum_offDiagonal_le :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      Summable (fun p : ℕ × ℕ ↦ if p.1 = p.2 then 0 else
          Λ p.1 / Real.sqrt p.1 * min ((p.1 : ℝ) / x) (x / p.1) *
            (Λ p.2 / Real.sqrt p.2 * min ((p.2 : ℝ) / x) (x / p.2)) /
            |Real.log p.2 - Real.log p.1|) ∧
        (∑' p : ℕ × ℕ, if p.1 = p.2 then 0 else
            Λ p.1 / Real.sqrt p.1 * min ((p.1 : ℝ) / x) (x / p.1) *
              (Λ p.2 / Real.sqrt p.2 * min ((p.2 : ℝ) / x) (x / p.2)) /
              |Real.log p.2 - Real.log p.1|)
          ≤ C * x * Real.log (2 * x) ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_summable_and_tsum_offDiagonal_cf_le
  exact ⟨C, hC, fun x hx ↦ h x hx⟩

/-! ### The mean square of the weighted prime sum -/

/-- `D (x, t)` is the Dirichlet series with coefficients `aₙ`: the factor `n^{-1/2}` of `aₙ`
together with `n^{-it}` rebuilds `n^{-1/2 - it}`. -/
private lemma cf_mul_cpow {x : ℝ} (t : ℝ) (n : ℕ) :
    ((cf x n : ℝ) : ℂ) * (n : ℂ) ^ (-(t : ℂ) * Complex.I)
      = (Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * Complex.I) * ((wgt x n : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cf_zero]
  have hnne : n ≠ 0 := by omega
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hnne
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsqrtR : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
  have hsqrt : ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hnR]
    norm_num
  have hsplit : (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * Complex.I)
      = (n : ℂ) ^ ((1 : ℂ) / 2) * (n : ℂ) ^ ((t : ℂ) * Complex.I) :=
    Complex.cpow_add _ _ hn0
  have hneg : (n : ℂ) ^ (-(t : ℂ) * Complex.I) = ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ := by
    rw [show -(t : ℂ) * Complex.I = -((t : ℂ) * Complex.I) by ring, Complex.cpow_neg]
  have hne : (n : ℂ) ^ ((t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact hn0 h.1
  have hsne : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by
    simpa using Complex.ofReal_ne_zero.mpr (ne_of_gt hsqrtR)
  unfold cf
  push_cast
  rw [hneg, hsplit, ← hsqrt]
  field_simp

private lemma tsum_cf_cpow_eq {x : ℝ} (t : ℝ) :
    (∑' n : ℕ, ((cf x n : ℝ) : ℂ) * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) = weightedPrimeSum x t := by
  unfold weightedPrimeSum
  exact tsum_congr fun n ↦ cf_mul_cpow t n

private lemma norm_cf_ofReal {x : ℝ} (hx : 0 < x) (n : ℕ) : ‖((cf x n : ℝ) : ℂ)‖ = cf x n := by
  rw [Complex.norm_real, Real.norm_of_nonneg (cf_nonneg hx n)]

/-- **The mean square of the weighted prime sum.** There is an absolute constant `C > 0` such that
for all `x ≥ 1` and `T ≥ 3`,
`|∫_0^T |D (x, t)|² dt - T log x| ≤ C (T + x log² (2x))`.

The error `x log² (2x)` exceeds the `x log (2x)` of the sharp Montgomery--Vaughan mean value
theorem by one logarithm: for these coefficients the off-diagonal sum is `≍ x log² (2x)`. -/
@[zz_tag "lem_D_mean_square"]
theorem exists_abs_integral_norm_weightedPrimeSum_sq_sub_le :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x → ∀ T : ℝ, 3 ≤ T →
      |(∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2) - T * Real.log x|
        ≤ C * (T + x * Real.log (2 * x) ^ 2) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_summable_and_tsum_offDiagonal_cf_le
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_abs_tsum_vonMangoldt_sq_div_min_sq_sub_log_le
  refine ⟨2 * C₁ + C₂, by positivity, fun x hx T hT ↦ ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hnorm : ∀ n : ℕ, ‖((cf x n : ℝ) : ℂ)‖ = cf x n := fun n ↦ norm_cf_ofReal hx0 n
  have ha0 : ((cf x 0 : ℝ) : ℂ) = 0 := by rw [cf_zero]; norm_num
  have hsum : Summable (fun n : ℕ ↦ ‖((cf x n : ℝ) : ℂ)‖) :=
    (summable_cf hx0).congr fun n ↦ (hnorm n).symm
  obtain ⟨hoffsum, hoffle⟩ := hb₁ x hx
  have hoffeq : ∀ p : ℕ × ℕ,
      (if p.1 = p.2 then 0 else cf x p.1 * cf x p.2 / |Real.log p.2 - Real.log p.1|)
        = (if p.1 = p.2 then 0 else
            ‖((cf x p.1 : ℝ) : ℂ)‖ * ‖((cf x p.2 : ℝ) : ℂ)‖ / |Real.log p.2 - Real.log p.1|) := by
    intro p
    rw [hnorm, hnorm]
  have hoff : Summable (fun p : ℕ × ℕ ↦ if p.1 = p.2 then 0 else
      ‖((cf x p.1 : ℝ) : ℂ)‖ * ‖((cf x p.2 : ℝ) : ℂ)‖ / |Real.log p.2 - Real.log p.1|) :=
    hoffsum.congr hoffeq
  have key := abs_integral_norm_sq_sub_le_tsum_div_abs_log_sub_log
    (fun n ↦ ((cf x n : ℝ) : ℂ)) ha0 hsum hoff T
  simp only [tsum_cf_cpow_eq] at key
  have hdiag : (∑' n : ℕ, ‖((cf x n : ℝ) : ℂ)‖ ^ 2)
      = ∑' n : ℕ, Λ n ^ 2 / (n : ℝ) * wgt x n ^ 2 := by
    refine tsum_congr fun n ↦ ?_
    rw [hnorm]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [cf_zero]
      simp
    · unfold cf
      rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hdiagle : |(∑' n : ℕ, Λ n ^ 2 / (n : ℝ) * wgt x n ^ 2) - Real.log x| ≤ C₂ := hb₂ x hx
  have herr : (∑' p : ℕ × ℕ, if p.1 = p.2 then 0 else
      ‖((cf x p.1 : ℝ) : ℂ)‖ * ‖((cf x p.2 : ℝ) : ℂ)‖ / |Real.log p.2 - Real.log p.1|)
      ≤ C₁ * x * Real.log (2 * x) ^ 2 := by
    rw [← tsum_congr hoffeq]
    exact hoffle
  rw [hdiag] at key
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hTdiag : |T * (∑' n : ℕ, Λ n ^ 2 / (n : ℝ) * wgt x n ^ 2) - T * Real.log x| ≤ T * C₂ := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hT0]
    exact mul_le_mul_of_nonneg_left hdiagle hT0
  have htri : |(∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2) - T * Real.log x|
      ≤ 2 * (C₁ * x * Real.log (2 * x) ^ 2) + T * C₂ := by
    have hsplit : (∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2) - T * Real.log x
        = ((∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2)
            - T * ∑' n : ℕ, Λ n ^ 2 / (n : ℝ) * wgt x n ^ 2)
          + (T * (∑' n : ℕ, Λ n ^ 2 / (n : ℝ) * wgt x n ^ 2) - T * Real.log x) := by ring
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    have h2 : 2 * (∑' p : ℕ × ℕ, if p.1 = p.2 then 0 else
        ‖((cf x p.1 : ℝ) : ℂ)‖ * ‖((cf x p.2 : ℝ) : ℂ)‖ / |Real.log p.2 - Real.log p.1|)
        ≤ 2 * (C₁ * x * Real.log (2 * x) ^ 2) := by linarith [herr]
    linarith [key, hTdiag]
  have hLnn : (0 : ℝ) ≤ x * Real.log (2 * x) ^ 2 := by positivity
  nlinarith [htri, mul_nonneg hC₁.le hT0, mul_nonneg hC₂.le hLnn]

end ZetaZeros
