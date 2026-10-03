/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.PairCorrelation.MontgomeryExplicit
public import ZetaZeros.PairCorrelation.OffDiagonal
public import ZetaZeros.PairCorrelation.Elementary

/-!
# The evaluation of the mean square of the sum over zeros

Montgomery's explicit-formula lemma writes the zero side as `ℓ = -D + P + E`, where
`D (x, t)` is the weighted prime sum, `P (t) = log (|t| + 2) / x` and `E` is an error of size
`O (1/x + √x / (1 + t²))`.  Squaring and integrating over `[0, T]` therefore evaluates

`L (x, T) = ∫_0^T |ℓ (x, t)|² dt`

from the two mean squares `∫_0^T |D|² = T log x + O (T + x log² (2x))` and
`∫_0^T P² = x^{-2} T log² T + O (x^{-2} T log T)`, the remaining four contributions being errors.

## Main results

* `ZetaZeros.exists_abs_zeroSideMeanSquare_sub_sub_le`: assuming
  `ZetaZeros.LandauSymmetrisedFormula`, for `1 ≤ x ≤ T` and `T ≥ 3` the quantity
  `|L (x, T) - T log x - x^{-2} T log² T|` is `≪`
  `T + x log² T + x^{-2} T log T + x^{-1} T (log T)^{3/2} + (T/x)^{1/2} log² T`.

## Implementation notes

The cross term `∫_0^T |D| P` is bounded through the *pointwise* inequality
`2 a b ≤ λ a² + λ⁻¹ b²` at one explicit value of `λ`, which gives the Cauchy--Schwarz bound with
a single majorant and no `L²` inner product.

The choice of `λ` is where the shape of the error is decided.  The mean square of the weighted
prime sum has *two* parts, `∫_0^T |D|² ≪ T log T + x log² T`, and they want different values:
`λ = √(log T) / x` turns the first into `x^{-1} T (log T)^{3/2}` but the second into
`(log T)^{5/2}`, while `λ = √(T/x) / x` turns the second into `(T/x)^{1/2} log² T` but the first
into something larger.  Taking

`λ = min {√(log T), √(T/x)} / x`

serves both: each part is estimated with whichever of `λ ≤ √(log T)/x` and `λ ≤ √(T/x)/x` suits
it, and the reciprocal side uses `λ⁻¹ ≤ x/√(log T) + x/√(T/x)`, contributing one copy of each of
the two admissible shapes.  The term `(T/x)^{1/2} log² T` is not collapsed to `x^{-1} T log² T`
using `x ≤ T`: normalised by `T log T` the collapsed form does not tend to `0`.

The same device absorbs the part `1/x` of the error `E` into the cross term with `D`, while the
part `√x / (1 + t²)` is handled by the *trivial* pointwise bound `‖D (x, t)‖ ≪ √x log 2x`,
Cauchy--Schwarz there producing a term `(T x log T)^{1/2}` that none of the stated errors
dominates.

Both series are shown to be continuous in the height `t`, which is what makes the four integrands
interval integrable on `[0, T]`.  For the weighted prime sum the majorant of the series does not
involve `t` at all, so `continuous_tsum` applies directly; for the sum over zeros the majorant
`m_ρ / (1 + (t - im ρ)²)` does, and the comparison `1 + u² ≤ 2 (1 + t²) (1 + (t - u)²)` converts
it into the `t`-free majorant `2 (1 + M²) m_ρ / (1 + (im ρ)²)` on a window `|t| ≤ M`.
-/

public section

namespace ZetaZeros

open Complex MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

/-! ### Elementary arithmetic -/

/-- A product of two reals at least `1` is at least `1`. -/
private lemma one_le_mul_aux {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by nlinarith

/-- A real at least `1` has square at least `1`. -/
private lemma one_le_sq_aux {a : ℝ} (ha : 1 ≤ a) : 1 ≤ a ^ 2 := by nlinarith

/-- For `x ≥ 1` the square root does not exceed `x`. -/
private lemma sqrt_le_self_aux {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ x), Real.sqrt_nonneg x]

/-- Dividing a nonnegative quantity by something at least `1` does not increase it. -/
private lemma div_le_self_of_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) : a / b ≤ a := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- Three absolute values against three bounds. -/
private lemma abs_add_add_le {a b c u v w : ℝ} (h1 : |a| ≤ u) (h2 : |b| ≤ v) (h3 : |c| ≤ w) :
    |a + b + c| ≤ u + v + w := by
  calc |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
    _ ≤ |a| + |b| + |c| := by linarith only [abs_add_le a b]
    _ ≤ u + v + w := by linarith only [h1, h2, h3]

/-! ### Continuity in the height -/

/-- The arithmetic behind the term bound for the sum over zeros: a nonnegative weight `m`, a
numerator `2 v` with `v ≤ w`, and a denominator at least `3/4 (1 + s²)`, give
`m ⬝ 2 v / N ≤ 8/3 ⬝ w ⬝ m / (1 + s²)`. -/
private lemma mul_two_div_le_aux {m s N v w : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) (hvw : v ≤ w)
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

/-- The term of `ℓ (x, t)` at a zero `ρ`, with its multiplicity, has norm at most
`8/3 √x ⬝ m_ρ / (1 + (t - im ρ)²)`: the numerator has norm `2 x^{re ρ - 1/2} ≤ 2 √x` and the
denominator is at least `3/4 (1 + (t - im ρ)²)`. -/
private lemma norm_zeroSideTerm_le {x t : ℝ} (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ ∈ allZeros) :
    ‖(zeroMultiplicity ρ : ℂ) * (2 * (x : ℂ) ^ (ρ - 1 / 2 - (t : ℂ) * I)
        / (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2))‖
      ≤ 8 / 3 * Real.sqrt x * ((zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) := by
  obtain ⟨-, h0, h1⟩ := hρ
  have hx0 : (0 : ℝ) < x := by linarith
  have hre : (ρ - 1 / 2 - (t : ℂ) * I).re = ρ.re - 1 / 2 := by simp
  have hnorm : ‖(zeroMultiplicity ρ : ℂ) * (2 * (x : ℂ) ^ (ρ - 1 / 2 - (t : ℂ) * I)
      / (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2))‖
      = (zeroMultiplicity ρ : ℝ) * (2 * x ^ (ρ.re - 1 / 2)
        / ‖1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2‖) := by
    rw [norm_mul, Complex.norm_natCast, norm_div, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
    norm_num
  rw [hnorm]
  refine mul_two_div_le_aux (Nat.cast_nonneg _) (Real.rpow_nonneg hx0.le _) ?_ ?_
  · rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  · have hden := three_quarters_add_sq_le_norm_one_sub_sq h0 h1 t
    nlinarith [sq_nonneg (t - ρ.im)]

/-- On a window `|t| ≤ M` the Poisson weight at height `t` is at most `2 (1 + M²)` times the one
at height `0`: this follows from `1 + u² ≤ 2 (1 + t²) (1 + (t - u)²)`. -/
private lemma div_one_add_sq_le_of_mem_Icc {m t u M : ℝ} (hm : 0 ≤ m) (h1 : -M ≤ t)
    (h2 : t ≤ M) :
    m / (1 + (t - u) ^ 2) ≤ 2 * (1 + M ^ 2) * (m / (1 + u ^ 2)) := by
  have hd1 : (0 : ℝ) < 1 + (t - u) ^ 2 := by positivity
  have hd2 : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have ht2 : t ^ 2 ≤ M ^ 2 := by nlinarith
  have key : 1 + u ^ 2 ≤ 2 * (1 + M ^ 2) * (1 + (t - u) ^ 2) := by
    nlinarith [sq_nonneg (t - (u - t)), sq_nonneg (t * (u - t)), sq_nonneg (t - u),
      mul_nonneg (sub_nonneg.2 ht2) (sq_nonneg (t - u))]
  calc m / (1 + (t - u) ^ 2) ≤ 2 * (1 + M ^ 2) * m / (1 + u ^ 2) := by
        rw [div_le_div_iff₀ hd1 hd2]
        nlinarith [mul_le_mul_of_nonneg_left key hm]
    _ = 2 * (1 + M ^ 2) * (m / (1 + u ^ 2)) := by ring

/-- **The weighted prime sum is continuous in the height.** The majorant
`Λ (n) n^{-1/2} min {n / x, x / n}` of the series does not involve `t`, so the convergence is
uniform in `t` and `continuous_tsum` applies. -/
private lemma continuous_weightedPrimeSum_height {x : ℝ} (hx : 1 ≤ x) :
    Continuous fun t : ℝ => weightedPrimeSum x t := by
  have hx0 : (0 : ℝ) < x := by linarith
  simp only [weightedPrimeSum]
  refine continuous_tsum (u := fun n : ℕ => Λ n / Real.sqrt n * min ((n : ℝ) / x) (x / n))
    (fun n => ?_) (summable_vonMangoldt_div_sqrt_mul_min hx0) (fun n t => ?_)
  · rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.cast_zero, ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_div,
        zero_mul]
      exact continuous_const
    · have hnc : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      refine Continuous.mul (Continuous.div continuous_const ?_ ?_) continuous_const
      · exact (continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)).const_cpow (Or.inl hnc)
      · intro t
        exact fun h => hnc (((Complex.cpow_eq_zero_iff _ _).1 h).1)
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
      have hre : ((1 : ℂ) / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
      have hmin : (0 : ℝ) ≤ min ((n : ℝ) / x) (x / (n : ℝ)) :=
        le_min (by positivity) (by positivity)
      have hden : ‖((n : ℕ) : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I)‖ = Real.sqrt n := by
        rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hn0, hre, Real.sqrt_eq_rpow]
      rw [norm_mul, norm_div, hden, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        abs_of_nonneg hmin]

/-- **The sum over zeros is continuous in the height**, on every window `[-M, M]`. The majorant
`m_ρ / (1 + (t - im ρ)²)` does involve `t`, and is replaced on the window by the `t`-free
`2 (1 + M²) m_ρ / (1 + (im ρ)²)`, summable by the Poisson-weighted count at height `0`. -/
private lemma continuousOn_zeroSide_height {x : ℝ} (hx : 1 ≤ x) (M : ℝ) :
    ContinuousOn (fun t : ℝ => zeroSide x t) (Set.Icc (-M) M) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hx0.ne'
  obtain ⟨CP, -, hCP⟩ := exists_summable_poissonWeight_tsum_le
  have hsumu : Summable fun ρ : allZeros =>
      (zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + ((ρ : ℂ).im) ^ 2) := by
    refine ((hCP 0).1).congr fun ρ => ?_
    norm_num
  simp only [zeroSide]
  refine continuousOn_tsum (u := fun ρ : allZeros => 8 / 3 * Real.sqrt x *
      (2 * (1 + M ^ 2) * ((zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + ((ρ : ℂ).im) ^ 2))))
    (fun ρ => ?_) ((hsumu.mul_left _).mul_left _) (fun ρ t ht => ?_)
  · obtain ⟨-, h0, h1⟩ := ρ.2
    refine Continuous.continuousOn ?_
    refine continuous_const.mul (Continuous.div (continuous_const.mul ?_) ?_ ?_)
    · exact (continuous_const.sub
        (Complex.continuous_ofReal.mul continuous_const)).const_cpow (Or.inl hxne)
    · exact continuous_const.sub ((continuous_const.sub (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))).pow 2)
    · intro t hz
      have h := three_quarters_add_sq_le_norm_one_sub_sq h0 h1 t
      rw [hz, norm_zero] at h
      nlinarith [sq_nonneg (t - (ρ : ℂ).im)]
  · refine le_trans (norm_zeroSideTerm_le hx ρ.2) ?_
    exact mul_le_mul_of_nonneg_left
      (div_one_add_sq_le_of_mem_Icc (Nat.cast_nonneg _) ht.1 ht.2) (by positivity)

/-! ### The pointwise expansion of the square -/

/-- The expansion of `|ℓ|²` around `|D|² + P²`, written with `E = ℓ + D - P`: for complex `z`,
`D` and real `r`,
`| ‖z‖² - ‖D‖² - r² | ≤ 2 |r| ‖D‖ + ‖z + D - r‖ (2 (‖D‖ + |r|) + ‖z + D - r‖)`.

The first summand is the cross term of `D` with `r`, which is exact because `r` is real; the
second collects the three contributions of `E`. -/
private lemma abs_sq_norm_sub_sq_norm_sub_sq_le (z D : ℂ) (r : ℝ) :
    |‖z‖ ^ 2 - ‖D‖ ^ 2 - r ^ 2|
      ≤ 2 * |r| * ‖D‖ + ‖z + D - (r : ℂ)‖ * (2 * (‖D‖ + |r|) + ‖z + D - (r : ℂ)‖) := by
  set E := z + D - (r : ℂ) with hE
  set w := -D + (r : ℂ) with hw
  have hzw : z = w + E := by rw [hE, hw]; ring
  have hwsq : ‖w‖ ^ 2 = ‖D‖ ^ 2 - 2 * r * D.re + r ^ 2 := by
    rw [hw, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hwle : ‖w‖ ≤ ‖D‖ + |r| := by
    rw [hw]
    calc ‖-D + (r : ℂ)‖ ≤ ‖(-D : ℂ)‖ + ‖((r : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖D‖ + |r| := by simp
  have hzle : ‖z‖ ≤ ‖w‖ + ‖E‖ := by rw [hzw]; exact norm_add_le _ _
  have hsum : ‖z‖ + ‖w‖ ≤ 2 * (‖D‖ + |r|) + ‖E‖ := by linarith only [hwle, hzle]
  have h1 : |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ ‖E‖ * (2 * (‖D‖ + |r|) + ‖E‖) := by
    have hfac : ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) := by ring
    have habs : |‖z‖ - ‖w‖| ≤ ‖E‖ := by
      calc |‖z‖ - ‖w‖| ≤ ‖z - w‖ := abs_norm_sub_norm_le _ _
        _ = ‖E‖ := by rw [hE, hw]; ring_nf
    have hnn : (0 : ℝ) ≤ ‖z‖ + ‖w‖ := by positivity
    rw [hfac, abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul habs hsum hnn (norm_nonneg _)
  have h2 : |‖w‖ ^ 2 - ‖D‖ ^ 2 - r ^ 2| ≤ 2 * |r| * ‖D‖ := by
    rw [hwsq, show ‖D‖ ^ 2 - 2 * r * D.re + r ^ 2 - ‖D‖ ^ 2 - r ^ 2 = -(2 * r * D.re) by ring,
      abs_neg, abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm D) (by positivity)
  calc |‖z‖ ^ 2 - ‖D‖ ^ 2 - r ^ 2|
      ≤ |‖z‖ ^ 2 - ‖w‖ ^ 2| + |‖w‖ ^ 2 - ‖D‖ ^ 2 - r ^ 2| := by
        rw [show ‖z‖ ^ 2 - ‖D‖ ^ 2 - r ^ 2
            = ‖z‖ ^ 2 - ‖w‖ ^ 2 + (‖w‖ ^ 2 - ‖D‖ ^ 2 - r ^ 2) by ring]
        exact abs_add_le _ _
    _ ≤ 2 * |r| * ‖D‖ + ‖E‖ * (2 * (‖D‖ + |r|) + ‖E‖) := by linarith only [h1, h2]

/-- The weighted arithmetic--geometric mean inequality at a single `λ > 0`, which replaces
Cauchy--Schwarz for the cross terms. -/
private lemma two_mul_mul_le (a b l : ℝ) (hl : 0 < l) : 2 * a * b ≤ l * a ^ 2 + b ^ 2 / l := by
  have h : l * a ^ 2 + b ^ 2 / l - 2 * a * b = (l * a - b) ^ 2 / l := by field_simp; ring
  have := div_nonneg (sq_nonneg (l * a - b)) hl.le
  linarith

/-- The whole pointwise estimate, as arithmetic in abstract reals.  Here `nd = ‖D‖`,
`nE = ‖E‖ ≤ e1 + e2`, `r = P ≤ LTx`, `A` bounds `nd`, and `lam` is the parameter of the
arithmetic--geometric mean step.  The two parts `e1` and `e2` of the error are treated
differently: `e1` enters the cross term with `D` through the mean inequality, `e2` through the
trivial bound `A`. -/
private lemma pointwise_majorant_le {nd nE r lam e1 e2 A LTx : ℝ} (hnd : 0 ≤ nd)
    (hndA : nd ≤ A) (hnE : 0 ≤ nE) (hnEe : nE ≤ e1 + e2) (hr : 0 ≤ r) (hrLT : r ≤ LTx)
    (he2 : 0 ≤ e2) (hlam : 0 < lam) :
    2 * r * nd + nE * (2 * (nd + r) + nE)
      ≤ lam * nd ^ 2 + (2 * r ^ 2 / lam
        + ((2 * A * e2 + 2 * e2 * LTx + 2 * e2 ^ 2)
          + (2 * e1 ^ 2 / lam + 2 * e1 * LTx + 2 * e1 ^ 2))) := by
  have s1 : nE * nd ≤ (e1 + e2) * nd := mul_le_mul_of_nonneg_right hnEe hnd
  have s2 : nE * r ≤ (e1 + e2) * r := mul_le_mul_of_nonneg_right hnEe hr
  have s2b : (e1 + e2) * r ≤ (e1 + e2) * LTx :=
    mul_le_mul_of_nonneg_left hrLT (by linarith only [hnE, hnEe])
  have s3 : nE ^ 2 ≤ (e1 + e2) ^ 2 := by nlinarith only [hnE, hnEe]
  have s4 : 2 * nd * (r + e1) ≤ lam * nd ^ 2 + (r + e1) ^ 2 / lam :=
    two_mul_mul_le nd (r + e1) lam hlam
  have s5 : (r + e1) ^ 2 / lam ≤ 2 * r ^ 2 / lam + 2 * e1 ^ 2 / lam := by
    have h : 2 * r ^ 2 / lam + 2 * e1 ^ 2 / lam - (r + e1) ^ 2 / lam = (r - e1) ^ 2 / lam := by
      field_simp; ring
    have := div_nonneg (sq_nonneg (r - e1)) hlam.le
    linarith
  have s6 : e2 * nd ≤ e2 * A := mul_le_mul_of_nonneg_left hndA he2
  have s7 : (e1 + e2) ^ 2 ≤ 2 * e1 ^ 2 + 2 * e2 ^ 2 := by nlinarith only [sq_nonneg (e1 - e2)]
  linarith only [s1, s2, s2b, s3, s4, s5, s6, s7]

/-! ### The evaluation of the mean square -/

/-- **Evaluation of the mean square of the sum over zeros.** Assume Landau's explicit formula in
the symmetrised form `ZetaZeros.LandauSymmetrisedFormula`. Then for `1 ≤ x ≤ T` and `T ≥ 3`,

`|L (x, T) - T log x - x^{-2} T log² T|`
`  ≪ T + x log² T + x^{-2} T log T + x^{-1} T (log T)^{3/2} + (T/x)^{1/2} log² T`. -/
theorem exists_abs_zeroSideMeanSquare_sub_sub_le (hLandau : LandauSymmetrisedFormula) :
    ∃ C > 0, ∀ x T : ℝ, 1 ≤ x → x ≤ T → 3 ≤ T →
      |zeroSideMeanSquare x T - T * Real.log x - T * Real.log T ^ 2 / x ^ 2|
        ≤ C * (T + x * Real.log T ^ 2 + T * Real.log T / x ^ 2
            + T * Real.sqrt (Real.log T) ^ 3 / x + Real.sqrt (T / x) * Real.log T ^ 2) := by
  obtain ⟨CM, hCM0, hCMb⟩ :=
    exists_norm_zeroSide_add_weightedPrimeSum_sub_div_le_of_one_le hLandau
  obtain ⟨CD, hCD0, hDb⟩ := exists_abs_integral_norm_weightedPrimeSum_sq_sub_le
  obtain ⟨CP, hCP0, hPb⟩ := exists_summable_and_norm_weightedPrimeSum_le
  obtain ⟨CL, hCL0, hLb⟩ := exists_abs_integral_log_sq_sub_le
  have hCPCM : (0 : ℝ) ≤ CP * CM := (mul_pos hCP0 hCM0).le
  have hCMsq : (0 : ℝ) ≤ CM ^ 2 := sq_nonneg CM
  refine ⟨5 + 10 * CD + 5 * CL + 8 * CP * CM + 12 * CM + 10 * CM ^ 2,
    by linarith only [hCD0.le, hCL0.le, hCM0.le, hCPCM, hCMsq], ?_⟩
  set C := 5 + 10 * CD + 5 * CL + 8 * CP * CM + 12 * CM + 10 * CM ^ 2 with hCdef
  intro x T hx hxT hT
  simp only [zeroSideMeanSquare]
  have hx0 : (0 : ℝ) < x := by linarith
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hT0 : (0 : ℝ) < T := by linarith
  have hTnn : (0 : ℝ) ≤ T := hT0.le
  have hlogT1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith only [Real.exp_one_lt_d9, hT]
  have hlogT0 : (0 : ℝ) ≤ Real.log T := by linarith only [hlogT1]
  have hlogTsq1 : (1 : ℝ) ≤ Real.log T ^ 2 := one_le_sq_aux hlogT1
  have hTsq : T + 2 ≤ T ^ 2 := by
    nlinarith only [mul_nonneg (by linarith only [hT] : (0 : ℝ) ≤ T - 2)
      (by linarith only [hT] : (0 : ℝ) ≤ T + 1)]
  have h2xT : 2 * x ≤ T ^ 2 := by
    nlinarith only [mul_nonneg (by linarith only [hT] : (0 : ℝ) ≤ T - 2)
      (by linarith only [hT] : (0 : ℝ) ≤ T), hxT]
  have hlogsq : Real.log (T ^ 2) = 2 * Real.log T := by
    rw [Real.log_pow]; push_cast; ring
  have hlog2x : Real.log (2 * x) ≤ 2 * Real.log T := by
    rw [← hlogsq]; exact Real.log_le_log (by positivity) h2xT
  have hlogT2 : Real.log (T + 2) ≤ 2 * Real.log T := by
    rw [← hlogsq]; exact Real.log_le_log (by positivity) hTsq
  have hlog2x0 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith only [hx])
  have hLT0 : (0 : ℝ) ≤ Real.log (T + 2) := Real.log_nonneg (by linarith only [hT])
  have hlogxT : Real.log x ≤ Real.log T := Real.log_le_log hx0 hxT
  have hlog2xsq : Real.log (2 * x) ^ 2 ≤ 4 * Real.log T ^ 2 := by
    nlinarith only [mul_self_le_mul_self hlog2x0 hlog2x]
  have hxlogT : Real.log T ≤ x * Real.log T ^ 2 := by
    nlinarith only [hx, hlogT1, hlogTsq1, hlogT0]
  have hsqx0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqxle : Real.sqrt x ≤ x := sqrt_le_self_aux hx
  have hsqxsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hx21 : (1 : ℝ) ≤ x ^ 2 := one_le_sq_aux hx
  set s := Real.sqrt (Real.log T) with hsdef
  have hs2 : s ^ 2 = Real.log T := by rw [hsdef]; exact Real.sq_sqrt hlogT0
  have hsnn : (0 : ℝ) ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.2 hlogT1
  have hspos : (0 : ℝ) < s := by linarith only [hs1]
  set w := Real.sqrt (T / x) with hwdef
  have hTxone : (1 : ℝ) ≤ T / x := (one_le_div hx0).2 hxT
  have hw2 : w ^ 2 = T / x := by rw [hwdef]; exact Real.sq_sqrt (by linarith only [hTxone])
  have hwnn : (0 : ℝ) ≤ w := by rw [hwdef]; exact Real.sqrt_nonneg _
  have hw1 : (1 : ℝ) ≤ w := by rw [hwdef]; exact Real.one_le_sqrt.2 hTxone
  have hwpos : (0 : ℝ) < w := by linarith only [hw1]
  have hTw : T = w ^ 2 * x := by rw [hw2]; field_simp
  have hxs1 : (1 : ℝ) ≤ x * s := one_le_mul_aux hx hs1
  have hxw1 : (1 : ℝ) ≤ x * w := one_le_mul_aux hx hw1
  set lam := min s w / x with hlamdef
  have hmpos : (0 : ℝ) < min s w := lt_min hspos hwpos
  have hlam0 : (0 : ℝ) < lam := by rw [hlamdef]; exact div_pos hmpos hx0
  have hlams : lam ≤ s / x := by
    rw [hlamdef, div_le_div_iff₀ hx0 hx0]
    nlinarith only [min_le_left s w, hx0]
  have hlamw : lam ≤ w / x := by
    rw [hlamdef, div_le_div_iff₀ hx0 hx0]
    nlinarith only [min_le_right s w, hx0]
  have hlaminv : 1 / lam ≤ x / s + x / w := by
    have hxm : 1 / lam = x / min s w := by rw [hlamdef]; field_simp
    rw [hxm]
    rcases le_total s w with h | h
    · rw [min_eq_left h]
      linarith only [div_nonneg hx0.le hwnn]
    · rw [min_eq_right h]
      linarith only [div_nonneg hx0.le hsnn]
  have hDcont : Continuous fun t : ℝ => weightedPrimeSum x t :=
    continuous_weightedPrimeSum_height hx
  have hZcont : ContinuousOn (fun t : ℝ => zeroSide x t) (Set.uIcc 0 T) := by
    refine (continuousOn_zeroSide_height hx T).mono ?_
    rw [Set.uIcc_of_le hTnn]
    exact Set.Icc_subset_Icc (by linarith only [hTnn]) le_rfl
  have hlogcont : Continuous fun t : ℝ => Real.log (|t| + 2) := by
    refine Real.continuousOn_log.comp_continuous (by fun_prop) fun t => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    positivity
  have hiZ : IntervalIntegrable (fun t : ℝ => ‖zeroSide x t‖ ^ 2) volume 0 T :=
    ((continuous_norm.comp_continuousOn hZcont).pow 2).intervalIntegrable
  have hiD : IntervalIntegrable (fun t : ℝ => ‖weightedPrimeSum x t‖ ^ 2) volume 0 T := by
    apply Continuous.intervalIntegrable
    exact hDcont.norm.pow 2
  have hiP : IntervalIntegrable (fun t : ℝ => Real.log (|t| + 2) ^ 2 / x ^ 2) volume 0 T := by
    apply Continuous.intervalIntegrable
    exact (hlogcont.pow 2).div_const _
  have hiA : IntervalIntegrable (fun t : ℝ => 1 / (1 + t ^ 2)) volume 0 T := by
    apply Continuous.intervalIntegrable
    exact continuous_const.div (continuous_const.add (continuous_pow 2)) fun t => by positivity
  set LT := Real.log (T + 2) with hLTdef
  set A := CP * Real.sqrt x * Real.log (2 * x) with hAdef
  set K1 := 2 * A * CM * Real.sqrt x + 2 * CM * LT * Real.sqrt x / x + 2 * CM ^ 2 * x
    with hK1def
  set K2 := 2 * CM ^ 2 / x ^ 2 / lam + 2 * CM * LT / x ^ 2 + 2 * CM ^ 2 / x ^ 2 with hK2def
  have hptwise : ∀ t ∈ Set.Icc (0 : ℝ) T,
      |‖zeroSide x t‖ ^ 2 - ‖weightedPrimeSum x t‖ ^ 2 - Real.log (|t| + 2) ^ 2 / x ^ 2|
        ≤ lam * ‖weightedPrimeSum x t‖ ^ 2
          + (2 / lam * (Real.log (|t| + 2) ^ 2 / x ^ 2) + (K1 * (1 / (1 + t ^ 2)) + K2)) := by
    intro t ht
    obtain ⟨ht0, htT⟩ := ht
    have habst : |t| = t := abs_of_nonneg ht0
    have hd0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have hlogt0 : (0 : ℝ) ≤ Real.log (|t| + 2) :=
      Real.log_nonneg (by linarith only [abs_nonneg t])
    have hr0 : (0 : ℝ) ≤ Real.log (|t| + 2) / x := div_nonneg hlogt0 hx0.le
    have hrLT : Real.log (|t| + 2) / x ≤ LT / x := by
      have h1 : Real.log (|t| + 2) ≤ LT :=
        Real.log_le_log (by positivity) (by rw [habst]; linarith only [htT])
      rw [div_le_div_iff₀ hx0 hx0]
      nlinarith only [h1, hx0]
    have hnd : ‖weightedPrimeSum x t‖ ≤ A := by rw [hAdef]; exact (hPb x hx t).2
    have hnEe : ‖zeroSide x t + weightedPrimeSum x t
        - ((Real.log (|t| + 2) / x : ℝ) : ℂ)‖ ≤ CM / x + CM * Real.sqrt x / (1 + t ^ 2) :=
      (hCMb x hx t).trans (le_of_eq (by ring))
    have hkey := abs_sq_norm_sub_sq_norm_sub_sq_le (zeroSide x t) (weightedPrimeSum x t)
      (Real.log (|t| + 2) / x)
    rw [abs_of_nonneg hr0] at hkey
    have habs2 := pointwise_majorant_le (nd := ‖weightedPrimeSum x t‖)
      (nE := ‖zeroSide x t + weightedPrimeSum x t - ((Real.log (|t| + 2) / x : ℝ) : ℂ)‖)
      (r := Real.log (|t| + 2) / x) (lam := lam) (e1 := CM / x)
      (e2 := CM * Real.sqrt x / (1 + t ^ 2)) (A := A) (LTx := LT / x)
      (norm_nonneg _) hnd (norm_nonneg _) hnEe hr0 hrLT
      (div_nonneg (mul_nonneg hCM0.le hsqx0) hd0.le) hlam0
    have he2sq : (CM * Real.sqrt x / (1 + t ^ 2)) ^ 2 = CM ^ 2 * x / (1 + t ^ 2) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hx0.le]
    have hs8 : 2 * (CM * Real.sqrt x / (1 + t ^ 2)) ^ 2
        ≤ 2 * CM ^ 2 * x * (1 / (1 + t ^ 2)) := by
      rw [he2sq]
      have hid : 2 * CM ^ 2 * x * (1 / (1 + t ^ 2)) - 2 * (CM ^ 2 * x / (1 + t ^ 2) ^ 2)
          = 2 * CM ^ 2 * x * (t ^ 2 / (1 + t ^ 2) ^ 2) := by
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ 2 * CM ^ 2 * x * (t ^ 2 / (1 + t ^ 2) ^ 2) :=
        mul_nonneg (mul_nonneg (by positivity) hx0.le) (by positivity)
      linarith only [hid, hnn]
    have hK1eq : 2 * A * (CM * Real.sqrt x / (1 + t ^ 2))
        + 2 * (CM * Real.sqrt x / (1 + t ^ 2)) * (LT / x)
        + 2 * CM ^ 2 * x * (1 / (1 + t ^ 2)) = K1 * (1 / (1 + t ^ 2)) := by
      rw [hK1def]
      field_simp
    have hK2eq : 2 * (CM / x) ^ 2 / lam + 2 * (CM / x) * (LT / x) + 2 * (CM / x) ^ 2 = K2 := by
      rw [hK2def]
      field_simp
    have hbridge : 2 * (Real.log (|t| + 2) / x) ^ 2 / lam
        = 2 / lam * (Real.log (|t| + 2) / x) ^ 2 := by ring
    rw [← div_pow]
    linarith only [hkey, habs2, hs8, hK1eq, hK2eq, hbridge]
  have hIPval : (∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2 / x ^ 2)
      = (∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2 :=
    intervalIntegral.integral_div _ _
  have hiG : IntervalIntegrable (fun t : ℝ => lam * ‖weightedPrimeSum x t‖ ^ 2
      + (2 / lam * (Real.log (|t| + 2) ^ 2 / x ^ 2) + (K1 * (1 / (1 + t ^ 2)) + K2)))
      volume 0 T :=
    (hiD.const_mul _).add ((hiP.const_mul _).add ((hiA.const_mul _).add intervalIntegrable_const))
  have hGval : (∫ t in (0 : ℝ)..T, (lam * ‖weightedPrimeSum x t‖ ^ 2
      + (2 / lam * (Real.log (|t| + 2) ^ 2 / x ^ 2) + (K1 * (1 / (1 + t ^ 2)) + K2))))
      = lam * (∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2)
        + (2 / lam * ((∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2)
          + (K1 * (∫ t in (0 : ℝ)..T, 1 / (1 + t ^ 2)) + K2 * T)) := by
    rw [intervalIntegral.integral_add (hiD.const_mul _)
        ((hiP.const_mul _).add ((hiA.const_mul _).add intervalIntegrable_const)),
      intervalIntegral.integral_add (hiP.const_mul _)
        ((hiA.const_mul _).add intervalIntegrable_const),
      intervalIntegral.integral_add (hiA.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, hIPval]
    simp only [smul_eq_mul, sub_zero]
    ring
  have hsub : (∫ t in (0 : ℝ)..T, ‖zeroSide x t‖ ^ 2)
      - (∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2)
      - (∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2
      = ∫ t in (0 : ℝ)..T, (‖zeroSide x t‖ ^ 2 - ‖weightedPrimeSum x t‖ ^ 2
          - Real.log (|t| + 2) ^ 2 / x ^ 2) := by
    rw [intervalIntegral.integral_sub (hiZ.sub hiD) hiP, intervalIntegral.integral_sub hiZ hiD,
      hIPval]
  have hmain : |(∫ t in (0 : ℝ)..T, ‖zeroSide x t‖ ^ 2)
      - (∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2)
      - (∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2|
      ≤ lam * (∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2)
        + (2 / lam * ((∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2)
          + (K1 * (∫ t in (0 : ℝ)..T, 1 / (1 + t ^ 2)) + K2 * T)) := by
    rw [hsub, ← hGval]
    refine (intervalIntegral.abs_integral_le_integral_abs hTnn).trans ?_
    exact intervalIntegral.integral_mono_on hTnn ((hiZ.sub hiD).sub hiP).abs hiG hptwise
  have hIDle : (∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2)
      ≤ (1 + CD) * (T * Real.log T) + 4 * CD * (x * Real.log T ^ 2) := by
    have h := abs_le.1 (hDb x hx T hT)
    have h1 : T * Real.log x ≤ T * Real.log T := mul_le_mul_of_nonneg_left hlogxT hTnn
    have h3 : CD * (x * Real.log (2 * x) ^ 2) ≤ CD * (x * (4 * Real.log T ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog2xsq hx0.le) hCD0.le
    have h4 : CD * T ≤ CD * (T * Real.log T) := by
      refine mul_le_mul_of_nonneg_left ?_ hCD0.le
      nlinarith only [mul_nonneg hTnn (by linarith only [hlogT1] : (0 : ℝ) ≤ Real.log T - 1)]
    linarith only [h.2, h1, h3, h4]
  have hIL0 : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2 :=
    intervalIntegral.integral_nonneg hTnn fun u _ => by positivity
  have hILle : (∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2)
      ≤ (1 + CL) * (T * Real.log T ^ 2) := by
    have h := abs_le.1 (hLb T hT)
    have h1 : CL * (T * Real.log T) ≤ CL * (T * Real.log T ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hCL0.le
      nlinarith only [mul_nonneg hTnn
        (by nlinarith only [hlogT1] : (0 : ℝ) ≤ Real.log T ^ 2 - Real.log T)]
    linarith only [h.2, h1]
  have hIA2 : (∫ t in (0 : ℝ)..T, 1 / (1 + t ^ 2)) ≤ 2 := by
    rw [integral_one_div_one_add_sq]
    linarith only [Real.arctan_lt_pi_div_two T, Real.pi_le_four, Real.arctan_zero]
  have P1 : lam * (∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2)
      ≤ (1 + CD) * (T * s ^ 3 / x) + 4 * CD * (w * Real.log T ^ 2) := by
    have hp1 : (0 : ℝ) ≤ (1 + CD) * (T * Real.log T) :=
      mul_nonneg (by linarith only [hCD0.le]) (mul_nonneg hTnn hlogT0)
    have hp2 : (0 : ℝ) ≤ 4 * CD * (x * Real.log T ^ 2) :=
      mul_nonneg (by linarith only [hCD0.le]) (mul_nonneg hx0.le (sq_nonneg _))
    have h1 : lam * (∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2)
        ≤ lam * ((1 + CD) * (T * Real.log T) + 4 * CD * (x * Real.log T ^ 2)) :=
      mul_le_mul_of_nonneg_left hIDle hlam0.le
    have h2 : lam * ((1 + CD) * (T * Real.log T)) ≤ s / x * ((1 + CD) * (T * Real.log T)) :=
      mul_le_mul_of_nonneg_right hlams hp1
    have h3 : lam * (4 * CD * (x * Real.log T ^ 2)) ≤ w / x * (4 * CD * (x * Real.log T ^ 2)) :=
      mul_le_mul_of_nonneg_right hlamw hp2
    have e2 : s / x * ((1 + CD) * (T * Real.log T)) = (1 + CD) * (T * s ^ 3 / x) := by
      rw [← hs2]; ring
    have e3 : w / x * (4 * CD * (x * Real.log T ^ 2)) = 4 * CD * (w * Real.log T ^ 2) := by
      field_simp
    linarith only [h1, h2, h3, e2, e3]
  have P2 : 2 / lam * ((∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2)
      ≤ 2 * (1 + CL) * (T * s ^ 3 / x) + 2 * (1 + CL) * (w * Real.log T ^ 2) := by
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    have hILx : (0 : ℝ) ≤ (∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2 :=
      div_nonneg hIL0 hx2.le
    have h2lam : 2 / lam ≤ 2 * (x / s) + 2 * (x / w) := by
      rw [show (2 : ℝ) / lam = 2 * (1 / lam) by ring]
      linarith only [mul_le_mul_of_nonneg_left hlaminv (by norm_num : (0 : ℝ) ≤ 2)]
    have hco : (0 : ℝ) ≤ 2 * (x / s) + 2 * (x / w) := by
      linarith only [div_nonneg hx0.le hsnn, div_nonneg hx0.le hwnn]
    have h1 : 2 / lam * ((∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2)
        ≤ (2 * (x / s) + 2 * (x / w))
          * ((∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2) :=
      mul_le_mul_of_nonneg_right h2lam hILx
    have hstep : (∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2
        ≤ (1 + CL) * (T * Real.log T ^ 2) / x ^ 2 := by
      rw [div_le_div_iff₀ hx2 hx2]
      nlinarith only [mul_le_mul_of_nonneg_right hILle hx2.le]
    have h2 : (2 * (x / s) + 2 * (x / w))
        * ((∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2)
        ≤ (2 * (x / s) + 2 * (x / w)) * ((1 + CL) * (T * Real.log T ^ 2) / x ^ 2) :=
      mul_le_mul_of_nonneg_left hstep hco
    have e : (2 * (x / s) + 2 * (x / w)) * ((1 + CL) * (T * Real.log T ^ 2) / x ^ 2)
        = 2 * (1 + CL) * (T * s ^ 3 / x) + 2 * (1 + CL) * (w * Real.log T ^ 2) := by
      rw [← hs2, hTw]
      field_simp
    linarith only [h1, h2, e]
  have hK10 : (0 : ℝ) ≤ K1 := by
    rw [hK1def, hAdef]
    have h1 : (0 : ℝ) ≤ 2 * (CP * Real.sqrt x * Real.log (2 * x)) * CM * Real.sqrt x :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg hCP0.le hsqx0) hlog2x0)) hCM0.le) hsqx0
    have h2 : (0 : ℝ) ≤ 2 * CM * LT * Real.sqrt x / x :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCM0.le) hLT0) hsqx0) hx0.le
    have h3 : (0 : ℝ) ≤ 2 * CM ^ 2 * x :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg CM)) hx0.le
    linarith only [h1, h2, h3]
  have hK1le : K1 ≤ (4 * CP * CM + 4 * CM + 2 * CM ^ 2) * (x * Real.log T ^ 2) := by
    rw [hK1def, hAdef]
    have t1 : 2 * (CP * Real.sqrt x * Real.log (2 * x)) * CM * Real.sqrt x
        ≤ 4 * CP * CM * (x * Real.log T ^ 2) := by
      rw [show 2 * (CP * Real.sqrt x * Real.log (2 * x)) * CM * Real.sqrt x
          = 2 * CP * CM * (Real.sqrt x * Real.sqrt x) * Real.log (2 * x) by ring, hsqxsq]
      have a1 : 2 * CP * CM * x * Real.log (2 * x) ≤ 2 * CP * CM * x * (2 * Real.log T) :=
        mul_le_mul_of_nonneg_left hlog2x
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCP0.le) hCM0.le) hx0.le)
      have a2 : (0 : ℝ) ≤ 4 * CP * CM * x * (Real.log T ^ 2 - Real.log T) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCP0.le)
          hCM0.le) hx0.le) (by nlinarith only [hlogT1])
      nlinarith only [a1, a2]
    have hsxdx : Real.sqrt x / x ≤ 1 := by rw [div_le_one hx0]; exact hsqxle
    have t2 : 2 * CM * LT * Real.sqrt x / x ≤ 4 * CM * (x * Real.log T ^ 2) := by
      rw [show 2 * CM * LT * Real.sqrt x / x = 2 * CM * LT * (Real.sqrt x / x) by ring]
      have b1 : 2 * CM * LT * (Real.sqrt x / x) ≤ 2 * CM * LT * 1 :=
        mul_le_mul_of_nonneg_left hsxdx (mul_nonneg (mul_nonneg (by norm_num) hCM0.le) hLT0)
      have b2 : 2 * CM * LT ≤ 2 * CM * (2 * Real.log T) :=
        mul_le_mul_of_nonneg_left hlogT2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCM0.le)
      have b3 : (0 : ℝ) ≤ 4 * CM * (x * Real.log T ^ 2 - Real.log T) :=
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCM0.le)
          (by linarith only [hxlogT])
      nlinarith only [b1, b2, b3]
    have t3 : 2 * CM ^ 2 * x ≤ 2 * CM ^ 2 * (x * Real.log T ^ 2) := by
      have c1 : (0 : ℝ) ≤ 2 * CM ^ 2 * x * (Real.log T ^ 2 - 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg CM)) hx0.le)
          (by linarith only [hlogTsq1])
      nlinarith only [c1]
    linarith only [t1, t2, t3]
  have P3 : K1 * (∫ t in (0 : ℝ)..T, 1 / (1 + t ^ 2))
      ≤ (8 * CP * CM + 8 * CM + 4 * CM ^ 2) * (x * Real.log T ^ 2) := by
    have h1 : K1 * (∫ t in (0 : ℝ)..T, 1 / (1 + t ^ 2)) ≤ K1 * 2 :=
      mul_le_mul_of_nonneg_left hIA2 hK10
    linarith only [h1, hK1le]
  have P4 : K2 * T ≤ 4 * CM * (T * Real.log T / x ^ 2) + 6 * CM ^ 2 * T := by
    rw [hK2def]
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    have hTx2 : (0 : ℝ) ≤ T / x ^ 2 := div_nonneg hTnn hx2.le
    have hTx2le : T / x ^ 2 ≤ T := div_le_self_of_one_le hTnn hx21
    have hCM2T : (0 : ℝ) ≤ 2 * CM ^ 2 * T := mul_nonneg (by positivity) hTnn
    rw [show (2 * CM ^ 2 / x ^ 2 / lam + 2 * CM * LT / x ^ 2 + 2 * CM ^ 2 / x ^ 2) * T
        = 2 * CM ^ 2 * T / x ^ 2 * (1 / lam) + 2 * CM * LT * (T / x ^ 2)
          + 2 * CM ^ 2 * (T / x ^ 2) by field_simp]
    have h1 : 2 * CM ^ 2 * T / x ^ 2 * (1 / lam)
        ≤ 2 * CM ^ 2 * T / x ^ 2 * (x / s + x / w) :=
      mul_le_mul_of_nonneg_left hlaminv (by positivity)
    have e1 : 2 * CM ^ 2 * T / x ^ 2 * (x / s + x / w)
        = 2 * CM ^ 2 * T / (x * s) + 2 * CM ^ 2 * T / (x * w) := by
      field_simp
    have b1 : 2 * CM ^ 2 * T / (x * s) ≤ 2 * CM ^ 2 * T :=
      div_le_self_of_one_le hCM2T hxs1
    have b2 : 2 * CM ^ 2 * T / (x * w) ≤ 2 * CM ^ 2 * T :=
      div_le_self_of_one_le hCM2T hxw1
    have h2 : 2 * CM * LT * (T / x ^ 2) ≤ 4 * CM * (T * Real.log T / x ^ 2) := by
      rw [show 4 * CM * (T * Real.log T / x ^ 2)
          = 2 * CM * (2 * Real.log T) * (T / x ^ 2) by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogT2
        (by linarith only [hCM0.le] : (0 : ℝ) ≤ 2 * CM)) hTx2
    have h3 : 2 * CM ^ 2 * (T / x ^ 2) ≤ 2 * CM ^ 2 * T :=
      mul_le_mul_of_nonneg_left hTx2le (by positivity)
    linarith only [h1, e1, b1, b2, h2, h3]
  have P5 : |(∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2) - T * Real.log x|
      ≤ CD * T + 4 * CD * (x * Real.log T ^ 2) := by
    refine (hDb x hx T hT).trans ?_
    have h3 : CD * (x * Real.log (2 * x) ^ 2) ≤ CD * (x * (4 * Real.log T ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog2xsq hx0.le) hCD0.le
    nlinarith only [h3]
  have P6 : |(∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2 - T * Real.log T ^ 2 / x ^ 2|
      ≤ CL * (T * Real.log T / x ^ 2) := by
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    rw [show (∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2 - T * Real.log T ^ 2 / x ^ 2
        = ((∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) - T * Real.log T ^ 2) / x ^ 2 by ring,
      abs_div, abs_of_pos hx2,
      show CL * (T * Real.log T / x ^ 2) = CL * (T * Real.log T) / x ^ 2 by ring,
      div_le_div_iff₀ hx2 hx2]
    nlinarith only [mul_le_mul_of_nonneg_right (hLb T hT) hx2.le]
  rw [show (∫ t in (0 : ℝ)..T, ‖zeroSide x t‖ ^ 2) - T * Real.log x
      - T * Real.log T ^ 2 / x ^ 2
      = ((∫ t in (0 : ℝ)..T, ‖zeroSide x t‖ ^ 2)
          - (∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2)
          - (∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2)
        + ((∫ t in (0 : ℝ)..T, ‖weightedPrimeSum x t‖ ^ 2) - T * Real.log x)
        + ((∫ t in (0 : ℝ)..T, Real.log (|t| + 2) ^ 2) / x ^ 2
          - T * Real.log T ^ 2 / x ^ 2) by ring]
  refine (abs_add_add_le hmain P5 P6).trans ?_
  have hbxl : (0 : ℝ) ≤ x * Real.log T ^ 2 := mul_nonneg hx0.le (sq_nonneg _)
  have hbtl : (0 : ℝ) ≤ T * Real.log T / x ^ 2 :=
    div_nonneg (mul_nonneg hTnn hlogT0) (by positivity)
  have hbs : (0 : ℝ) ≤ T * s ^ 3 / x := div_nonneg (mul_nonneg hTnn (by positivity)) hx0.le
  have hbw : (0 : ℝ) ≤ w * Real.log T ^ 2 := mul_nonneg hwnn (sq_nonneg _)
  have q1 : (3 + CD + 2 * CL) * (T * s ^ 3 / x) ≤ C * (T * s ^ 3 / x) := by
    refine mul_le_mul_of_nonneg_right ?_ hbs
    rw [hCdef]; linarith only [hCD0.le, hCL0.le, hCM0.le, hCPCM, hCMsq]
  have q2 : (2 + 4 * CD + 2 * CL) * (w * Real.log T ^ 2) ≤ C * (w * Real.log T ^ 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hbw
    rw [hCdef]; linarith only [hCD0.le, hCL0.le, hCM0.le, hCPCM, hCMsq]
  have q3 : (8 * CP * CM + 8 * CM + 4 * CM ^ 2 + 4 * CD) * (x * Real.log T ^ 2)
      ≤ C * (x * Real.log T ^ 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hbxl
    rw [hCdef]; linarith only [hCD0.le, hCL0.le, hCM0.le, hCPCM, hCMsq]
  have q4 : (4 * CM + CL) * (T * Real.log T / x ^ 2) ≤ C * (T * Real.log T / x ^ 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hbtl
    rw [hCdef]; linarith only [hCD0.le, hCL0.le, hCM0.le, hCPCM, hCMsq]
  have q5 : (6 * CM ^ 2 + CD) * T ≤ C * T := by
    refine mul_le_mul_of_nonneg_right ?_ hTnn
    rw [hCdef]; linarith only [hCD0.le, hCL0.le, hCM0.le, hCPCM, hCMsq]
  linarith only [P1, P2, P3, P4, q1, q2, q3, q4, q5]

end ZetaZeros
