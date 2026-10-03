/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeNumberTheoremAnd.MediumPNT
public import ZetaZeros.Meta.Attr

/-!
# Sums of the von Mangoldt function

The prime number theorem with an explicit remainder, the second moment `∑_{n ≤ y} Λ(n)²`, and two
weighted forms of the second moment.

## Main results

* `ZetaZeros.exists_abs_psi_sub_self_le`: the prime number theorem with remainder, as an
  explicit bound `|ψ y - y| ≤ C y exp (-c (log y) ^ (1/10))` valid for *every* `y ≥ 2`.
* `ZetaZeros.exists_abs_vonMangoldt_sq_sum_sub_le`: the second moment
  `∑_{n ≤ y} Λ(n)² = y log y - y + O (y / log y)`.
* `ZetaZeros.exists_abs_tsum_vonMangoldt_sq_div_min_sq_sub_log_le`: the weighted second moment
  `∑_n (Λ(n)² / n) min {n/x, x/n}² = log x + O(1)`.
* `ZetaZeros.exists_tsum_vonMangoldt_sq_mul_min_sq_le`: the weight of the second moment,
  `∑_n Λ(n)² min {n/x, x/n}² ≤ C x log (2x)`.
-/

@[expose] public section

namespace ZetaZeros

open Filter Finset MeasureTheory Topology
open scoped Chebyshev ArithmeticFunction.vonMangoldt

/-! ### The prime number theorem with remainder -/

/-- The prime number theorem with remainder: there are absolute constants `c > 0` and `C > 0`
such that `|∑_{n ≤ y} Λ n - y| ≤ C * y * exp (-c * (log y) ^ (1/10))` for every real `y ≥ 2`,
the sum `∑_{n ≤ y} Λ n` being `Chebyshev.psi y`.

This is `PrimeNumberTheoremAnd.MediumPNT`,
`(ψ - id) =O[atTop] fun x ↦ x * exp (-c * (log x) ^ (1/10))`, with the threshold of the big-O
removed: on an initial segment `[2, y₀]` one has `|ψ y - y| ≤ ψ y₀ + y₀`, while
`y * exp (-c * (log y) ^ (1/10))` is bounded below there by `2 * exp (-c * (log y₀) ^ (1/10)) > 0`.
-/
@[zz_tag "lem_pnt_remainder"]
theorem exists_abs_psi_sub_self_le :
    ∃ c > 0, ∃ C > 0, ∀ y : ℝ, 2 ≤ y →
      |ψ y - y| ≤ C * y * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  refine ⟨c, hc, ?_⟩
  set g : ℝ → ℝ := fun y ↦ y * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) with hg
  have hgpos : ∀ y : ℝ, 2 ≤ y → 0 < g y := fun y hy ↦ by
    have : (0 : ℝ) < y := by linarith
    rw [hg]; positivity
  have hganti : ∀ y z : ℝ, 2 ≤ y → y ≤ z →
      2 * Real.exp (-c * Real.log z ^ ((1 : ℝ) / 10)) ≤ g y := by
    intro y z hy hyz
    have hly : (0 : ℝ) ≤ Real.log y := Real.log_nonneg (by linarith)
    have hlyz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyz
    have hrpow : Real.log y ^ ((1 : ℝ) / 10) ≤ Real.log z ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow hly hlyz (by norm_num)
    have hexp : Real.exp (-c * Real.log z ^ ((1 : ℝ) / 10))
        ≤ Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    calc 2 * Real.exp (-c * Real.log z ^ ((1 : ℝ) / 10))
        ≤ y * Real.exp (-c * Real.log z ^ ((1 : ℝ) / 10)) := by gcongr
      _ ≤ g y := by simp only [hg]; gcongr
  obtain ⟨C₀, hC₀⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp hC₀
  set Y : ℝ := max y₀ 2 with hY
  have hY2 : (2 : ℝ) ≤ Y := le_max_right _ _
  have htail : ∀ y : ℝ, Y ≤ y → |ψ y - y| ≤ C₀ * g y := by
    intro y hy
    have h := hy₀ y ((le_max_left y₀ 2).trans hy)
    have hgy : 0 < g y := hgpos y (hY2.trans hy)
    have hy0 : (0 : ℝ) ≤ y := by linarith [hY2.trans hy]
    simpa [Real.norm_eq_abs, abs_of_pos hgy, abs_of_nonneg hy0, hg] using h
  set δ : ℝ := 2 * Real.exp (-c * Real.log Y ^ ((1 : ℝ) / 10)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  set C₁ : ℝ := (ψ Y + Y) / δ with hC₁
  have hC₁nonneg : 0 ≤ C₁ := by
    have := Chebyshev.psi_nonneg Y
    rw [hC₁]
    positivity
  have hhead : ∀ y : ℝ, 2 ≤ y → y ≤ Y → |ψ y - y| ≤ C₁ * g y := by
    intro y hy hyY
    have hδg : δ ≤ g y := hganti y Y hy hyY
    have hpsi : ψ y ≤ ψ Y := Chebyshev.psi_mono hyY
    have hnn := Chebyshev.psi_nonneg y
    calc |ψ y - y| ≤ ψ Y + Y := by rw [abs_le]; constructor <;> linarith
      _ = C₁ * δ := by rw [hC₁]; field_simp
      _ ≤ C₁ * g y := by gcongr
  have hmax : (0 : ℝ) ≤ max C₀ C₁ := hC₁nonneg.trans (le_max_right _ _)
  refine ⟨max C₀ C₁ + 1, by linarith, fun y hy ↦ ?_⟩
  have hgy : 0 < g y := hgpos y hy
  have hstep : |ψ y - y| ≤ max C₀ C₁ * g y := by
    rcases le_total y Y with h | h
    · exact (hhead y hy h).trans (by gcongr; exact le_max_right _ _)
    · exact (htail y h).trans (by gcongr; exact le_max_left _ _)
  calc |ψ y - y| ≤ max C₀ C₁ * g y := hstep
    _ ≤ (max C₀ C₁ + 1) * g y := by nlinarith
    _ = (max C₀ C₁ + 1) * y * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) := by rw [hg]; ring

/-! ### From `exp (-c (log y) ^ (1/10))` to `1 / log² y`

The weaker estimate `ψ y = y + O (y / log² y)`. -/

/-- `u ^ 20 exp (-c u) ≤ (20 / c) ^ 20` for `u > 0`, by `1 + v ≤ exp v` applied at `v = c u / 20`:
`exp (c u) = (exp (c u / 20)) ^ 20 ≥ (c u / 20) ^ 20`. -/
private lemma pow_twenty_mul_exp_neg_le {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    u ^ 20 * Real.exp (-(c * u)) ≤ (20 / c) ^ 20 := by
  have hv : 0 < c * u / 20 := by positivity
  have hu' : u ≠ 0 := hu.ne'
  have hc' : c ≠ 0 := hc.ne'
  have key : (c * u / 20) ^ 20 ≤ Real.exp (c * u) := by
    calc (c * u / 20) ^ 20 ≤ (c * u / 20 + 1) ^ 20 := by gcongr; linarith
      _ ≤ (Real.exp (c * u / 20)) ^ 20 := by gcongr; exact Real.add_one_le_exp _
      _ = Real.exp (c * u) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
  have hpos : (0 : ℝ) < (c * u / 20) ^ 20 := by positivity
  calc u ^ 20 * Real.exp (-(c * u)) ≤ u ^ 20 * ((c * u / 20) ^ 20)⁻¹ := by
        rw [Real.exp_neg]
        gcongr
    _ = (20 / c) ^ 20 := by field_simp

/-- The exponential saving of the prime number theorem beats every power of `log`: for `y ≥ 2`,
`log² y * exp (-c (log y) ^ (1/10)) ≤ (20 / c) ^ 20`. Substituting `u = (log y) ^ (1/10)` turns
`log² y` into `u ^ 20`. -/
private lemma log_sq_mul_exp_le {c : ℝ} (hc : 0 < c) {y : ℝ} (hy : 2 ≤ y) :
    Real.log y ^ 2 * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) ≤ (20 / c) ^ 20 := by
  have hL : 0 < Real.log y := Real.log_pos (by linarith)
  have hupos : 0 < Real.log y ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hL _
  have hu20 : (Real.log y ^ ((1 : ℝ) / 10)) ^ 20 = Real.log y ^ 2 := by
    rw [← Real.rpow_natCast (Real.log y ^ ((1 : ℝ) / 10)) 20, ← Real.rpow_mul hL.le,
      ← Real.rpow_natCast (Real.log y) 2]
    norm_num
  rw [← hu20, neg_mul]
  exact pow_twenty_mul_exp_neg_le hc hupos

/-- The prime number theorem with remainder `O (y / log² y)`: there is an absolute `A > 0` with
`|ψ y - y| ≤ A * y / log² y` for every `y ≥ 2`. -/
private lemma exists_abs_psi_sub_self_le_div_log_sq :
    ∃ A > 0, ∀ y : ℝ, 2 ≤ y → |ψ y - y| ≤ A * y / Real.log y ^ 2 := by
  obtain ⟨c, hc, C, hC, h⟩ := exists_abs_psi_sub_self_le
  refine ⟨C * (20 / c) ^ 20, by positivity, fun y hy ↦ ?_⟩
  have hL : 0 < Real.log y := Real.log_pos (by linarith)
  have hy0 : (0 : ℝ) < y := by linarith
  rw [le_div_iff₀ (by positivity)]
  calc |ψ y - y| * Real.log y ^ 2
      ≤ (C * y * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10))) * Real.log y ^ 2 :=
        mul_le_mul_of_nonneg_right (h y hy) (by positivity)
    _ = C * y * (Real.log y ^ 2 * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10))) := by ring
    _ ≤ C * y * (20 / c) ^ 20 := by
        have := log_sq_mul_exp_le hc hy
        have hCy : (0 : ℝ) ≤ C * y := by positivity
        nlinarith
    _ = C * (20 / c) ^ 20 * y := by ring

/-- `log³ y ≤ 216 √y` for `y ≥ 2`, from `log y ≤ 6 y ^ (1/6)`. -/
private lemma log_cube_le_sqrt {y : ℝ} (hy : 2 ≤ y) :
    Real.log y ^ 3 ≤ 216 * Real.sqrt y := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hL : 0 < Real.log y := Real.log_pos (by linarith)
  have h6 : Real.log y ≤ 6 * y ^ ((1 : ℝ) / 6) := by
    have h := Real.log_le_rpow_div hy0 (by norm_num : (0 : ℝ) < 1 / 6)
    have : y ^ ((1 : ℝ) / 6) / (1 / 6) = 6 * y ^ ((1 : ℝ) / 6) := by ring
    linarith [this ▸ h]
  have hcube : (y ^ ((1 : ℝ) / 6)) ^ 3 = Real.sqrt y := by
    rw [← Real.rpow_natCast (y ^ ((1 : ℝ) / 6)) 3, ← Real.rpow_mul hy0, Real.sqrt_eq_rpow]
    norm_num
  calc Real.log y ^ 3 ≤ (6 * y ^ ((1 : ℝ) / 6)) ^ 3 := by gcongr
    _ = 216 * (y ^ ((1 : ℝ) / 6)) ^ 3 := by ring
    _ = 216 * Real.sqrt y := by rw [hcube]

/-- The same estimate for `θ`: `|θ y - y| ≤ A * y / log² y` for `y ≥ 2`. The passage from `ψ` to
`θ` costs `|ψ y - θ y| ≤ 2 √y log y`, which is `O (y / log² y)` because `log³ y ≤ 216 √y`. -/
private lemma exists_abs_theta_sub_self_le_div_log_sq :
    ∃ A > 0, ∀ y : ℝ, 2 ≤ y → |θ y - y| ≤ A * y / Real.log y ^ 2 := by
  obtain ⟨A, hA, h⟩ := exists_abs_psi_sub_self_le_div_log_sq
  refine ⟨A + 432, by positivity, fun y hy ↦ ?_⟩
  have hL : 0 < Real.log y := Real.log_pos (by linarith)
  have hy0 : (0 : ℝ) < y := by linarith
  have h1 := abs_le.mp (h y hy)
  have h2 := abs_le.mp (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : (1 : ℝ) ≤ y))
  have h3 : 2 * Real.sqrt y * Real.log y ≤ 432 * y / Real.log y ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
    have hs : (0 : ℝ) ≤ 2 * Real.sqrt y := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (log_cube_le_sqrt hy) hs, hsq]
  have hsplit : (A + 432) * y / Real.log y ^ 2
      = A * y / Real.log y ^ 2 + 432 * y / Real.log y ^ 2 := by ring
  rw [abs_le, hsplit]
  constructor <;> linarith

/-! ### The second moment `∑_{n ≤ y} Λ(n)²` -/

/-- The weight whose partial sums are `θ`: `log n` at a prime `n`, and `0` elsewhere. -/
private noncomputable def primeLog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

private lemma sum_primeLog (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLog k = θ t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  simp [primeLog]

private lemma sum_log_mul_primeLog (y : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, Real.log k * primeLog k
      = ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (if k.Prime then Λ k ^ 2 else 0) := by
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : k.Prime
  · simp [primeLog, hk, ArithmeticFunction.vonMangoldt_apply_prime hk, sq]
  · simp [primeLog, hk]

/-- Only prime powers contribute to `∑_{n ≤ y} Λ(n)²`, and the prime contribution is
`∑_{p ≤ y} (log p)²`; the rest is the proper prime powers. -/
private lemma sq_sum_eq_prime_part_add (y : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, Λ n ^ 2
      = (∑ k ∈ Finset.Icc 0 ⌊y⌋₊, Real.log k * primeLog k)
        + ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (if k.Prime then 0 else Λ k ^ 2) := by
  rw [sum_log_mul_primeLog, ← Finset.sum_add_distrib]
  have h : ∀ k ∈ Finset.Icc 0 ⌊y⌋₊,
      (if k.Prime then Λ k ^ 2 else 0) + (if k.Prime then 0 else Λ k ^ 2) = Λ k ^ 2 := by
    intro k _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp

/-- The proper prime powers contribute `O (√y log² y)` to the second moment: each term is at most
`log y` times the corresponding term of `ψ - θ`. -/
private lemma sum_not_prime_sq_le {y : ℝ} (hy : 2 ≤ y) :
    ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (if k.Prime then 0 else Λ k ^ 2)
      ≤ 2 * Real.sqrt y * Real.log y ^ 2 := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hL : 0 < Real.log y := Real.log_pos (by linarith)
  have hterm : ∀ k ∈ Finset.Icc 0 ⌊y⌋₊,
      (if k.Prime then 0 else Λ k ^ 2) ≤ Real.log y * (if k.Prime then 0 else Λ k) := by
    intro k hk
    have hky : (k : ℝ) ≤ y :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2).trans (Nat.floor_le hy0)
    split_ifs with h
    · simp
    · rcases Nat.eq_zero_or_pos k with rfl | hk1
      · simp
      · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
        have hlk : Real.log k ≤ Real.log y := Real.log_le_log hk0 hky
        have h1 : Λ k ≤ Real.log k := ArithmeticFunction.vonMangoldt_le_log
        have h2 : (0 : ℝ) ≤ Λ k := ArithmeticFunction.vonMangoldt_nonneg
        nlinarith
  have hdiff : ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (if k.Prime then 0 else Λ k) = ψ y - θ y := by
    rw [Chebyshev.psi_eq_sum_Icc, ← sum_primeLog, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : k.Prime
    · simp [primeLog, hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
    · simp [primeLog, hk]
  have hpt : ψ y - θ y ≤ 2 * Real.sqrt y * Real.log y :=
    Chebyshev.psi_sub_theta_le (by linarith)
  calc ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (if k.Prime then 0 else Λ k ^ 2)
      ≤ ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, Real.log y * (if k.Prime then 0 else Λ k) :=
        Finset.sum_le_sum hterm
    _ = Real.log y * (ψ y - θ y) := by rw [← Finset.mul_sum, hdiff]
    _ ≤ Real.log y * (2 * Real.sqrt y * Real.log y) := by gcongr
    _ = 2 * Real.sqrt y * Real.log y ^ 2 := by ring

/-- Partial summation for the prime part of the second moment:
`∑_{p ≤ y} (log p)² = θ y log y - ∫_2^y θ(t)/t dt`, i.e. Abel summation with the weight
`primeLog` (whose partial sums are `θ`) against `f = log`. -/
private lemma abel_prime_part (y : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, Real.log k * primeLog k
      = Real.log y * θ y - ∫ t in Set.Ioc (2 : ℝ) y, t⁻¹ * θ t := by
  have hc0 : primeLog 0 = 0 := by simp [primeLog]
  have hc1 : primeLog 1 = 0 := by simp [primeLog]
  have hf_diff : ∀ t ∈ Set.Icc (2 : ℝ) y, DifferentiableAt ℝ Real.log t := by
    intro t ht
    have h2 := (Set.mem_Icc.mp ht).1
    exact Real.differentiableAt_log (by intro h; rw [h] at h2; norm_num at h2)
  have hf_int : IntegrableOn (deriv Real.log) (Set.Icc (2 : ℝ) y) := by
    have hcont : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc (2 : ℝ) y) := by
      refine ContinuousOn.inv₀ continuousOn_id fun t ht ↦ ?_
      have := (Set.mem_Icc.mp ht).1
      exact ne_of_gt (by linarith)
    simpa [Real.deriv_log'] using hcont.integrableOn_compact isCompact_Icc
  simpa [Real.deriv_log', sum_primeLog] using
    sum_mul_eq_sub_integral_mul₁ primeLog hc0 hc1 y hf_diff hf_int

/-- `log y ≤ 4 √y` for `y ≥ 1`, hence `√y ≤ 4 y / log y`. -/
private lemma log_le_four_mul_sqrt {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ 4 * Real.sqrt y := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have h1 := Real.log_le_rpow_div hy0 (by norm_num : (0 : ℝ) < 1 / 4)
  have h2 : y ^ ((1 : ℝ) / 4) ≤ y ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  rw [Real.sqrt_eq_rpow]
  have h3 : y ^ ((1 : ℝ) / 4) / (1 / 4) = 4 * y ^ ((1 : ℝ) / 4) := by ring
  linarith [h3 ▸ h1]

/-- `∫_2^y θ(t)/t dt = y - 2 + O (y / log y)`: the main term comes from `θ(t) = t`, and the error
`|θ(t) - t| / t ≤ A / log² t` is integrated by splitting `[2, y]` at `√y` — below the split point
the integrand is `O(1)` over a range of length `≤ √y ≤ 4 y / log y`, above it the integrand is
`O(1 / log² y)` over a range of length `≤ y`. -/
private lemma exists_abs_integral_theta_div_sub_le :
    ∃ B > 0, ∀ y : ℝ, 2 ≤ y →
      |(∫ t in Set.Ioc (2 : ℝ) y, t⁻¹ * θ t) - (y - 2)| ≤ B * y / Real.log y := by
  obtain ⟨A, hA, hth⟩ := exists_abs_theta_sub_self_le_div_log_sq
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨4 * A / Real.log 2 ^ 2 + 4 * A / Real.log 2, by positivity, fun y hy ↦ ?_⟩
  have hy0 : (0 : ℝ) < y := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hL : 0 < Real.log y := Real.log_pos (by linarith)
  have hl2y : Real.log 2 ≤ Real.log y := Real.log_le_log two_pos hy
  have hgint : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Set.Icc (2 : ℝ) y) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine ContinuousOn.inv₀ continuousOn_id fun t ht ↦ ?_
    have := (Set.mem_Icc.mp ht).1
    exact ne_of_gt (by linarith)
  have hint1 : IntegrableOn (fun t : ℝ ↦ t⁻¹ * θ t) (Set.Icc (2 : ℝ) y) := by
    simpa [sum_primeLog] using
      integrableOn_mul_sum_Icc (m := 0) primeLog (by norm_num : (0 : ℝ) ≤ 2) hgint
  have hFint : IntegrableOn (fun t : ℝ ↦ t⁻¹ * θ t - 1) (Set.Icc (2 : ℝ) y) :=
    hint1.sub (continuousOn_const.integrableOn_compact isCompact_Icc)
  have hmain : (∫ t in Set.Ioc (2 : ℝ) y, t⁻¹ * θ t) - (y - 2)
      = ∫ t in Set.Ioc (2 : ℝ) y, (t⁻¹ * θ t - 1) := by
    rw [MeasureTheory.integral_sub (hint1.mono_set Set.Ioc_subset_Icc_self)
      ((continuousOn_const.integrableOn_compact (E := ℝ) isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self)]
    congr 1
    rw [← intervalIntegral.integral_of_le (by linarith : (2 : ℝ) ≤ y)]
    simp
  have hF : ∀ t ∈ Set.Icc (2 : ℝ) y, |t⁻¹ * θ t - 1| ≤ A / Real.log t ^ 2 := by
    intro t ht
    obtain ⟨ht2, hty⟩ := Set.mem_Icc.mp ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hLt : 0 < Real.log t := Real.log_pos (by linarith)
    have hbd := hth t ht2
    rw [show t⁻¹ * θ t - 1 = (θ t - t) / t by field_simp, abs_div, abs_of_pos ht0]
    calc |θ t - t| / t ≤ (A * t / Real.log t ^ 2) / t := by gcongr
      _ = A / Real.log t ^ 2 := by field_simp
  set s : ℝ := max (Real.sqrt y) 2 with hs
  have hs2 : (2 : ℝ) ≤ s := le_max_right _ _
  have hsqy : Real.sqrt y ≤ s := le_max_left _ _
  have hsy : s ≤ y := max_le (Real.sqrt_le_self_iff.mpr (Or.inr hy1)) hy
  have hsub2 : s - 2 ≤ Real.sqrt y := by
    rcases le_total (Real.sqrt y) 2 with h | h
    · rw [hs, max_eq_right h]; linarith [Real.sqrt_nonneg y]
    · rw [hs, max_eq_left h]; linarith
  have hlogs : Real.log y / 2 ≤ Real.log s := by
    rw [← Real.log_sqrt hy0.le]
    exact Real.log_le_log (Real.sqrt_pos.mpr hy0) hsqy
  have hii1 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ * θ t - 1) volume 2 s :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hs2).mpr
      (hFint.mono_set (Set.Icc_subset_Icc le_rfl hsy))
  have hii2 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ * θ t - 1) volume s y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hsy).mpr
      (hFint.mono_set (Set.Icc_subset_Icc hs2 le_rfl))
  have hb1 : ‖∫ t in (2 : ℝ)..s, (t⁻¹ * θ t - 1)‖ ≤ A / Real.log 2 ^ 2 * |s - 2| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    rw [Set.uIoc_of_le hs2, Set.mem_Ioc] at ht
    have hmem : t ∈ Set.Icc (2 : ℝ) y := Set.mem_Icc.mpr ⟨ht.1.le, ht.2.trans hsy⟩
    have hLt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    refine (hF t hmem).trans ?_
    have h2t : Real.log 2 ≤ Real.log t := Real.log_le_log two_pos ht.1.le
    rw [div_le_div_iff₀ (pow_pos hLt 2) (pow_pos hl2 2)]
    nlinarith [mul_le_mul h2t h2t hl2.le (hl2.le.trans h2t), hA.le]
  have hb2 : ‖∫ t in s..y, (t⁻¹ * θ t - 1)‖ ≤ 4 * A / Real.log y ^ 2 * |y - s| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    rw [Set.uIoc_of_le hsy, Set.mem_Ioc] at ht
    have hmem : t ∈ Set.Icc (2 : ℝ) y := Set.mem_Icc.mpr ⟨hs2.trans ht.1.le, ht.2⟩
    have hLt : 0 < Real.log t := Real.log_pos (by linarith [hs2, ht.1])
    refine (hF t hmem).trans ?_
    have hst : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) ht.1.le
    have hty2 : Real.log y / 2 ≤ Real.log t := hlogs.trans hst
    rw [div_le_div_iff₀ (pow_pos hLt 2) (pow_pos hL 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hty2)
      (by linarith : (0 : ℝ) ≤ Real.log t + Real.log y / 2), hA.le]
  have hsplit : (∫ t in (2 : ℝ)..y, (t⁻¹ * θ t - 1))
      = (∫ t in (2 : ℝ)..s, (t⁻¹ * θ t - 1)) + ∫ t in s..y, (t⁻¹ * θ t - 1) :=
    (intervalIntegral.integral_add_adjacent_intervals hii1 hii2).symm
  rw [hmain, ← intervalIntegral.integral_of_le (by linarith : (2 : ℝ) ≤ y), hsplit,
    le_div_iff₀ hL]
  simp only [Real.norm_eq_abs] at hb1 hb2
  have habs := (abs_add_le _ _).trans (add_le_add hb1 hb2)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - 2),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - s)] at habs
  have hsqL : Real.sqrt y * Real.log y ≤ 4 * y := by
    nlinarith [log_le_four_mul_sqrt hy1, Real.sq_sqrt hy0.le, Real.sqrt_nonneg y, hL.le]
  have hLne : Real.log y ≠ 0 := hL.ne'
  have k1 : A / Real.log 2 ^ 2 * (s - 2) * Real.log y ≤ 4 * A / Real.log 2 ^ 2 * y := by
    have h0 : (0 : ℝ) ≤ A / Real.log 2 ^ 2 := by positivity
    have hstep : (s - 2) * Real.log y ≤ 4 * y := by
      nlinarith [hsub2, hL.le, Real.sqrt_nonneg y, hsqL]
    calc A / Real.log 2 ^ 2 * (s - 2) * Real.log y
        = A / Real.log 2 ^ 2 * ((s - 2) * Real.log y) := by ring
      _ ≤ A / Real.log 2 ^ 2 * (4 * y) := mul_le_mul_of_nonneg_left hstep h0
      _ = 4 * A / Real.log 2 ^ 2 * y := by ring
  have k2 : 4 * A / Real.log y ^ 2 * (y - s) * Real.log y ≤ 4 * A / Real.log 2 * y := by
    have hys : (0 : ℝ) ≤ y - s := by linarith
    have hrw : 4 * A / Real.log y ^ 2 * (y - s) * Real.log y
        = 4 * A * (y - s) / Real.log y := by field_simp
    have hrw2 : 4 * A / Real.log 2 * y = 4 * A * y / Real.log 2 := by ring
    rw [hrw, hrw2, div_le_div_iff₀ hL hl2]
    have h1 : (y - s) * Real.log 2 ≤ y * Real.log y := by nlinarith [hl2.le, hl2y, hy0.le]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * A)]
  have hfinal : (4 * A / Real.log 2 ^ 2 + 4 * A / Real.log 2) * y
      = 4 * A / Real.log 2 ^ 2 * y + 4 * A / Real.log 2 * y := by ring
  rw [hfinal]
  nlinarith [habs, hL, k1, k2]

/-- **The second moment of the von Mangoldt function.** There is an absolute `C > 0` such that
`|∑_{n ≤ y} Λ(n)² - (y log y - y)| ≤ C * y / log y` for every `y ≥ 2`.

Only prime powers contribute, and `Λ(p^k)² = (log p)²`; the terms with `k ≥ 2` are
`O(√y log² y)` because each is at most `log y` times the corresponding term of `ψ - θ`, and
`|ψ - θ| ≤ 2 √y log y`. The primes are handled through `θ`: partial summation gives
`∑_{p ≤ y} (log p)² = θ(y) log y - ∫_2^y θ(u)/u du`, and `θ(y) = y + O(y / log² y)` turns this
into `y log y - y + O(y / log y)`. -/
@[zz_tag "lem_lambda_sq_count"]
theorem exists_abs_vonMangoldt_sq_sum_sub_le :
    ∃ C > 0, ∀ y : ℝ, 2 ≤ y →
      |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, Λ n ^ 2) - (y * Real.log y - y)| ≤ C * y / Real.log y := by
  obtain ⟨A, hA, hth⟩ := exists_abs_theta_sub_self_le_div_log_sq
  obtain ⟨B, hB, hI⟩ := exists_abs_integral_theta_div_sub_le
  refine ⟨2 + A + B + 432, by positivity, fun y hy ↦ ?_⟩
  have hy0 : (0 : ℝ) < y := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hL : 0 < Real.log y := Real.log_pos (by linarith)
  have hE1 : |Real.log y * (θ y - y)| ≤ A * y / Real.log y := by
    rw [abs_mul, abs_of_pos hL]
    calc Real.log y * |θ y - y|
        ≤ Real.log y * (A * y / Real.log y ^ 2) :=
          mul_le_mul_of_nonneg_left (hth y hy) hL.le
      _ = A * y / Real.log y := by field_simp
  have hlog_le : Real.log y ≤ y := by
    have := Real.log_le_sub_one_of_pos hy0
    linarith
  have hE2 : (2 : ℝ) ≤ 2 * y / Real.log y := by
    rw [le_div_iff₀ hL]; nlinarith
  have hE4 : 2 * Real.sqrt y * Real.log y ^ 2 ≤ 432 * y / Real.log y := by
    rw [le_div_iff₀ hL]
    nlinarith [mul_le_mul_of_nonneg_left (log_cube_le_sqrt hy)
      (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt y), Real.sq_sqrt hy0.le]
  have hD0 : 0 ≤ ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (if k.Prime then 0 else Λ k ^ 2) :=
    Finset.sum_nonneg fun k _ ↦ by split_ifs <;> positivity
  have hD := sum_not_prime_sq_le hy
  have hdecomp : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, Λ n ^ 2) - (y * Real.log y - y)
      = Real.log y * (θ y - y) - ((∫ t in Set.Ioc (2 : ℝ) y, t⁻¹ * θ t) - (y - 2)) + 2
        + ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (if k.Prime then 0 else Λ k ^ 2) := by
    rw [sq_sum_eq_prime_part_add y, abel_prime_part y]; ring
  have hfinal : (2 + A + B + 432) * y / Real.log y
      = A * y / Real.log y + B * y / Real.log y + 2 * y / Real.log y
        + 432 * y / Real.log y := by ring
  rw [hdecomp, hfinal, abs_le]
  have t1 := abs_le.mp hE1
  have t2 := abs_le.mp (hI y hy)
  constructor <;> linarith


/-! ### The second moment `M t = ∑_{n ≤ t} Λ(n)²` -/

private noncomputable def M (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Λ k ^ 2

private lemma M_def (t : ℝ) : M t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Λ k ^ 2 := rfl

private lemma M_eq_sum_Ioc (t : ℝ) : M t = ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, Λ k ^ 2 := by
  rw [M_def, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊t⌋₊)]
  simp

private lemma M_nonneg (t : ℝ) : 0 ≤ M t := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

private lemma M_eq_zero {t : ℝ} (ht : t < 2) : M t = 0 := by
  have hfl : ⌊t⌋₊ ≤ 1 := by
    rcases le_or_gt t 0 with h | h
    · simp [Nat.floor_of_nonpos h]
    · have h2 : ⌊t⌋₊ < 2 := (Nat.floor_lt h.le).mpr (by exact_mod_cast ht)
      omega
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hk1 : k ≤ 1 := (Finset.mem_Icc.mp hk).2.trans hfl
  interval_cases k <;> simp

/-! ### Elementary bounds -/

private lemma vonMangoldt_sq_le (n : ℕ) : Λ n ^ 2 ≤ 4 * (n : ℝ) := by
  have h0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : Real.log n ≤ 2 * Real.sqrt n := by
    have h := Real.log_le_rpow_div hn (by norm_num : (0 : ℝ) < 1 / 2)
    have he : (n : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * ((n : ℝ) ^ ((1 : ℝ) / 2)) := by ring
    rw [Real.sqrt_eq_rpow]
    linarith [he ▸ h]
  have h3 : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn
  nlinarith [Real.sqrt_nonneg ((n : ℝ))]

private lemma vonMangoldt_sq_div_cube_le (n : ℕ) : Λ n ^ 2 / (n : ℝ) ^ 3 ≤ 4 / (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [vonMangoldt_sq_le n, sq_nonneg ((n : ℝ)), hn0.le]

private lemma summable_four_div_sq : Summable (fun n : ℕ ↦ 4 / (n : ℝ) ^ 2) := by
  have h : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine (h.mul_left 4).congr fun n ↦ ?_
  rw [mul_one_div]

private lemma M_natCast_le {N : ℕ} (hN : 1 ≤ N) : M (N : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [M_def, Nat.floor_natCast]
  have h : ∑ k ∈ Finset.Icc 0 N, Λ k ^ 2 ≤ ∑ _k ∈ Finset.Icc 0 N, 4 * (N : ℝ) := by
    refine Finset.sum_le_sum fun k hk ↦ (vonMangoldt_sq_le k).trans ?_
    have : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    linarith
  have hcard : ∑ _k ∈ Finset.Icc 0 N, 4 * (N : ℝ) = ((N : ℝ) + 1) * (4 * (N : ℝ)) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    push_cast
    ring
  rw [hcard] at h
  nlinarith

/-! ### Integrability -/

private lemma integrableOn_M {a b : ℝ} (ha : 0 ≤ a) : IntegrableOn M (Set.Icc a b) := by
  have h1 : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Icc a b) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have h2 := integrableOn_mul_sum_Icc (m := 0) (fun n : ℕ ↦ Λ n ^ 2) ha h1
  exact h2.congr_fun (fun t _ ↦ one_mul _) measurableSet_Icc

private lemma intervalIntegrable_M {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable M volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (integrableOn_M ha)

private lemma continuousOn_L {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ ↦ t * Real.log t - t) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ {(0 : ℝ)}ᶜ := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (lt_of_lt_of_le ha ht.1)
  exact (continuousOn_id.mul (Real.continuousOn_log.mono hsub)).sub continuousOn_id

private lemma intervalIntegrable_L {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ t * Real.log t - t) volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    ((continuousOn_L ha).integrableOn_compact isCompact_Icc)

private lemma continuousOn_inv_pow {a b : ℝ} (ha : 0 < a) (k : ℕ) :
    ContinuousOn (fun t : ℝ ↦ ((t : ℝ) ^ k)⁻¹) (Set.Icc a b) := by
  refine ContinuousOn.inv₀ (by fun_prop) fun t ht ↦ ?_
  exact pow_ne_zero k (ne_of_gt (lt_of_lt_of_le ha ht.1))

private lemma intervalIntegrable_M_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ M t / t ^ 4) volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ?_
  simp only [div_eq_mul_inv]
  exact (integrableOn_M ha.le).mul_continuousOn (continuousOn_inv_pow ha 4) isCompact_Icc

private lemma intervalIntegrable_L_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ (t * Real.log t - t) / t ^ 4) volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ?_
  simp only [div_eq_mul_inv]
  exact ((continuousOn_L ha).integrableOn_compact isCompact_Icc).mul_continuousOn
    (continuousOn_inv_pow ha 4) isCompact_Icc

private lemma intervalIntegrable_err_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ (M t - (t * Real.log t - t)) / t ^ 4) volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ?_
  simp only [div_eq_mul_inv]
  exact ((integrableOn_M ha.le).sub
    ((continuousOn_L ha).integrableOn_compact isCompact_Icc)).mul_continuousOn
      (continuousOn_inv_pow ha 4) isCompact_Icc

private lemma intervalIntegrable_const_div_cube {K a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ K / t ^ 3) volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ?_
  simp only [div_eq_mul_inv]
  exact ((continuousOn_const (c := K)).integrableOn_compact isCompact_Icc).mul_continuousOn
    (continuousOn_inv_pow ha 3) isCompact_Icc

/-! ### Abel summation -/

private lemma abel_left (x : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (k : ℝ) * Λ k ^ 2
      = x * M x - ∫ t in Set.Ioc (1 : ℝ) x, M t := by
  have hc : (fun n : ℕ ↦ Λ n ^ 2) 0 = 0 := by simp
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ (fun s : ℝ ↦ s) t :=
    fun t _ ↦ differentiableAt_id
  have hint : IntegrableOn (deriv (fun s : ℝ ↦ s)) (Set.Icc (1 : ℝ) x) := by
    rw [deriv_id'']
    exact continuousOn_const.integrableOn_compact isCompact_Icc
  have key := sum_mul_eq_sub_integral_mul₀ (fun n : ℕ ↦ Λ n ^ 2) hc x hdiff hint
  simpa only [deriv_id'', one_mul, M_def] using key

private lemma deriv_inv_cube {t : ℝ} (ht : t ≠ 0) :
    deriv (fun s : ℝ ↦ (s ^ 3)⁻¹) t = -3 / t ^ 4 := by
  have h : HasDerivAt (fun s : ℝ ↦ (s ^ 3)⁻¹)
      (-(((3 : ℕ) : ℝ) * t ^ (3 - 1)) / (t ^ 3) ^ 2) t :=
    (hasDerivAt_pow 3 t).inv (pow_ne_zero 3 ht)
  rw [h.deriv]
  push_cast
  rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 3 ht)) (pow_ne_zero 4 ht)]
  ring

private lemma abel_right {x : ℝ} (hx : 2 ≤ x) {N : ℕ} (hN : x ≤ (N : ℝ)) :
    ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, Λ k ^ 2 / (k : ℝ) ^ 3
      = M (N : ℝ) / (N : ℝ) ^ 3 - M x / x ^ 3
        + 3 * ∫ t in Set.Ioc x (N : ℝ), M t / t ^ 4 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hne : ∀ t ∈ Set.Icc x (N : ℝ), t ≠ 0 := fun t ht ↦ ne_of_gt (lt_of_lt_of_le hx0 ht.1)
  have hdiff : ∀ t ∈ Set.Icc x (N : ℝ), DifferentiableAt ℝ (fun s : ℝ ↦ (s ^ 3)⁻¹) t := by
    intro t ht
    exact (differentiableAt_pow 3).inv (pow_ne_zero 3 (hne t ht))
  have hcont : ContinuousOn (fun t : ℝ ↦ -3 / t ^ 4) (Set.Icc x (N : ℝ)) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht ↦ ?_
    exact pow_ne_zero 4 (hne t ht)
  have hint : IntegrableOn (deriv (fun s : ℝ ↦ (s ^ 3)⁻¹)) (Set.Icc x (N : ℝ)) :=
    (hcont.integrableOn_compact isCompact_Icc).congr_fun
      (fun t ht ↦ (deriv_inv_cube (hne t ht)).symm) measurableSet_Icc
  have key := sum_mul_eq_sub_sub_integral_mul (fun n : ℕ ↦ Λ n ^ 2) hx0.le hN hdiff hint
  simp only [← M_def] at key
  rw [Nat.floor_natCast] at key
  have hI : (∫ t in Set.Ioc x (N : ℝ), deriv (fun s : ℝ ↦ (s ^ 3)⁻¹) t * M t)
      = -3 * ∫ t in Set.Ioc x (N : ℝ), M t / t ^ 4 := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans hx0 ht.1)
    rw [deriv_inv_cube ht0]
    ring
  have hL : ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, Λ k ^ 2 / (k : ℝ) ^ 3
      = ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, ((k : ℝ) ^ 3)⁻¹ * Λ k ^ 2 :=
    Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hL, key, hI]
  ring

/-! ### The exact integrals -/

private lemma integral_L {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, (t * Real.log t - t)
      = (x ^ 2 * Real.log x / 2 - 3 * x ^ 2 / 4) - (2 * Real.log 2 - 3) := by
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun s : ℝ ↦ s ^ 2 * Real.log s / 2 - 3 * s ^ 2 / 4)
        (t * Real.log t - t) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
    have htne : t ≠ 0 := ht0.ne'
    have h1 : HasDerivAt (fun s : ℝ ↦ s ^ 2 * Real.log s)
        (((2 : ℕ) : ℝ) * t ^ (2 - 1) * Real.log t + t ^ 2 * t⁻¹) t :=
      (hasDerivAt_pow 2 t).mul (Real.hasDerivAt_log htne)
    have h2 : HasDerivAt (fun s : ℝ ↦ 3 * s ^ 2) (3 * (((2 : ℕ) : ℝ) * t ^ (2 - 1))) t :=
      HasDerivAt.const_mul 3 (hasDerivAt_pow 2 t)
    refine ((h1.div_const 2).sub (h2.div_const 4)).congr_deriv ?_
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_L (by norm_num) hx)]
  norm_num
  ring

private lemma integral_L_div {x b : ℝ} (hx : 0 < x) (hxb : x ≤ b) :
    ∫ t in x..b, (t * Real.log t - t) / t ^ 4
      = (1 - 2 * Real.log b) / (4 * b ^ 2) - (1 - 2 * Real.log x) / (4 * x ^ 2) := by
  have hderiv : ∀ t ∈ Set.uIcc x b,
      HasDerivAt (fun s : ℝ ↦ (1 - 2 * Real.log s) / (4 * s ^ 2))
        ((t * Real.log t - t) / t ^ 4) t := by
    intro t ht
    rw [Set.uIcc_of_le hxb] at ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hx ht.1
    have htne : t ≠ 0 := ht0.ne'
    have hc : HasDerivAt (fun s : ℝ ↦ 1 - 2 * Real.log s) (0 - 2 * t⁻¹) t :=
      (hasDerivAt_const t (1 : ℝ)).sub (HasDerivAt.const_mul 2 (Real.hasDerivAt_log htne))
    have hd : HasDerivAt (fun s : ℝ ↦ 4 * s ^ 2) (4 * (((2 : ℕ) : ℝ) * t ^ (2 - 1))) t :=
      HasDerivAt.const_mul 4 (hasDerivAt_pow 2 t)
    refine (hc.div hd (by
      simpa using mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero 2 htne))).congr_deriv ?_
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_L_div hx hxb)]

private lemma integral_const_div_cube {K x b : ℝ} (hx : 0 < x) (hxb : x ≤ b) :
    ∫ t in x..b, K / t ^ 3 = K / (2 * x ^ 2) - K / (2 * b ^ 2) := by
  have hderiv : ∀ t ∈ Set.uIcc x b,
      HasDerivAt (fun s : ℝ ↦ -K / (2 * s ^ 2)) (K / t ^ 3) t := by
    intro t ht
    rw [Set.uIcc_of_le hxb] at ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hx ht.1
    have htne : t ≠ 0 := ht0.ne'
    have hd : HasDerivAt (fun s : ℝ ↦ 2 * s ^ 2) (2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1))) t :=
      HasDerivAt.const_mul 2 (hasDerivAt_pow 2 t)
    refine ((hasDerivAt_const t (-K)).div hd (by
      simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 htne))).congr_deriv ?_
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_const_div_cube hx hxb)]
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le hx hxb
  field_simp
  ring

/-! ### The two error estimates -/

private lemma err_left {C : ℝ} (hC : 0 < C)
    (hM : ∀ y : ℝ, 2 ≤ y → |M y - (y * Real.log y - y)| ≤ C * y / Real.log y)
    {x : ℝ} (hx : 2 ≤ x) :
    |(∫ t in (2 : ℝ)..x, M t) - (∫ t in (2 : ℝ)..x, (t * Real.log t - t))|
      ≤ C * x * (x - 2) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsub : (∫ t in (2 : ℝ)..x, M t) - (∫ t in (2 : ℝ)..x, (t * Real.log t - t))
      = ∫ t in (2 : ℝ)..x, (M t - (t * Real.log t - t)) :=
    (intervalIntegral.integral_sub (intervalIntegrable_M (by norm_num) hx)
      (intervalIntegrable_L (by norm_num) hx)).symm
  rw [hsub]
  have hb : ∀ t ∈ Set.uIoc (2 : ℝ) x, ‖M t - (t * Real.log t - t)‖ ≤ C * x / Real.log 2 := by
    intro t ht
    rw [Set.uIoc_of_le hx, Set.mem_Ioc] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1.le
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log two_pos ht2
    have hlt0 : 0 < Real.log t := lt_of_lt_of_le hl2 hlt
    rw [Real.norm_eq_abs]
    refine (hM t ht2).trans ?_
    rw [div_le_div_iff₀ hlt0 hl2]
    have s1 : C * t * Real.log 2 ≤ C * x * Real.log 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht.2 hC.le) hl2.le
    have s2 : C * x * Real.log 2 ≤ C * x * Real.log t :=
      mul_le_mul_of_nonneg_left hlt (mul_nonneg hC.le (by linarith))
    linarith
  have hkey := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 2)] at hkey
  calc |∫ t in (2 : ℝ)..x, (M t - (t * Real.log t - t))| ≤ C * x / Real.log 2 * (x - 2) := hkey
    _ = C * x * (x - 2) / Real.log 2 := by ring

private lemma err_right {C : ℝ} (hC : 0 < C)
    (hM : ∀ y : ℝ, 2 ≤ y → |M y - (y * Real.log y - y)| ≤ C * y / Real.log y)
    {x b : ℝ} (hx : 2 ≤ x) (hxb : x ≤ b) :
    |(∫ t in x..b, M t / t ^ 4) - (∫ t in x..b, (t * Real.log t - t) / t ^ 4)|
      ≤ C / Real.log 2 / (2 * x ^ 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hx0 : (0 : ℝ) < x := by linarith
  have hfi : IntervalIntegrable (fun t : ℝ ↦ (M t - (t * Real.log t - t)) / t ^ 4) volume x b :=
    intervalIntegrable_err_div hx0 hxb
  have hgi : IntervalIntegrable (fun t : ℝ ↦ C / Real.log 2 / t ^ 3) volume x b :=
    intervalIntegrable_const_div_cube hx0 hxb
  have hsub : (∫ t in x..b, M t / t ^ 4) - (∫ t in x..b, (t * Real.log t - t) / t ^ 4)
      = ∫ t in x..b, (M t - (t * Real.log t - t)) / t ^ 4 := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_M_div hx0 hxb)
      (intervalIntegrable_L_div hx0 hxb)]
    exact intervalIntegral.integral_congr fun t _ ↦ by ring
  have hpt : ∀ t ∈ Set.Icc x b,
      |(M t - (t * Real.log t - t)) / t ^ 4| ≤ C / Real.log 2 / t ^ 3 := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := le_trans hx ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log two_pos ht2
    have hlt0 : 0 < Real.log t := lt_of_lt_of_le hl2 hlt
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 4),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : |M t - (t * Real.log t - t)| ≤ C * t / Real.log 2 := by
      refine (hM t ht2).trans ?_
      rw [div_le_div_iff₀ hlt0 hl2]
      have s2 : C * t * Real.log 2 ≤ C * t * Real.log t :=
        mul_le_mul_of_nonneg_left hlt (mul_nonneg hC.le ht0.le)
      linarith
    calc |M t - (t * Real.log t - t)| * t ^ 3 ≤ C * t / Real.log 2 * t ^ 3 := by gcongr
      _ = C / Real.log 2 * t ^ 4 := by
          field_simp
  have hupper : (∫ t in x..b, (M t - (t * Real.log t - t)) / t ^ 4)
      ≤ ∫ t in x..b, C / Real.log 2 / t ^ 3 :=
    intervalIntegral.integral_mono_on hxb hfi hgi fun t ht ↦ (le_abs_self _).trans (hpt t ht)
  have hlower : (∫ t in x..b, -((M t - (t * Real.log t - t)) / t ^ 4))
      ≤ ∫ t in x..b, C / Real.log 2 / t ^ 3 :=
    intervalIntegral.integral_mono_on hxb hfi.neg hgi fun t ht ↦ (neg_le_abs _).trans (hpt t ht)
  rw [intervalIntegral.integral_neg] at hlower
  rw [integral_const_div_cube hx0 hxb] at hupper hlower
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le hx0 hxb
  have hpos : 0 ≤ C / Real.log 2 / (2 * b ^ 2) := by positivity
  rw [hsub, abs_le]
  constructor <;> linarith

/-! ### Summability -/

private lemma summand_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Λ n ^ 2 / n * min ((n : ℝ) / x) (x / n) ^ 2 ≤ x ^ 2 * (4 / (n : ℝ) ^ 2) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : min ((n : ℝ) / x) (x / n) ≤ x / n := min_le_right _ _
  have h2 : (0 : ℝ) ≤ min ((n : ℝ) / x) (x / n) := le_min (by positivity) (by positivity)
  have h3 : min ((n : ℝ) / x) (x / n) ^ 2 ≤ (x / n) ^ 2 := by nlinarith
  have h4 : (0 : ℝ) ≤ Λ n ^ 2 / n := by positivity
  have h5 : Λ n ^ 2 / n * min ((n : ℝ) / x) (x / n) ^ 2 ≤ Λ n ^ 2 / n * (x / n) ^ 2 :=
    mul_le_mul_of_nonneg_left h3 h4
  have h6 : Λ n ^ 2 / (n : ℝ) * (x / n) ^ 2 = x ^ 2 * (Λ n ^ 2 / (n : ℝ) ^ 3) := by ring
  have h7 : x ^ 2 * (Λ n ^ 2 / (n : ℝ) ^ 3) ≤ x ^ 2 * (4 / (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left (vonMangoldt_sq_div_cube_le n) (by positivity)
  linarith [h5, h6 ▸ h7]

private lemma summand_nonneg {x : ℝ} (n : ℕ) :
    0 ≤ Λ n ^ 2 / n * min ((n : ℝ) / x) (x / n) ^ 2 := by
  have h4 : (0 : ℝ) ≤ Λ n ^ 2 / n := by positivity
  have h2 : (0 : ℝ) ≤ min ((n : ℝ) / x) (x / n) ^ 2 := sq_nonneg _
  positivity

private lemma summable_F {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ Λ n ^ 2 / n * min ((n : ℝ) / x) (x / n) ^ 2) :=
  Summable.of_nonneg_of_le (fun n ↦ summand_nonneg n) (fun n ↦ summand_le hx n)
    (summable_four_div_sq.mul_left (x ^ 2))

/-! ### The arithmetic of the five error terms -/

private lemma bound_const_div {y : ℝ} (hy : 4 ≤ y) :
    -(3 / 4 : ℝ) ≤ (2 * Real.log 2 - 3) / y ∧ (2 * Real.log 2 - 3) / y ≤ 0 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hl' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hy0 : (0 : ℝ) < y := by linarith
  refine ⟨?_, div_nonpos_of_nonpos_of_nonneg (by linarith) hy0.le⟩
  rw [le_div_iff₀ hy0]
  linarith

private lemma bound_log_term {y n : ℝ} (hy : 0 ≤ y) (hn : 160 ≤ n) (hyn : y ≤ n / 40) :
    |3 * y * (1 - 2 * Real.log n) / (4 * n ^ 2)| ≤ 1 / 10 := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlogn : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn0; linarith
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hy (sub_nonneg.mpr hlogn),
      mul_nonneg (sub_nonneg.mpr hyn) hn0.le, sq_nonneg n]
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hy hlog0, mul_nonneg (sub_nonneg.mpr hn) hn0.le]

private lemma bound_M_term {y n m : ℝ} (hy : 0 ≤ y) (hn : 160 ≤ n) (hyn : y ≤ n / 40)
    (hm : m ≤ 16 * n ^ 2) : y * m / n ^ 3 ≤ 1 / 2 := by
  have hn0 : (0 : ℝ) < n := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h2 : y * m ≤ y * (16 * n ^ 2) := mul_le_mul_of_nonneg_left hm hy
  have h3 : y * (16 * n ^ 2) ≤ n / 40 * (16 * n ^ 2) :=
    mul_le_mul_of_nonneg_right hyn (by positivity)
  have h4 : n / 40 * (16 * n ^ 2) ≤ 1 / 2 * n ^ 3 := by nlinarith [pow_pos hn0 3]
  linarith

private lemma bound_e1 {e x C L : ℝ} (hx : 2 ≤ x) (hC : 0 < C) (hL : 0 < L)
    (he : |e| ≤ C * x * (x - 2) / L) : |e / x ^ 2| ≤ C / L := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2), div_le_div_iff₀ (by positivity) hL]
  calc |e| * L ≤ C * x * (x - 2) / L * L := by gcongr
    _ = C * x * (x - 2) := by field_simp
    _ ≤ C * x ^ 2 := by nlinarith [mul_pos hC hx0]

private lemma bound_e2 {e x C L : ℝ} (hx : 2 ≤ x) (hL : 0 < L)
    (he : |e| ≤ C / L / (2 * x ^ 2)) : |3 * x ^ 2 * e| ≤ 3 * (C / L) / 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 * x ^ 2)]
  calc 3 * x ^ 2 * |e| ≤ 3 * x ^ 2 * (C / L / (2 * x ^ 2)) := by gcongr
    _ = 3 * (C / L) / 2 := by field_simp

private lemma five_bound {A B D E G c : ℝ} (hA1 : -(3 / 4) ≤ A) (hA2 : A ≤ 0)
    (hB : |B| ≤ 1 / 10) (hD : |D| ≤ c) (hE1 : 0 ≤ E) (hE2 : E ≤ 1 / 2)
    (hG : |G| ≤ 3 * c / 2) (hc : 0 < c) : |A + B - D + E + G| ≤ 2 + 3 * c := by
  rw [abs_le] at hB hD hG ⊢
  constructor <;> linarith [hB.1, hB.2, hD.1, hD.2, hG.1, hG.2]

/-! ### The main estimate for `x ≥ 2` -/

private lemma main_bound {C : ℝ} (hC : 0 < C)
    (hM : ∀ y : ℝ, 2 ≤ y → |M y - (y * Real.log y - y)| ≤ C * y / Real.log y)
    {x : ℝ} (hx : 2 ≤ x) (F : ℕ → ℝ)
    (hF : ∀ n : ℕ, F n = Λ n ^ 2 / n * min ((n : ℝ) / x) (x / n) ^ 2) :
    |(∑' n : ℕ, F n) - Real.log x| ≤ 2 + 3 * (C / Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hx4 : (4 : ℝ) ≤ x ^ 2 := by nlinarith
  have hsum : Summable F := (summable_F hx0).congr fun n ↦ (hF n).symm
  have hKx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxK : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have hzero : (∫ t in (1 : ℝ)..2, M t) = 0 := by
    rw [intervalIntegral.integral_of_le one_le_two, MeasureTheory.integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo
        (g := fun _ ↦ (0 : ℝ)) (fun t ht ↦ M_eq_zero ht.2)]
    simp
  have hI1eq : (∫ t in Set.Ioc (1 : ℝ) x, M t) = ∫ t in (2 : ℝ)..x, M t := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_M zero_le_one one_le_two) (intervalIntegrable_M zero_le_two hx)
    rw [← intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ x), ← hadd, hzero]
    ring
  have hev : ∀ᶠ N : ℕ in atTop,
      |∑ n ∈ Finset.range (N + 1), F n - Real.log x| ≤ 2 + 3 * (C / Real.log 2) := by
    filter_upwards [eventually_ge_atTop (⌊x⌋₊ + 1), eventually_ge_atTop ⌈40 * x ^ 2⌉₊]
      with N hN1 hN2
    have hN40 : 40 * x ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN2)
    have hN160 : (160 : ℝ) ≤ (N : ℝ) := by nlinarith
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hN1nat : 1 ≤ N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · rw [h] at hNpos; norm_num at hNpos
      · exact h
    have hKN : ⌊x⌋₊ ≤ N := by omega
    have hNx : x ≤ (N : ℝ) := by
      have h : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN1
      linarith
    have hF0 : F 0 = 0 := by rw [hF]; simp
    have hsplit : ∑ n ∈ Finset.range (N + 1), F n
        = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, F n + ∑ n ∈ Finset.Ioc ⌊x⌋₊ N, F n := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le N), hF0,
        zero_add, ← Finset.sum_Ioc_consecutive F (Nat.zero_le ⌊x⌋₊) hKN]
    have hleft : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, F n
        = (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (k : ℝ) * Λ k ^ 2) / x ^ 2 := by
      have h1 : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, F n = ((n : ℝ) * Λ n ^ 2) / x ^ 2 := by
        intro n hn
        obtain ⟨hn0, hnK⟩ := Finset.mem_Ioc.mp hn
        have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
        have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnK) hKx
        have hmin : min ((n : ℝ) / x) (x / n) = (n : ℝ) / x := by
          refine min_eq_left ?_
          rw [div_le_div_iff₀ hx0 hn0']
          nlinarith
        rw [hF, hmin]
        field_simp
      rw [Finset.sum_congr rfl h1, ← Finset.sum_div]
      congr 1
      rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
      simp
    have hright : ∑ n ∈ Finset.Ioc ⌊x⌋₊ N, F n
        = x ^ 2 * ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, Λ k ^ 2 / (k : ℝ) ^ 3 := by
      have h2 : ∀ n ∈ Finset.Ioc ⌊x⌋₊ N, F n = x ^ 2 * (Λ n ^ 2 / (n : ℝ) ^ 3) := by
        intro n hn
        obtain ⟨hKn, hnN⟩ := Finset.mem_Ioc.mp hn
        have hxn : x < (n : ℝ) := by
          have h : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hKn
          linarith
        have hn0' : (0 : ℝ) < n := by linarith
        have hmin : min ((n : ℝ) / x) (x / n) = x / (n : ℝ) := by
          refine min_eq_right ?_
          rw [div_le_div_iff₀ hn0' hx0]
          nlinarith
        rw [hF, hmin]
        field_simp
      rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
    have hA := abel_left x
    have hB := abel_right hx hNx
    rw [hI1eq] at hA
    rw [← intervalIntegral.integral_of_le hNx] at hB
    have hJ1 := integral_L hx
    have hJ2 := integral_L_div hx0 hNx
    obtain ⟨e₁, he₁def⟩ : ∃ e : ℝ,
        e = (∫ t in (2 : ℝ)..x, M t) - (∫ t in (2 : ℝ)..x, (t * Real.log t - t)) := ⟨_, rfl⟩
    obtain ⟨e₂, he₂def⟩ : ∃ e : ℝ, e = (∫ t in x..(N : ℝ), M t / t ^ 4)
        - (∫ t in x..(N : ℝ), (t * Real.log t - t) / t ^ 4) := ⟨_, rfl⟩
    have he₁ : |e₁| ≤ C * x * (x - 2) / Real.log 2 := by
      rw [he₁def]; exact err_left hC hM hx
    have he₂ : |e₂| ≤ C / Real.log 2 / (2 * x ^ 2) := by
      rw [he₂def]; exact err_right hC hM hx hNx
    have hI1 : (∫ t in (2 : ℝ)..x, M t)
        = ((x ^ 2 * Real.log x / 2 - 3 * x ^ 2 / 4) - (2 * Real.log 2 - 3)) + e₁ := by
      rw [he₁def, hJ1]; ring
    have hI2 : (∫ t in x..(N : ℝ), M t / t ^ 4)
        = ((1 - 2 * Real.log (N : ℝ)) / (4 * (N : ℝ) ^ 2)
            - (1 - 2 * Real.log x) / (4 * x ^ 2)) + e₂ := by
      rw [he₂def, hJ2]; ring
    have hmain : ∑ n ∈ Finset.range (N + 1), F n - Real.log x
        = (2 * Real.log 2 - 3) / x ^ 2
          + 3 * x ^ 2 * (1 - 2 * Real.log (N : ℝ)) / (4 * (N : ℝ) ^ 2)
          - e₁ / x ^ 2 + x ^ 2 * M (N : ℝ) / (N : ℝ) ^ 3 + 3 * x ^ 2 * e₂ := by
      rw [hsplit, hleft, hright, hA, hB, hI1, hI2]
      field_simp
      ring
    rw [hmain]
    have hxN : x ^ 2 ≤ (N : ℝ) / 40 := by linarith
    have hx2nn : (0 : ℝ) ≤ x ^ 2 := by positivity
    have b1 := bound_const_div hx4
    have b2 := bound_log_term hx2nn hN160 hxN
    have b3 := bound_e1 hx hC hl2 he₁
    have b4a : 0 ≤ x ^ 2 * M (N : ℝ) / (N : ℝ) ^ 3 := by
      have := M_nonneg (N : ℝ)
      positivity
    have b4b := bound_M_term hx2nn hN160 hxN (M_natCast_le hN1nat)
    have b5 := bound_e2 hx hl2 he₂
    exact five_bound b1.1 b1.2 b2 b3 b4a b4b b5 (div_pos hC hl2)
  have hten0 : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range (N + 1), F n) atTop
      (𝓝 (∑' n : ℕ, F n)) := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact le_of_tendsto ((hten0.sub tendsto_const_nhds).abs) hev

/-! ### The theorem -/

@[zz_tag "lem_lambda_sq_sum"]
theorem exists_abs_tsum_vonMangoldt_sq_div_min_sq_sub_log_le :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      |(∑' n : ℕ, Λ n ^ 2 / n * min ((n : ℝ) / x) (x / n) ^ 2) - Real.log x| ≤ C := by
  obtain ⟨C, hC, hMb⟩ := ZetaZeros.exists_abs_vonMangoldt_sq_sum_sub_le
  have hM : ∀ y : ℝ, 2 ≤ y → |M y - (y * Real.log y - y)| ≤ C * y / Real.log y := by
    intro y hy
    rw [M_eq_sum_Ioc]
    exact hMb y hy
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hC₀ : 0 ≤ ∑' n : ℕ, 4 / (n : ℝ) ^ 2 := tsum_nonneg fun n ↦ by positivity
  have hCpos : 0 < 3 * (C / Real.log 2) := by positivity
  refine ⟨2 + 3 * (C / Real.log 2) + 4 * (∑' n : ℕ, 4 / (n : ℝ) ^ 2) + 1, by linarith,
    fun x hx ↦ ?_⟩
  rcases le_or_gt 2 x with hx2 | hx2
  · exact le_trans (main_bound hC hM hx2 _ fun n ↦ rfl) (by linarith)
  · have hx0 : (0 : ℝ) < x := by linarith
    have hsum : Summable (fun n : ℕ ↦ Λ n ^ 2 / n * min ((n : ℝ) / x) (x / n) ^ 2) :=
      summable_F hx0
    have hle : (∑' n : ℕ, Λ n ^ 2 / n * min ((n : ℝ) / x) (x / n) ^ 2)
        ≤ x ^ 2 * ∑' n : ℕ, 4 / (n : ℝ) ^ 2 := by
      calc (∑' n : ℕ, Λ n ^ 2 / n * min ((n : ℝ) / x) (x / n) ^ 2)
          ≤ ∑' n : ℕ, x ^ 2 * (4 / (n : ℝ) ^ 2) :=
            Summable.tsum_le_tsum (fun n ↦ summand_le hx0 n) hsum
              (summable_four_div_sq.mul_left _)
        _ = x ^ 2 * ∑' n : ℕ, 4 / (n : ℝ) ^ 2 := tsum_mul_left
    have hge : 0 ≤ ∑' n : ℕ, Λ n ^ 2 / n * min ((n : ℝ) / x) (x / n) ^ 2 :=
      tsum_nonneg fun n ↦ summand_nonneg n
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlogx' : Real.log x ≤ 1 := le_trans (Real.log_le_log hx0 hx2.le) hl2'
    have hx4 : x ^ 2 ≤ 4 := by nlinarith
    have hxsq : x ^ 2 * (∑' n : ℕ, 4 / (n : ℝ) ^ 2) ≤ 4 * ∑' n : ℕ, 4 / (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hx4 hC₀
    rw [abs_le]
    constructor <;> linarith

/-! ### The weight of the second moment

The upper bound `∑_n Λ(n)² min {n/x, x/n}² ≤ C x log (2x)`. Only the *size* of
`M y = ∑_{n ≤ y} Λ(n)²` enters, not its asymptotic; the tail `∑_{n > x} Λ(n)² / n²` is treated by
Abel summation against the weight `n ↦ (n²)⁻¹`. -/

private lemma log_le_two_mul_sqrt {y : ℝ} (hy : 0 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h := Real.log_le_rpow_div hy (by norm_num : (0 : ℝ) < 1 / 2)
  have he : (y : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * ((y : ℝ) ^ ((1 : ℝ) / 2)) := by ring
  rw [Real.sqrt_eq_rpow]
  linarith [he ▸ h]

/-- `Λ(n)² ≤ 16 √n`, from `Λ n ≤ log n = 2 log √n ≤ 4 √(√n)`. -/
private lemma vonMangoldt_sq_le_sqrt (n : ℕ) : Λ n ^ 2 ≤ 16 * Real.sqrt n := by
  have h0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h2 : Real.log n ≤ 4 * Real.sqrt (Real.sqrt n) := by
    have h := log_le_two_mul_sqrt hs
    rw [Real.log_sqrt hn] at h
    linarith
  have h3 : Real.sqrt (Real.sqrt n) ^ 2 = Real.sqrt n := Real.sq_sqrt hs
  nlinarith [Real.sqrt_nonneg (Real.sqrt (n : ℝ))]

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

private lemma minWeight_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 ≤ min ((n : ℝ) / x) (x / n) :=
  le_min (by positivity) (by positivity)

/-- The uniform majorant `Λ(n)² min {n/x, x/n}² ≤ 16 x² (√n / n²)`, using only `min ≤ x/n`. -/
private lemma vonMangoldt_sq_mul_min_sq_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Λ n ^ 2 * min ((n : ℝ) / x) (x / n) ^ 2 ≤ 16 * x ^ 2 * (Real.sqrt n / (n : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmin : min ((n : ℝ) / x) (x / n) ^ 2 ≤ (x / n) ^ 2 := by
    have h1 := min_le_right ((n : ℝ) / x) (x / n)
    have h2 := minWeight_nonneg hx n
    nlinarith
  have hL : (0 : ℝ) ≤ Λ n ^ 2 := sq_nonneg _
  calc Λ n ^ 2 * min ((n : ℝ) / x) (x / n) ^ 2 ≤ Λ n ^ 2 * (x / n) ^ 2 :=
        mul_le_mul_of_nonneg_left hmin hL
    _ = x ^ 2 * (Λ n ^ 2 / (n : ℝ) ^ 2) := by field_simp
    _ ≤ x ^ 2 * (16 * Real.sqrt n / (n : ℝ) ^ 2) := by
        gcongr
        exact vonMangoldt_sq_le_sqrt n
    _ = 16 * x ^ 2 * (Real.sqrt n / (n : ℝ) ^ 2) := by ring

private lemma summable_weighted {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ Λ n ^ 2 * min ((n : ℝ) / x) (x / n) ^ 2) :=
  Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun n ↦ vonMangoldt_sq_mul_min_sq_le hx n)
    (summable_sqrt_div_sq.mul_left (16 * x ^ 2))

/-- `M y ≤ (1 + C / log 2) y log (2y)` for `y ≥ 2`: the asymptotic `M y = y log y - y + O(y/log y)`
with the error and the `-y` both absorbed, using `log (2y) ≥ log 4 ≥ 1`. -/
private lemma M_le_mul_log {C : ℝ} (hC : 0 < C)
    (hM : ∀ y : ℝ, 2 ≤ y → |M y - (y * Real.log y - y)| ≤ C * y / Real.log y)
    {y : ℝ} (hy : 2 ≤ y) :
    M y ≤ (1 + C / Real.log 2) * (y * Real.log (2 * y)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hly : Real.log 2 ≤ Real.log y := Real.log_le_log two_pos hy
  have hly0 : 0 < Real.log y := lt_of_lt_of_le hl2 hly
  have hmono : Real.log y ≤ Real.log (2 * y) := Real.log_le_log hy0 (by linarith)
  have hone : (1 : ℝ) ≤ Real.log (2 * y) := by
    refine le_trans ?_ (Real.log_le_log (by norm_num) (by linarith : (4 : ℝ) ≤ 2 * y))
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have h1 : M y - (y * Real.log y - y) ≤ C * y / Real.log 2 := by
    refine le_trans (le_of_abs_le (hM y hy)) ?_
    rw [div_le_div_iff₀ hly0 hl2]
    nlinarith [mul_le_mul_of_nonneg_left hly (mul_nonneg hC.le hy0.le)]
  have h2 : C * y / Real.log 2 = C / Real.log 2 * y := by field_simp
  have h3 : y ≤ y * Real.log (2 * y) := by nlinarith
  have h4 : 0 ≤ C / Real.log 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 h4]

private lemma intervalIntegrable_M_div_cube {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ M t / t ^ 3) volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ?_
  simp only [div_eq_mul_inv]
  exact (integrableOn_M ha.le).mul_continuousOn (continuousOn_inv_pow ha 3) isCompact_Icc

private lemma deriv_inv_sq {t : ℝ} (ht : t ≠ 0) :
    deriv (fun s : ℝ ↦ (s ^ 2)⁻¹) t = -2 / t ^ 3 := by
  have h : HasDerivAt (fun s : ℝ ↦ (s ^ 2)⁻¹)
      (-(((2 : ℕ) : ℝ) * t ^ (2 - 1)) / (t ^ 2) ^ 2) t :=
    (hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht)
  rw [h.deriv]
  push_cast
  rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 ht)) (pow_ne_zero 3 ht)]
  ring

/-- Abel summation for the tail `∑_{x < k ≤ N} Λ(k)² / k²`, against the weight `t ↦ (t²)⁻¹`. -/
private lemma abel_right_sq {x : ℝ} (hx : 2 ≤ x) {N : ℕ} (hN : x ≤ (N : ℝ)) :
    ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, Λ k ^ 2 / (k : ℝ) ^ 2
      = M (N : ℝ) / (N : ℝ) ^ 2 - M x / x ^ 2
        + 2 * ∫ t in Set.Ioc x (N : ℝ), M t / t ^ 3 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hne : ∀ t ∈ Set.Icc x (N : ℝ), t ≠ 0 := fun t ht ↦ ne_of_gt (lt_of_lt_of_le hx0 ht.1)
  have hdiff : ∀ t ∈ Set.Icc x (N : ℝ), DifferentiableAt ℝ (fun s : ℝ ↦ (s ^ 2)⁻¹) t := by
    intro t ht
    exact (differentiableAt_pow 2).inv (pow_ne_zero 2 (hne t ht))
  have hcont : ContinuousOn (fun t : ℝ ↦ -2 / t ^ 3) (Set.Icc x (N : ℝ)) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht ↦ ?_
    exact pow_ne_zero 3 (hne t ht)
  have hint : IntegrableOn (deriv (fun s : ℝ ↦ (s ^ 2)⁻¹)) (Set.Icc x (N : ℝ)) :=
    (hcont.integrableOn_compact isCompact_Icc).congr_fun
      (fun t ht ↦ (deriv_inv_sq (hne t ht)).symm) measurableSet_Icc
  have key := sum_mul_eq_sub_sub_integral_mul (fun n : ℕ ↦ Λ n ^ 2) hx0.le hN hdiff hint
  simp only [← M_def] at key
  rw [Nat.floor_natCast] at key
  have hI : (∫ t in Set.Ioc x (N : ℝ), deriv (fun s : ℝ ↦ (s ^ 2)⁻¹) t * M t)
      = -2 * ∫ t in Set.Ioc x (N : ℝ), M t / t ^ 3 := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans hx0 ht.1)
    rw [deriv_inv_sq ht0]
    ring
  have hL : ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, Λ k ^ 2 / (k : ℝ) ^ 2
      = ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, ((k : ℝ) ^ 2)⁻¹ * Λ k ^ 2 :=
    Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hL, key, hI]
  ring

private lemma intervalIntegrable_log_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ Real.log (2 * t) / t ^ 2) volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ?_
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  have hpos : ∀ t ∈ Set.Icc a b, (0 : ℝ) < t := fun t ht ↦ lt_of_lt_of_le ha ht.1
  refine ContinuousOn.div ?_ (by fun_prop) fun t ht ↦ pow_ne_zero 2 (hpos t ht).ne'
  exact ContinuousOn.log (by fun_prop) fun t ht ↦ by
    have := hpos t ht
    positivity

/-- `∫_x^b log (2t) / t² dt`, whose primitive is `-(log (2t) + 1) / t`. -/
private lemma integral_log_div_sq {x b : ℝ} (hx : 0 < x) (hxb : x ≤ b) :
    ∫ t in x..b, Real.log (2 * t) / t ^ 2
      = (Real.log (2 * x) + 1) / x - (Real.log (2 * b) + 1) / b := by
  have hderiv : ∀ t ∈ Set.uIcc x b,
      HasDerivAt (fun s : ℝ ↦ -((Real.log (2 * s) + 1) / s)) (Real.log (2 * t) / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hxb] at ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hx ht.1
    have htne : t ≠ 0 := ht0.ne'
    have h2 : HasDerivAt (fun s : ℝ ↦ 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    have hlog : HasDerivAt (fun s : ℝ ↦ Real.log (2 * s)) (2 / (2 * t)) t :=
      h2.log (by positivity)
    refine ((hlog.add_const 1).div (hasDerivAt_id' (x := t)) htne).neg.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_log_div_sq hx hxb)]
  ring

/-- The tail integral of the Abel formula, bounded by `M t ≤ K t log (2t)`. -/
private lemma integral_M_div_cube_le {K x b : ℝ} (hK : 0 ≤ K)
    (hMle : ∀ y : ℝ, 2 ≤ y → M y ≤ K * (y * Real.log (2 * y)))
    (hx : 2 ≤ x) (hxb : x ≤ b) :
    (∫ t in Set.Ioc x b, M t / t ^ 3) ≤ K * ((Real.log (2 * x) + 1) / x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le hx0 hxb
  rw [← intervalIntegral.integral_of_le hxb]
  have hpt : ∀ t ∈ Set.Icc x b, M t / t ^ 3 ≤ K * (Real.log (2 * t) / t ^ 2) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := le_trans hx ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hrw : K * (Real.log (2 * t) / t ^ 2) * t ^ 3 = K * (t * Real.log (2 * t)) := by
      field_simp
    rw [div_le_iff₀ (by positivity), hrw]
    exact hMle t ht2
  have hmono : (∫ t in x..b, M t / t ^ 3) ≤ ∫ t in x..b, K * (Real.log (2 * t) / t ^ 2) :=
    intervalIntegral.integral_mono_on hxb (intervalIntegrable_M_div_cube hx0 hxb)
      ((intervalIntegrable_log_div_sq hx0 hxb).const_mul K) hpt
  rw [intervalIntegral.integral_const_mul, integral_log_div_sq hx0 hxb] at hmono
  have hpos : 0 ≤ (Real.log (2 * b) + 1) / b := by
    have hlb : (0 : ℝ) ≤ Real.log (2 * b) := Real.log_nonneg (by linarith)
    positivity
  nlinarith [mul_nonneg hK hpos]

private lemma tendsto_log_two_mul_div_atTop :
    Filter.Tendsto (fun N : ℕ ↦ Real.log (2 * (N : ℝ)) / (N : ℝ)) Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun y : ℝ ↦ Real.log y / y) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hg : Filter.Tendsto (fun N : ℕ ↦ 2 * (N : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop two_pos tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto (fun N : ℕ ↦ 2 * (Real.log (2 * (N : ℝ)) / (2 * (N : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa using (h0.comp hg).const_mul (2 : ℝ)
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ne_atTop 0] with N hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  field_simp

/-- The partial sums of the weighted second moment, bounded uniformly apart from a boundary term
`x² K log (2N) / N` that vanishes as `N → ∞`. The sum splits at `x`: below `x` the weight is at
most `1`, above it is `x²/n²` and Abel summation applies. -/
private lemma sum_Icc_weighted_le {K x : ℝ} (hK : 0 ≤ K)
    (hMle : ∀ y : ℝ, 2 ≤ y → M y ≤ K * (y * Real.log (2 * y)))
    (hx : 2 ≤ x) {N : ℕ} (hN : x ≤ (N : ℝ)) :
    ∑ k ∈ Finset.Icc 0 N, Λ k ^ 2 * min ((k : ℝ) / x) (x / k) ^ 2
      ≤ K * (x * Real.log (2 * x)) + x ^ 2 * (K * (Real.log (2 * (N : ℝ)) / (N : ℝ)))
        + 2 * x * (K * (Real.log (2 * x) + 1)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := le_trans hx hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hfl : ⌊x⌋₊ ≤ N := by
    have := Nat.floor_le_floor hN
    rwa [Nat.floor_natCast] at this
  have hflx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hIcc : ∑ k ∈ Finset.Icc 0 N, Λ k ^ 2 * min ((k : ℝ) / x) (x / k) ^ 2
      = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, Λ k ^ 2 * min ((k : ℝ) / x) (x / k) ^ 2
        + ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, Λ k ^ 2 * min ((k : ℝ) / x) (x / k) ^ 2 := by
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊x⌋₊) hfl,
      ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le N)]
    simp
  have hpart1 : ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, Λ k ^ 2 * min ((k : ℝ) / x) (x / k) ^ 2 ≤ M x := by
    rw [M_eq_sum_Ioc]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkx : (k : ℝ) ≤ x := le_trans (Nat.cast_le.mpr (Finset.mem_Ioc.mp hk).2) hflx
    have hmin1 : min ((k : ℝ) / x) (x / k) ≤ 1 := by
      refine le_trans (min_le_left _ _) ?_
      rw [div_le_one hx0]
      exact hkx
    have hmin0 : (0 : ℝ) ≤ min ((k : ℝ) / x) (x / k) := minWeight_nonneg hx0 k
    have hsq : min ((k : ℝ) / x) (x / k) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (Λ k)]
  have hpart2 : ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, Λ k ^ 2 * min ((k : ℝ) / x) (x / k) ^ 2
      ≤ x ^ 2 * ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, Λ k ^ 2 / (k : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hk1 : 1 ≤ k := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hmin : min ((k : ℝ) / x) (x / k) ^ 2 ≤ (x / k) ^ 2 := by
      have h1 := min_le_right ((k : ℝ) / x) (x / k)
      have h2 := minWeight_nonneg hx0 k
      nlinarith
    calc Λ k ^ 2 * min ((k : ℝ) / x) (x / k) ^ 2 ≤ Λ k ^ 2 * (x / k) ^ 2 :=
          mul_le_mul_of_nonneg_left hmin (sq_nonneg _)
      _ = x ^ 2 * (Λ k ^ 2 / (k : ℝ) ^ 2) := by field_simp
  have hA : ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, Λ k ^ 2 / (k : ℝ) ^ 2
      ≤ K * (Real.log (2 * (N : ℝ)) / (N : ℝ)) + 2 * (K * ((Real.log (2 * x) + 1) / x)) := by
    rw [abel_right_sq hx hN]
    have hMN : M (N : ℝ) / (N : ℝ) ^ 2 ≤ K * (Real.log (2 * (N : ℝ)) / (N : ℝ)) := by
      rw [div_le_iff₀ (by positivity)]
      have hrw : K * (Real.log (2 * (N : ℝ)) / (N : ℝ)) * (N : ℝ) ^ 2
          = K * ((N : ℝ) * Real.log (2 * (N : ℝ))) := by field_simp
      rw [hrw]
      exact hMle _ hN2
    have hMx : 0 ≤ M x / x ^ 2 := div_nonneg (M_nonneg x) (by positivity)
    have hInt := integral_M_div_cube_le hK hMle hx hN
    linarith
  have hx2A : x ^ 2 * ∑ k ∈ Finset.Ioc ⌊x⌋₊ N, Λ k ^ 2 / (k : ℝ) ^ 2
      ≤ x ^ 2 * (K * (Real.log (2 * (N : ℝ)) / (N : ℝ)))
        + 2 * x * (K * (Real.log (2 * x) + 1)) := by
    have h := mul_le_mul_of_nonneg_left hA (sq_nonneg x)
    have hrw : x ^ 2 * (K * (Real.log (2 * (N : ℝ)) / (N : ℝ))
          + 2 * (K * ((Real.log (2 * x) + 1) / x)))
        = x ^ 2 * (K * (Real.log (2 * (N : ℝ)) / (N : ℝ)))
          + 2 * x * (K * (Real.log (2 * x) + 1)) := by
      field_simp
    linarith [hrw ▸ h]
  have hMx' : M x ≤ K * (x * Real.log (2 * x)) := hMle x hx
  rw [hIcc]
  linarith

/-- The `N → ∞` limit of `sum_Icc_weighted_le`. -/
private lemma tsum_weighted_le {K x : ℝ} (hK : 0 ≤ K)
    (hMle : ∀ y : ℝ, 2 ≤ y → M y ≤ K * (y * Real.log (2 * y)))
    (hx : 2 ≤ x) :
    (∑' n : ℕ, Λ n ^ 2 * min ((n : ℝ) / x) (x / n) ^ 2)
      ≤ K * (x * Real.log (2 * x)) + 2 * x * (K * (Real.log (2 * x) + 1)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs := summable_weighted hx0
  have hlim1 : Filter.Tendsto
      (fun N : ℕ ↦ ∑ k ∈ Finset.Icc 0 N, Λ k ^ 2 * min ((k : ℝ) / x) (x / k) ^ 2)
      Filter.atTop (nhds (∑' n : ℕ, Λ n ^ 2 * min ((n : ℝ) / x) (x / n) ^ 2)) := by
    refine (hs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)).congr fun N ↦ ?_
    simp only [Function.comp_apply]
    congr 1
    ext k
    simp
  have h2 : Filter.Tendsto (fun N : ℕ ↦ x ^ 2 * (K * (Real.log (2 * (N : ℝ)) / (N : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_log_two_mul_div_atTop.const_mul K).const_mul (x ^ 2)
  have hlim2 : Filter.Tendsto
      (fun N : ℕ ↦ K * (x * Real.log (2 * x)) + x ^ 2 * (K * (Real.log (2 * (N : ℝ)) / (N : ℝ)))
        + 2 * x * (K * (Real.log (2 * x) + 1))) Filter.atTop
      (nhds (K * (x * Real.log (2 * x)) + 2 * x * (K * (Real.log (2 * x) + 1)))) := by
    simpa using ((tendsto_const_nhds.add h2).add tendsto_const_nhds)
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈x⌉₊] with N hNc
  exact sum_Icc_weighted_le hK hMle hx (le_trans (Nat.le_ceil x) (Nat.cast_le.mpr hNc))

/-- **The weight of the second moment.** There is an absolute `C > 0` such that
`∑_n Λ(n)² min {n/x, x/n}² ≤ C x log (2x)` for every `x ≥ 1`.

Only the size `M y = ∑_{n ≤ y} Λ(n)² ≤ K y log (2y)` enters, which the second moment supplies with
its error and its `-y` both absorbed. The sum splits at `x`: the part `n ≤ x` is at most `M x`,
because the weight there is at most `1`; the part `n > x` is `x² ∑_{n > x} Λ(n)² / n²`, and Abel
summation against `t ↦ (t²)⁻¹` turns it into `x² (M N / N² - M x / x² + 2 ∫_x^N M t / t³ dt)`,
whose integral is `≤ K (log (2x) + 1) / x` by the same size bound. The boundary term
`M N / N² ≤ K log (2N) / N` vanishes in the limit `N → ∞`. -/
@[zz_tag "lem_lambda_sq_weight"]
theorem exists_tsum_vonMangoldt_sq_mul_min_sq_le :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      (∑' n : ℕ, Λ n ^ 2 * min ((n : ℝ) / x) (x / n) ^ 2) ≤ C * x * Real.log (2 * x) := by
  obtain ⟨C₀, hC₀, hMb⟩ := ZetaZeros.exists_abs_vonMangoldt_sq_sum_sub_le
  have hM : ∀ y : ℝ, 2 ≤ y → |M y - (y * Real.log y - y)| ≤ C₀ * y / Real.log y := by
    intro y hy
    rw [M_eq_sum_Ioc]
    exact hMb y hy
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K : ℝ := 1 + C₀ / Real.log 2 with hKdef
  have hK : 0 ≤ K := by
    have : 0 < C₀ / Real.log 2 := by positivity
    rw [hKdef]; linarith
  have hMle : ∀ y : ℝ, 2 ≤ y → M y ≤ K * (y * Real.log (2 * y)) :=
    fun y hy ↦ M_le_mul_log hC₀ hM hy
  set S : ℝ := ∑' n : ℕ, Real.sqrt n / (n : ℝ) ^ 2 with hSdef
  have hS : 0 ≤ S := tsum_nonneg fun n ↦ by positivity
  refine ⟨5 * K + 64 * S / Real.log 2 + 1, by positivity, fun x hx ↦ ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog2x : Real.log 2 ≤ Real.log (2 * x) := Real.log_le_log two_pos (by linarith)
  have hlogpos : 0 < Real.log (2 * x) := lt_of_lt_of_le hl2 hlog2x
  have hxlog : 0 < x * Real.log (2 * x) := by positivity
  rcases le_or_gt 2 x with hx2 | hx2
  · have hone : (1 : ℝ) ≤ Real.log (2 * x) := by
      refine le_trans ?_ (Real.log_le_log (by norm_num) (by linarith : (4 : ℝ) ≤ 2 * x))
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    have hmain := tsum_weighted_le hK hMle hx2
    have hstep : K * (x * Real.log (2 * x)) + 2 * x * (K * (Real.log (2 * x) + 1))
        ≤ 5 * K * (x * Real.log (2 * x)) := by
      have h1 : Real.log (2 * x) + 1 ≤ 2 * Real.log (2 * x) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * x) hK)]
    have hrest : 0 ≤ (64 * S / Real.log 2 + 1) * (x * Real.log (2 * x)) := by positivity
    calc (∑' n : ℕ, Λ n ^ 2 * min ((n : ℝ) / x) (x / n) ^ 2)
        ≤ 5 * K * (x * Real.log (2 * x)) := le_trans hmain hstep
      _ ≤ (5 * K + 64 * S / Real.log 2 + 1) * x * Real.log (2 * x) := by nlinarith
  · have hle : (∑' n : ℕ, Λ n ^ 2 * min ((n : ℝ) / x) (x / n) ^ 2) ≤ 16 * x ^ 2 * S := by
      calc (∑' n : ℕ, Λ n ^ 2 * min ((n : ℝ) / x) (x / n) ^ 2)
          ≤ ∑' n : ℕ, 16 * x ^ 2 * (Real.sqrt n / (n : ℝ) ^ 2) :=
            Summable.tsum_le_tsum (fun n ↦ vonMangoldt_sq_mul_min_sq_le hx0 n)
              (summable_weighted hx0) (summable_sqrt_div_sq.mul_left _)
        _ = 16 * x ^ 2 * S := tsum_mul_left
    have hx4 : x ^ 2 ≤ 4 := by nlinarith
    have h64 : 16 * x ^ 2 * S ≤ 64 * S := by nlinarith
    have hbig : 64 * S ≤ 64 * S / Real.log 2 * (x * Real.log (2 * x)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      have h1 : Real.log 2 ≤ x * Real.log (2 * x) := by nlinarith
      nlinarith
    have hrest : 0 ≤ (5 * K + 1) * (x * Real.log (2 * x)) := by positivity
    calc (∑' n : ℕ, Λ n ^ 2 * min ((n : ℝ) / x) (x / n) ^ 2) ≤ 64 * S := le_trans hle h64
      _ ≤ (5 * K + 64 * S / Real.log 2 + 1) * x * Real.log (2 * x) := by nlinarith

end ZetaZeros
