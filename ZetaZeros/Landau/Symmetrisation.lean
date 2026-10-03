/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.PairCorrelation.MontgomeryExplicit

/-!
# From Landau's symmetrically truncated formula to the symmetrised identity

Landau's explicit formula at a point `s` holds as a limit of *symmetric partial sums*: the sum of
`m_ρ x^{ρ - s} / (s - ρ)` over the zeros `ρ ∈ 𝒩*` with `|im ρ| ≤ U` tends to `R (x, s)` as
`U → ∞`. The unordered sum over `𝒩*` does not exist: the terms have norm `≍ m_ρ / (1 + |im ρ|)`
and a dyadic block `U < |im ρ| ≤ 2 U` carries `≍ U log U` of them, so the family is not summable
and `ZetaZeros.LandauExplicitFormulaHasSum` is false.

This file deduces from the truncated formula the symmetrised identity
`ℓ (x, t) = x R (3/2 + it) - x⁻¹ R (-1/2 + it)`, in which no limit appears. Pairing the point
`3/2 + it`, scaled by `x`, against `-1/2 + it`, scaled by `x⁻¹`, replaces `1/(s - ρ)` by
`2/(1 - A²)` with `A = ρ - (1/2 + it)`, so the paired terms decay like `|im ρ - t|⁻²`; that family
is `ZetaZeros.summable_zeroSideTerm`, and its `tsum` is `ZetaZeros.zeroSide`.

The truncated formula itself, `ZetaZeros.LandauTruncatedLimit`, is proved as
`ZetaZeros.landauTruncatedLimit`.

## Main definitions

* `ZetaZeros.heightWindow`: the zeros of `𝒩*` with `|im ρ| ≤ U`, as a `Finset allZeros`.
* `ZetaZeros.LandauTruncatedLimit`: Landau's explicit formula as a limit of symmetric partial sums.

## Main results

* `ZetaZeros.tendsto_heightWindow`: the windows tend to `atTop` in the lattice of finite subsets
  of `𝒩*`.
* `ZetaZeros.landauSymmetrisedFormula_of_truncatedLimit`: `ZetaZeros.LandauTruncatedLimit`
  implies `ZetaZeros.LandauSymmetrisedFormula`.
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter Topology

/-! ### The symmetric windows of zeros -/

/-- The zeros of `𝒩*` of ordinate at most `U` in absolute value form a finite subset of `ℂ`: such a
zero has `|re ρ| ≤ 1` and `|im ρ| ≤ |U|`, hence lies in the closed ball of radius `1 + |U|`, and a
compact set meets only finitely many zeros of `ζ`. -/
private lemma heightWindowSet_finite (U : ℝ) : {ρ ∈ allZeros | |ρ.im| ≤ U}.Finite := by
  refine ((isCompact_closedBall (0 : ℂ) (1 + |U|)).inter_riemannZetaZeros_finite).subset
    fun ρ hρ => ?_
  obtain ⟨⟨hζ, h₀, h₁⟩, him⟩ := hρ
  refine ⟨?_, mem_riemannZetaZeros.mpr hζ⟩
  have h : |ρ.im| ≤ |U| := him.trans (le_abs_self U)
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    _ ≤ 1 + |U| := by rw [abs_of_pos h₀]; linarith

/-- The zeros `ρ ∈ 𝒩*` with `|im ρ| ≤ U` form a finite subset of the subtype `𝒩*`. -/
theorem heightWindow_finite (U : ℝ) : {ρ : allZeros | |(ρ : ℂ).im| ≤ U}.Finite :=
  (Set.Finite.preimage Subtype.val_injective.injOn (heightWindowSet_finite U)).subset
    fun ρ hρ => ⟨ρ.2, hρ⟩

/-- **The symmetric window of zeros at height `U`**: the zeros `ρ ∈ 𝒩*` with `|im ρ| ≤ U`, as a
`Finset` of the subtype `allZeros`. -/
noncomputable def heightWindow (U : ℝ) : Finset allZeros := (heightWindow_finite U).toFinset

@[simp]
theorem mem_heightWindow {U : ℝ} {ρ : allZeros} : ρ ∈ heightWindow U ↔ |(ρ : ℂ).im| ≤ U :=
  Set.Finite.mem_toFinset (heightWindow_finite U)

/-- **The windows exhaust `𝒩*`.** As `U → ∞` the symmetric windows tend to `atTop` in the lattice
of finite subsets of `𝒩*`: any given finite set of zeros is contained in every window of height at
least the largest ordinate occurring in it. -/
theorem tendsto_heightWindow : Tendsto heightWindow atTop atTop := by
  refine tendsto_atTop.2 fun s => eventually_atTop.2
    ⟨((s.sup fun ρ => ⌈|(ρ : ℂ).im|⌉₊ : ℕ) : ℝ), fun U hU ρ hρ => ?_⟩
  rw [mem_heightWindow]
  have h₁ : |(ρ : ℂ).im| ≤ (⌈|(ρ : ℂ).im|⌉₊ : ℝ) := Nat.le_ceil _
  have h₂ : ((⌈|(ρ : ℂ).im|⌉₊ : ℕ) : ℝ) ≤ ((s.sup fun σ => ⌈|(σ : ℂ).im|⌉₊ : ℕ) : ℝ) :=
    Nat.cast_le.2 (Finset.le_sup (f := fun σ : allZeros => ⌈|(σ : ℂ).im|⌉₊) hρ)
  linarith

/-! ### Landau's explicit formula as a limit of symmetric partial sums -/

/-- **Landau's explicit formula, symmetrically truncated**: for `x > 1` not a prime power and `s`
with `s ≠ 1`, `ζ s ≠ 0` and `s ≠ -2n` for every `n ≥ 1`,

`lim_{U → ∞} ∑_{ρ ∈ 𝒩*, |im ρ| ≤ U} m_ρ x^{ρ - s} / (s - ρ) = R (x, s)`,

with `R = ZetaZeros.landauRHS`. It is proved as `ZetaZeros.landauTruncatedLimit`. -/
def LandauTruncatedLimit : Prop :=
  ∀ x : ℝ, 1 < x → NotPrimePowerReal x → ∀ s : ℂ, s ≠ 1 → riemannZeta s ≠ 0 →
    (∀ n : ℕ, 1 ≤ n → s ≠ -(2 * (n : ℂ))) →
      Tendsto (fun U : ℝ => ∑ ρ ∈ heightWindow U, landauZeroTerm x s ρ) atTop
        (nhds (landauRHS x s))

/-! ### The symmetrisation -/

/-- The two factors of the symmetrised denominator are non-zero: their product is
`1 - (ρ - (1/2 + it))²`, whose modulus is at least `3/4` by
`ZetaZeros.three_quarters_add_sq_le_norm_one_sub_sq`. -/
private lemma one_sub_ne_zero_and_one_add_ne_zero {ρ : ℂ} (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) (t : ℝ) :
    1 - (ρ - (1 / 2 + (t : ℂ) * I)) ≠ 0 ∧ 1 + (ρ - (1 / 2 + (t : ℂ) * I)) ≠ 0 := by
  set A : ℂ := ρ - (1 / 2 + (t : ℂ) * I) with hA
  have hne : 1 - A ^ 2 ≠ 0 := by
    intro h
    have hle := three_quarters_add_sq_le_norm_one_sub_sq h₀ h₁ t
    rw [hA] at h
    rw [h, norm_zero] at hle
    nlinarith [sq_nonneg (t - ρ.im)]
  have hprod : (1 - A) * (1 + A) = 1 - A ^ 2 := by ring
  rw [← hprod] at hne
  exact ⟨fun h => hne (by rw [h, zero_mul]), fun h => hne (by rw [h, mul_zero])⟩

/-- **The symmetrised term.** For `x > 0` and a zero `ρ` of the open critical strip, `x` times
the term of Landau's zero side at `3/2 + it` minus `x⁻¹` times the term at `-1/2 + it` is the
term of `ℓ (x, t)` at `ρ`, namely `m_ρ ⬝ 2 x^{ρ - 1/2 - it} / (1 - A²)` with
`A = ρ - (1/2 + it)`. -/
private lemma landauZeroTerm_symmetrise {x : ℝ} (hx : 0 < x) {ρ : ℂ} (h₀ : 0 < ρ.re)
    (h₁ : ρ.re < 1) (t : ℝ) :
    (x : ℂ) * ((zeroMultiplicity ρ : ℂ) *
        ((x : ℂ) ^ (ρ - ((3 / 2 : ℂ) + (t : ℂ) * I)) / ((3 / 2 : ℂ) + (t : ℂ) * I - ρ)))
      - (x : ℂ)⁻¹ * ((zeroMultiplicity ρ : ℂ) *
        ((x : ℂ) ^ (ρ - (-(1 / 2 : ℂ) + (t : ℂ) * I)) / (-(1 / 2 : ℂ) + (t : ℂ) * I - ρ)))
      = (zeroMultiplicity ρ : ℂ) * (2 * (x : ℂ) ^ (ρ - 1 / 2 - (t : ℂ) * I)
          / (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2)) := by
  have hx0 : (x : ℂ) ≠ 0 := by simpa using hx.ne'
  set u : ℂ := (x : ℂ) ^ (ρ - 1 / 2 - (t : ℂ) * I) with hu
  have hup : (x : ℂ) ^ (ρ - ((3 / 2 : ℂ) + (t : ℂ) * I)) = u * (x : ℂ)⁻¹ := by
    rw [show ρ - ((3 / 2 : ℂ) + (t : ℂ) * I) = (ρ - 1 / 2 - (t : ℂ) * I) + (-1) from by ring,
      Complex.cpow_add _ _ hx0, Complex.cpow_neg_one, hu]
  have hum : (x : ℂ) ^ (ρ - (-(1 / 2 : ℂ) + (t : ℂ) * I)) = u * (x : ℂ) := by
    rw [show ρ - (-(1 / 2 : ℂ) + (t : ℂ) * I) = (ρ - 1 / 2 - (t : ℂ) * I) + 1 from by ring,
      Complex.cpow_add _ _ hx0, Complex.cpow_one, hu]
  obtain ⟨hne₁, hne₂⟩ := one_sub_ne_zero_and_one_add_ne_zero h₀ h₁ t
  set A : ℂ := ρ - (1 / 2 + (t : ℂ) * I) with hA
  have hd₁ : (3 / 2 : ℂ) + (t : ℂ) * I - ρ = 1 - A := by rw [hA]; ring
  have hd₂ : -(1 / 2 : ℂ) + (t : ℂ) * I - ρ = -(1 + A) := by rw [hA]; ring
  rw [hup, hum, hd₁, hd₂, show (1 : ℂ) - A ^ 2 = (1 - A) * (1 + A) from by ring]
  field_simp
  ring

/-- **The symmetrised formula follows from the symmetrically truncated one**: if
`ZetaZeros.LandauTruncatedLimit` holds then so does `ZetaZeros.LandauSymmetrisedFormula`, i.e. for
`x > 1` not a prime power and real `t`,
`ℓ (x, t) = x R (x, 3/2 + it) - x⁻¹ R (x, -1/2 + it)`. -/
theorem landauSymmetrisedFormula_of_truncatedLimit (hL : LandauTruncatedLimit) :
    LandauSymmetrisedFormula := by
  intro x hx hnpp t
  have hx0 : (0 : ℝ) < x := by linarith
  set a : ℂ := (3 / 2 : ℂ) + (t : ℂ) * I with ha
  set b : ℂ := -(1 / 2 : ℂ) + (t : ℂ) * I with hb
  have hare : a.re = 3 / 2 := by simp [ha]
  have hbre : b.re = -(1 / 2) := by simp [hb]
  have ha1 : a ≠ 1 := fun h => by rw [h] at hare; norm_num at hare
  have haζ : riemannZeta a ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (s := a) (by rw [hare]; norm_num)
  have han : ∀ n : ℕ, 1 ≤ n → a ≠ -(2 * (n : ℂ)) := by
    intro n _ h
    have hre : a.re = -(2 * (n : ℝ)) := by rw [h]; simp
    rw [hare] at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hb1 : b ≠ 1 := fun h => by rw [h] at hbre; norm_num at hbre
  have hbζ : riemannZeta b ≠ 0 := riemannZeta_ne_zero_of_re_eq_neg_half hbre
  have hbn : ∀ n : ℕ, 1 ≤ n → b ≠ -(2 * (n : ℂ)) := by
    intro n hn h
    have hre : b.re = -(2 * (n : ℝ)) := by rw [h]; simp
    rw [hbre] at hre
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hpair := ((hL x hx hnpp a ha1 haζ han).const_mul (x : ℂ)).sub
    ((hL x hx hnpp b hb1 hbζ hbn).const_mul (x : ℂ)⁻¹)
  have hsum : Tendsto (fun s : Finset allZeros => ∑ ρ ∈ s,
      (zeroMultiplicity (ρ : ℂ) : ℂ) * (2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
        / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2))) atTop (nhds (zeroSide x t)) :=
    (summable_zeroSideTerm hx.le).hasSum
  have hzs : Tendsto (fun U : ℝ => ∑ ρ ∈ heightWindow U,
      (zeroMultiplicity (ρ : ℂ) : ℂ) * (2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
        / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2))) atTop (nhds (zeroSide x t)) :=
    hsum.comp tendsto_heightWindow
  refine tendsto_nhds_unique hzs (hpair.congr fun U => ?_)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ρ _ => landauZeroTerm_symmetrise hx0 ρ.2.2.1 ρ.2.2.2 t

end ZetaZeros
