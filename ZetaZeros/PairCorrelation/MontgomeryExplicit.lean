/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.PairCorrelation.Function
public import ZetaZeros.Landau.Perron

/-!
# Montgomery's explicit-formula lemma from Landau's explicit formula

Montgomery's explicit-formula lemma is the symmetrised form of Landau's explicit formula at
`σ = 3/2`: subtracting Landau's identity at `s = -1/2 + it` from the one at `s = 3/2 + it`, after
multiplying by `x^{s - 1/2}`, replaces the zero side by the absolutely convergent `ℓ (x, t)` of
`ZetaZeros.zeroSide` and the prime side by `-D (x, t)` of `ZetaZeros.weightedPrimeSum`, leaving
three error terms of size `O (1/x + √x / (1 + t²))`.

The results of this file take Landau's formula as a hypothesis, in the symmetrised form
`ZetaZeros.LandauSymmetrisedFormula`; it is proved as `ZetaZeros.landauSymmetrisedFormula`.

## The three forms of Landau's formula

`ZetaZeros.LandauExplicitFormula` states Landau's formula with the sum over the zeros written as a
`tsum`. That sum is **not absolutely convergent**: its terms have norm `≍ m_ρ / (1 + |t - im ρ|)`,
and the multiplicity in a unit window at height `γ` is `≍ log γ`, so the series behaves like
`∑_k log k / k`. `ZetaZeros.LandauExplicitFormulaHasSum` states the same identity as a `HasSum`,
so with absolute convergence included; by the previous remark it is false.

`ZetaZeros.LandauSymmetrisedFormula` is the single identity

`ℓ (x, t) = x ⬝ R (3/2 + it) - x⁻¹ ⬝ R (-1/2 + it)`,

`R` being the right-hand side of Landau's formula. Both sides are absolutely convergent.
`ZetaZeros.landauSymmetrisedFormula_of_hasSum` derives it from the `HasSum` form.

## Main definitions

* `ZetaZeros.LandauExplicitFormula`, `ZetaZeros.LandauExplicitFormulaHasSum`,
  `ZetaZeros.LandauSymmetrisedFormula`: the three forms of Landau's formula.

## Main results

* `ZetaZeros.exists_norm_zeroSide_add_weightedPrimeSum_sub_div_le`: assuming
  `LandauSymmetrisedFormula`, Montgomery's explicit-formula lemma for `x > 1` not a prime power.
* `ZetaZeros.exists_norm_zeroSide_add_weightedPrimeSum_sub_div_le_of_one_le`: assuming
  `LandauSymmetrisedFormula`, the same bound for every `x ≥ 1`.
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter Topology
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-! ### The shape of Landau's explicit formula -/

/-- A real number that is not a prime power, the hypothesis on `x` in Landau's explicit formula:
the prime side `∑_{n ≤ x} Λ (n) n^{-s}` jumps exactly at the prime powers, so the formula can only
hold off them. Stated as `x ≠ n` for every prime power `n : ℕ`, since `x` is real and the notion of
a prime power belongs to `ℕ`. -/
def NotPrimePowerReal (x : ℝ) : Prop := ∀ n : ℕ, IsPrimePow n → x ≠ (n : ℝ)

/-- The term at a zero `ρ` of the left-hand side of Landau's explicit formula,
`m_ρ x^{ρ - s} / (s - ρ)`. -/
noncomputable def landauZeroTerm (x : ℝ) (s : ℂ) (ρ : allZeros) : ℂ :=
  (zeroMultiplicity (ρ : ℂ) : ℂ) * ((x : ℂ) ^ ((ρ : ℂ) - s) / (s - (ρ : ℂ)))

/-- The prime side of Landau's explicit formula, `∑_{n ≤ x} Λ (n) n^{-s}`. -/
noncomputable def landauPrimeSum (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) / (n : ℂ) ^ s

/-- The sum over the trivial zeros in Landau's explicit formula,
`∑_{n ≥ 1} x^{-2n - s} / (2n + s)`, written with the index shifted so that `n` runs over `ℕ`. -/
noncomputable def landauTrivialSum (x : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - s) / (2 * ((n : ℂ) + 1) + s)

/-- The right-hand side of Landau's explicit formula,
`R (s) = ∑_{n ≤ x} Λ (n) n^{-s} + (ζ'/ζ) (s) - x^{1-s} / (1-s) - ∑_{n ≥ 1} x^{-2n-s} / (2n+s)`. -/
noncomputable def landauRHS (x : ℝ) (s : ℂ) : ℂ :=
  landauPrimeSum x s + logDeriv riemannZeta s - (x : ℂ) ^ (1 - s) / (1 - s)
    - landauTrivialSum x s

/-- **Landau's explicit formula**, with the sum over the zeros written as a `tsum`: for `x > 1`
not a prime power and `s` with `s ≠ 1`, `ζ s ≠ 0` and `s ≠ -2n` for every `n ≥ 1`,

`∑_{ρ ∈ 𝒩*} m_ρ x^{ρ - s} / (s - ρ) = ∑_{n ≤ x} Λ (n) n^{-s} + (ζ'/ζ) (s) - x^{1-s} / (1-s)
  - ∑_{n ≥ 1} x^{-2n-s} / (2n+s)`.

The left-hand side is only conditionally convergent, so as a `tsum` it takes the junk value `0`
and this `Prop` does not assert convergence; `ZetaZeros.LandauExplicitFormulaHasSum` is the form
that asserts the convergence too. -/
def LandauExplicitFormula : Prop :=
  ∀ x : ℝ, 1 < x → NotPrimePowerReal x → ∀ s : ℂ, s ≠ 1 → riemannZeta s ≠ 0 →
    (∀ n : ℕ, 1 ≤ n → s ≠ -(2 * (n : ℂ))) →
      ∑' ρ : allZeros, landauZeroTerm x s ρ = landauRHS x s

/-- **Landau's explicit formula with its left-hand side absolutely convergent**: the same identity
as `ZetaZeros.LandauExplicitFormula`, stated as a `HasSum`, so that the summability of the family
over `𝒩*` is part of the assertion.

This `Prop` is false: the terms have norm `≍ m_ρ / (1 + |t - im ρ|)` and the multiplicity of a
unit window at height `γ` is `≍ log γ`, so the family is not summable. -/
def LandauExplicitFormulaHasSum : Prop :=
  ∀ x : ℝ, 1 < x → NotPrimePowerReal x → ∀ s : ℂ, s ≠ 1 → riemannZeta s ≠ 0 →
    (∀ n : ℕ, 1 ≤ n → s ≠ -(2 * (n : ℂ))) →
      HasSum (landauZeroTerm x s) (landauRHS x s)

/-- **The symmetrised form of Landau's explicit formula**: for `x > 1` not a prime power and every
real `t`,

`ℓ (x, t) = x ⬝ R (3/2 + it) - x⁻¹ ⬝ R (-1/2 + it)`,

where `R` is `ZetaZeros.landauRHS` and `ℓ` is `ZetaZeros.zeroSide`. Both sides are absolutely
convergent series, unlike the two sides of `ZetaZeros.LandauExplicitFormula` taken separately: the
difference of the two zero sides pairs the terms at `3/2 + it` and `-1/2 + it`, which replaces
`1 / (s - ρ)` by `2 / (1 - (ρ - (1/2 + it))²)` and turns a conditionally convergent series into an
absolutely convergent one. -/
def LandauSymmetrisedFormula : Prop :=
  ∀ x : ℝ, 1 < x → NotPrimePowerReal x → ∀ t : ℝ,
    zeroSide x t
      = (x : ℂ) * landauRHS x ((3 / 2 : ℂ) + (t : ℂ) * I)
        - (x : ℂ)⁻¹ * landauRHS x (-(1 / 2 : ℂ) + (t : ℂ) * I)

/-! ### The symmetrisation of the zero side -/

/-- The symmetrised denominator is non-zero: its modulus is at least `3/4`. -/
private lemma one_sub_sq_ne_zero {ρ : ℂ} (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) (t : ℝ) :
    1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2 ≠ 0 := by
  intro h
  have hle := three_quarters_add_sq_le_norm_one_sub_sq h₀ h₁ t
  rw [h, norm_zero] at hle
  nlinarith [sq_nonneg (t - ρ.im)]

/-- The two factors of the symmetrised denominator are non-zero: their product is
`1 - (ρ - (1/2 + it))²`, whose modulus is at least `3/4`. -/
private lemma one_sub_ne_zero_and_one_add_ne_zero {ρ : ℂ} (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) (t : ℝ) :
    1 - (ρ - (1 / 2 + (t : ℂ) * I)) ≠ 0 ∧ 1 + (ρ - (1 / 2 + (t : ℂ) * I)) ≠ 0 := by
  set A : ℂ := ρ - (1 / 2 + (t : ℂ) * I) with hA
  have hprod : (1 - A) * (1 + A) = 1 - A ^ 2 := by ring
  have hne : 1 - A ^ 2 ≠ 0 := hA ▸ one_sub_sq_ne_zero h₀ h₁ t
  rw [← hprod] at hne
  exact ⟨fun h => hne (by rw [h, zero_mul]), fun h => hne (by rw [h, mul_zero])⟩

/-- **The term identity of the symmetrisation.** For `x > 0` and a zero `ρ` of the open critical
strip, the term of `ℓ (x, t)` at `ρ` is `x` times the term of Landau's zero side at `3/2 + it`
minus `x⁻¹` times the term at `-1/2 + it`.

Multiplying by `x^{s - 1/2}` turns `x^{ρ - s}` into `x^{ρ - 1/2}` in both, and with
`A = ρ - (1/2 + it)` the two denominators are `1 - A` and `-1 - A`, so the difference of the
reciprocals is `1/(1 - A) + 1/(1 + A) = 2/(1 - A²)`. -/
private lemma landauZeroTerm_symmetrise {x : ℝ} (hx : 0 < x) {ρ : ℂ} (h₀ : 0 < ρ.re)
    (h₁ : ρ.re < 1) (t : ℝ) :
    (x : ℂ) * ((zeroMultiplicity ρ : ℂ) *
        ((x : ℂ) ^ (ρ - ((3 / 2 : ℂ) + (t : ℂ) * I)) / ((3 / 2 : ℂ) + (t : ℂ) * I - ρ)))
      - (x : ℂ)⁻¹ * ((zeroMultiplicity ρ : ℂ) *
        ((x : ℂ) ^ (ρ - (-(1 / 2 : ℂ) + (t : ℂ) * I)) / (-(1 / 2 : ℂ) + (t : ℂ) * I - ρ)))
      = (zeroMultiplicity ρ : ℂ) * (2 * (x : ℂ) ^ (ρ - 1 / 2 - (t : ℂ) * I)
          / (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2)) := by
  have hx0 : (x : ℂ) ≠ 0 := by
    simpa using hx.ne'
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
  rw [hup, hum, hd₁, hd₂]
  have hsq : 1 - A ^ 2 = (1 - A) * (1 + A) := by ring
  rw [hsq]
  field_simp
  ring

/-- **The symmetrised formula follows from Landau's formula with absolute convergence.**
Subtracting the identity at `-1/2 + it`, scaled by `x⁻¹`, from the one at `3/2 + it`, scaled by
`x`, pairs the two zero sides term by term into the zero side `ℓ (x, t)` of Montgomery's lemma.

The hypotheses of Landau's formula hold at both points: neither is `1`, neither is a zero of `ζ`
(the non-trivial zeros have real part in `(0, 1)`, and `ζ` does not vanish on `re s = -1/2`), and
neither is a negative even integer, their real parts being `3/2` and `-1/2`. -/
theorem landauSymmetrisedFormula_of_hasSum (hL : LandauExplicitFormulaHasSum) :
    LandauSymmetrisedFormula := by
  intro x hx hnpp t
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := hx.le
  set a : ℂ := (3 / 2 : ℂ) + (t : ℂ) * I with ha
  set b : ℂ := -(1 / 2 : ℂ) + (t : ℂ) * I with hb
  have hare : a.re = 3 / 2 := by simp [ha]
  have hbre : b.re = -(1 / 2) := by simp [hb]
  have ha1 : a ≠ 1 := fun h => by rw [h] at hare; norm_num at hare
  have haζ : riemannZeta a ≠ 0 := by
    intro h
    have := riemannZeta_ne_zero_of_one_le_re (s := a) (by rw [hare]; norm_num)
    exact this h
  have han : ∀ n : ℕ, 1 ≤ n → a ≠ -(2 * (n : ℂ)) := by
    intro n _ h
    have : a.re = -(2 * (n : ℝ)) := by rw [h]; simp
    rw [hare] at this
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hb1 : b ≠ 1 := fun h => by rw [h] at hbre; norm_num at hbre
  have hbζ : riemannZeta b ≠ 0 := riemannZeta_ne_zero_of_re_eq_neg_half hbre
  have hbn : ∀ n : ℕ, 1 ≤ n → b ≠ -(2 * (n : ℂ)) := by
    intro n hn h
    have hre : b.re = -(2 * (n : ℝ)) := by rw [h]; simp
    rw [hbre] at hre
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hA := hL x hx hnpp a ha1 haζ han
  have hB := hL x hx hnpp b hb1 hbζ hbn
  have hpair := (hA.mul_left (x : ℂ)).sub (hB.mul_left (x : ℂ)⁻¹)
  have hterm : ∀ ρ : allZeros,
      (x : ℂ) * landauZeroTerm x a ρ - (x : ℂ)⁻¹ * landauZeroTerm x b ρ
        = (zeroMultiplicity (ρ : ℂ) : ℂ) * (2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I)
            / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2)) := by
    intro ρ
    obtain ⟨-, h₀, h₁⟩ := ρ.2
    exact landauZeroTerm_symmetrise hx0 h₀ h₁ t
  rw [zeroSide, ((hpair.congr_fun fun ρ => (hterm ρ).symm).tsum_eq)]

/-! ### The prime side -/

/-- The term of `D (x, t)` at `n`, in absolute value: `Λ (n) n^{-1/2}` times a weight at most
`x / n`, so at most `x` times the term of the absolutely convergent Dirichlet series of `Λ` at
`3/2`. -/
private lemma norm_weightedPrimeSumTerm_le {x : ℝ} (hx : 1 ≤ x) (t : ℝ) (n : ℕ) :
    ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) *
        ((min ((n : ℝ) / x) (x / (n : ℝ)) : ℝ) : ℂ)‖
      ≤ x * ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hx0 : (0 : ℝ) < x := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hΛ0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hmin0 : (0 : ℝ) ≤ min ((n : ℝ) / x) (x / (n : ℝ)) := le_min (by positivity) (by positivity)
  have hpow : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hn0 _
  have e₁ : ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) *
        ((min ((n : ℝ) / x) (x / (n : ℝ)) : ℝ) : ℂ)‖
      = Λ n / (n : ℝ) ^ ((1 : ℝ) / 2) * min ((n : ℝ) / x) (x / (n : ℝ)) := by
    rw [norm_mul, norm_div, Complex.norm_natCast_cpow_of_pos hn, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΛ0,
      abs_of_nonneg hmin0]
    norm_num
  have e₂ : ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ = Λ n / (n : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [LSeries.term_of_ne_zero hn.ne', norm_div, Complex.norm_natCast_cpow_of_pos hn,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ0]
    norm_num
  have hsplit : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 / 2 + 1 from by ring, Real.rpow_add hn0, Real.rpow_one]
  rw [e₁, e₂, hsplit]
  calc Λ n / (n : ℝ) ^ ((1 : ℝ) / 2) * min ((n : ℝ) / x) (x / (n : ℝ))
      ≤ Λ n / (n : ℝ) ^ ((1 : ℝ) / 2) * (x / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ = x * (Λ n / ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ))) := by
        field_simp

/-- The terms of `D (x, t)` are absolutely summable, by comparison with the Dirichlet series of `Λ`
at `3/2`. -/
private lemma summable_weightedPrimeSumTerm {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    Summable fun n : ℕ => (Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) *
      ((min ((n : ℝ) / x) (x / (n : ℝ)) : ℝ) : ℂ) := by
  have hre : ((3 / 2 : ℂ)).re = 3 / 2 := by norm_num
  have h32 : Summable fun n : ℕ => ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (3 / 2 : ℂ))
      (by rw [hre]; norm_num)).norm
  exact Summable.of_norm_bounded (h32.mul_left x) (norm_weightedPrimeSumTerm_le hx t)

/-- A sum over `Finset.Icc 1 m` of a function vanishing at `0` is the sum over `Finset.range
(m + 1)`: the only index of the larger set outside the smaller one is `0`. -/
private lemma sum_Icc_one_eq_sum_range_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ)
    (hf : f 0 = 0) : ∑ n ∈ Finset.Icc 1 m, f n = ∑ n ∈ Finset.range (m + 1), f n := by
  refine Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)
  · rw [Finset.mem_Icc] at hn
    exact Finset.mem_range.2 (by omega)
  · rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hn'
    have : n = 0 := by omega
    rw [this, hf]

/-- **The prime side of Montgomery's lemma.** For `x ≥ 1` and real `t`,

`x ⬝ (∑_{n ≤ x} Λ (n) n^{-3/2-it} + (ζ'/ζ) (3/2 + it)) - x⁻¹ ⬝ ∑_{n ≤ x} Λ (n) n^{1/2-it}
  = -D (x, t)`.

On the line `re s = 3/2` the Dirichlet series `-(ζ'/ζ) (s) = ∑_n Λ (n) n^{-s}` converges
absolutely, so the first two terms combine to `-x ∑_{n > x} Λ (n) n^{-3/2-it}`, which is the tail
of `D (x, t)` with weight `x / n`; the third term is its head, with weight `n / x`. -/
private lemma landauPrimeSum_symmetrise {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    (x : ℂ) * (landauPrimeSum x ((3 / 2 : ℂ) + (t : ℂ) * I)
          + logDeriv riemannZeta ((3 / 2 : ℂ) + (t : ℂ) * I))
        - (x : ℂ)⁻¹ * landauPrimeSum x (-(1 / 2 : ℂ) + (t : ℂ) * I)
      = -weightedPrimeSum x t := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxne : (x : ℂ) ≠ 0 := by simpa using hx0.ne'
  set K : ℕ := ⌊x⌋₊ + 1 with hK
  set a : ℂ := (3 / 2 : ℂ) + (t : ℂ) * I with ha
  set b : ℂ := -(1 / 2 : ℂ) + (t : ℂ) * I with hb
  have hare : a.re = 3 / 2 := by simp [ha]
  have has : LSeriesSummable ↗Λ a :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by rw [hare]; norm_num)
  have hlog : logDeriv riemannZeta a = -∑' n : ℕ, LSeries.term ↗Λ a n := by
    rw [logDeriv_apply, show (∑' n : ℕ, LSeries.term ↗Λ a n) = LSeries ↗Λ a from rfl,
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by rw [hare]; norm_num),
      neg_div, neg_neg]
  have hhead_a : ∑ n ∈ Finset.range K, LSeries.term ↗Λ a n = landauPrimeSum x a := by
    rw [landauPrimeSum, hK, sum_Icc_one_eq_sum_range_succ _ _ (by simp)]
    refine Finset.sum_congr rfl fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp [hn0, LSeries.term]
    · rw [LSeries.term_of_ne_zero hn0.ne']
  have hsplit_a : (∑ n ∈ Finset.range K, LSeries.term ↗Λ a n)
      + ∑' i : ℕ, LSeries.term ↗Λ a (i + K) = ∑' n : ℕ, LSeries.term ↗Λ a n :=
    has.sum_add_tsum_nat_add K
  set g : ℕ → ℂ := fun n => (Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) *
    ((min ((n : ℝ) / x) (x / (n : ℝ)) : ℝ) : ℂ) with hg
  have hgs : Summable g := summable_weightedPrimeSumTerm hx t
  have hsplit_g : (∑ n ∈ Finset.range K, g n) + ∑' i : ℕ, g (i + K) = weightedPrimeSum x t :=
    hgs.sum_add_tsum_nat_add K
  have hhead_g : ∑ n ∈ Finset.range K, g n = (x : ℂ)⁻¹ * landauPrimeSum x b := by
    rw [landauPrimeSum, sum_Icc_one_eq_sum_range_succ _ _ (by simp), Finset.mul_sum, ← hK]
    refine Finset.sum_congr rfl fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp [hn0, hg]
    have hnx : (n : ℝ) ≤ x := by
      rw [Finset.mem_range, hK] at hn
      exact (Nat.le_floor_iff hx0.le).1 (by omega)
    have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hmin : min ((n : ℝ) / x) (x / (n : ℝ)) = (n : ℝ) / x :=
      min_eq_left (by rw [div_le_div_iff₀ hx0 hn0']; nlinarith)
    have hbne : (n : ℂ) ^ b ≠ 0 := fun h => hnne (Complex.cpow_eq_zero_iff _ _ |>.1 h).1
    have hexp : (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) = (n : ℂ) * (n : ℂ) ^ b := by
      rw [show (1 : ℂ) / 2 + (t : ℂ) * I = 1 + b from by rw [hb]; ring,
        Complex.cpow_add _ _ hnne, Complex.cpow_one]
    simp only [hg]
    rw [hmin, hexp, Complex.ofReal_div, Complex.ofReal_natCast]
    field_simp
  have htail_g : ∑' i : ℕ, g (i + K) = (x : ℂ) * ∑' i : ℕ, LSeries.term ↗Λ a (i + K) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    have hn0 : 0 < i + K := by omega
    have hn0' : (0 : ℝ) < ((i + K : ℕ) : ℝ) := by exact_mod_cast hn0
    have hnne : ((i + K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hxn : x < ((i + K : ℕ) : ℝ) := by
      have h1 : x < (K : ℝ) := by
        rw [hK]
        push_cast
        exact Nat.lt_floor_add_one x
      have h2 : (K : ℝ) ≤ ((i + K : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_left K i
      linarith
    have hmin : min (((i + K : ℕ) : ℝ) / x) (x / ((i + K : ℕ) : ℝ))
        = x / ((i + K : ℕ) : ℝ) :=
      min_eq_right (by rw [div_le_div_iff₀ hn0' hx0]; nlinarith)
    have hane : ((i + K : ℕ) : ℂ) ^ a ≠ 0 := fun h => hnne (Complex.cpow_eq_zero_iff _ _ |>.1 h).1
    have hexp : ((i + K : ℕ) : ℂ) ^ a
        = ((i + K : ℕ) : ℂ) * ((i + K : ℕ) : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) := by
      rw [show a = 1 + ((1 : ℂ) / 2 + (t : ℂ) * I) from by rw [ha]; ring,
        Complex.cpow_add _ _ hnne, Complex.cpow_one]
    simp only [hg]
    rw [hmin, LSeries.term_of_ne_zero hn0.ne' _ _, hexp, Complex.ofReal_div,
      Complex.ofReal_natCast]
    have hnne' : ((i + K : ℕ) : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) ≠ 0 :=
      fun h => hnne (Complex.cpow_eq_zero_iff _ _ |>.1 h).1
    field_simp
  have hzeta : ∑' n : ℕ, LSeries.term ↗Λ a n
      = landauPrimeSum x a + ∑' i : ℕ, LSeries.term ↗Λ a (i + K) := by
    rw [← hsplit_a, hhead_a]
  rw [hlog, hzeta, ← hsplit_g, hhead_g, htail_g]
  ring


/-! ### The poles at `s = 1` -/

/-- The algebra of the pole pair, with the two denominators opaque: when `z₁ + z₂ = 2`,
`v (u v⁻¹ / (-z₁)) - v⁻¹ (u v / z₂) = -2u / (z₁ z₂)`. -/
private lemma pole_algebra {u v z₁ z₂ : ℂ} (hv : v ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hsum : z₁ + z₂ = 2) :
    v * (u * v⁻¹ / (-z₁)) - v⁻¹ * (u * v / z₂) = -(u * (2 / (z₁ * z₂))) := by
  rw [← hsum]
  field_simp
  ring

/-- **The two pole terms, combined.** The terms `x^{1-s} / (1-s)` of Landau's formula at
`3/2 + it` and at `-1/2 + it` both become `x^{1/2-it}` after the scaling, and the two denominators
`-(1/2 + it)` and `3/2 - it` add to `2`, so the pair collapses to
`-2 x^{1/2-it} / ((1/2 + it) (3/2 - it))`. -/
private lemma polePair_eq {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x : ℂ) * ((x : ℂ) ^ (1 - ((3 / 2 : ℂ) + (t : ℂ) * I)) / (1 - ((3 / 2 : ℂ) + (t : ℂ) * I)))
        - (x : ℂ)⁻¹ * ((x : ℂ) ^ (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I))
          / (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I)))
      = -((x : ℂ) ^ ((1 : ℂ) / 2 - (t : ℂ) * I) *
          (2 / (((1 : ℂ) / 2 + (t : ℂ) * I) * ((3 : ℂ) / 2 - (t : ℂ) * I)))) := by
  have hxne : (x : ℂ) ≠ 0 := by simpa using hx.ne'
  have hz₁ : ((1 : ℂ) / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hz₂ : ((3 : ℂ) / 2 - (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h₁ : (x : ℂ) ^ (1 - ((3 / 2 : ℂ) + (t : ℂ) * I))
      = (x : ℂ) ^ ((1 : ℂ) / 2 - (t : ℂ) * I) * (x : ℂ)⁻¹ := by
    rw [show (1 : ℂ) - ((3 / 2 : ℂ) + (t : ℂ) * I) = ((1 : ℂ) / 2 - (t : ℂ) * I) + (-1) from by
      ring, Complex.cpow_add _ _ hxne, Complex.cpow_neg_one]
  have h₂ : (x : ℂ) ^ (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I))
      = (x : ℂ) ^ ((1 : ℂ) / 2 - (t : ℂ) * I) * (x : ℂ) := by
    rw [show (1 : ℂ) - (-(1 / 2 : ℂ) + (t : ℂ) * I) = ((1 : ℂ) / 2 - (t : ℂ) * I) + 1 from by
      ring, Complex.cpow_add _ _ hxne, Complex.cpow_one]
  rw [h₁, h₂, show (1 : ℂ) - ((3 / 2 : ℂ) + (t : ℂ) * I) = -((1 : ℂ) / 2 + (t : ℂ) * I) from by
    ring, show (1 : ℂ) - (-(1 / 2 : ℂ) + (t : ℂ) * I) = (3 : ℂ) / 2 - (t : ℂ) * I from by ring]
  exact pole_algebra hxne hz₁ hz₂ (by ring)

/-- `|1/2 + it| ⬝ |3/2 - it| ≥ 3/8 (1 + t²)`: each factor dominates both its own real part and
`|t|`, so the product dominates both `3/4` and `t²`. -/
private lemma three_eighths_mul_le_norm_mul_norm (t : ℝ) :
    3 / 8 * (1 + t ^ 2) ≤ ‖(1 : ℂ) / 2 + (t : ℂ) * I‖ * ‖(3 : ℂ) / 2 - (t : ℂ) * I‖ := by
  have hre₁ : ((1 : ℂ) / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
  have him₁ : ((1 : ℂ) / 2 + (t : ℂ) * I).im = t := by simp
  have hre₂ : ((3 : ℂ) / 2 - (t : ℂ) * I).re = 3 / 2 := by simp
  have him₂ : ((3 : ℂ) / 2 - (t : ℂ) * I).im = -t := by simp
  have h₁ : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) / 2 + (t : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((1 : ℂ) / 2 + (t : ℂ) * I)
    rw [hre₁] at this
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at this
    exact this
  have h₂ : (3 : ℝ) / 2 ≤ ‖(3 : ℂ) / 2 - (t : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((3 : ℂ) / 2 - (t : ℂ) * I)
    rw [hre₂] at this
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)] at this
    exact this
  have h₃ : |t| ≤ ‖(1 : ℂ) / 2 + (t : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((1 : ℂ) / 2 + (t : ℂ) * I)
    rwa [him₁] at this
  have h₄ : |t| ≤ ‖(3 : ℂ) / 2 - (t : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((3 : ℂ) / 2 - (t : ℂ) * I)
    rwa [him₂, abs_neg] at this
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  have habs0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  nlinarith [mul_le_mul h₃ h₄ habs0 (by linarith : (0 : ℝ) ≤ ‖(1 : ℂ) / 2 + (t : ℂ) * I‖),
    mul_le_mul h₁ h₂ (by norm_num : (0 : ℝ) ≤ 3 / 2)
      (by linarith : (0 : ℝ) ≤ ‖(1 : ℂ) / 2 + (t : ℂ) * I‖)]

/-- **The bound for the pole pair**, `O (√x / (1 + t²))`. The two terms must be combined before
being estimated: separately each is of size `√x / |t|`. -/
private lemma norm_polePair_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖(x : ℂ) * ((x : ℂ) ^ (1 - ((3 / 2 : ℂ) + (t : ℂ) * I)) / (1 - ((3 / 2 : ℂ) + (t : ℂ) * I)))
        - (x : ℂ)⁻¹ * ((x : ℂ) ^ (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I))
          / (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I)))‖
      ≤ 6 * Real.sqrt x / (1 + t ^ 2) := by
  have hcpow : ‖(x : ℂ) ^ ((1 : ℂ) / 2 - (t : ℂ) * I)‖ = Real.sqrt x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Real.sqrt_eq_rpow]
    norm_num
  have hden := three_eighths_mul_le_norm_mul_norm t
  have ht : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hdenpos : (0 : ℝ) < ‖(1 : ℂ) / 2 + (t : ℂ) * I‖ * ‖(3 : ℂ) / 2 - (t : ℂ) * I‖ :=
    lt_of_lt_of_le (by positivity) hden
  rw [polePair_eq hx t, norm_neg, norm_mul, norm_div, norm_mul, hcpow,
    show ‖(2 : ℂ)‖ = 2 from by norm_num]
  have hstep : 2 / (‖(1 : ℂ) / 2 + (t : ℂ) * I‖ * ‖(3 : ℂ) / 2 - (t : ℂ) * I‖)
      ≤ 6 / (1 + t ^ 2) := by
    rw [div_le_div_iff₀ hdenpos ht]
    linarith
  calc Real.sqrt x * (2 / (‖(1 : ℂ) / 2 + (t : ℂ) * I‖ * ‖(3 : ℂ) / 2 - (t : ℂ) * I‖))
      ≤ Real.sqrt x * (6 / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg x)
    _ = 6 * Real.sqrt x / (1 + t ^ 2) := by ring

/-! ### The trivial zeros -/

/-- `∑_{n ≥ 0} (n+1)^{-2}` converges. Its value is `π²/6`, but only the convergence is used:
the constant of the trivial-zero bound is left existential. -/
private lemma summable_one_div_natCast_add_one_sq :
    Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).2 one_lt_two
  refine ((summable_nat_add_iff 1).2 h).congr fun n => ?_
  push_cast
  ring

/-- The algebra of the trivial-zero pair, with the two denominators opaque: when `q = p + 2`,
`v (w v⁻¹ / q) - v⁻¹ (w v / p) = -2w / (p q)`. -/
private lemma trivial_algebra {w v p q : ℂ} (hv : v ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : q = p + 2) :
    v * (w * v⁻¹ / q) - v⁻¹ * (w * v / p) = -(w * (2 / (p * q))) := by
  subst hpq
  field_simp
  ring

/-- The series over the trivial zeros converges for `x > 1` and `re s ≥ -1`: the numerator decays
geometrically, at ratio `x^{-2}`, while the denominator is at least `1`. -/
private lemma summable_landauTrivialTerm {x : ℝ} (hx : 1 < x) {s : ℂ} (hs : -1 ≤ s.re) :
    Summable fun n : ℕ => (x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - s) / (2 * ((n : ℂ) + 1) + s) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set σ : ℝ := s.re with hσ
  have hr : x ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have hr0 : (0 : ℝ) ≤ x ^ (-2 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hx0 _)
  have hmaj : Summable fun n : ℕ => x ^ (-2 - σ) * (x ^ (-2 : ℝ)) ^ n :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  refine Summable.of_norm_bounded hmaj fun n => ?_
  have hnum : ‖(x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - s)‖ = x ^ (-(2 * ((n : ℝ) + 1)) - σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    congr 1
    simp [hσ]
  have hden : (1 : ℝ) ≤ ‖2 * ((n : ℂ) + 1) + s‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    have hre : (2 * ((n : ℂ) + 1) + s).re = 2 * ((n : ℝ) + 1) + σ := by
      simp [hσ]
    rw [hre]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have heq : x ^ (-(2 * ((n : ℝ) + 1)) - σ) = x ^ (-2 - σ) * (x ^ (-2 : ℝ)) ^ n := by
    rw [← Real.rpow_natCast (x ^ (-2 : ℝ)) n, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    ring
  rw [norm_div, hnum, heq]
  have hpos : (0 : ℝ) < x ^ (-2 - σ) * (x ^ (-2 : ℝ)) ^ n := by
    have : (0 : ℝ) < x ^ (-2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    positivity
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖2 * ((n : ℂ) + 1) + s‖)]
  nlinarith

/-- **The two sums over the trivial zeros, combined.** After the scaling both numerators become
`x^{-2(n+1) - 1/2 - it}`, and the two denominators differ by `2`, so the pair collapses to the
series with the quadratic denominator `(2(n+1) - 1/2 + it) (2(n+1) + 3/2 + it)`. -/
private lemma trivialPair_eq {x : ℝ} (hx : 1 < x) (t : ℝ) :
    (x : ℂ) * landauTrivialSum x ((3 / 2 : ℂ) + (t : ℂ) * I)
        - (x : ℂ)⁻¹ * landauTrivialSum x (-(1 / 2 : ℂ) + (t : ℂ) * I)
      = -∑' n : ℕ, (x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - 1 / 2 - (t : ℂ) * I) *
          (2 / ((2 * ((n : ℂ) + 1) - 1 / 2 + (t : ℂ) * I) *
            (2 * ((n : ℂ) + 1) + 3 / 2 + (t : ℂ) * I))) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxne : (x : ℂ) ≠ 0 := by simpa using hx0.ne'
  have hA := (summable_landauTrivialTerm hx (s := (3 / 2 : ℂ) + (t : ℂ) * I)
    (by simp; norm_num)).hasSum
  have hB := (summable_landauTrivialTerm hx (s := -(1 / 2 : ℂ) + (t : ℂ) * I)
    (by simp; norm_num)).hasSum
  have hpair := (hA.mul_left (x : ℂ)).sub (hB.mul_left (x : ℂ)⁻¹)
  have hterm : ∀ n : ℕ,
      (x : ℂ) * ((x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - ((3 / 2 : ℂ) + (t : ℂ) * I))
          / (2 * ((n : ℂ) + 1) + ((3 / 2 : ℂ) + (t : ℂ) * I)))
        - (x : ℂ)⁻¹ * ((x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - (-(1 / 2 : ℂ) + (t : ℂ) * I))
          / (2 * ((n : ℂ) + 1) + (-(1 / 2 : ℂ) + (t : ℂ) * I)))
      = -((x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - 1 / 2 - (t : ℂ) * I) *
          (2 / ((2 * ((n : ℂ) + 1) - 1 / 2 + (t : ℂ) * I) *
            (2 * ((n : ℂ) + 1) + 3 / 2 + (t : ℂ) * I)))) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : (2 * ((n : ℂ) + 1) - 1 / 2 + (t : ℂ) * I) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hq : (2 * ((n : ℂ) + 1) + 3 / 2 + (t : ℂ) * I) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have e₁ : (x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - ((3 / 2 : ℂ) + (t : ℂ) * I))
        = (x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - 1 / 2 - (t : ℂ) * I) * (x : ℂ)⁻¹ := by
      rw [show -(2 * ((n : ℂ) + 1)) - ((3 / 2 : ℂ) + (t : ℂ) * I)
          = (-(2 * ((n : ℂ) + 1)) - 1 / 2 - (t : ℂ) * I) + (-1) from by ring,
        Complex.cpow_add _ _ hxne, Complex.cpow_neg_one]
    have e₂ : (x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - (-(1 / 2 : ℂ) + (t : ℂ) * I))
        = (x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - 1 / 2 - (t : ℂ) * I) * (x : ℂ) := by
      rw [show -(2 * ((n : ℂ) + 1)) - (-(1 / 2 : ℂ) + (t : ℂ) * I)
          = (-(2 * ((n : ℂ) + 1)) - 1 / 2 - (t : ℂ) * I) + 1 from by ring,
        Complex.cpow_add _ _ hxne, Complex.cpow_one]
    rw [e₁, e₂,
      show 2 * ((n : ℂ) + 1) + ((3 / 2 : ℂ) + (t : ℂ) * I)
        = 2 * ((n : ℂ) + 1) + 3 / 2 + (t : ℂ) * I from by ring,
      show 2 * ((n : ℂ) + 1) + (-(1 / 2 : ℂ) + (t : ℂ) * I)
        = 2 * ((n : ℂ) + 1) - 1 / 2 + (t : ℂ) * I from by ring]
    exact trivial_algebra hxne hp hq (by ring)
  rw [landauTrivialSum, landauTrivialSum,
    ← (hpair.congr_fun fun n => (hterm n).symm).tsum_eq, tsum_neg]

/-- **The bound for the trivial-zero pair**, `O (1/x)`. The two terms must be combined before being
estimated: separately each is unbounded as `x → 1⁺`, since the geometric decay `x^{-2n}`
degenerates there, and only the quadratic denominator left by the pairing survives. -/
private lemma norm_trivialPair_le {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ‖(x : ℂ) * landauTrivialSum x ((3 / 2 : ℂ) + (t : ℂ) * I)
        - (x : ℂ)⁻¹ * landauTrivialSum x (-(1 / 2 : ℂ) + (t : ℂ) * I)‖
      ≤ 8 / 9 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) / x := by
  have hx0 : (0 : ℝ) < x := by linarith
  set c : ℕ → ℂ := fun n => (x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - 1 / 2 - (t : ℂ) * I) *
    (2 / ((2 * ((n : ℂ) + 1) - 1 / 2 + (t : ℂ) * I) *
      (2 * ((n : ℂ) + 1) + 3 / 2 + (t : ℂ) * I))) with hc
  have hbound : ∀ n : ℕ, ‖c n‖ ≤ 8 / 9 * x ^ (-(5 : ℝ) / 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnum : ‖(x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - 1 / 2 - (t : ℂ) * I)‖
        ≤ x ^ (-(5 : ℝ) / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      refine Real.rpow_le_rpow_of_exponent_le hx.le ?_
      simp
      linarith
    have hp : 3 / 2 * ((n : ℝ) + 1) ≤ ‖2 * ((n : ℂ) + 1) - 1 / 2 + (t : ℂ) * I‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      simp
      linarith
    have hq : 3 / 2 * ((n : ℝ) + 1) ≤ ‖2 * ((n : ℂ) + 1) + 3 / 2 + (t : ℂ) * I‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      simp
      linarith
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hden : 9 / 4 * ((n : ℝ) + 1) ^ 2
        ≤ ‖2 * ((n : ℂ) + 1) - 1 / 2 + (t : ℂ) * I‖
          * ‖2 * ((n : ℂ) + 1) + 3 / 2 + (t : ℂ) * I‖ := by
      nlinarith [mul_le_mul hp hq (by positivity) (by linarith)]
    have hdenpos : (0 : ℝ) < ‖2 * ((n : ℂ) + 1) - 1 / 2 + (t : ℂ) * I‖
        * ‖2 * ((n : ℂ) + 1) + 3 / 2 + (t : ℂ) * I‖ := lt_of_lt_of_le (by positivity) hden
    have hxpow : (0 : ℝ) < x ^ (-(5 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
    rw [hc]
    simp only [norm_mul, norm_div, norm_mul]
    rw [show ‖(2 : ℂ)‖ = 2 from by norm_num]
    have hstep : 2 / (‖2 * ((n : ℂ) + 1) - 1 / 2 + (t : ℂ) * I‖
        * ‖2 * ((n : ℂ) + 1) + 3 / 2 + (t : ℂ) * I‖)
        ≤ 8 / 9 * (1 / ((n : ℝ) + 1) ^ 2) := by
      rw [div_le_iff₀ hdenpos]
      have h1 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
      have hne : ((n : ℝ) + 1) ^ 2 ≠ 0 := ne_of_gt h1
      have key : 8 / 9 * (1 / ((n : ℝ) + 1) ^ 2) * (9 / 4 * ((n : ℝ) + 1) ^ 2) = 2 := by
        field_simp
        ring
      linarith [mul_le_mul_of_nonneg_left hden
        (show (0 : ℝ) ≤ 8 / 9 * (1 / ((n : ℝ) + 1) ^ 2) by positivity)]
    calc ‖(x : ℂ) ^ (-(2 * ((n : ℂ) + 1)) - 1 / 2 - (t : ℂ) * I)‖
          * (2 / (‖2 * ((n : ℂ) + 1) - 1 / 2 + (t : ℂ) * I‖
            * ‖2 * ((n : ℂ) + 1) + 3 / 2 + (t : ℂ) * I‖))
        ≤ x ^ (-(5 : ℝ) / 2) * (8 / 9 * (1 / ((n : ℝ) + 1) ^ 2)) := by
          refine mul_le_mul hnum hstep (by positivity) (le_of_lt hxpow)
      _ = 8 / 9 * x ^ (-(5 : ℝ) / 2) * (1 / ((n : ℝ) + 1) ^ 2) := by ring
  have hsumv : Summable fun n : ℕ => 8 / 9 * x ^ (-(5 : ℝ) / 2) * (1 / ((n : ℝ) + 1) ^ 2) :=
    summable_one_div_natCast_add_one_sq.mul_left _
  have hnormsum : Summable fun n : ℕ => ‖c n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsumv
  have hle : ∑' n : ℕ, ‖c n‖
      ≤ ∑' n : ℕ, 8 / 9 * x ^ (-(5 : ℝ) / 2) * (1 / ((n : ℝ) + 1) ^ 2) :=
    hnormsum.tsum_le_tsum hbound hsumv
  have hS0 : (0 : ℝ) ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 :=
    tsum_nonneg fun n => by positivity
  have hxpow : (0 : ℝ) < x ^ (-(5 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
  have hxle : x ^ (-(5 : ℝ) / 2) ≤ x⁻¹ := by
    have h1 : x ^ (-(5 : ℝ) / 2) ≤ x ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
    rwa [Real.rpow_neg_one] at h1
  rw [trivialPair_eq hx t, norm_neg]
  calc ‖∑' n : ℕ, c n‖ ≤ ∑' n : ℕ, ‖c n‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, 8 / 9 * x ^ (-(5 : ℝ) / 2) * (1 / ((n : ℝ) + 1) ^ 2) := hle
    _ = 8 / 9 * x ^ (-(5 : ℝ) / 2) * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := tsum_mul_left
    _ ≤ 8 / 9 * x⁻¹ * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hxle (show (0 : ℝ) ≤ 8 / 9 by norm_num)
        exact mul_le_mul_of_nonneg_right this hS0
    _ = 8 / 9 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) / x := by
        rw [div_eq_mul_inv]
        ring

/-! ### Montgomery's explicit-formula lemma -/

/-- The exact decomposition in Montgomery's lemma. Assuming the symmetrised form of Landau's
explicit formula, `ℓ (x, t) + D (x, t) - log (|t| + 2) / x` is the sum of exactly three error
terms: the logarithmic derivative on the line `re s = -1/2` measured against `log (|t| + 2)`, the
pole pair, and the trivial-zero pair. -/
private lemma zeroSide_add_weightedPrimeSum_sub_div_eq (hL : LandauSymmetrisedFormula) {x : ℝ}
    (hx : 1 < x) (hnpp : NotPrimePowerReal x) (t : ℝ) :
    zeroSide x t + weightedPrimeSum x t - ((Real.log (|t| + 2) / x : ℝ) : ℂ)
      = -((x : ℂ)⁻¹ * (logDeriv riemannZeta (-(1 / 2 : ℂ) + (t : ℂ) * I)
            + (Real.log (|t| + 2) : ℂ)))
        - ((x : ℂ) * ((x : ℂ) ^ (1 - ((3 / 2 : ℂ) + (t : ℂ) * I))
              / (1 - ((3 / 2 : ℂ) + (t : ℂ) * I)))
          - (x : ℂ)⁻¹ * ((x : ℂ) ^ (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I))
              / (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I))))
        - ((x : ℂ) * landauTrivialSum x ((3 / 2 : ℂ) + (t : ℂ) * I)
          - (x : ℂ)⁻¹ * landauTrivialSum x (-(1 / 2 : ℂ) + (t : ℂ) * I)) := by
  rw [hL x hx hnpp t, landauRHS, landauRHS, Complex.ofReal_div]
  linear_combination landauPrimeSum_symmetrise hx.le t

/-- **Montgomery's explicit-formula lemma.** Assume `ZetaZeros.LandauSymmetrisedFormula`. There is
an absolute constant `C > 0` such that for every `x > 1` that is not a prime power and every real
`t`,

`|ℓ (x, t) + D (x, t) - log (|t| + 2) / x| ≤ C (1/x + √x / (1 + t²))`.

The difference is the sum of three error terms, bounded in turn: `O (1/x)` from the vertical-line
estimate for `ζ'/ζ` on `re s = -1/2`, `O (√x / (1 + t²))` from the pole pair, and `O (1/x)` from
the trivial-zero pair. -/
theorem exists_norm_zeroSide_add_weightedPrimeSum_sub_div_le (hL : LandauSymmetrisedFormula) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → NotPrimePowerReal x → ∀ t : ℝ,
      ‖zeroSide x t + weightedPrimeSum x t - ((Real.log (|t| + 2) / x : ℝ) : ℂ)‖
        ≤ C * (1 / x + Real.sqrt x / (1 + t ^ 2)) := by
  obtain ⟨C₁, hC₁, hC₁b⟩ := exists_norm_deriv_riemannZeta_div_add_log_le
  have hS0 : (0 : ℝ) ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := tsum_nonneg fun n => by positivity
  refine ⟨C₁ + 8 / 9 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) + 6, by linarith,
    fun x hx hnpp t => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have ht : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hu0 : (0 : ℝ) < 1 / x := by positivity
  have hv0 : (0 : ℝ) ≤ Real.sqrt x / (1 + t ^ 2) := by positivity
  have hA : ‖(x : ℂ)⁻¹ * (logDeriv riemannZeta (-(1 / 2 : ℂ) + (t : ℂ) * I)
      + (Real.log (|t| + 2) : ℂ))‖ ≤ C₁ / x := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, logDeriv_apply]
    rw [inv_mul_eq_div, div_le_div_iff₀ hx0 hx0]
    nlinarith [hC₁b t]
  have htri := norm_sub_le (-((x : ℂ)⁻¹ * (logDeriv riemannZeta (-(1 / 2 : ℂ) + (t : ℂ) * I)
        + (Real.log (|t| + 2) : ℂ)))
      - ((x : ℂ) * ((x : ℂ) ^ (1 - ((3 / 2 : ℂ) + (t : ℂ) * I))
            / (1 - ((3 / 2 : ℂ) + (t : ℂ) * I)))
        - (x : ℂ)⁻¹ * ((x : ℂ) ^ (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I))
            / (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I)))))
    ((x : ℂ) * landauTrivialSum x ((3 / 2 : ℂ) + (t : ℂ) * I)
      - (x : ℂ)⁻¹ * landauTrivialSum x (-(1 / 2 : ℂ) + (t : ℂ) * I))
  have htri' := norm_sub_le (-((x : ℂ)⁻¹ * (logDeriv riemannZeta (-(1 / 2 : ℂ) + (t : ℂ) * I)
        + (Real.log (|t| + 2) : ℂ))))
    ((x : ℂ) * ((x : ℂ) ^ (1 - ((3 / 2 : ℂ) + (t : ℂ) * I))
          / (1 - ((3 / 2 : ℂ) + (t : ℂ) * I)))
      - (x : ℂ)⁻¹ * ((x : ℂ) ^ (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I))
          / (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I))))
  rw [norm_neg] at htri'
  have hpole := norm_polePair_le hx0 t
  have htriv := norm_trivialPair_le hx t
  rw [zeroSide_add_weightedPrimeSum_sub_div_eq hL hx hnpp t]
  have hchain : ‖-((x : ℂ)⁻¹ * (logDeriv riemannZeta (-(1 / 2 : ℂ) + (t : ℂ) * I)
          + (Real.log (|t| + 2) : ℂ)))
        - ((x : ℂ) * ((x : ℂ) ^ (1 - ((3 / 2 : ℂ) + (t : ℂ) * I))
              / (1 - ((3 / 2 : ℂ) + (t : ℂ) * I)))
          - (x : ℂ)⁻¹ * ((x : ℂ) ^ (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I))
              / (1 - (-(1 / 2 : ℂ) + (t : ℂ) * I))))
        - ((x : ℂ) * landauTrivialSum x ((3 / 2 : ℂ) + (t : ℂ) * I)
          - (x : ℂ)⁻¹ * landauTrivialSum x (-(1 / 2 : ℂ) + (t : ℂ) * I))‖
      ≤ C₁ / x + 6 * Real.sqrt x / (1 + t ^ 2)
        + 8 / 9 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) / x := by
    linarith
  refine hchain.trans ?_
  have hdiv : C₁ / x = C₁ * (1 / x) := by ring
  have hdiv' : 8 / 9 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) / x
      = 8 / 9 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) * (1 / x) := by ring
  have hdiv'' : 6 * Real.sqrt x / (1 + t ^ 2) = 6 * (Real.sqrt x / (1 + t ^ 2)) := by ring
  rw [hdiv, hdiv', hdiv'']
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ C₁ + 8 / 9 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) by
    linarith) hv0]

/-! ### From `x` off the prime powers to every `x ≥ 1` -/

/-- Immediately to the right of any real there is a point that is not a natural number: of the two
candidates `x + δ/2` and `x + δ/3` at most one can be, since they differ by less than `1`. -/
private lemma exists_gt_lt_add_forall_ne_natCast (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℝ, x < y ∧ y < x + ε ∧ ∀ n : ℕ, y ≠ (n : ℝ) := by
  have hδ : 0 < min ε 1 := lt_min hε one_pos
  have hδ1 : min ε 1 ≤ 1 := min_le_right _ _
  have hδε : min ε 1 ≤ ε := min_le_left _ _
  by_cases h : ∀ n : ℕ, x + min ε 1 / 2 ≠ (n : ℝ)
  · exact ⟨x + min ε 1 / 2, by linarith, by linarith, h⟩
  · push Not at h
    obtain ⟨m, hm⟩ := h
    refine ⟨x + min ε 1 / 3, by linarith, by linarith, fun k hk => ?_⟩
    have hmk : (k : ℝ) < (m : ℝ) := by rw [← hm, ← hk]; linarith
    have hkm : k < m := by exact_mod_cast hmk
    have hone : (1 : ℝ) ≤ (m : ℝ) - (k : ℝ) := by
      have h1 : k + 1 ≤ m := hkm
      have h2 := (Nat.cast_le (α := ℝ)).2 h1
      push_cast at h2
      linarith
    have hdiff : (m : ℝ) - (k : ℝ) = min ε 1 / 6 := by rw [← hm, ← hk]; ring
    linarith

/-- `x ↦ x^c`, as a map `ℝ → ℂ`, is continuous away from `0`. -/
private lemma continuousOn_ofReal_cpow (c : ℂ) {X : ℝ} :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ c) (Set.Icc 1 X) := fun x hx =>
  (Complex.continuousAt_ofReal_cpow_const x c
    (Or.inr (by have : (1 : ℝ) ≤ x := hx.1; intro h; rw [h] at this; norm_num at this)))
      |>.continuousWithinAt

/-- The shape of the term bound: a nonnegative weight `m`, a numerator `2 v` with `v ≤ w`, and a
denominator at least `3/4 (1 + s²)`, give `m ⬝ 2 v / N ≤ 8/3 ⬝ w ⬝ m / (1 + s²)`. -/
private lemma mul_two_div_le' {m s N v w : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) (hvw : v ≤ w)
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

/-- The term of `ℓ (x, t)` at a zero `ρ`, bounded uniformly for `x` in `[1, X]`: the numerator is
at most `2 √X` and the denominator at least `3/4 (1 + (t - im ρ)²)`. -/
private lemma mul_norm_zeroSideTerm_le_sqrt {x X : ℝ} (hx : 1 ≤ x) (hxX : x ≤ X) {ρ : ℂ}
    (hρ : ρ ∈ allZeros) (t : ℝ) :
    (zeroMultiplicity ρ : ℝ) * ‖2 * (x : ℂ) ^ (ρ - 1 / 2 - (t : ℂ) * I)
        / (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2)‖
      ≤ 8 / 3 * Real.sqrt X * ((zeroMultiplicity ρ : ℝ) / (1 + (t - ρ.im) ^ 2)) := by
  obtain ⟨-, h0, h1⟩ := hρ
  have hx0 : (0 : ℝ) < x := by linarith
  have hre : (ρ - 1 / 2 - (t : ℂ) * I).re = ρ.re - 1 / 2 := by simp
  have hnorm : ‖2 * (x : ℂ) ^ (ρ - 1 / 2 - (t : ℂ) * I)
      / (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2)‖
      = 2 * x ^ (ρ.re - 1 / 2) / ‖1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2‖ := by
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
    norm_num
  rw [hnorm]
  refine mul_two_div_le' (Nat.cast_nonneg _) (Real.rpow_nonneg hx0.le _) ?_ ?_
  · rw [Real.sqrt_eq_rpow]
    calc x ^ (ρ.re - 1 / 2) ≤ x ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ ≤ X ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow hx0.le hxX (by norm_num)
  · have hden := three_quarters_add_sq_le_norm_one_sub_sq h0 h1 t
    nlinarith [sq_nonneg (t - ρ.im)]

/-- **`ℓ (x, t)` is continuous in `x` on `[1, X]`.** Each term is continuous, and on a bounded
range the series is dominated by the Poisson-weighted count scaled by `√X`. -/
private lemma continuousOn_zeroSide {X : ℝ} (t : ℝ) :
    ContinuousOn (fun x : ℝ => zeroSide x t) (Set.Icc 1 X) := by
  obtain ⟨C, -, hC⟩ := exists_summable_poissonWeight_tsum_le
  obtain ⟨hsum, -⟩ := hC t
  simp only [zeroSide]
  refine continuousOn_tsum (u := fun ρ : allZeros => 8 / 3 * Real.sqrt X *
    ((zeroMultiplicity (ρ : ℂ) : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2))) (fun ρ => ?_)
    (hsum.mul_left _) (fun ρ x hx => ?_)
  · obtain ⟨-, h0, h1⟩ := ρ.2
    refine continuousOn_const.mul (ContinuousOn.div (continuousOn_const.mul
      (continuousOn_ofReal_cpow _)) continuousOn_const fun x hx => ?_)
    exact one_sub_sq_ne_zero h0 h1 t
  · rw [norm_mul, Complex.norm_natCast]
    exact mul_norm_zeroSideTerm_le_sqrt hx.1 hx.2 ρ.2 t

/-- **`D (x, t)` is continuous in `x` on `[1, X]`.** Each term is continuous away from `0`, and on
a bounded range the series is dominated by `X` times the Dirichlet series of `Λ` at `3/2`. -/
private lemma continuousOn_weightedPrimeSum {X : ℝ} (t : ℝ) :
    ContinuousOn (fun x : ℝ => weightedPrimeSum x t) (Set.Icc 1 X) := by
  have hre : ((3 / 2 : ℂ)).re = 3 / 2 := by norm_num
  have h32 : Summable fun n : ℕ => ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (3 / 2 : ℂ))
      (by rw [hre]; norm_num)).norm
  simp only [weightedPrimeSum]
  refine continuousOn_tsum (u := fun n : ℕ => X * ‖LSeries.term ↗Λ (3 / 2 : ℂ) n‖)
    (fun n => ?_) (h32.mul_left X) (fun n x hx => ?_)
  · refine continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_)
    have hne : ∀ x ∈ Set.Icc (1 : ℝ) X, x ≠ 0 := by
      intro x hx h
      have h1 : (1 : ℝ) ≤ x := hx.1
      rw [h] at h1
      norm_num at h1
    exact ContinuousOn.inf (continuousOn_const.div continuousOn_id hne)
      (continuousOn_id.div_const _)
  · exact le_trans (norm_weightedPrimeSumTerm_le hx.1 t n)
      (mul_le_mul_of_nonneg_right hx.2 (norm_nonneg _))

/-- **The explicit-formula lemma for every `x ≥ 1`.** Assume `ZetaZeros.LandauSymmetrisedFormula`.
The bound of Montgomery's lemma holds without the hypothesis that `x` is not a prime power, and for
`x = 1` as well.

Both sides are continuous in `x` on `[1, X]` -- for `ℓ` because the series is dominated there by
`√X` times the Poisson-weighted count, for `D` because it is dominated by `X` times the Dirichlet
series of `Λ` at `3/2` -- and every point of `[1, X]` is a limit of points `> 1` that are not
natural numbers, hence not prime powers. -/
theorem exists_norm_zeroSide_add_weightedPrimeSum_sub_div_le_of_one_le
    (hL : LandauSymmetrisedFormula) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ t : ℝ,
      ‖zeroSide x t + weightedPrimeSum x t - ((Real.log (|t| + 2) / x : ℝ) : ℂ)‖
        ≤ C * (1 / x + Real.sqrt x / (1 + t ^ 2)) := by
  obtain ⟨C, hC0, hCb⟩ := exists_norm_zeroSide_add_weightedPrimeSum_sub_div_le hL
  refine ⟨C, hC0, fun x₀ hx₀ t => ?_⟩
  have hx₀mem : x₀ ∈ Set.Icc 1 (x₀ + 1) := ⟨hx₀, by linarith⟩
  have hsub : {x : ℝ | x ∈ Set.Icc 1 (x₀ + 1) ∧ 1 < x ∧ NotPrimePowerReal x}
      ⊆ Set.Icc 1 (x₀ + 1) := fun y hy => hy.1
  have hcl : x₀ ∈ closure {x : ℝ | x ∈ Set.Icc 1 (x₀ + 1) ∧ 1 < x ∧ NotPrimePowerReal x} := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨y, hy₁, hy₂, hy₃⟩ := exists_gt_lt_add_forall_ne_natCast x₀ (lt_min hε one_pos)
    have hmin₁ : min ε 1 ≤ ε := min_le_left _ _
    have hmin₂ : min ε 1 ≤ 1 := min_le_right _ _
    refine ⟨y, ⟨⟨by linarith, by linarith⟩, by linarith, fun n _ => hy₃ n⟩, ?_⟩
    rw [Real.dist_eq, abs_of_neg (by linarith : x₀ - y < 0)]
    linarith
  have : (𝓝[{x : ℝ | x ∈ Set.Icc 1 (x₀ + 1) ∧ 1 < x ∧ NotPrimePowerReal x}] x₀).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hne : ∀ x ∈ Set.Icc (1 : ℝ) (x₀ + 1), x ≠ 0 := by
    intro x hx h
    have : (1 : ℝ) ≤ x := hx.1
    rw [h] at this
    norm_num at this
  have hZ : ContinuousOn (fun x : ℝ => zeroSide x t) (Set.Icc 1 (x₀ + 1)) :=
    continuousOn_zeroSide (X := x₀ + 1) t
  have hD : ContinuousOn (fun x : ℝ => weightedPrimeSum x t) (Set.Icc 1 (x₀ + 1)) :=
    continuousOn_weightedPrimeSum (X := x₀ + 1) t
  have hlog : ContinuousOn (fun x : ℝ => ((Real.log (|t| + 2) / x : ℝ) : ℂ))
      (Set.Icc 1 (x₀ + 1)) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.div continuousOn_id hne)
  have hFc : ContinuousOn
      (fun x : ℝ => ‖zeroSide x t + weightedPrimeSum x t
        - ((Real.log (|t| + 2) / x : ℝ) : ℂ)‖) (Set.Icc 1 (x₀ + 1)) :=
    ((hZ.add hD).sub hlog).norm
  have hGc : ContinuousOn (fun x : ℝ => C * (1 / x + Real.sqrt x / (1 + t ^ 2)))
      (Set.Icc 1 (x₀ + 1)) :=
    continuousOn_const.mul ((continuousOn_const.div continuousOn_id hne).add
      (Real.continuous_sqrt.continuousOn.div_const _))
  refine le_of_tendsto_of_tendsto ((hFc x₀ hx₀mem).mono hsub) ((hGc x₀ hx₀mem).mono hsub) ?_
  exact eventually_nhdsWithin_of_forall fun y hy => hCb y hy.2.1 hy.2.2 t

end ZetaZeros
