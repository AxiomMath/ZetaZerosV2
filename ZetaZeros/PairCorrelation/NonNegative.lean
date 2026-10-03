/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.PairCorrelation.Truncation

/-!
# The pair-correlation function is non-negative

`F (x, T)` is a non-negative real number for every `x > 0` and every `T`, and so is its
normalisation `F_T (α)` as soon as `T > 1` makes the normalising factor positive.

The reason is that `F` is a mean square in disguise. In the reflected form
`F (x, T) = ∑_{ρ, ρ' ∈ 𝒩 (T)} m_ρ m_ρ' x^{ρ + conj ρ' - 1} w (ρ + conj ρ' - 1)` the weight is the
integral of the pair kernel over the line, `w (ρ + conj ρ' - 1) = (2/π) ∫_ℝ κ_{ρ,ρ'} (t) dt`, and
the kernel factors as
`κ_{ρ,ρ'} (t) = (1 - (ρ - (1/2 + it))²)⁻¹ ⬝ conj ((1 - (ρ' - (1/2 + it))²)⁻¹)`.
Together with `x^{ρ + conj ρ' - 1} = x^{ρ - 1/2} ⬝ conj (x^{ρ' - 1/2})` this makes the term at
`(ρ, ρ')` the product of `e_ρ (t) = m_ρ x^{ρ - 1/2} (1 - (ρ - (1/2 + it))²)⁻¹` with the conjugate
of `e_{ρ'} (t)`, so the double sum is `|∑_{ρ ∈ 𝒩 (T)} e_ρ (t)|²` and

`(π/2) F (x, T) = ∫_ℝ |∑_{ρ ∈ 𝒩 (T)} e_ρ (t)|² dt ≥ 0`.

The inner sum is the partial sum of the zero side `ℓ (x, t)` of the explicit formula over the zeros
up to height `T`, divided by the unimodular `2 x^{-it}`. The identity is *exact*: the sum runs over
`𝒩 (T)` and the integral over the whole line, which is the one combination for which no truncation
error arises. Non-negativity therefore does not come from `L (x, T) = ∫₀^T |ℓ (x, t)|² dt ≥ 0`
through `exists_norm_pairCorrelation_sub_zeroSideMeanSquare_div_le`: that comparison carries an
error `O(x log³T)`, which dwarfs `F (x, T)` itself and so decides nothing about its sign.

## Main results

* `ZetaZeros.zero_le_pairCorrelation_re`: `0 ≤ re F (x, T)` for `x > 0`.
* `ZetaZeros.zero_le_normalizedPairCorrelation_re`: `0 ≤ re F_T (α)` for `T > 1`.
* `ZetaZeros.zero_le_normalizedPairCorrelation_mul_re`: `0 ≤ re (F_T (α) c)` for a real `c ≥ 0`.

## Implementation notes

`F` is real (`conj_pairCorrelation`, and `normalizedPairCorrelation_im` for `F_T`), so
non-negativity is stated as non-negativity of the real part.

Only `0 < x` is used for `F (x, T)`, and only `1 < T` for `F_T (α)`, the latter solely to make the
normalising factor `T / (2π) ⬝ log T` positive.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory

/-! ### The two factors of the pair kernel -/

/-- The conjugated factor obeys the same lower bound as the factor itself. -/
private lemma three_quarters_add_sq_le_norm_conj {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (t : ℝ) :
    3 / 4 + (t - ρ.im) ^ 2 ≤ ‖1 - ((starRingEnd ℂ) ρ - (1 / 2 - (t : ℂ) * I)) ^ 2‖ := by
  rw [← conj_denom, Complex.norm_conj]
  exact three_quarters_add_sq_le_norm_one_sub_sq h0 h1 t

/-! ### The pair-correlation function as a mean square -/

/-- The factor of the zero side of the explicit formula carried by a single zero:
`e_ρ (t) = m_ρ x^{ρ - 1/2} (1 - (ρ - (1/2 + it))²)⁻¹`. The term of `ℓ (x, t)` at `ρ` is
`2 x^{-it} e_ρ (t)`, so the two differ by a unimodular factor and a constant. -/
private noncomputable def zeroFactor (x t : ℝ) (ρ : ℂ) : ℂ :=
  (zeroMultiplicity ρ : ℂ) * (x : ℂ) ^ (ρ - 1 / 2) *
    (1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2)⁻¹

/-- The coefficient of the reflected form of `F (x, T)` at a pair of zeros. -/
private noncomputable def reflectedCoeff (x : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
    (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1)

/-- The non-trivial zeros up to height `T`, as a `Finset`. -/
private noncomputable def zerosFinset (T : ℝ) : Finset ℂ := (nontrivialZeros_finite T).toFinset

private lemma mem_zerosFinset {T : ℝ} {ρ : ℂ} : ρ ∈ zerosFinset T ↔ ρ ∈ nontrivialZeros T := by
  simp [zerosFinset]

private lemma finsum_zerosFinset {M : Type*} [AddCommMonoid M] (T : ℝ) (f : ℂ → M) :
    ∑ᶠ ρ ∈ nontrivialZeros T, f ρ = ∑ ρ ∈ zerosFinset T, f ρ :=
  finsum_mem_eq_finite_toFinset_sum f (nontrivialZeros_finite T)

/-- A power of a positive real base commutes with conjugation of the exponent. -/
private lemma conj_cpow_ofReal {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ z) = (x : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : ((x : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact fun h => Real.pi_ne_zero h.symm
  have h := Complex.conj_cpow ((x : ℝ) : ℂ) ((starRingEnd ℂ) z) harg
  simp only [Complex.conj_ofReal, Complex.conj_conj] at h
  exact h.symm

/-- The conjugate of the zero-side factor is the same expression with `ρ` conjugated, which is
where the second factor of the pair kernel comes from. -/
private lemma conj_zeroFactor {x : ℝ} (hx : 0 < x) (t : ℝ) (ρ : ℂ) :
    (starRingEnd ℂ) (zeroFactor x t ρ)
      = (zeroMultiplicity ρ : ℂ) * (x : ℂ) ^ ((starRingEnd ℂ) ρ - 1 / 2) *
          (1 - ((starRingEnd ℂ) ρ - (1 / 2 - (t : ℂ) * I)) ^ 2)⁻¹ := by
  rw [zeroFactor, map_mul, map_mul, map_natCast, map_inv₀, conj_cpow_ofReal hx, conj_denom,
    show (starRingEnd ℂ) (ρ - 1 / 2) = (starRingEnd ℂ) ρ - 1 / 2 from by
      simp only [map_sub, map_div₀, map_one, map_ofNat]]

/-- **The term of the reflected form factors.** The term at `(ρ, ρ')` of the reflected double sum,
with the pair kernel in place of the weight, is `e_ρ (t)` times the conjugate of `e_{ρ'} (t)`. -/
private lemma reflectedCoeff_mul_pairKernel {x : ℝ} (hx : 0 < x) (t : ℝ) (ρ ρ' : ℂ) :
    reflectedCoeff x ρ ρ' * pairKernel ρ ρ' t
      = zeroFactor x t ρ * (starRingEnd ℂ) (zeroFactor x t ρ') := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpow : (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1)
      = (x : ℂ) ^ (ρ - 1 / 2) * (x : ℂ) ^ ((starRingEnd ℂ) ρ' - 1 / 2) := by
    rw [← Complex.cpow_add _ _ hx0,
      show ρ - 1 / 2 + ((starRingEnd ℂ) ρ' - 1 / 2) = ρ + (starRingEnd ℂ) ρ' - 1 from by ring]
  rw [reflectedCoeff, conj_zeroFactor hx, zeroFactor, pairKernel, hpow, mul_inv]
  push_cast
  ring

/-- **The double sum over pairs is a square modulus.** -/
private lemma sum_sum_reflectedCoeff_mul_pairKernel {x : ℝ} (hx : 0 < x) (t : ℝ) (A : Finset ℂ) :
    ∑ ρ ∈ A, ∑ ρ' ∈ A, reflectedCoeff x ρ ρ' * pairKernel ρ ρ' t
      = (Complex.normSq (∑ ρ ∈ A, zeroFactor x t ρ) : ℂ) := by
  have hconj : (starRingEnd ℂ) (∑ ρ ∈ A, zeroFactor x t ρ)
      = ∑ ρ ∈ A, (starRingEnd ℂ) (zeroFactor x t ρ) := map_sum _ _ _
  rw [← Complex.mul_conj, hconj, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ =>
    reflectedCoeff_mul_pairKernel hx t ρ ρ'

/-- **`F (x, T)` is a mean square.** For `x > 0`,
`(π/2) F (x, T) = ∫_ℝ |∑_{ρ ∈ 𝒩 (T)} e_ρ (t)|² dt`.

The reflected form of `F (x, T)` turns the weight into the integral of the pair kernel over the
line; the sum over the finitely many pairs of zeros may then be taken inside the integral, where it
collapses to the square modulus of a single sum over the zeros. -/
private lemma ofReal_pi_div_two_mul_pairCorrelation {x : ℝ} (hx : 0 < x) (T : ℝ) :
    ((Real.pi / 2 : ℝ) : ℂ) * pairCorrelation x T
      = ((∫ t : ℝ, Complex.normSq (∑ ρ ∈ zerosFinset T, zeroFactor x t ρ) : ℝ) : ℂ) := by
  have hstrip : ∀ ρ ∈ zerosFinset T, 0 < ρ.re ∧ ρ.re < 1 := fun ρ hρ => by
    obtain ⟨-, h0, h1, -, -⟩ := mem_zerosFinset.1 hρ
    exact ⟨h0, h1⟩
  have hint : ∀ ρ ∈ zerosFinset T, ∀ ρ' ∈ zerosFinset T,
      Integrable fun t : ℝ => reflectedCoeff x ρ ρ' * pairKernel ρ ρ' t := fun ρ hρ ρ' hρ' =>
    (integrable_pairKernel (hstrip ρ hρ).1 (hstrip ρ hρ).2 (hstrip ρ' hρ').1
      (hstrip ρ' hρ').2).const_mul _
  rw [← integral_complex_ofReal]
  calc ((Real.pi / 2 : ℝ) : ℂ) * pairCorrelation x T
      = ∑ ρ ∈ zerosFinset T, ∑ ρ' ∈ zerosFinset T,
          reflectedCoeff x ρ ρ' * ∫ t : ℝ, pairKernel ρ ρ' t := by
        rw [pairCorrelation_eq_reflected, finsum_zerosFinset, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [finsum_zerosFinset, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ' hρ' => ?_
        rw [integral_pairKernel (hstrip ρ hρ).1 (hstrip ρ hρ).2 (hstrip ρ' hρ').1
          (hstrip ρ' hρ').2, reflectedCoeff]
        push_cast
        ring
    _ = ∑ ρ ∈ zerosFinset T, ∑ ρ' ∈ zerosFinset T,
          ∫ t : ℝ, reflectedCoeff x ρ ρ' * pairKernel ρ ρ' t :=
        Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ =>
          (integral_const_mul _ _).symm
    _ = ∫ t : ℝ, ∑ ρ ∈ zerosFinset T, ∑ ρ' ∈ zerosFinset T,
          reflectedCoeff x ρ ρ' * pairKernel ρ ρ' t := by
        rw [integral_finsetSum _ fun ρ hρ =>
          integrable_finsetSum _ fun ρ' hρ' => hint ρ hρ ρ' hρ']
        exact Finset.sum_congr rfl fun ρ hρ =>
          (integral_finsetSum _ fun ρ' hρ' => hint ρ hρ ρ' hρ').symm
    _ = ∫ t : ℝ, (Complex.normSq (∑ ρ ∈ zerosFinset T, zeroFactor x t ρ) : ℂ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun t =>
          sum_sum_reflectedCoeff_mul_pairKernel hx t (zerosFinset T))

/-! ### Non-negativity -/

/-- **The pair-correlation function is non-negative.** For every `x > 0` and every `T`,
`0 ≤ re F (x, T)` -- and `F (x, T)` is real, by `conj_pairCorrelation`.

`(π/2) F (x, T)` is the integral over the line of the square modulus of the partial sum of the
zero side of the explicit formula over the zeros up to height `T`. -/
theorem zero_le_pairCorrelation_re {x : ℝ} (hx : 0 < x) (T : ℝ) :
    0 ≤ (pairCorrelation x T).re := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hnn : 0 ≤ ∫ t : ℝ, Complex.normSq (∑ ρ ∈ zerosFinset T, zeroFactor x t ρ) :=
    integral_nonneg fun t => Complex.normSq_nonneg _
  have h := congrArg Complex.re (ofReal_pi_div_two_mul_pairCorrelation hx T)
  rw [Complex.re_ofReal_mul, Complex.ofReal_re] at h
  nlinarith

/-- **The normalised pair-correlation function is non-negative.** For `T > 1` and every real `α`,
`0 ≤ re F_T (α)` -- and `F_T (α)` is real, by `normalizedPairCorrelation_im`.

The hypothesis is used only to make the normalising factor `T / (2π) ⬝ log T` positive. -/
theorem zero_le_normalizedPairCorrelation_re {T : ℝ} (hT : 1 < T) (α : ℝ) :
    0 ≤ (normalizedPairCorrelation T α).re := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hc : 0 < T / (2 * Real.pi) * Real.log T := by
    have := Real.log_pos hT
    positivity
  rw [normalizedPairCorrelation, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  exact mul_nonneg (inv_nonneg.mpr hc.le)
    (zero_le_pairCorrelation_re (Real.rpow_pos_of_pos hT0 α) T)

/-- **The sign of the integrand of the pair-correlation formula.** For `T > 1` and a non-negative
real `c`, `0 ≤ re (F_T (α) c)`. -/
theorem zero_le_normalizedPairCorrelation_mul_re {T : ℝ} (hT : 1 < T) (α : ℝ) {c : ℝ}
    (hc : 0 ≤ c) : 0 ≤ (normalizedPairCorrelation T α * (c : ℂ)).re := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (zero_le_normalizedPairCorrelation_re hT α) hc

end ZetaZeros
