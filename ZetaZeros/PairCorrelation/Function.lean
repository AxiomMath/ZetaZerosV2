/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import ZetaZeros.PairCorrelation.Symmetry
public import ZetaZeros.Landau.ZeroSums
public import ZetaZeros.Zeta.Finite

/-!
# The pair-correlation function and the symmetries that make it real and even

The pair-correlation function: the double sum

`F (x, T) = ∑_{ρ, ρ' ∈ 𝒩 (T)} m_ρ m_ρ' x^{ρ - ρ'} w (ρ - ρ')`

over pairs of non-trivial zeros up to height `T`, its normalisation

`F_T (α) = (T / (2π) ⬝ log T)⁻¹ F (T^α, T)`,

the related objects -- the pair kernel `κ_{ρ,ρ'}`, the mean square `L (x, T)` of the sum over
zeros, and the weighted prime sum `D (x, t)` -- and the two symmetries of `F_T`.

Both symmetries come from a symmetry of the *index set*, not of the terms. The reflection
`σ ↦ 1 - conj σ` is an involution of `𝒩 (T)` preserving multiplicity, so reindexing the inner sum
by it turns the exponent `ρ - ρ'` into `ρ + conj ρ' - 1`; in that shape conjugating a term produces
the term with the two indices exchanged, and a finite sum invariant under a permutation of its
terms equals its own conjugate, so `F` is real. Evenness is the plain exchange of the two indices
in the original shape: it inverts the exponent, which replaces `x` by `1 / x`, and leaves the
weight alone because `w` is even.

## Main results

* `ZetaZeros.pairCorrelation`: the pair-correlation function `F (x, T)`.
* `ZetaZeros.normalizedPairCorrelation`: its normalisation `F_T (α)`.
* `ZetaZeros.pairKernel`: the pair kernel `κ_{ρ,ρ'} (t)`.
* `ZetaZeros.zeroSideMeanSquare`: the mean square `L (x, T)` of the sum over zeros.
* `ZetaZeros.weightedPrimeSum`: the weighted prime sum `D (x, t)`.
* `ZetaZeros.pairCorrelation_eq_reflected`: the reflected form of `F (x, T)`.
* `ZetaZeros.normalizedPairCorrelation_im`: `F_T (α)` is real.
* `ZetaZeros.normalizedPairCorrelation_neg`: `F_T (-α) = F_T (α)`.

## Implementation notes

`F (x, T)` is a sum over a finite *set* of zeros whose terms carry the multiplicities, so it is
written as an iterated `finsum`, exactly as `pairCorrelationSum` is; `nontrivialZeros_finite`
converts it to a `Finset` sum whenever a permutation of the terms is needed.

The reality of `F_T (α)` is stated as the vanishing of its imaginary part rather than as
membership in the range of the coercion.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

/-! ### The pair-correlation function and its companions -/

/-- **The pair-correlation function.** For `x > 0` and `T ≥ 3`,
`F (x, T) = ∑_{ρ, ρ' ∈ 𝒩 (T)} m_ρ m_ρ' x^{ρ - ρ'} w (ρ - ρ')`, the double sum over ordered pairs
of non-trivial zeros with imaginary part in `(0, T]`, each counted with its multiplicity and
weighted by `w (z) = 4 / (4 - z²)` at the difference of the two zeros. -/
@[zz_tag "def_F_x_T"]
noncomputable def pairCorrelation (x T : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ nontrivialZeros T, ∑ᶠ ρ' ∈ nontrivialZeros T,
    ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
      (x : ℂ) ^ (ρ - ρ') * pairWeight (ρ - ρ')

/-- **The normalised pair-correlation function.** For real `α` and `T ≥ 3`,
`F_T (α) = (T / (2π) ⬝ log T)⁻¹ F (T^α, T)`: the pair-correlation function at `x = T^α`, divided
by the leading term of the count of the zeros up to height `T`. -/
@[zz_tag "def_F_alpha"]
noncomputable def normalizedPairCorrelation (T α : ℝ) : ℂ :=
  ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ)⁻¹ * pairCorrelation (T ^ α) T

/-- **The pair kernel.** For `ρ, ρ' ∈ ℂ` and real `t`,
`κ_{ρ,ρ'} (t) = ((1 - (ρ - (1/2 + it))²) (1 - (conj ρ' - (1/2 - it))²))⁻¹`: the product of the
denominator of the term of the sum over zeros at `ρ` with the conjugate of the one at `ρ'`, whose
integral over the line is the pair weight. -/
@[zz_tag "def_kernel_pair"]
noncomputable def pairKernel (ρ ρ' : ℂ) (t : ℝ) : ℂ :=
  ((1 - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2) *
    (1 - ((starRingEnd ℂ) ρ' - (1 / 2 - (t : ℂ) * I)) ^ 2))⁻¹

/-- **The mean square of the sum over zeros.** For `x ≥ 1` and `T ≥ 3`,
`L (x, T) = ∫₀^T |ℓ (x, t)|² dt`, the second moment over the window `[0, T]` of the zero side
`ℓ (x, t)` of the explicit formula. -/
@[zz_tag "def_L"]
noncomputable def zeroSideMeanSquare (x T : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, ‖zeroSide x t‖ ^ 2

/-- **The weighted prime sum.** For `x ≥ 1` and real `t`,
`D (x, t) = ∑_{n ≥ 1} Λ (n) n^{-1/2 - it} min {n / x, x / n}`, the prime side of the explicit
formula. The index `n = 0` contributes nothing, since `Λ (0) = 0`. -/
@[zz_tag "def_lambda_sum"]
noncomputable def weightedPrimeSum (x t : ℝ) : ℂ :=
  ∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) / 2 + (t : ℂ) * I) *
    ((min ((n : ℝ) / x) (x / (n : ℝ)) : ℝ) : ℂ)

/-! ### The reflection of the zero set -/

/-- The reflected conjugate of a non-trivial zero is a non-trivial zero at the same height: the
functional equation moves `conj ρ` to `1 - conj ρ`, and the reflection fixes the imaginary part. -/
private lemma one_sub_conj_mem {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros T) :
    1 - (starRingEnd ℂ) ρ ∈ nontrivialZeros T := by
  obtain ⟨hzero, hre0, hre1, him0, himT⟩ := hρ
  have hzc : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by rw [riemannZeta_conj, hzero, map_zero]
  have hne1 : (starRingEnd ℂ) ρ ≠ 1 := by
    intro hEq
    have hre : ((starRingEnd ℂ) ρ).re = 1 := by rw [hEq]; simp
    rw [Complex.conj_re] at hre
    linarith
  have hnen : ∀ n : ℕ, (starRingEnd ℂ) ρ ≠ -(n : ℂ) := by
    intro n hEq
    have hre : ((starRingEnd ℂ) ρ).re = -(n : ℝ) := by rw [hEq]; simp
    rw [Complex.conj_re] at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [riemannZeta_one_sub hnen hne1, hzc, mul_zero]
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
  · simpa [Complex.sub_im, Complex.conj_im] using him0
  · simpa [Complex.sub_im, Complex.conj_im] using himT

/-- The reflection is injective. -/
private lemma one_sub_conj_injOn (T : ℝ) :
    Set.InjOn (fun σ : ℂ => 1 - (starRingEnd ℂ) σ) (nontrivialZeros T) := fun _ _ _ _ h =>
  (starRingEnd ℂ).injective (sub_right_injective h)

/-- The reflection maps the zeros up to height `T` *onto* themselves: it maps them into themselves
and is an involution. -/
private lemma one_sub_conj_image (T : ℝ) :
    (fun σ : ℂ => 1 - (starRingEnd ℂ) σ) '' nontrivialZeros T = nontrivialZeros T := by
  refine Set.Subset.antisymm ?_ fun ρ hρ => ⟨1 - (starRingEnd ℂ) ρ, one_sub_conj_mem hρ, ?_⟩
  · rintro ρ ⟨σ, hσ, rfl⟩
    exact one_sub_conj_mem hσ
  · simp

/-- Reindexing a sum over the zeros up to height `T` by the reflection. -/
private lemma finsum_nontrivialZeros_reflect {M : Type*} [AddCommMonoid M] (T : ℝ) (f : ℂ → M) :
    ∑ᶠ ρ ∈ nontrivialZeros T, f ρ
      = ∑ᶠ ρ ∈ nontrivialZeros T, f (1 - (starRingEnd ℂ) ρ) := by
  conv_lhs => rw [← one_sub_conj_image T]
  exact finsum_mem_image (one_sub_conj_injOn T)

/-- A sum over the zeros up to height `T` as a `Finset` sum. -/
private lemma finsum_nontrivialZeros {M : Type*} [AddCommMonoid M] (T : ℝ) (f : ℂ → M) :
    ∑ᶠ ρ ∈ nontrivialZeros T, f ρ = ∑ ρ ∈ (nontrivialZeros_finite T).toFinset, f ρ :=
  finsum_mem_eq_finite_toFinset_sum f (nontrivialZeros_finite T)

/-! ### Elementary identities for the weight and for real powers -/

/-- The argument of a positive real is not `π`, so the branch cut of the logarithm is nowhere near
a positive real base. -/
private lemma arg_ofReal_ne_pi {x : ℝ} (hx : 0 < x) : ((x : ℝ) : ℂ).arg ≠ Real.pi := by
  rw [Complex.arg_ofReal_of_nonneg hx.le]
  exact fun h => Real.pi_ne_zero h.symm

/-- A power of a positive real base commutes with conjugation of the exponent. -/
private lemma conj_ofReal_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ z) = (x : ℂ) ^ ((starRingEnd ℂ) z) := by
  have h := Complex.conj_cpow ((x : ℝ) : ℂ) ((starRingEnd ℂ) z) (arg_ofReal_ne_pi hx)
  simp only [Complex.conj_ofReal, Complex.conj_conj] at h
  exact h.symm

/-- Inverting a positive real base negates the exponent. -/
private lemma ofReal_inv_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ z = (x : ℂ) ^ (-z) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (arg_ofReal_ne_pi hx), Complex.cpow_neg]

/-- The pair weight is a quotient of polynomials with real coefficients, so it commutes with
conjugation. -/
private lemma conj_pairWeight (z : ℂ) :
    (starRingEnd ℂ) (pairWeight z) = pairWeight ((starRingEnd ℂ) z) := by
  simp [pairWeight, map_div₀, map_ofNat]

/-- The pair weight is even. -/
private lemma pairWeight_neg (z : ℂ) : pairWeight (-z) = pairWeight z := by
  simp [pairWeight]

/-! ### The reflected form -/

/-- **The reflected form of the pair-correlation function.** Reindexing the inner sum of
`F (x, T)` by the reflection `σ ↦ 1 - conj σ` of `𝒩 (T)` replaces the difference `ρ - ρ'` of the
two zeros by `ρ + conj ρ' - 1`:
`F (x, T) = ∑_{ρ, ρ' ∈ 𝒩 (T)} m_ρ m_ρ' x^{ρ + conj ρ' - 1} w (ρ + conj ρ' - 1)`. -/
@[zz_tag "lem_F_reflected"]
theorem pairCorrelation_eq_reflected (x T : ℝ) :
    pairCorrelation x T = ∑ᶠ ρ ∈ nontrivialZeros T, ∑ᶠ ρ' ∈ nontrivialZeros T,
      ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
        (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1) * pairWeight (ρ + (starRingEnd ℂ) ρ' - 1) := by
  rw [pairCorrelation]
  refine finsum_mem_congr rfl fun ρ _ => ?_
  rw [finsum_nontrivialZeros_reflect T]
  refine finsum_mem_congr rfl fun σ hσ => ?_
  have harg : ρ - (1 - (starRingEnd ℂ) σ) = ρ + (starRingEnd ℂ) σ - 1 := by ring
  rw [zeroMultiplicity_one_sub_conj hσ.2.1 hσ.2.2.1, harg]

/-! ### Reality -/

/-- `F (x, T)` equals its own conjugate: in the reflected form the conjugate of the term at
`(ρ, ρ')` is the term at `(ρ', ρ)`, so conjugation permutes the terms of the finite sum. -/
theorem conj_pairCorrelation {x : ℝ} (hx : 0 < x) (T : ℝ) :
    (starRingEnd ℂ) (pairCorrelation x T) = pairCorrelation x T := by
  rw [pairCorrelation_eq_reflected]
  simp only [finsum_nontrivialZeros]
  calc (starRingEnd ℂ) (∑ ρ ∈ (nontrivialZeros_finite T).toFinset,
          ∑ ρ' ∈ (nontrivialZeros_finite T).toFinset,
            ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
              (x : ℂ) ^ (ρ + (starRingEnd ℂ) ρ' - 1) *
                pairWeight (ρ + (starRingEnd ℂ) ρ' - 1))
      = ∑ ρ ∈ (nontrivialZeros_finite T).toFinset, ∑ ρ' ∈ (nontrivialZeros_finite T).toFinset,
          ((zeroMultiplicity ρ' * zeroMultiplicity ρ : ℕ) : ℂ) *
            (x : ℂ) ^ (ρ' + (starRingEnd ℂ) ρ - 1) *
              pairWeight (ρ' + (starRingEnd ℂ) ρ - 1) := by
        simp only [map_sum]
        refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
        have hz : (starRingEnd ℂ) (ρ + (starRingEnd ℂ) ρ' - 1) = ρ' + (starRingEnd ℂ) ρ - 1 := by
          simp only [map_sub, map_add, Complex.conj_conj, map_one]
          ring
        rw [map_mul, map_mul, conj_ofReal_cpow hx, conj_pairWeight, hz, map_natCast,
          Nat.mul_comm (zeroMultiplicity ρ) (zeroMultiplicity ρ')]
    _ = ∑ ρ' ∈ (nontrivialZeros_finite T).toFinset, ∑ ρ ∈ (nontrivialZeros_finite T).toFinset,
          ((zeroMultiplicity ρ' * zeroMultiplicity ρ : ℕ) : ℂ) *
            (x : ℂ) ^ (ρ' + (starRingEnd ℂ) ρ - 1) *
              pairWeight (ρ' + (starRingEnd ℂ) ρ - 1) := Finset.sum_comm

/-- **The normalised pair-correlation function is real.** For `T > 0` and every real `α`, the
imaginary part of `F_T (α)` vanishes: the normalising factor is real and `F (T^α, T)` equals its
own conjugate. -/
@[zz_tag "lem_F_real"]
theorem normalizedPairCorrelation_im {T : ℝ} (hT : 0 < T) (α : ℝ) :
    (normalizedPairCorrelation T α).im = 0 := by
  rw [← Complex.conj_eq_iff_im, normalizedPairCorrelation, map_mul, map_inv₀, Complex.conj_ofReal,
    conj_pairCorrelation (Real.rpow_pos_of_pos hT α)]

/-! ### Evenness -/

/-- Inverting `x` leaves `F (x, T)` unchanged: exchanging the two summation indices inverts
`x^{ρ - ρ'}` and fixes `w (ρ - ρ')`, because `w` is even. -/
theorem pairCorrelation_inv {x : ℝ} (hx : 0 < x) (T : ℝ) :
    pairCorrelation x⁻¹ T = pairCorrelation x T := by
  simp only [pairCorrelation, finsum_nontrivialZeros]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hpow : ((x⁻¹ : ℝ) : ℂ) ^ (b - a) = (x : ℂ) ^ (a - b) := by
    rw [ofReal_inv_cpow hx, neg_sub]
  have hw : pairWeight (b - a) = pairWeight (a - b) := by
    rw [← neg_sub a b, pairWeight_neg]
  rw [hpow, hw, Nat.mul_comm]

/-- **The normalised pair-correlation function is even.** For `T > 0` and every real `α`,
`F_T (-α) = F_T (α)`: the substitution `T^{-α} = (T^α)⁻¹` turns the claim into the invariance of
`F (x, T)` under inverting `x`. -/
@[zz_tag "lem_F_even"]
theorem normalizedPairCorrelation_neg {T : ℝ} (hT : 0 < T) (α : ℝ) :
    normalizedPairCorrelation T (-α) = normalizedPairCorrelation T α := by
  rw [normalizedPairCorrelation, normalizedPairCorrelation, Real.rpow_neg hT.le,
    pairCorrelation_inv (Real.rpow_pos_of_pos hT α)]

/-! ### The pair kernel integrates to the weight -/

/-- A point off the real axis is not real. -/
private lemma ofReal_sub_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    (t : ℂ) - z ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact hz (by rw [← h]; simp)

/-- **The residue integral with both factors shifted.** For `b` and `c` with `|im b| < 1` and
`|im c| < 1`,
`∫ dt / ((1 + (t + b)²) (1 + (t + c)²)) = 2π / (4 + (c - b)²)`. -/
private lemma integral_inv_quad_mul_quad {b c : ℂ} (hb : |b.im| < 1) (hc : |c.im| < 1) :
    ∫ t : ℝ, ((1 + ((t : ℂ) + b) ^ 2) * (1 + ((t : ℂ) + c) ^ 2))⁻¹
      = 2 * (Real.pi : ℂ) / (4 + (c - b) ^ 2) := by
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
  obtain ⟨hc1, hc2⟩ := abs_lt.mp hc
  have hz1 : (0 : ℝ) < (I - b).im := by
    simp only [Complex.sub_im, Complex.I_im]; linarith
  have hw1 : (-I - b).im < 0 := by
    simp only [Complex.sub_im, Complex.neg_im, Complex.I_im]; linarith
  have hz2 : (0 : ℝ) < (I - c).im := by
    simp only [Complex.sub_im, Complex.I_im]; linarith
  have hw2 : (-I - c).im < 0 := by
    simp only [Complex.sub_im, Complex.neg_im, Complex.I_im]; linarith
  have hfacb : ∀ t : ℝ, (1 : ℂ) + ((t : ℂ) + b) ^ 2
      = ((t : ℂ) - (I - b)) * ((t : ℂ) - (-I - b)) := fun t => by
    linear_combination Complex.I_sq
  have hfacc : ∀ t : ℝ, (1 : ℂ) + ((t : ℂ) + c) ^ 2
      = ((t : ℂ) - (I - c)) * ((t : ℂ) - (-I - c)) := fun t => by
    linear_combination Complex.I_sq
  by_cases ha0 : c - b = 0
  · have hcb : c = b := by linear_combination ha0
    subst hcb
    have hA : Integrable fun t : ℝ =>
        (2 : ℂ)⁻¹ * (((t : ℂ) - (I - c)) * ((t : ℂ) - (-I - c)))⁻¹ :=
      (integrable_inv_ofReal_sub_mul_sub (ne_of_gt hz1) (ne_of_lt hw1)).const_mul _
    have hB : Integrable fun t : ℝ => (4 : ℂ)⁻¹ * (((t : ℂ) - (I - c)) ^ 2)⁻¹ :=
      (integrable_inv_ofReal_sub_sq (ne_of_gt hz1)).const_mul _
    have hC : Integrable fun t : ℝ => (4 : ℂ)⁻¹ * (((t : ℂ) - (-I - c)) ^ 2)⁻¹ :=
      (integrable_inv_ofReal_sub_sq (ne_of_lt hw1)).const_mul _
    have hBC : Integrable fun t : ℝ => (4 : ℂ)⁻¹ * (((t : ℂ) - (I - c)) ^ 2)⁻¹
        + (4 : ℂ)⁻¹ * (((t : ℂ) - (-I - c)) ^ 2)⁻¹ := hB.add hC
    have key : ∀ t : ℝ, ((1 + ((t : ℂ) + c) ^ 2) * (1 + ((t : ℂ) + c) ^ 2))⁻¹
        = (2 : ℂ)⁻¹ * (((t : ℂ) - (I - c)) * ((t : ℂ) - (-I - c)))⁻¹
          - ((4 : ℂ)⁻¹ * (((t : ℂ) - (I - c)) ^ 2)⁻¹
            + (4 : ℂ)⁻¹ * (((t : ℂ) - (-I - c)) ^ 2)⁻¹) := by
      intro t
      have h1 : (t : ℂ) - (I - c) ≠ 0 := ofReal_sub_ne_zero_of_im_ne_zero (ne_of_gt hz1) t
      have h2 : (t : ℂ) - (-I - c) ≠ 0 := ofReal_sub_ne_zero_of_im_ne_zero (ne_of_lt hw1) t
      rw [hfacb t]
      field_simp
      linear_combination 8 * Complex.I_sq
    simp only [key]
    rw [integral_sub hA hBC, integral_add hB hC, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_inv_ofReal_sub_mul_sub hz1 hw1,
      integral_inv_ofReal_sub_sq (ne_of_gt hz1), integral_inv_ofReal_sub_sq (ne_of_lt hw1),
      show (I - c) - (-I - c) = 2 * I by ring]
    simp only [sub_self, mul_zero, add_zero, sub_zero]
    field_simp
    ring
  · have hp : (c - b) + 2 * I ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.re_ofNat, Complex.I_im,
        Complex.im_ofNat, Complex.I_re, Complex.zero_im] at him
      norm_num at him
      linarith
    have hm : 2 * I - (c - b) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat, Complex.I_im,
        Complex.im_ofNat, Complex.I_re, Complex.zero_im] at him
      norm_num at him
      linarith
    have hprod : ((c - b) + 2 * I) * (2 * I - (c - b)) = -(4 + (c - b) ^ 2) := by
      linear_combination 4 * Complex.I_sq
    have h4z : (4 : ℂ) + (c - b) ^ 2 ≠ 0 := by
      intro h
      rw [h, neg_zero] at hprod
      exact mul_ne_zero hp hm hprod
    have key : ∀ t : ℝ, ((1 + ((t : ℂ) + b) ^ 2) * (1 + ((t : ℂ) + c) ^ 2))⁻¹
        = (2 * I * (c - b))⁻¹ * ((((t : ℂ) - (I - b)) * ((t : ℂ) - (-I - c)))⁻¹
          - (((t : ℂ) - (I - c)) * ((t : ℂ) - (-I - b)))⁻¹) := by
      intro t
      have h1 : (t : ℂ) - (I - b) ≠ 0 := ofReal_sub_ne_zero_of_im_ne_zero (ne_of_gt hz1) t
      have h2 : (t : ℂ) - (-I - b) ≠ 0 := ofReal_sub_ne_zero_of_im_ne_zero (ne_of_lt hw1) t
      have h3 : (t : ℂ) - (I - c) ≠ 0 := ofReal_sub_ne_zero_of_im_ne_zero (ne_of_gt hz2) t
      have h4 : (t : ℂ) - (-I - c) ≠ 0 := ofReal_sub_ne_zero_of_im_ne_zero (ne_of_lt hw2) t
      rw [hfacb t, hfacc t]
      field_simp
      ring
    simp only [key]
    rw [integral_const_mul, integral_sub
        (integrable_inv_ofReal_sub_mul_sub (ne_of_gt hz1) (ne_of_lt hw2))
        (integrable_inv_ofReal_sub_mul_sub (ne_of_gt hz2) (ne_of_lt hw1)),
      integral_inv_ofReal_sub_mul_sub hz1 hw2, integral_inv_ofReal_sub_mul_sub hz2 hw1,
      show (I - b) - (-I - c) = (c - b) + 2 * I by ring,
      show (I - c) - (-I - b) = 2 * I - (c - b) by ring,
      div_sub_div _ _ hp hm, hprod]
    field_simp
    ring

/-- **The pair kernel integrates to the weight.** For `ρ` and `ρ'` in the open critical strip,
`∫ κ_{ρ,ρ'} (t) dt = (π / 2) w (ρ + conj ρ' - 1)`.

Both factors of the kernel are quadratics in `t` after the shifts
`1 - (ρ - (1/2 + it))² = 1 + (t + i (ρ - 1/2))²` and
`1 - (conj ρ' - (1/2 - it))² = 1 + (t - i (conj ρ' - 1/2))²`, whose shifts have imaginary parts
`re ρ - 1/2` and `1/2 - re ρ'`, both of modulus less than `1/2`. The difference of the shifts is
`-i (ρ + conj ρ' - 1)`, so the residue integral produces `2π / (4 - (ρ + conj ρ' - 1)²)`. -/
@[zz_tag "lem_kernel_integral"]
theorem integral_pairKernel {ρ ρ' : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (h0' : 0 < ρ'.re)
    (h1' : ρ'.re < 1) :
    ∫ t : ℝ, pairKernel ρ ρ' t
      = (Real.pi : ℂ) / 2 * pairWeight (ρ + (starRingEnd ℂ) ρ' - 1) := by
  have hbim : (I * (ρ - 1 / 2)).im = ρ.re - 1 / 2 := by simp
  have hcim : ((-I) * ((starRingEnd ℂ) ρ' - 1 / 2)).im = 1 / 2 - ρ'.re := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    norm_num
  have hb : |(I * (ρ - 1 / 2)).im| < 1 := by
    rw [hbim, abs_lt]; constructor <;> linarith
  have hc : |((-I) * ((starRingEnd ℂ) ρ' - 1 / 2)).im| < 1 := by
    rw [hcim, abs_lt]; constructor <;> linarith
  have hintegrand : ∀ t : ℝ, pairKernel ρ ρ' t
      = ((1 + ((t : ℂ) + I * (ρ - 1 / 2)) ^ 2) *
        (1 + ((t : ℂ) + (-I) * ((starRingEnd ℂ) ρ' - 1 / 2)) ^ 2))⁻¹ := by
    intro t
    have e1 : (1 : ℂ) - (ρ - (1 / 2 + (t : ℂ) * I)) ^ 2
        = 1 + ((t : ℂ) + I * (ρ - 1 / 2)) ^ 2 := by
      linear_combination (-((ρ - 1 / 2) ^ 2 + (t : ℂ) ^ 2)) * Complex.I_sq
    have e2 : (1 : ℂ) - ((starRingEnd ℂ) ρ' - (1 / 2 - (t : ℂ) * I)) ^ 2
        = 1 + ((t : ℂ) + (-I) * ((starRingEnd ℂ) ρ' - 1 / 2)) ^ 2 := by
      linear_combination (-(((starRingEnd ℂ) ρ' - 1 / 2) ^ 2 + (t : ℂ) ^ 2)) * Complex.I_sq
    rw [pairKernel, e1, e2]
  simp only [hintegrand]
  rw [integral_inv_quad_mul_quad hb hc, pairWeight,
    show (-I) * ((starRingEnd ℂ) ρ' - 1 / 2) - I * (ρ - 1 / 2)
      = (-I) * (ρ + (starRingEnd ℂ) ρ' - 1) by ring,
    show ((-I) * (ρ + (starRingEnd ℂ) ρ' - 1)) ^ 2 = -((ρ + (starRingEnd ℂ) ρ' - 1) ^ 2) from by
      linear_combination ((ρ + (starRingEnd ℂ) ρ' - 1) ^ 2) * Complex.I_sq]
  ring

end ZetaZeros
