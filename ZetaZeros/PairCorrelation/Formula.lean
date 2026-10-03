/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.PairCorrelation.Elementary
public import ZetaZeros.PairCorrelation.Truncation
public import ZetaZeros.Zeta.Inputs

/-!
# The pair-correlation formula from the evaluation of the mean square

The asymptotic for `F_T (α)` on `0 ≤ α ≤ 1 - ε`, the expression of a sum over pairs of zeros
against a test function as an integral against `F_T`, and the pair-correlation formula for test
functions vanishing on a neighbourhood of `±1`.

The results other than `pairCorrelationSum_eq_ofReal_integral` take as hypothesis `hEval` the
evaluation of the mean square of the sum over zeros: for `1 ≤ x ≤ T` and `T ≥ 3`, the quantity
`|L (x, T) - T log x - x^{-2} T log²T|` is at most a constant times
`T + x log²T + T log T / x² + T (log T)^{3/2} / x + (T/x)^{1/2} log²T`.
This evaluation is proved as `ZetaZeros.lEvaluation`. The fifth error term is kept as
`(T/x)^{1/2} log²T` rather than `T log²T / x`: the latter normalises to `T^{-α} log T`, whose
integral against a test function is not `o (1)`.

The asymptotic of `F_T (α)` holds on `0 ≤ α ≤ 1 - ε`, where the truncation error `T^{α-1} log²T`
is smaller than any power of `log T`; the only information on the zeros used is `0 < re ρ < 1`.

## Main results

* `ZetaZeros.exists_abs_normalizedPairCorrelation_sub_le`: the asymptotic for `F_T (α)` on
  `0 ≤ α ≤ 1 - ε`, given `hEval`.
* `ZetaZeros.pairCorrelationSum_eq_ofReal_integral`: the sum over pairs of zeros against a
  compactly supported `L¹` test function is `(T / 2π) log T` times the integral of `F_T` against
  the test function.
* `ZetaZeros.exists_norm_pairCorrelationSum_div_sub_le`: the pair-correlation formula at rate
  `O(1 / √log T)` for test functions vanishing on a neighbourhood of `±1`, given `hEval`.
* `ZetaZeros.pairCorrelation_of_margin`: `ZetaZeros.PairCorrelation`, given `hEval`.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory Filter

/-! ### Elementary rewriting of a real power at a complex exponent -/

/-- A real power of a positive real base, raised to a complex exponent, is an exponential:
`(T^α)^z = exp ((α log T) z)`. -/
private lemma ofReal_rpow_cpow {T : ℝ} (hT : 0 < T) (α : ℝ) (z : ℂ) :
    ((T ^ α : ℝ) : ℂ) ^ z = Complex.exp (((α * Real.log T : ℝ) : ℂ) * z) := by
  have hpos : (0 : ℝ) < T ^ α := Real.rpow_pos_of_pos hT α
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne')]
  congr 2
  rw [← Complex.ofReal_log hpos.le, Real.log_rpow hT]

/-- A sum over the non-trivial zeros up to height `T` as a `Finset` sum. -/
private lemma finsum_nontrivialZeros_eq {M : Type*} [AddCommMonoid M] (T : ℝ) (f : ℂ → M) :
    ∑ᶠ ρ ∈ nontrivialZeros T, f ρ = ∑ ρ ∈ (nontrivialZeros_finite T).toFinset, f ρ :=
  finsum_mem_eq_finite_toFinset_sum f (nontrivialZeros_finite T)

/-- An exponentially damped function times an integrable one is interval integrable. -/
private lemma intervalIntegrable_rpow_neg_mul {T : ℝ} (hT : 0 < T) (c : ℝ) {g : ℝ → ℝ}
    (hg : Integrable g) (a b : ℝ) :
    IntervalIntegrable (fun α => T ^ (-(c * α)) * g α) volume a b := by
  refine hg.intervalIntegrable.continuousOn_mul (Continuous.continuousOn ?_)
  have hEq : (fun α : ℝ => T ^ (-(c * α))) = fun α : ℝ => Real.exp (-(c * α) * Real.log T) := by
    funext α
    rw [Real.rpow_def_of_pos hT, mul_comm]
  rw [hEq]
  fun_prop

/-- The integrand of the pair sum, at one pair of zeros, is integrable against a compactly
supported `L¹` function: the power is continuous, and on the support of `g` its modulus is at most
`T^R`, because the exponent has real part of modulus at most one. -/
private lemma integrable_ofReal_rpow_cpow_mul {T R : ℝ} (hT : 1 ≤ T) {g : ℝ → ℝ}
    (hg : Integrable g) (hsupp : ∀ α : ℝ, R < |α| → g α = 0) {z : ℂ} (hz : |z.re| ≤ 1) (c : ℂ) :
    Integrable fun α : ℝ => c * ((T ^ α : ℝ) : ℂ) ^ z * (g α : ℂ) := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hcont : Continuous fun α : ℝ => c * ((T ^ α : ℝ) : ℂ) ^ z := by
    have hEq : (fun α : ℝ => c * ((T ^ α : ℝ) : ℂ) ^ z)
        = fun α : ℝ => c * Complex.exp (((α * Real.log T : ℝ) : ℂ) * z) := by
      funext α
      rw [ofReal_rpow_cpow hT0]
    rw [hEq]
    fun_prop
  refine Integrable.mono' (hg.abs.const_mul (‖c‖ * T ^ R))
    (hcont.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable)) ?_
  filter_upwards with α
  by_cases hα : R < |α|
  · simp [hsupp α hα]
  · replace hα : |α| ≤ R := not_lt.1 hα
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hT0 α)]
    have hb : α * z.re ≤ R := by
      have h1 : α * z.re ≤ |α * z.re| := le_abs_self _
      have h2 : |α * z.re| = |α| * |z.re| := abs_mul _ _
      nlinarith [abs_nonneg α, abs_nonneg z.re]
    have hpow : (T ^ α) ^ z.re ≤ T ^ R := by
      rw [← Real.rpow_mul hT0.le]
      exact Real.rpow_le_rpow_of_exponent_le hT hb
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (norm_nonneg c)) (abs_nonneg _)

/-- `T^{-(α+1)/2} log T ≤ T^{-α}` whenever `α ≤ 1 - ε` and `log³T ≤ T^ε`. -/
private lemma rpow_neg_half_add_mul_log_le {T ε α : ℝ} (hT0 : 0 < T) (hT1 : 1 ≤ T)
    (hL0 : 0 < Real.log T) (hL1 : 1 ≤ Real.log T) (hlog3 : Real.log T ^ 3 ≤ T ^ ε)
    (hα1 : α ≤ 1 - ε) :
    T ^ (-((α + 1) / 2)) * Real.log T ≤ T ^ (-(1 * α)) := by
  have hlogle2 : Real.log T ≤ T ^ (ε / 2) := by
    have h1 : Real.log T ^ 2 ≤ T ^ ε := le_trans (by nlinarith) hlog3
    have h2 : (T ^ (ε / 2)) ^ 2 = T ^ ε := by
      rw [← Real.rpow_natCast (T ^ (ε / 2)) 2, ← Real.rpow_mul hT0.le]
      norm_num
    nlinarith [Real.rpow_pos_of_pos hT0 (ε / 2)]
  have hsplit : T ^ (-((α + 1) / 2)) = T ^ ((α - 1) / 2) * T ^ (-(1 * α)) := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  have hexp' : T ^ ((α - 1) / 2) ≤ T ^ (-(ε / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hkey : T ^ (-(ε / 2)) * Real.log T ≤ 1 := by
    rw [Real.rpow_neg hT0.le, inv_mul_eq_div, div_le_one (Real.rpow_pos_of_pos hT0 (ε / 2))]
    exact hlogle2
  have hp : (0 : ℝ) < T ^ (-(1 * α)) := Real.rpow_pos_of_pos hT0 _
  calc T ^ (-((α + 1) / 2)) * Real.log T
      = T ^ ((α - 1) / 2) * Real.log T * T ^ (-(1 * α)) := by rw [hsplit]; ring
    _ ≤ T ^ (-(ε / 2)) * Real.log T * T ^ (-(1 * α)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp' hL0.le) hp.le
    _ ≤ 1 * T ^ (-(1 * α)) := mul_le_mul_of_nonneg_right hkey hp.le
    _ = T ^ (-(1 * α)) := one_mul _

/-! ### The pair sum as an integral against `F_T` -/

/-- The exponential of the Fourier phase at the rescaled difference of two zeros is the real power
`(T^u)^(ρ - ρ')`: the two factors `2π` cancel and `i² = -1`. -/
private lemma exp_neg_two_pi_I_rescaledDiff {T : ℝ} (hT : 0 < T) (ρ ρ' : ℂ) (u : ℝ) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * rescaledDiff T ρ ρ' * (u : ℂ))
      = ((T ^ u : ℝ) : ℂ) ^ (ρ - ρ') := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ofReal_rpow_cpow hT, rescaledDiff]
  congr 1
  push_cast
  field_simp
  linear_combination (-((ρ - ρ') * (Real.log T : ℂ) * (u : ℂ))) * Complex.I_sq

/-- **The pair sum as an integral against `F_T`.** For a compactly supported integrable `g` and
`T ≥ 3`,
`∑_{ρ, ρ' ∈ 𝒩 (T)} m_ρ m_ρ' ĝ (z_{ρ,ρ'} (T)) w (ρ - ρ') = (T / 2π) log T ∫ F_T (α) g (α) dα`.

The Fourier transform at the rescaled difference is the integral of `g (α) T^{α (ρ - ρ')}`, the
finite sum over pairs may be exchanged with the integral, and the sum inside is `F (T^α, T)`. -/
@[zz_tag "lem_pair_sum_F"]
theorem pairCorrelationSum_eq_ofReal_integral {g : ℝ → ℝ} {R : ℝ} (hg : Integrable g)
    (hsupp : ∀ α : ℝ, R < |α| → g α = 0) {T : ℝ} (hT : 3 ≤ T) :
    pairCorrelationSum g T
      = ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ) *
          ∫ α : ℝ, normalizedPairCorrelation T α * (g α : ℂ) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hS : (T / (2 * Real.pi) * Real.log T) ≠ 0 := by positivity
  have hSC : ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS
  have hre : ∀ ρ ∈ (nontrivialZeros_finite T).toFinset,
      ∀ ρ' ∈ (nontrivialZeros_finite T).toFinset, |(ρ - ρ').re| ≤ 1 := by
    intro ρ hρ ρ' hρ'
    simp only [Set.Finite.mem_toFinset] at hρ hρ'
    obtain ⟨-, h1, h2, -, -⟩ := hρ
    obtain ⟨-, h3, h4, -, -⟩ := hρ'
    rw [Complex.sub_re, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hInt : ∀ ρ ∈ (nontrivialZeros_finite T).toFinset,
      ∀ ρ' ∈ (nontrivialZeros_finite T).toFinset,
      Integrable fun α : ℝ =>
        ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) * pairWeight (ρ - ρ') *
          ((T ^ α : ℝ) : ℂ) ^ (ρ - ρ') * (g α : ℂ) := by
    intro ρ hρ ρ' hρ'
    exact integrable_ofReal_rpow_cpow_mul hT1 hg hsupp (hre ρ hρ ρ' hρ')
      (((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) * pairWeight (ρ - ρ'))
  have step : (∫ α : ℝ, pairCorrelation (T ^ α) T * (g α : ℂ)) = pairCorrelationSum g T := by
    have hpt : ∀ α : ℝ, pairCorrelation (T ^ α) T * (g α : ℂ)
        = ∑ ρ ∈ (nontrivialZeros_finite T).toFinset,
            ∑ ρ' ∈ (nontrivialZeros_finite T).toFinset,
              ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) * pairWeight (ρ - ρ') *
                ((T ^ α : ℝ) : ℂ) ^ (ρ - ρ') * (g α : ℂ) := by
      intro α
      rw [pairCorrelation, finsum_nontrivialZeros_eq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [finsum_nontrivialZeros_eq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun ρ' _ => by ring
    calc (∫ α : ℝ, pairCorrelation (T ^ α) T * (g α : ℂ))
        = ∫ α : ℝ, ∑ ρ ∈ (nontrivialZeros_finite T).toFinset,
            ∑ ρ' ∈ (nontrivialZeros_finite T).toFinset,
              ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) * pairWeight (ρ - ρ') *
                ((T ^ α : ℝ) : ℂ) ^ (ρ - ρ') * (g α : ℂ) :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = ∑ ρ ∈ (nontrivialZeros_finite T).toFinset,
            ∑ ρ' ∈ (nontrivialZeros_finite T).toFinset,
              ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
                fourierC g (rescaledDiff T ρ ρ') * pairWeight (ρ - ρ') := by
          rw [integral_finsetSum _ fun ρ hρ =>
            integrable_finsetSum _ fun ρ' hρ' => hInt ρ hρ ρ' hρ']
          refine Finset.sum_congr rfl fun ρ hρ => ?_
          rw [integral_finsetSum _ fun ρ' hρ' => hInt ρ hρ ρ' hρ']
          refine Finset.sum_congr rfl fun ρ' _ => ?_
          have hc : ∀ α : ℝ,
              ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) * pairWeight (ρ - ρ') *
                  ((T ^ α : ℝ) : ℂ) ^ (ρ - ρ') * (g α : ℂ)
                = (((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) * pairWeight (ρ - ρ')) *
                    ((g α : ℂ) *
                      Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I *
                        rescaledDiff T ρ ρ' * (α : ℂ))) := by
            intro α
            rw [exp_neg_two_pi_I_rescaledDiff hT0]
            ring
          rw [integral_congr_ae (Eventually.of_forall hc), integral_const_mul]
          rw [show (∫ α : ℝ, (g α : ℂ) *
              Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * rescaledDiff T ρ ρ' * (α : ℂ)))
                = fourierC g (rescaledDiff T ρ ρ') from rfl]
          ring
      _ = pairCorrelationSum g T := by
          rw [pairCorrelationSum, finsum_nontrivialZeros_eq]
          exact Finset.sum_congr rfl fun ρ _ => (finsum_nontrivialZeros_eq _ _).symm
  have hnorm : (∫ α : ℝ, normalizedPairCorrelation T α * (g α : ℂ))
      = ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ)⁻¹ *
          ∫ α : ℝ, pairCorrelation (T ^ α) T * (g α : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun α => ?_)
    simp only [normalizedPairCorrelation]
    ring
  rw [hnorm, step, mul_inv_cancel_left₀ hSC]

/-! ### The asymptotic for the normalised pair-correlation function -/

/-- **The asymptotic for the normalised pair-correlation function.** Assume the evaluation `hEval`
of the mean square. There is an absolute constant `C > 0` such that for every `T ≥ 3`, every
`ε ∈ (0, 1)` and every `α` with `0 ≤ α ≤ 1 - ε`, the quantity
`|F_T (α) - T^{-2α} log T - α|` is at most `C` times
`T^{-2α} + 1 / log T + T^{-α} √log T + T^{α-1} log²T + T^{-(α+1)/2} log T`. -/
theorem exists_abs_normalizedPairCorrelation_sub_le
    (hEval : ∃ C > 0, ∀ x T : ℝ, 1 ≤ x → x ≤ T → 3 ≤ T →
      |zeroSideMeanSquare x T - T * Real.log x - T * Real.log T ^ 2 / x ^ 2|
        ≤ C * (T + x * Real.log T ^ 2 + T * Real.log T / x ^ 2
            + T * Real.sqrt (Real.log T) ^ 3 / x
            + Real.sqrt (T / x) * Real.log T ^ 2)) :
    ∃ C > 0, ∀ T : ℝ, 3 ≤ T → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 - ε →
      ‖normalizedPairCorrelation T α - ((T ^ (-(2 * α)) * Real.log T + α : ℝ) : ℂ)‖
        ≤ C * (T ^ (-(2 * α)) + 1 / Real.log T + T ^ (-α) * Real.sqrt (Real.log T)
            + T ^ (α - 1) * Real.log T ^ 2
            + T ^ (-((α + 1) / 2)) * Real.log T) := by
  obtain ⟨C₁, hC₁, htr⟩ := exists_norm_pairCorrelation_sub_zeroSideMeanSquare_div_le
  obtain ⟨C₂, hC₂, hev⟩ := hEval
  refine ⟨C₂ + 2 * Real.pi * C₁, by positivity, ?_⟩
  intro T hT ε hε0 hε1 α hα0 hα1
  have hT0 : (0 : ℝ) < T := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log T := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    exact le_of_lt ((Real.lt_log_iff_exp_lt hT0).2 (lt_of_lt_of_le he hT))
  have hL0 : (0 : ℝ) < Real.log T := by linarith
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hx0 : (0 : ℝ) < T ^ α := Real.rpow_pos_of_pos hT0 α
  have hx1 : (1 : ℝ) ≤ T ^ α := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ T by linarith) hα0
  have hxT : T ^ α ≤ T := by
    calc T ^ α ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ T by linarith) (by linarith)
      _ = T := Real.rpow_one T
  have e1 : T ^ (-(2 * α)) = ((T ^ α) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hT0.le, show (2 : ℝ) * α = α * ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul hT0.le, Real.rpow_natCast]
  have e2 : T ^ (-α) = (T ^ α)⁻¹ := by rw [Real.rpow_neg hT0.le]
  have e3 : T ^ (α - 1) = T ^ α / T := by rw [Real.rpow_sub hT0, Real.rpow_one]
  have hTx : T / T ^ α = T ^ (1 - α) := by rw [Real.rpow_sub hT0, Real.rpow_one]
  have e4 : T ^ (-((α + 1) / 2)) = Real.sqrt (T / T ^ α) / T := by
    rw [hTx, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le,
      show ((1 : ℝ) - α) * (1 / 2) = -((α + 1) / 2) + 1 by ring, Real.rpow_add hT0,
      Real.rpow_one]
    field_simp
  rw [e1, e2, e3, e4]
  have hofReal : (((normalizedPairCorrelation T α).re : ℝ) : ℂ) = normalizedPairCorrelation T α :=
    Complex.ext (by simp) (by simp [normalizedPairCorrelation_im hT0 α])
  have hnormeq : ‖normalizedPairCorrelation T α - ((((T ^ α) ^ 2)⁻¹ * Real.log T + α : ℝ) : ℂ)‖
      = |(normalizedPairCorrelation T α).re - (((T ^ α) ^ 2)⁻¹ * Real.log T + α)| := by
    conv_lhs => rw [← hofReal]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnormeq]
  rw [show (normalizedPairCorrelation T α).re
      = (T / (2 * Real.pi) * Real.log T)⁻¹ * (pairCorrelation (T ^ α) T).re from by
    simp only [normalizedPairCorrelation]
    rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]]
  have hP : |(pairCorrelation (T ^ α) T).re -
        zeroSideMeanSquare (T ^ α) T / (2 * Real.pi)| ≤ C₁ * T ^ α * Real.log T ^ 3 := by
    have h1 : |(pairCorrelation (T ^ α) T -
          ((zeroSideMeanSquare (T ^ α) T / (2 * Real.pi) : ℝ) : ℂ)).re|
        ≤ C₁ * T ^ α * Real.log T ^ 3 :=
      le_trans (Complex.abs_re_le_norm _) (htr _ T hx1 hT)
    rwa [Complex.sub_re, Complex.ofReal_re] at h1
  have hsq : Real.sqrt (Real.log T) ^ 3 = Real.log T * Real.sqrt (Real.log T) := by
    rw [pow_succ, Real.sq_sqrt hL0.le]
  have hb2 : |zeroSideMeanSquare (T ^ α) T / (T * Real.log T) -
        (((T ^ α) ^ 2)⁻¹ * Real.log T + α)|
      ≤ C₂ * (((T ^ α) ^ 2)⁻¹ + 1 / Real.log T
          + (T ^ α)⁻¹ * Real.sqrt (Real.log T) + T ^ α / T * Real.log T
          + Real.sqrt (T / T ^ α) / T * Real.log T) := by
    have hid : zeroSideMeanSquare (T ^ α) T / (T * Real.log T) -
          (((T ^ α) ^ 2)⁻¹ * Real.log T + α)
        = (zeroSideMeanSquare (T ^ α) T - T * Real.log (T ^ α) -
            T * Real.log T ^ 2 / (T ^ α) ^ 2) / (T * Real.log T) := by
      rw [Real.log_rpow hT0]
      field_simp
      ring
    rw [hid, abs_div, abs_of_pos (show (0 : ℝ) < T * Real.log T by positivity),
      div_le_iff₀ (show (0 : ℝ) < T * Real.log T by positivity)]
    refine le_trans (hev _ T hx1 hxT hT) (le_of_eq ?_)
    rw [hsq]
    field_simp
    ring
  have hb1 : |(T / (2 * Real.pi) * Real.log T)⁻¹ *
        ((pairCorrelation (T ^ α) T).re - zeroSideMeanSquare (T ^ α) T / (2 * Real.pi))|
      ≤ 2 * Real.pi * C₁ * (T ^ α / T) * Real.log T ^ 2 := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < (T / (2 * Real.pi) * Real.log T)⁻¹ by positivity)]
    refine le_trans (mul_le_mul_of_nonneg_left hP (by positivity)) (le_of_eq ?_)
    field_simp
  rw [show (T / (2 * Real.pi) * Real.log T)⁻¹ * (pairCorrelation (T ^ α) T).re -
        (((T ^ α) ^ 2)⁻¹ * Real.log T + α)
      = (T / (2 * Real.pi) * Real.log T)⁻¹ *
          ((pairCorrelation (T ^ α) T).re - zeroSideMeanSquare (T ^ α) T / (2 * Real.pi))
        + (zeroSideMeanSquare (T ^ α) T / (T * Real.log T) -
            (((T ^ α) ^ 2)⁻¹ * Real.log T + α)) from by field_simp; ring]
  refine le_trans (abs_add_le _ _) (le_trans (add_le_add hb1 hb2) ?_)
  have hxTpos : (0 : ℝ) < T ^ α / T := by positivity
  have hLsq : (1 : ℝ) ≤ Real.log T ^ 2 := by nlinarith
  have hn1 : (0 : ℝ) ≤ ((T ^ α) ^ 2)⁻¹ := by positivity
  have hn2 : (0 : ℝ) ≤ 1 / Real.log T := by positivity
  have hn3 : (0 : ℝ) ≤ (T ^ α)⁻¹ * Real.sqrt (Real.log T) := by positivity
  have hn4 : (0 : ℝ) ≤ Real.sqrt (T / T ^ α) / T * Real.log T := by positivity
  have hpos : (0 : ℝ) ≤ 2 * Real.pi * C₁ := by positivity
  have habs : T ^ α / T * Real.log T ≤ T ^ α / T * Real.log T ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hxTpos.le
  nlinarith [mul_nonneg hpos hn1, mul_nonneg hpos hn2, mul_nonneg hpos hn3,
    mul_nonneg hpos hn4, mul_le_mul_of_nonneg_left habs hC₂.le,
    mul_le_mul_of_nonneg_left hLsq (mul_pos hC₂ hxTpos).le]

/-! ### Two elementary comparisons of logarithmic rates -/

/-- For every `ε > 0` the cube of the logarithm is eventually dominated by `T^ε`. -/
private lemma exists_log_cube_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ T₂ : ℝ, 3 ≤ T₂ ∧ ∀ T : ℝ, T₂ ≤ T → Real.log T ^ 3 ≤ T ^ ε := by
  have hlo := (isLittleO_log_rpow_atTop (r := ε / 3) (by positivity)).def
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.1 hlo
  refine ⟨max 3 T₃, le_max_left _ _, fun T hT => ?_⟩
  have hT3 : (3 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have h1 : Real.log T ≤ T ^ (ε / 3) := by
    have hb := hT₃ T (le_trans (le_max_right _ _) hT)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at hb
    calc Real.log T ≤ |Real.log T| := le_abs_self _
      _ ≤ |T ^ (ε / 3)| := hb
      _ = T ^ (ε / 3) := abs_of_pos (Real.rpow_pos_of_pos hT0 _)
  have h0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  calc Real.log T ^ 3 ≤ (T ^ (ε / 3)) ^ 3 := pow_le_pow_left₀ h0 h1 3
    _ = T ^ ε := by
        rw [← Real.rpow_natCast (T ^ (ε / 3)) 3, ← Real.rpow_mul hT0.le]
        norm_num

/-- `log log T ≤ 2 √log T` whenever `log T ≥ 1`: apply `log u ≤ u - 1` to `u = √log T`. -/
private lemma log_log_le_two_mul_sqrt {T : ℝ} (hL : 1 ≤ Real.log T) :
    Real.log (Real.log T) ≤ 2 * Real.sqrt (Real.log T) := by
  have hL0 : (0 : ℝ) < Real.log T := by linarith
  have hs : 0 < Real.sqrt (Real.log T) := Real.sqrt_pos.2 hL0
  have h1 : Real.log (Real.sqrt (Real.log T)) ≤ Real.sqrt (Real.log T) - 1 :=
    Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.log T) = 2 * Real.log (Real.sqrt (Real.log T)) := by
    rw [← Real.sq_sqrt hL0.le, Real.log_pow]
    norm_num
  rw [h2]
  linarith

/-- `√L (a / L) = a / √L` for positive `L`. -/
private lemma sqrt_mul_div_eq (a : ℝ) {L : ℝ} (hL : 0 < L) :
    Real.sqrt L * (a / L) = a / Real.sqrt L := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  calc Real.sqrt L * (a / L) = Real.sqrt L * (a / (Real.sqrt L * Real.sqrt L)) := by rw [hsq]
    _ = a / Real.sqrt L := by field_simp

/-! ### The pair-correlation formula for test functions vanishing near `±1` -/

/-- **The pair-correlation formula for test functions vanishing near `±1`.** Assume the evaluation
`hEval` of the mean square. For `g` integrable, even, with `|g α - g 0| ≤ K |α|` for `|α| < δ`, and
vanishing on `|α| ≥ 1 - ε`, the pair sum normalised by `(T / 2π) log T` approaches
`pairMainTerm g = g 0 + 2 ∫₀¹ α g (α) dα` at rate `O(1 / √log T)`. -/
theorem exists_norm_pairCorrelationSum_div_sub_le
    (hEval : ∃ C > 0, ∀ x T : ℝ, 1 ≤ x → x ≤ T → 3 ≤ T →
      |zeroSideMeanSquare x T - T * Real.log x - T * Real.log T ^ 2 / x ^ 2|
        ≤ C * (T + x * Real.log T ^ 2 + T * Real.log T / x ^ 2
            + T * Real.sqrt (Real.log T) ^ 3 / x
            + Real.sqrt (T / x) * Real.log T ^ 2))
    {g : ℝ → ℝ} {K δ ε : ℝ} (hg : Integrable g) (heven : ∀ α : ℝ, g (-α) = g α)
    (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hlip : ∀ α : ℝ, |α| < δ → |g α - g 0| ≤ K * |α|)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hsupp : ∀ α : ℝ, 1 - ε ≤ |α| → g α = 0) :
    ∃ T₀ ≥ 3, ∃ C > 0, ∀ T : ℝ, T₀ ≤ T →
      ‖pairCorrelationSum g T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ) -
          ((pairMainTerm g : ℝ) : ℂ)‖ ≤ C / Real.sqrt (Real.log T) := by
  obtain ⟨C₃, hC₃, hasym⟩ := exists_abs_normalizedPairCorrelation_sub_le hEval
  have hM : 0 < |g 0| + K * δ + 1 := by positivity
  have hbdd : ∀ᵐ α : ℝ, |α| < δ → |g α| ≤ |g 0| + K * δ + 1 :=
    Eventually.of_forall fun α hα => by
      have := abs_le_of_abs_sub_le_mul_abs hK hlip hα
      linarith
  obtain ⟨C₁, hC₁, hexp⟩ := exists_integral_rpow_neg_mul_abs_le hg hM hδ0 hδ1 hbdd
  obtain ⟨T₁, hT₁3, C₂, hC₂, hmain⟩ :=
    exists_abs_integral_rpow_neg_two_mul_sub_le hg hK hδ0 hδ1 hlip
  obtain ⟨T₂, hT₂3, hT₂⟩ := exists_log_cube_le_rpow hε0
  have hG0 : (0 : ℝ) ≤ ∫ α : ℝ, |g α| := integral_nonneg fun α => abs_nonneg _
  refine ⟨max (max T₁ T₂) (Real.exp 4),
    le_trans hT₁3 (le_trans (le_max_left _ _) (le_max_left _ _)),
    2 * C₂ + 4 * C₃ * (C₁ + ∫ α : ℝ, |g α|), by nlinarith, ?_⟩
  intro T hT
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
  have hTT₂ : T₂ ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
  have hTexp : Real.exp 4 ≤ T := le_trans (le_max_right _ _) hT
  have hT3 : (3 : ℝ) ≤ T := le_trans hT₁3 hTT₁
  have hT0 : (0 : ℝ) < T := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log T := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    exact le_of_lt ((Real.lt_log_iff_exp_lt hT0).2 (lt_of_lt_of_le he hT3))
  have hL0 : (0 : ℝ) < Real.log T := by linarith
  have hq0 : (0 : ℝ) < Real.sqrt (Real.log T) := Real.sqrt_pos.2 hL0
  have hqq : Real.sqrt (Real.log T) * Real.sqrt (Real.log T) = Real.log T :=
    Real.mul_self_sqrt hL0.le
  have hq1 : (1 : ℝ) ≤ Real.sqrt (Real.log T) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hL1
  have hsL : Real.sqrt (Real.log T) ≤ Real.log T := Real.sqrt_le_self_iff.2 (Or.inr hL1)
  have hSC : ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, F = fun α => (normalizedPairCorrelation T α).re := ⟨_, rfl⟩
  have hFofReal : ∀ α : ℝ, ((F α : ℝ) : ℂ) = normalizedPairCorrelation T α := fun α => by
    rw [hFdef]
    exact Complex.ext (by simp) (by simp [normalizedPairCorrelation_im hT0 α])
  have hFeven : ∀ α : ℝ, F (-α) = F α := fun α => by
    rw [hFdef]
    simp only
    rw [normalizedPairCorrelation_neg hT0 α]
  have hCcont : Continuous fun α : ℝ => normalizedPairCorrelation T α := by
    have hEq : (fun α : ℝ => normalizedPairCorrelation T α)
        = fun α : ℝ => ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ)⁻¹ *
            ∑ ρ ∈ (nontrivialZeros_finite T).toFinset,
              ∑ ρ' ∈ (nontrivialZeros_finite T).toFinset,
                ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
                  Complex.exp (((α * Real.log T : ℝ) : ℂ) * (ρ - ρ')) *
                    pairWeight (ρ - ρ') := by
      funext α
      simp only [normalizedPairCorrelation]
      rw [pairCorrelation, finsum_nontrivialZeros_eq]
      refine congrArg _ (Finset.sum_congr rfl fun ρ _ => ?_)
      rw [finsum_nontrivialZeros_eq]
      exact Finset.sum_congr rfl fun ρ' _ => by rw [ofReal_rpow_cpow hT0]
    rw [hEq]
    refine continuous_const.mul (continuous_finsetSum _ fun ρ _ => ?_)
    exact continuous_finsetSum _ fun ρ' _ => by fun_prop
  have hFcont : Continuous F := by
    rw [hFdef]
    exact Continuous.comp Complex.continuous_re hCcont
  have hprodII : ∀ a b : ℝ, IntervalIntegrable (fun α => F α * g α) volume a b := fun a b =>
    hg.intervalIntegrable.continuousOn_mul hFcont.continuousOn
  have hvanish : ∀ α : ℝ, 1 ≤ |α| → F α * g α = 0 := fun α hα => by
    rw [hsupp α (by linarith), mul_zero]
  have hprodInt : Integrable fun α : ℝ => F α * g α := by
    obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hFcont.continuousOn
    have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 0 (by norm_num))
    refine Integrable.mono' (hg.abs.const_mul C₀)
      (hFcont.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
    filter_upwards with α
    by_cases hα : 1 ≤ |α|
    · rw [hvanish α hα]
      simpa using mul_nonneg hC₀0 (abs_nonneg (g α))
    · replace hα : |α| < 1 := not_le.1 hα
      have hmem : α ∈ Set.Icc (-1 : ℝ) 1 := by
        rw [Set.mem_Icc]
        rcases abs_lt.1 hα with ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_of_eq (Real.norm_eq_abs (F α)).symm) (hC₀ α hmem)) (abs_nonneg _)
  have hfold : (∫ α : ℝ, F α * g α) = 2 * ∫ α in (0 : ℝ)..1, F α * g α := by
    have h1 : (∫ α : ℝ, F α * g α) = ∫ α in Set.Ioc (-1 : ℝ) 1, F α * g α := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun α hα => ?_).symm
      rw [Set.mem_Ioc] at hα
      refine hvanish α ?_
      rcases not_and_or.1 hα with h | h
      · replace h : α ≤ -1 := not_lt.1 h
        rw [abs_of_nonpos (by linarith)]
        linarith
      · replace h : 1 < α := not_le.1 h
        rw [abs_of_nonneg (by linarith)]
        linarith
    have h2 : (∫ α in Set.Ioc (-1 : ℝ) 1, F α * g α) = ∫ α in (-1 : ℝ)..1, F α * g α :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    have h3 : (∫ α in (-1 : ℝ)..0, F α * g α) = ∫ α in (0 : ℝ)..1, F α * g α := by
      have hcn := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun α => F α * g α)
      rw [neg_zero] at hcn
      rw [← hcn]
      refine intervalIntegral.integral_congr fun α _ => ?_
      rw [hFeven α, heven α]
    have h4 : (∫ α in (-1 : ℝ)..1, F α * g α)
        = (∫ α in (-1 : ℝ)..0, F α * g α) + ∫ α in (0 : ℝ)..1, F α * g α :=
      (intervalIntegral.integral_add_adjacent_intervals (hprodII _ _) (hprodII _ _)).symm
    rw [h1, h2, h4, h3]
    ring
  have hII1 : IntervalIntegrable
      (fun α => Real.log T * (T ^ (-(2 * α)) * g α)) volume 0 1 :=
    (intervalIntegrable_rpow_neg_mul hT0 2 hg 0 1).const_mul (Real.log T)
  have hII2 : IntervalIntegrable (fun α => α * g α) volume 0 1 :=
    hg.intervalIntegrable.continuousOn_mul continuous_id.continuousOn
  have hu : IntervalIntegrable (fun α => T ^ (-(1 * α)) * |g α|) volume 0 1 :=
    intervalIntegrable_rpow_neg_mul hT0 1 hg.abs 0 1
  have hv : IntervalIntegrable (fun α => |g α|) volume 0 1 := hg.abs.intervalIntegrable
  have hdecomp : (∫ α in (0 : ℝ)..1, F α * g α)
      = Real.log T * (∫ α in (0 : ℝ)..1, T ^ (-(2 * α)) * g α)
        + (∫ α in (0 : ℝ)..1, α * g α)
        + ∫ α in (0 : ℝ)..1,
            (F α * g α - Real.log T * (T ^ (-(2 * α)) * g α) - α * g α) := by
    rw [intervalIntegral.integral_sub ((hprodII 0 1).sub hII1) hII2,
      intervalIntegral.integral_sub (hprodII 0 1) hII1,
      intervalIntegral.integral_const_mul]
    ring
  have hL4 : (4 : ℝ) ≤ Real.log T := (Real.le_log_iff_exp_le hT0).2 hTexp
  have hsq2 : (2 : ℝ) ≤ Real.sqrt (Real.log T) := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL4
  have hTeps : T ^ (-ε) * Real.log T ^ 2 ≤ 1 / Real.log T := by
    have h1 : Real.log T ^ 3 ≤ T ^ ε := hT₂ T hTT₂
    have h2 : (0 : ℝ) < T ^ ε := Real.rpow_pos_of_pos hT0 ε
    rw [Real.rpow_neg hT0.le, le_div_iff₀ hL0, inv_mul_eq_div, div_mul_eq_mul_div,
      div_le_one h2]
    nlinarith
  have hrem : |∫ α in (0 : ℝ)..1,
        (F α * g α - Real.log T * (T ^ (-(2 * α)) * g α) - α * g α)|
      ≤ (C₃ * (2 + Real.sqrt (Real.log T))) * (∫ α in (0 : ℝ)..1, T ^ (-(1 * α)) * |g α|)
        + (C₃ * (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2)) *
            ∫ α in (0 : ℝ)..1, |g α| := by
    have hbII : IntervalIntegrable
        (fun α => (C₃ * (2 + Real.sqrt (Real.log T))) * (T ^ (-(1 * α)) * |g α|)
          + (C₃ * (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2)) * |g α|) volume 0 1 :=
      (hu.const_mul _).add (hv.const_mul _)
    have hpt : ∀ α ∈ Set.Icc (0 : ℝ) 1,
        |F α * g α - Real.log T * (T ^ (-(2 * α)) * g α) - α * g α|
          ≤ (C₃ * (2 + Real.sqrt (Real.log T))) * (T ^ (-(1 * α)) * |g α|)
            + (C₃ * (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2)) * |g α| := by
      intro α hα
      obtain ⟨hα0, hα1⟩ := hα
      by_cases hgz : 1 - ε ≤ |α|
      · rw [hsupp α hgz]
        simp
      · replace hgz : |α| < 1 - ε := not_le.1 hgz
        have hα1' : α ≤ 1 - ε := le_of_lt (lt_of_le_of_lt (le_abs_self α) hgz)
        have hasy := hasym T hT3 ε hε0 hε1 α hα0 hα1'
        rw [show ‖normalizedPairCorrelation T α -
              ((T ^ (-(2 * α)) * Real.log T + α : ℝ) : ℂ)‖
            = |F α - (T ^ (-(2 * α)) * Real.log T + α)| from by
          rw [← hFofReal α, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]] at hasy
        rw [show F α * g α - Real.log T * (T ^ (-(2 * α)) * g α) - α * g α
            = (F α - (T ^ (-(2 * α)) * Real.log T + α)) * g α from by ring, abs_mul]
        have h2α : T ^ (-(2 * α)) ≤ T ^ (-(1 * α)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        have hεb : T ^ (α - 1) ≤ T ^ (-ε) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        have hLsq : (0 : ℝ) ≤ Real.log T ^ 2 := by positivity
        have hfifth : T ^ (-((α + 1) / 2)) * Real.log T ≤ T ^ (-(1 * α)) :=
          rpow_neg_half_add_mul_log_le hT0 (by linarith) hL0 hL1 (hT₂ T hTT₂) hα1'
        have hD : T ^ (α - 1) * Real.log T ^ 2 ≤ T ^ (-ε) * Real.log T ^ 2 :=
          mul_le_mul_of_nonneg_right hεb hLsq
        have hE : T ^ (-(2 * α)) + 1 / Real.log T
              + T ^ (-α) * Real.sqrt (Real.log T) + T ^ (α - 1) * Real.log T ^ 2
              + T ^ (-((α + 1) / 2)) * Real.log T
            ≤ (2 + Real.sqrt (Real.log T)) * T ^ (-(1 * α))
              + (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2) := by
          rw [show T ^ (-α) = T ^ (-(1 * α)) from by rw [one_mul],
            show (2 + Real.sqrt (Real.log T)) * T ^ (-(1 * α))
              = T ^ (-(1 * α)) + T ^ (-(1 * α))
                + T ^ (-(1 * α)) * Real.sqrt (Real.log T) from by ring]
          linarith [h2α, hfifth, hD]
        calc |F α - (T ^ (-(2 * α)) * Real.log T + α)| * |g α|
            ≤ (C₃ * (T ^ (-(2 * α)) + 1 / Real.log T
                + T ^ (-α) * Real.sqrt (Real.log T)
                + T ^ (α - 1) * Real.log T ^ 2
                + T ^ (-((α + 1) / 2)) * Real.log T)) * |g α| :=
              mul_le_mul_of_nonneg_right hasy (abs_nonneg _)
          _ ≤ (C₃ * ((2 + Real.sqrt (Real.log T)) * T ^ (-(1 * α))
                + (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2))) * |g α| :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hE hC₃.le) (abs_nonneg _)
          _ = _ := by ring
    calc |∫ α in (0 : ℝ)..1,
            (F α * g α - Real.log T * (T ^ (-(2 * α)) * g α) - α * g α)|
        ≤ ∫ α in (0 : ℝ)..1,
            |F α * g α - Real.log T * (T ^ (-(2 * α)) * g α) - α * g α| :=
          intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ α in (0 : ℝ)..1,
            ((C₃ * (2 + Real.sqrt (Real.log T))) * (T ^ (-(1 * α)) * |g α|)
              + (C₃ * (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2)) * |g α|) :=
          intervalIntegral.integral_mono_on (by norm_num)
            (((hprodII 0 1).sub hII1).sub hII2).abs hbII hpt
      _ = _ := by
          rw [intervalIntegral.integral_add (hu.const_mul _) (hv.const_mul _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hu1 : (∫ α in (0 : ℝ)..1, T ^ (-(1 * α)) * |g α|) ≤ C₁ / Real.log T :=
    hexp T hT3 1 le_rfl
  have hU0 : (0 : ℝ) ≤ ∫ α in (0 : ℝ)..1, T ^ (-(1 * α)) * |g α| :=
    intervalIntegral.integral_nonneg (by norm_num) fun α _ => by positivity
  have hv1 : (∫ α in (0 : ℝ)..1, |g α|) ≤ ∫ α : ℝ, |g α| := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_le_integral hg.abs (Eventually.of_forall fun α => abs_nonneg _)
  have hV0 : (0 : ℝ) ≤ ∫ α in (0 : ℝ)..1, |g α| :=
    intervalIntegral.integral_nonneg (by norm_num) fun α _ => abs_nonneg _
  have hA1 : (2 + Real.sqrt (Real.log T)) * (∫ α in (0 : ℝ)..1, T ^ (-(1 * α)) * |g α|)
      ≤ 2 * C₁ / Real.sqrt (Real.log T) := by
    have hle : (2 : ℝ) + Real.sqrt (Real.log T) ≤ 2 * Real.sqrt (Real.log T) := by linarith
    have h1 : (2 + Real.sqrt (Real.log T)) * (∫ α in (0 : ℝ)..1, T ^ (-(1 * α)) * |g α|)
        ≤ (2 * Real.sqrt (Real.log T)) * (C₁ / Real.log T) :=
      le_trans (mul_le_mul_of_nonneg_right hle hU0)
        (mul_le_mul_of_nonneg_left hu1 (by positivity))
    have h2 : (2 * Real.sqrt (Real.log T)) * (C₁ / Real.log T)
        = 2 * C₁ / Real.sqrt (Real.log T) := by
      rw [show (2 * Real.sqrt (Real.log T)) * (C₁ / Real.log T)
          = Real.sqrt (Real.log T) * ((2 * C₁) / Real.log T) from by ring]
      exact sqrt_mul_div_eq (2 * C₁) hL0
    linarith
  have hA2 : (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2) * (∫ α in (0 : ℝ)..1, |g α|)
      ≤ 2 * (∫ α : ℝ, |g α|) / Real.sqrt (Real.log T) := by
    have htwo : (2 : ℝ) / Real.log T = 1 / Real.log T + 1 / Real.log T := by ring
    have hle : 1 / Real.log T + T ^ (-ε) * Real.log T ^ 2 ≤ 2 / Real.log T := by
      rw [htwo]
      linarith
    have h1 : (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2) * (∫ α in (0 : ℝ)..1, |g α|)
        ≤ (2 / Real.log T) * ∫ α : ℝ, |g α| :=
      le_trans (mul_le_mul_of_nonneg_right hle hV0)
        (mul_le_mul_of_nonneg_left hv1 (by positivity))
    have h2 : (2 / Real.log T) * (∫ α : ℝ, |g α|)
        ≤ 2 * (∫ α : ℝ, |g α|) / Real.sqrt (Real.log T) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hL0 hq0]
      nlinarith [hG0, hsL]
    linarith
  have hb1 : |2 * Real.log T * (∫ α in (0 : ℝ)..1, T ^ (-(2 * α)) * g α) - g 0|
      ≤ 2 * C₂ / Real.sqrt (Real.log T) := by
    have hr : Real.log (Real.log T) / Real.log T ≤ 2 / Real.sqrt (Real.log T) := by
      rw [div_le_div_iff₀ hL0 hq0]
      nlinarith [mul_le_mul_of_nonneg_right (log_log_le_two_mul_sqrt hL1) hq0.le, hqq]
    have := hmain T hTT₁
    have h2 : C₂ * (Real.log (Real.log T) / Real.log T) ≤ C₂ * (2 / Real.sqrt (Real.log T)) :=
      mul_le_mul_of_nonneg_left hr hC₂.le
    have h3 : C₂ * (2 / Real.sqrt (Real.log T)) = 2 * C₂ / Real.sqrt (Real.log T) := by
      ring
    linarith
  have hfinal : |(∫ α : ℝ, F α * g α) - pairMainTerm g|
      ≤ (2 * C₂ + 4 * C₃ * (C₁ + ∫ α : ℝ, |g α|)) / Real.sqrt (Real.log T) := by
    rw [show (∫ α : ℝ, F α * g α) - pairMainTerm g
        = (2 * Real.log T * (∫ α in (0 : ℝ)..1, T ^ (-(2 * α)) * g α) - g 0)
          + 2 * (∫ α in (0 : ℝ)..1,
              (F α * g α - Real.log T * (T ^ (-(2 * α)) * g α) - α * g α)) from by
      rw [hfold, hdecomp, pairMainTerm]
      ring]
    refine le_trans (abs_add_le _ _) ?_
    have hb2 : |2 * (∫ α in (0 : ℝ)..1,
          (F α * g α - Real.log T * (T ^ (-(2 * α)) * g α) - α * g α))|
        ≤ 4 * C₃ * (C₁ + ∫ α : ℝ, |g α|) / Real.sqrt (Real.log T) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hstep : (C₃ * (2 + Real.sqrt (Real.log T))) *
              (∫ α in (0 : ℝ)..1, T ^ (-(1 * α)) * |g α|)
            + (C₃ * (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2)) *
                (∫ α in (0 : ℝ)..1, |g α|)
          ≤ C₃ * (2 * C₁ / Real.sqrt (Real.log T))
            + C₃ * (2 * (∫ α : ℝ, |g α|) / Real.sqrt (Real.log T)) := by
        have e1 : (C₃ * (2 + Real.sqrt (Real.log T))) *
            (∫ α in (0 : ℝ)..1, T ^ (-(1 * α)) * |g α|)
            = C₃ * ((2 + Real.sqrt (Real.log T)) *
              ∫ α in (0 : ℝ)..1, T ^ (-(1 * α)) * |g α|) := by ring
        have e2 : (C₃ * (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2)) *
            (∫ α in (0 : ℝ)..1, |g α|)
            = C₃ * ((1 / Real.log T + T ^ (-ε) * Real.log T ^ 2) *
              ∫ α in (0 : ℝ)..1, |g α|) := by ring
        rw [e1, e2]
        exact add_le_add (mul_le_mul_of_nonneg_left hA1 hC₃.le)
          (mul_le_mul_of_nonneg_left hA2 hC₃.le)
      have hsum : C₃ * (2 * C₁ / Real.sqrt (Real.log T))
            + C₃ * (2 * (∫ α : ℝ, |g α|) / Real.sqrt (Real.log T))
          = 2 * C₃ * (C₁ + ∫ α : ℝ, |g α|) / Real.sqrt (Real.log T) := by
        ring
      have hfin : 2 * (2 * C₃ * (C₁ + ∫ α : ℝ, |g α|) / Real.sqrt (Real.log T))
          = 4 * C₃ * (C₁ + ∫ α : ℝ, |g α|) / Real.sqrt (Real.log T) := by
        ring
      calc 2 * |∫ α in (0 : ℝ)..1,
              (F α * g α - Real.log T * (T ^ (-(2 * α)) * g α) - α * g α)|
          ≤ 2 * ((C₃ * (2 + Real.sqrt (Real.log T))) *
              (∫ α in (0 : ℝ)..1, T ^ (-(1 * α)) * |g α|)
              + (C₃ * (1 / Real.log T + T ^ (-ε) * Real.log T ^ 2)) *
                ∫ α in (0 : ℝ)..1, |g α|) :=
            mul_le_mul_of_nonneg_left hrem (by norm_num)
        _ ≤ 2 * (2 * C₃ * (C₁ + ∫ α : ℝ, |g α|) / Real.sqrt (Real.log T)) := by
            rw [← hsum]
            exact mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ = _ := hfin
    have hsplit : (2 * C₂ + 4 * C₃ * (C₁ + ∫ α : ℝ, |g α|)) / Real.sqrt (Real.log T)
        = 2 * C₂ / Real.sqrt (Real.log T)
          + 4 * C₃ * (C₁ + ∫ α : ℝ, |g α|) / Real.sqrt (Real.log T) := by
      field_simp
    rw [hsplit]
    exact add_le_add hb1 hb2
  have hY : (∫ α : ℝ, normalizedPairCorrelation T α * (g α : ℂ))
      = ((∫ α : ℝ, F α * g α : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun α => ?_)
    have hpt : normalizedPairCorrelation T α * (g α : ℂ) = ((F α * g α : ℝ) : ℂ) := by
      rw [← hFofReal α]
      push_cast
      ring
    exact hpt
  rw [pairCorrelationSum_eq_ofReal_integral hg
      (R := 1 - ε) (fun α hα => hsupp α hα.le) hT3, hY, mul_div_cancel_left₀ _ hSC,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hfinal

/-- **The pair-correlation formula from the evaluation of the mean square.** The bound `hEval` on
the mean square implies `ZetaZeros.PairCorrelation`. -/
theorem pairCorrelation_of_margin
    (hEval : ∃ C > 0, ∀ x T : ℝ, 1 ≤ x → x ≤ T → 3 ≤ T →
      |zeroSideMeanSquare x T - T * Real.log x - T * Real.log T ^ 2 / x ^ 2|
        ≤ C * (T + x * Real.log T ^ 2 + T * Real.log T / x ^ 2
            + T * Real.sqrt (Real.log T) ^ 3 / x
            + Real.sqrt (T / x) * Real.log T ^ 2)) :
    PairCorrelation := by
  intro f hf
  obtain ⟨heven, hint, ⟨ε, hε0, hε1, hsupp⟩, K, hlip⟩ := hf
  obtain ⟨T₀, hT₀, C, hC, hbound⟩ :=
    exists_norm_pairCorrelationSum_div_sub_le hEval hint heven
      (show (0 : ℝ) < |K| + 1 by positivity) (show (0 : ℝ) < 1 by norm_num) le_rfl
      (fun α _ => le_trans (hlip α)
        (mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (abs_nonneg α)))
      hε0 hε1 hsupp
  exact ⟨C, hC, T₀, hbound⟩

end ZetaZeros
