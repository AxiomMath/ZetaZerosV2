/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
public import ZetaZeros.Zeta.AllZeros
public import ZetaZeros.Landau.Perron
public import ZetaZeros.Analytic.Xi
public import ZetaZeros.Landau.ZeroSums

/-!
# The partial fractions of `ξ' / ξ` and of `ζ' / ζ` over the non-trivial zeros

The genus-one Hadamard expansion of the logarithmic derivative of the completed zeta function,
reindexed from the zero indices `Complex.Hadamard.divisorZeroIndex₀ riemannXi Set.univ` (in which
a zero of order `m` contributes `m` indices) onto the set `𝒩*` of `ZetaZeros.allZeros`, each zero
weighted by its multiplicity `m_ρ = ZetaZeros.zeroMultiplicity ρ`; its transport to `ζ' / ζ`; the
absolute summability of the combined two-point family over `𝒩*`; and the limit of the right edge
of the Perron contour for Landau's explicit formula.

## Main results

* `ZetaZeros.riemannXi_eq_zero_iff_mem_allZeros`: `ξ s = 0 ↔ s ∈ 𝒩*`, on the whole plane.
* `ZetaZeros.summable_zeroMultiplicity_mul_logDerivTerm`: the partial-fraction series over `𝒩*`
  converges absolutely off the zeros.
* `ZetaZeros.exists_logDeriv_riemannXi_eq_add_tsum_allZeros`: there is a constant `B` with
  `(ξ' / ξ)(z) = B + ∑_{ρ ∈ 𝒩*} m_ρ (1 / (z - ρ) + 1 / ρ)` for every `z` off `𝒩*`.
* `ZetaZeros.exists_logDeriv_riemannZeta_eq_add_tsum_allZeros`: the corresponding expansion of
  `ζ' / ζ` on the right half-plane.
* `ZetaZeros.summable_landauCombinedTerm`: the two-point family
  `ρ ↦ m_ρ 2 x^{ρ - 1/2} / (1 - (ρ - (1/2 + it))²)` is absolutely summable over `𝒩*`.
* `ZetaZeros.exists_pos_le_abs_log_div_natCast`: a real `x > 0` that is not a prime power lies at a
  positive logarithmic distance from every prime power.
* `ZetaZeros.tendsto_integral_logDeriv_riemannZeta_perron`: the truncated Perron integral of
  `(-ζ'/ζ)(w) x^{w - s}/(w - s)` along `re (w - s) = σ` tends to `∑_{n ≤ x} Λ(n) n^{-s}`.
-/

@[expose] public section

namespace ZetaZeros

open Complex Complex.Hadamard Filter Topology
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-! ## The zeros of `ξ`, globally -/

/-- **The zeros of `ξ` are exactly `𝒩*`.** -/
theorem riemannXi_eq_zero_iff_mem_allZeros (s : ℂ) : riemannXi s = 0 ↔ s ∈ allZeros := by
  by_cases h : -2 < s.re
  · simpa only [allZeros, Set.mem_ofPred_eq] using riemannXi_eq_zero_iff h
  · push Not at h
    refine ⟨fun hxi => ?_, fun hs => absurd hs.2.1 (by linarith)⟩
    have hre : -2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]; linarith
    have h1 : riemannXi (1 - s) = 0 := (riemannXi_functional_equation s).trans hxi
    obtain ⟨-, -, hlt⟩ := (riemannXi_eq_zero_iff hre).mp h1
    simp only [Complex.sub_re, Complex.one_re] at hlt
    linarith

/-! ## The enumeration of `𝒩*` by the zero indices of `ξ` -/

/-- Every zero index of `ξ` points at a non-trivial zero of `ζ`. -/
private theorem divisorZeroIndex₀_val_mem_allZeros
    (p : divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    divisorZeroIndex₀_val p ∈ allZeros := by
  have hsupp := divisorZeroIndex₀_val_mem_divisor_support p
  rw [divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi] at hsupp
  exact (riemannXi_eq_zero_iff_mem_allZeros _).mp
    (apply_eq_zero_of_analyticOrderNatAt_ne_zero (by exact_mod_cast hsupp))

/-- The fibre of the zero index of `ξ` over `ρ ∈ 𝒩*` has exactly `m_ρ` elements. -/
private theorem card_divisorZeroIndex₀_fiberFinset_riemannXi {ρ : ℂ} (hρ : ρ ∈ allZeros) :
    (divisorZeroIndex₀_fiberFinset riemannXi ρ).card = zeroMultiplicity ρ := by
  obtain ⟨-, h0, h1⟩ := hρ
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  rw [divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt differentiable_riemannXi hρ0,
    analyticOrderNatAt_riemannXi h0 h1]

/-- A sum indexed by the zeros of `ξ` with multiplicity is the sum over `𝒩*` of the same terms
weighted by `m_ρ`, and has the same value. -/
private theorem hasSum_allZeros_of_hasSum_divisorZeroIndex₀ {f : ℂ → ℂ} {a : ℂ}
    (hf : HasSum (fun p : divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
      f (divisorZeroIndex₀_val p)) a) :
    HasSum (fun ρ : allZeros => (zeroMultiplicity ρ.1 : ℂ) * f ρ.1) a := by
  classical
  set g : divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) → allZeros :=
    fun p => ⟨divisorZeroIndex₀_val p, divisorZeroIndex₀_val_mem_allZeros p⟩ with hg
  have hfun : ∀ ρ : allZeros,
      (∑' p : ↥(g ⁻¹' {ρ}), f (divisorZeroIndex₀_val p.1))
        = (zeroMultiplicity ρ.1 : ℂ) * f ρ.1 := by
    intro ρ
    have hpre : g ⁻¹' {ρ} = ↑(divisorZeroIndex₀_fiberFinset riemannXi ρ.1) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hg, Finset.mem_coe,
        mem_divisorZeroIndex₀_fiberFinset, Subtype.ext_iff]
    rw [hpre, Finset.tsum_subtype' (divisorZeroIndex₀_fiberFinset riemannXi ρ.1)
      (fun p => f (divisorZeroIndex₀_val p))]
    have hconst : ∀ p ∈ divisorZeroIndex₀_fiberFinset riemannXi ρ.1,
        f (divisorZeroIndex₀_val p) = f ρ.1 := fun p hp => by
      rw [(mem_divisorZeroIndex₀_fiberFinset riemannXi ρ.1 p).1 hp]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const,
      card_divisorZeroIndex₀_fiberFinset_riemannXi ρ.2, nsmul_eq_mul]
  simpa only [hfun] using hf.tsum_fiberwise g

/-- A family summable over the zero indices of `ξ` is summable over `𝒩*` when weighted by
`m_ρ`. -/
private theorem summable_allZeros_of_summable_divisorZeroIndex₀ {f : ℂ → ℂ}
    (hf : Summable (fun p : divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
      f (divisorZeroIndex₀_val p))) :
    Summable (fun ρ : allZeros => (zeroMultiplicity ρ.1 : ℂ) * f ρ.1) :=
  (hasSum_allZeros_of_hasSum_divisorZeroIndex₀ hf.hasSum).summable

/-! ## The partial fraction of `ξ' / ξ` -/

/-- The derivative of a polynomial of degree at most `1` is constant. -/
private lemma eval_derivative_eq_of_degree_le_one {P : Polynomial ℂ} (hP : P.degree ≤ 1) (z : ℂ) :
    Polynomial.eval z P.derivative = Polynomial.eval 0 P.derivative := by
  have hnat : P.natDegree ≤ 1 := Polynomial.natDegree_le_iff_degree_le.mpr hP
  have hd : P.derivative.natDegree = 0 := by
    have := Polynomial.natDegree_derivative_le P
    omega
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hd
  rw [← hc, Polynomial.eval_C, Polynomial.eval_C]

/-- **The partial-fraction series over `𝒩*` converges absolutely** off the zeros. -/
theorem summable_zeroMultiplicity_mul_logDerivTerm {z : ℂ} (hz : ∀ ρ ∈ allZeros, z ≠ ρ) :
    Summable (fun ρ : allZeros =>
      (zeroMultiplicity ρ.1 : ℂ) * (1 / (z - ρ.1) + 1 / ρ.1)) :=
  summable_allZeros_of_summable_divisorZeroIndex₀ (f := fun w => 1 / (z - w) + 1 / w)
    (summable_riemannXi_logDerivTerms_divisorZeroIndex₀
      fun p => hz _ (divisorZeroIndex₀_val_mem_allZeros p))

/-- **The partial-fraction expansion of `ξ' / ξ` over `𝒩*` with multiplicity.** There is a constant
`B` with

`(ξ' / ξ)(z) = B + ∑_{ρ ∈ 𝒩*} m_ρ (1 / (z - ρ) + 1 / ρ)`

for every `z` that is not a non-trivial zero of `ζ`. -/
theorem exists_logDeriv_riemannXi_eq_add_tsum_allZeros :
    ∃ B : ℂ, ∀ z : ℂ, (∀ ρ ∈ allZeros, z ≠ ρ) →
      HasSum (fun ρ : allZeros => (zeroMultiplicity ρ.1 : ℂ) * (1 / (z - ρ.1) + 1 / ρ.1))
        (logDeriv riemannXi z - B) := by
  obtain ⟨P, hPdeg, hPfac⟩ := riemannXi_hadamard_factorization_no_monomial
  refine ⟨Polynomial.eval 0 P.derivative, fun z hz => ?_⟩
  have hz' : ∀ p : divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ divisorZeroIndex₀_val p :=
    fun p => hz _ (divisorZeroIndex₀_val_mem_allZeros p)
  have hsum := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hz'
  have heq := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hPfac hz'
  rw [eval_derivative_eq_of_degree_le_one hPdeg] at heq
  have hfib := hasSum_allZeros_of_hasSum_divisorZeroIndex₀
    (f := fun w => 1 / (z - w) + 1 / w) hsum.hasSum
  have hval : ∑' p : divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p)
      = logDeriv riemannXi z - Polynomial.eval 0 P.derivative := by
    rw [heq]; ring
  rwa [hval] at hfib

/-! ## The partial fraction of `ζ' / ζ` -/

/-- **The partial-fraction expansion of `ζ' / ζ` over `𝒩*` with multiplicity.** There is a constant
`B` such that, for every `s` in the right half-plane that is neither `1` nor a zero of `ζ`,

`(ζ' / ζ)(s) = B + ∑_{ρ ∈ 𝒩*} m_ρ (1 / (s - ρ) + 1 / ρ) - 1 / s - 1 / (s - 1)
  + log π / 2 - digamma (s / 2) / 2`. -/
theorem exists_logDeriv_riemannZeta_eq_add_tsum_allZeros :
    ∃ B : ℂ, ∀ s : ℂ, 0 < s.re → s ≠ 1 → riemannZeta s ≠ 0 →
      deriv riemannZeta s / riemannZeta s
        = B + (∑' ρ : allZeros, (zeroMultiplicity ρ.1 : ℂ) * (1 / (s - ρ.1) + 1 / ρ.1))
          - 1 / s - 1 / (s - 1) + (Real.log Real.pi : ℂ) / 2 - digamma (s / 2) / 2 := by
  obtain ⟨B, hB⟩ := exists_logDeriv_riemannXi_eq_add_tsum_allZeros
  refine ⟨B, fun s h0 h1 hζ => ?_⟩
  have hz : ∀ ρ ∈ allZeros, s ≠ ρ := fun ρ hρ h => hζ (h ▸ hρ.1)
  rw [(hB s hz).tsum_eq, logDeriv_riemannXi_eq h0 h1 hζ]
  ring

/-! ## Landau's formula in combined form -/

/-- **The combined two-point family is absolutely summable.** For `x ≥ 1` and real `t`,

`ρ ↦ m_ρ ⬝ 2 x^{ρ - 1/2} / (1 - (ρ - (1/2 + it))²)`

is absolutely summable over `𝒩*`. -/
theorem summable_landauCombinedTerm {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    Summable (fun ρ : allZeros => (zeroMultiplicity (ρ : ℂ) : ℂ) *
      (2 * (x : ℂ) ^ ((ρ : ℂ) - 1 / 2)
        / (1 - ((ρ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2))) := by
  have hx0 : (x : ℂ) ≠ 0 := by
    simpa using (lt_of_lt_of_le zero_lt_one hx).ne'
  refine ((summable_zeroSideTerm (x := x) (t := t) hx).mul_left
    ((x : ℂ) ^ ((t : ℂ) * I))).congr fun ρ => ?_
  have hsplit : (x : ℂ) ^ ((ρ : ℂ) - 1 / 2)
      = (x : ℂ) ^ ((ρ : ℂ) - 1 / 2 - (t : ℂ) * I) * (x : ℂ) ^ ((t : ℂ) * I) := by
    rw [← Complex.cpow_add _ _ hx0]
    congr 1
    ring
  rw [hsplit]
  ring

/-! ## The right edge of the Perron contour -/

/-- **`x` sits at a positive logarithmic distance from every prime power.** If the real `x > 0` is
not (the cast of) a prime power, there is a `δ > 0` with `|log (x / n)| ≥ δ` for every `n` in the
support of `Λ`. -/
theorem exists_pos_le_abs_log_div_natCast {x : ℝ} (hx : 0 < x)
    (hxpp : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ≠ x) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, Λ n ≠ 0 → d ≤ |Real.log (x / n)| := by
  classical
  set S : Finset ℕ := (Finset.range ⌈2 * x⌉₊).filter (fun n => Λ n ≠ 0) with hS
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : ∀ n ∈ S, 0 < |Real.log (x / n)| := by
    intro n hn
    have hΛ : Λ n ≠ 0 := (Finset.mem_filter.1 hn).2
    have hn1 : 1 < n := (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ).one_lt
    have hn0 : (0 : ℝ) < n := by positivity
    have hne : (n : ℝ) ≠ x := hxpp n (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
    have hdiv : x / n ≠ 1 := fun h => hne (by field_simp at h; linarith [h])
    exact abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one (by positivity) hdiv)
  have hbig : ∀ n : ℕ, Λ n ≠ 0 → ⌈2 * x⌉₊ ≤ n → Real.log 2 ≤ |Real.log (x / n)| := by
    intro n hn hge
    have hn1 : 1 < n := (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hn).one_lt
    have hn0 : (0 : ℝ) < n := by positivity
    have h2x : 2 * x ≤ (n : ℝ) := (Nat.le_ceil (2 * x)).trans (Nat.cast_le.2 hge)
    have hhalf : x / n ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]
      linarith
    have hlogle : Real.log (x / n) ≤ -Real.log 2 := by
      have := Real.log_le_log (by positivity) hhalf
      rwa [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at this
    rw [abs_of_neg (by linarith), le_neg]
    exact hlogle
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨Real.log 2, hlog2, fun n hn => hbig n hn ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    rw [hS, Finset.filter_eq_empty_iff] at hSe
    exact hSe (Finset.mem_range.2 hlt) hn
  · refine ⟨min (Real.log 2) (S.inf' hSne fun n => |Real.log (x / n)|),
      lt_min hlog2 ((Finset.lt_inf'_iff hSne).2 hpos), fun n hn => ?_⟩
    rcases lt_or_ge n ⌈2 * x⌉₊ with hlt | hge
    · exact (min_le_right _ _).trans
        (Finset.inf'_le _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, hn⟩))
    · exact (min_le_left _ _).trans (hbig n hn hge)

/-- The complex power of a quotient of positive reals splits. -/
private lemma ofReal_div_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℂ) :
    ((a / b : ℝ) : ℂ) ^ u = (a : ℂ) ^ u / (b : ℂ) ^ u := by
  have ha0 : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hb0 : ((b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have hab : ((a / b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  rw [Complex.cpow_def_of_ne_zero hab, Complex.cpow_def_of_ne_zero ha0,
    Complex.cpow_def_of_ne_zero hb0, ← Complex.exp_sub]
  congr 1
  rw [← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le,
    ← Complex.ofReal_log (div_pos ha hb).le, Real.log_div ha.ne' hb.ne']
  push_cast
  ring

/-- The point `σ + iv` of the recentred contour is never `0`, since `σ > 0`. -/
private lemma perronPoint_ne_zero {σ : ℝ} (hσ : 0 < σ) (v : ℝ) :
    ((σ : ℂ) + (v : ℂ) * I) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.zero_re] at hre
  exact hσ.ne' (by linarith)

/-- The recentred Perron kernel `u ↦ x^u / u` is continuous along the vertical line `re u = σ`. -/
private lemma continuous_perronKernel {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) :
    Continuous fun v : ℝ => (x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I) := by
  have hu : Continuous fun v : ℝ => ((σ : ℂ) + (v : ℂ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact (hu.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 hx.ne'))).div hu
    (perronPoint_ne_zero hσ)

/-- The `n`-th term of the Dirichlet series against the recentred Perron kernel is continuous
along the line. -/
private lemma continuous_perronDirichletTerm {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) (s : ℂ) (n : ℕ) :
    Continuous fun v : ℝ => LSeries.term ↗Λ (s + ((σ : ℂ) + (v : ℂ) * I)) n
      * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I)) := by
  have hu : Continuous fun v : ℝ => ((σ : ℂ) + (v : ℂ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using continuous_const
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    simp only [LSeries.term_of_ne_zero hn]
    refine (continuous_const.div ((continuous_const.add hu).const_cpow (Or.inl hn0))
      fun v => Complex.cpow_ne_zero_iff.2 (Or.inl hn0)).mul (continuous_perronKernel hx hσ)

/-- **The pointwise bound on the recentred integrand.** On the line `re u = σ` the `n`-th term is
at most `x^σ / σ` times the `n`-th term of the Dirichlet series at the real abscissa
`σ + re s`. -/
private lemma norm_perronDirichletTerm_le {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) (s : ℂ) (n : ℕ)
    (v : ℝ) :
    ‖LSeries.term ↗Λ (s + ((σ : ℂ) + (v : ℂ) * I)) n
        * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I))‖
      ≤ ‖LSeries.term ↗Λ ((σ + s.re : ℝ) : ℂ) n‖ * (x ^ σ / σ) := by
  have hre : ((σ : ℂ) + (v : ℂ) * I).re = σ := by simp
  have h1 : ‖LSeries.term ↗Λ (s + ((σ : ℂ) + (v : ℂ) * I)) n‖
      ≤ ‖LSeries.term ↗Λ ((σ + s.re : ℝ) : ℂ) n‖ :=
    LSeries.norm_term_le_of_re_le_re _ (by simp [hre]; linarith) n
  have hnorm : σ ≤ ‖(σ : ℂ) + (v : ℂ) * I‖ := by
    calc σ = |((σ : ℂ) + (v : ℂ) * I).re| := by rw [hre, abs_of_pos hσ]
      _ ≤ _ := Complex.abs_re_le_norm _
  have h2 : ‖(x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I)‖ ≤ x ^ σ / σ := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
    gcongr
  rw [norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)

/-- **Recentring the contour.** Integrating the `n`-th Dirichlet term against the Perron kernel
over the segment `re u = σ`, `|im u| ≤ T` gives exactly `Λ(n) n^{-s}` times the truncated Perron
integral at the point `x / n`:

`(1/2π) ∫_{-T}^{T} Λ(n) n^{-(s + u)} x^u / u dv = Λ(n) n^{-s} ⬝ perronTruncated (x/n) σ T`. -/
private lemma integral_perronDirichletTerm {x : ℝ} (hx : 0 < x) (s : ℂ) {σ T : ℝ} (n : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ v in (-T)..T,
        LSeries.term ↗Λ (s + ((σ : ℂ) + (v : ℂ) * I)) n
          * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I))
      = LSeries.term ↗Λ s n * perronTruncated (x / n) σ T := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have key : ∀ v : ℝ, LSeries.term ↗Λ (s + ((σ : ℂ) + (v : ℂ) * I)) n
        * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I))
        = LSeries.term ↗Λ s n
          * (((x / n : ℝ) : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I)) := by
      intro v
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, ofReal_div_cpow hx hnpos,
        Complex.cpow_add _ _ hn0, Complex.ofReal_natCast]
      ring
    simp only [key]
    rw [intervalIntegral.integral_const_mul, perronTruncated_eq_two_pi_inv_mul_integral]
    ring

/-- **The right edge of the Landau contour, term by term.** For `T ≥ 0` the recentred truncated
integral of `(-ζ'/ζ)(w) x^{w - s}/(w - s)` over `re w - re s = σ`, `|im (w - s)| ≤ T` is the sum
over `n` of `Λ(n) n^{-s}` times the truncated Perron integral at `x / n`. -/
private theorem integral_logDeriv_riemannZeta_perron_eq_tsum {x : ℝ} (hx : 0 < x) {s : ℂ} {σ T : ℝ}
    (hσ : 0 < σ) (hσs : 1 < σ + s.re) (hT : 0 ≤ T) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ v in (-T)..T,
        (-(deriv riemannZeta (s + ((σ : ℂ) + (v : ℂ) * I))
            / riemannZeta (s + ((σ : ℂ) + (v : ℂ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I))
      = ∑' n : ℕ, LSeries.term ↗Λ s n * perronTruncated (x / n) σ T := by
  have hTle : -T ≤ T := by linarith
  have hcre : 1 < (((σ + s.re : ℝ)) : ℂ).re := by simpa using hσs
  have hMsum : Summable fun n : ℕ => ‖LSeries.term ↗Λ ((σ + s.re : ℝ) : ℂ) n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hcre).norm
  have hseries : ∀ v : ℝ, (-(deriv riemannZeta (s + ((σ : ℂ) + (v : ℂ) * I))
      / riemannZeta (s + ((σ : ℂ) + (v : ℂ) * I))))
        * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I))
      = ∑' n : ℕ, LSeries.term ↗Λ (s + ((σ : ℂ) + (v : ℂ) * I)) n
          * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I)) := by
    intro v
    have hw : 1 < (s + ((σ : ℂ) + (v : ℂ) * I)).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im]
      linarith
    rw [tsum_mul_right, ← neg_div,
      ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
    rfl
  have hswap : (∫ v in (-T)..T, ∑' n : ℕ, LSeries.term ↗Λ (s + ((σ : ℂ) + (v : ℂ) * I)) n
        * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I)))
      = ∑' n : ℕ, ∫ v in (-T)..T, LSeries.term ↗Λ (s + ((σ : ℂ) + (v : ℂ) * I)) n
        * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I)) := by
    simp only [intervalIntegral.integral_of_le hTle]
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun n => (continuous_perronDirichletTerm hx hσ s n).integrableOn_Ioc) ?_).symm
    refine Summable.of_nonneg_of_le (fun n => MeasureTheory.integral_nonneg fun v => norm_nonneg _)
      (fun n => ?_) (hMsum.mul_right (2 * T * (x ^ σ / σ)))
    have hint : ∫ v in Set.Ioc (-T) T,
        ‖LSeries.term ↗Λ (s + ((σ : ℂ) + (v : ℂ) * I)) n
          * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I))‖
        ≤ ∫ v in Set.Ioc (-T) T, ‖LSeries.term ↗Λ ((σ + s.re : ℝ) : ℂ) n‖ * (x ^ σ / σ) := by
      refine MeasureTheory.setIntegral_mono_on
        ((continuous_perronDirichletTerm hx hσ s n).norm.integrableOn_Ioc)
        (MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc
        fun v _ => norm_perronDirichletTerm_le hx hσ s n v
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hTle, smul_eq_mul] at hint
    refine hint.trans ?_
    have h2T : T - -T = 2 * T := by ring
    rw [h2T] at hint ⊢
    nlinarith [norm_nonneg (LSeries.term ↗Λ ((σ + s.re : ℝ) : ℂ) n),
      Real.rpow_nonneg hx.le σ, hσ]
  simp only [hseries]
  rw [hswap, ← tsum_mul_left]
  exact tsum_congr fun n => integral_perronDirichletTerm hx s n

/-- **The truncated Perron error at the `n`-th Dirichlet term.** With `d` a positive lower bound
for `|log (x / n)|` over the support of `Λ`, the error committed by truncating the `n`-th term at
height `T` is at most `x^σ / (π d T)` times the `n`-th term of the Dirichlet series at the abscissa
`σ + re s`. -/
private lemma norm_term_mul_perronTruncated_sub_le {x : ℝ} (hx : 0 < x) {s : ℂ} {σ d T : ℝ}
    (hσ : 0 < σ) (hd0 : 0 < d) (hT : 0 < T) (hd : ∀ n : ℕ, Λ n ≠ 0 → d ≤ |Real.log (x / n)|)
    (n : ℕ) :
    ‖LSeries.term ↗Λ s n * (perronTruncated (x / n) σ T - (if 1 < x / n then 1 else 0))‖
      ≤ x ^ σ / (Real.pi * d * T) * ‖LSeries.term ↗Λ ((σ + s.re : ℝ) : ℂ) n‖ := by
  have hpi := Real.pi_pos
  have hxσ : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, zero_mul, norm_zero]
    positivity
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnσ : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
    have hns : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hnpos s.re
    have hterm : ‖LSeries.term ↗Λ s n‖ = Λ n / (n : ℝ) ^ s.re := by
      rw [LSeries.norm_term_eq, ite_eq_right hn, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hR : ‖LSeries.term ↗Λ ((σ + s.re : ℝ) : ℂ) n‖ = Λ n / (n : ℝ) ^ (σ + s.re) := by
      rw [LSeries.norm_term_eq, ite_eq_right hn, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.ofReal_re]
    rcases eq_or_ne (Λ n) 0 with hΛ | hΛ
    · rw [norm_mul, hterm, hR, hΛ]
      simp
    · have hy : 0 < x / n := div_pos hx hnpos
      have hdle := hd n hΛ
      have hy1 : x / n ≠ 1 := by
        intro h
        rw [h, Real.log_one, abs_zero] at hdle
        linarith
      have herr := norm_perronTruncated_sub_indicator_le hy hy1 hσ hT
      have hfrac : (x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)
          ≤ (x / n) ^ σ / (Real.pi * T * d) := by
        have h1 : (0 : ℝ) < Real.pi * T * d := by positivity
        gcongr
      rw [norm_mul, hterm, hR]
      calc Λ n / (n : ℝ) ^ s.re
            * ‖perronTruncated (x / n) σ T - (if 1 < x / n then 1 else 0)‖
          ≤ Λ n / (n : ℝ) ^ s.re * ((x / n) ^ σ / (Real.pi * T * d)) := by
            have hnn : (0 : ℝ) ≤ Λ n / (n : ℝ) ^ s.re := by positivity
            exact mul_le_mul_of_nonneg_left (herr.trans hfrac) hnn
        _ = x ^ σ / (Real.pi * d * T) * (Λ n / (n : ℝ) ^ (σ + s.re)) := by
            rw [Real.div_rpow hx.le hnpos.le, Real.rpow_add hnpos]
            field_simp

/-- **The right edge of the Landau contour: the prime sum.** For `x > 0` that is not the cast of a
prime power, and `σ > 0` with `σ + re s > 1`, the recentred truncated Perron integral of
`(-ζ'/ζ)(w) x^{w - s} / (w - s)` over the segment `re (w - s) = σ`, `|im (w - s)| ≤ T` converges,
as `T → ∞`, to the finite prime sum

`∑_{n ≤ x} Λ(n) n^{-s}`. -/
theorem tendsto_integral_logDeriv_riemannZeta_perron {x : ℝ} (hx : 0 < x)
    (hxpp : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ≠ x) {s : ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hσs : 1 < σ + s.re) :
    Tendsto (fun T : ℝ => (1 / (2 * (Real.pi : ℂ))) * ∫ v in (-T)..T,
        (-(deriv riemannZeta (s + ((σ : ℂ) + (v : ℂ) * I))
            / riemannZeta (s + ((σ : ℂ) + (v : ℂ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I)))
      atTop (𝓝 (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) / (n : ℂ) ^ s)) := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_pos_le_abs_log_div_natCast hx hxpp
  have hpi := Real.pi_pos
  have hcre : 1 < (((σ + s.re : ℝ)) : ℂ).re := by simpa using hσs
  have hMsum : Summable fun n : ℕ => ‖LSeries.term ↗Λ ((σ + s.re : ℝ) : ℂ) n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hcre).norm
  set M : ℝ := ∑' n : ℕ, ‖LSeries.term ↗Λ ((σ + s.re : ℝ) : ℂ) n‖ with hM
  have hind_zero : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊,
      LSeries.term ↗Λ s n * (if 1 < x / n then (1 : ℂ) else 0) = 0 := by
    intro n hn
    rw [Finset.mem_Icc, not_and_or] at hn
    rcases hn with h1 | h2
    · have hn0 : n = 0 := by omega
      subst hn0
      simp
    · have hlt : ⌊x⌋₊ < n := by omega
      have hxn : x < n := (Nat.floor_lt hx.le).1 hlt
      have hnpos : (0 : ℝ) < n := lt_trans hx hxn
      rw [ite_eq_right (by rw [not_lt, div_le_one hnpos]; linarith), mul_zero]
  have hind_summable : Summable fun n : ℕ =>
      LSeries.term ↗Λ s n * (if 1 < x / n then (1 : ℂ) else 0) :=
    summable_of_ne_finset_zero hind_zero
  have hAeq : ∑' n : ℕ, LSeries.term ↗Λ s n * (if 1 < x / n then (1 : ℂ) else 0)
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) / (n : ℂ) ^ s := by
    rw [tsum_eq_sum hind_zero]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    have hn0 : n ≠ 0 := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnx : (n : ℝ) ≤ x := le_trans (Nat.cast_le.2 hn2) (Nat.floor_le hx.le)
    rcases lt_or_eq_of_le hnx with hlt | heq
    · rw [ite_eq_left (by rw [one_lt_div hnpos]; exact hlt), mul_one, LSeries.term_of_ne_zero hn0]
    · have hΛ : Λ n = 0 := by
        by_contra h
        exact hxpp n (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 h) heq
      rw [LSeries.term_of_ne_zero hn0, hΛ]
      simp
  have hbound : ∀ T : ℝ, 0 < T →
      ‖(1 / (2 * (Real.pi : ℂ))) * (∫ v in (-T)..T,
          (-(deriv riemannZeta (s + ((σ : ℂ) + (v : ℂ) * I))
              / riemannZeta (s + ((σ : ℂ) + (v : ℂ) * I))))
            * ((x : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) / ((σ : ℂ) + (v : ℂ) * I)))
        - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) / (n : ℂ) ^ s‖
      ≤ x ^ σ * M / (Real.pi * d * T) := by
    intro T hT
    have hnormsum : Summable fun n : ℕ => ‖LSeries.term ↗Λ s n
        * (perronTruncated (x / n) σ T - (if 1 < x / n then (1 : ℂ) else 0))‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _)
        (fun n => norm_term_mul_perronTruncated_sub_le hx hσ hd0 hT hd n) (hMsum.mul_left _)
    have hPsum : Summable fun n : ℕ => LSeries.term ↗Λ s n * perronTruncated (x / n) σ T := by
      refine ((Summable.of_norm hnormsum).add hind_summable).congr fun n => ?_
      ring
    rw [integral_logDeriv_riemannZeta_perron_eq_tsum hx hσ hσs hT.le, ← hAeq,
      ← hPsum.tsum_sub hind_summable, tsum_congr (fun n : ℕ => by ring :
        ∀ n : ℕ, LSeries.term ↗Λ s n * perronTruncated (x / n) σ T
          - LSeries.term ↗Λ s n * (if 1 < x / n then (1 : ℂ) else 0)
          = LSeries.term ↗Λ s n
            * (perronTruncated (x / n) σ T - (if 1 < x / n then (1 : ℂ) else 0)))]
    refine (norm_tsum_le_tsum_norm hnormsum).trans ?_
    calc ∑' n : ℕ, ‖LSeries.term ↗Λ s n
            * (perronTruncated (x / n) σ T - (if 1 < x / n then (1 : ℂ) else 0))‖
        ≤ ∑' n : ℕ, x ^ σ / (Real.pi * d * T)
            * ‖LSeries.term ↗Λ ((σ + s.re : ℝ) : ℂ) n‖ :=
          hnormsum.tsum_le_tsum (fun n => norm_term_mul_perronTruncated_sub_le hx hσ hd0 hT hd n)
            (hMsum.mul_left _)
      _ = x ^ σ / (Real.pi * d * T) * M := tsum_mul_left
      _ = x ^ σ * M / (Real.pi * d * T) := by ring
  have hg : Tendsto (fun T : ℝ => x ^ σ * M / (Real.pi * d * T)) atTop (𝓝 0) := by
    have h : Tendsto (fun T : ℝ => (x ^ σ * M / (Real.pi * d)) * T⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (x ^ σ * M / (Real.pi * d))
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    field_simp
  refine tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm' ?_ hg)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact hbound T hT

end ZetaZeros
