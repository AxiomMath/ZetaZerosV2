/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import Zeta23.MV.Final
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Montgomery--Vaughan mean-value theorem

This file turns the vendored weighted Hilbert inequality into the finite exponential-polynomial
mean-value estimate used in `blueprint/unconditional.tex`, `lem_mv_meanvalue_finite`.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex MeasureTheory Filter
open scoped BigOperators ComplexConjugate Interval Topology

/-- A finite exponential polynomial with real frequencies. -/
noncomputable def finiteExponentialPolynomial {ι : Type*} [Fintype ι]
    (freq : ι → ℝ) (a : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ r, a r * Complex.exp (-Complex.I * (((freq r) * t : ℝ) : ℂ))

/-- Multiplication of the coefficients by the endpoint phase occurring at time `T`. -/
noncomputable def endpointTwist {ι : Type*} (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) (r : ι) : ℂ :=
  a r * Complex.exp (-Complex.I * ((((freq r) * T : ℝ)) : ℂ))

/-- The endpoint phase turns a frequency difference into the corresponding pair of twists. -/
theorem endpointTwist_mul_conj {ι : Type*} (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ)
    (r s : ι) :
    endpointTwist freq a T r * conj (endpointTwist freq a T s) =
      a r * conj (a s) *
        Complex.exp (-Complex.I * ((((freq r - freq s) * T : ℝ)) : ℂ)) := by
  simp only [endpointTwist, map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I,
    Complex.conj_ofReal]
  rw [show a r * Complex.exp (-Complex.I * (freq r * T : ℝ)) *
      (conj (a s) * Complex.exp (-(-Complex.I) * (freq s * T : ℝ))) =
      a r * conj (a s) *
        (Complex.exp (-Complex.I * (freq r * T : ℝ)) *
          Complex.exp (-(-Complex.I) * (freq s * T : ℝ))) by ring_nf,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- Expanding the squared modulus of a finite exponential polynomial as a double sum. -/
theorem finiteExponentialPolynomial_mul_conj {ι : Type*} [Fintype ι]
    (freq : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    finiteExponentialPolynomial freq a t *
        conj (finiteExponentialPolynomial freq a t) =
      ∑ r, ∑ s, a r * conj (a s) *
        Complex.exp (-Complex.I * ((((freq r) - freq s) * t : ℝ) : ℂ)) := by
  simp only [finiteExponentialPolynomial, map_sum, map_mul, ← Complex.exp_conj,
    map_neg, Complex.conj_I, Complex.conj_ofReal, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [show a r * Complex.exp (-Complex.I * (freq r * t : ℝ)) *
      (conj (a s) * Complex.exp (-(-Complex.I) * (freq s * t : ℝ))) =
      a r * conj (a s) *
        (Complex.exp (-Complex.I * (freq r * t : ℝ)) *
          Complex.exp (-(-Complex.I) * (freq s * t : ℝ))) by ring_nf,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- The exponential integral which occurs after expanding the square of a finite Dirichlet
polynomial. -/
theorem intervalIntegral_exp_neg_I_mul_sub (u v T : ℝ) (huv : u ≠ v) :
    (∫ t : ℝ in 0..T,
        Complex.exp (-Complex.I * (((u - v) * t : ℝ) : ℂ))) =
      Complex.I / ((u - v : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * (((u - v) * T : ℝ) : ℂ)) - 1) := by
  have hsub : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hc : -Complex.I * ((u - v : ℝ) : ℂ) ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (ofReal_ne_zero.mpr hsub)
  rw [show (fun t : ℝ => Complex.exp (-Complex.I * (((u - v) * t : ℝ) : ℂ))) =
      fun t : ℝ => Complex.exp ((-Complex.I * ((u - v : ℝ) : ℂ)) * (t : ℂ)) by
        funext t
        congr 1
        push_cast
        ring_nf]
  rw [integral_exp_mul_complex hc]
  simp only [ofReal_zero, mul_zero, exp_zero]
  have hexp :
      Complex.exp (-Complex.I * (((u - v) * T : ℝ) : ℂ)) =
        Complex.exp ((-Complex.I * ((u - v : ℝ) : ℂ)) * (T : ℂ)) := by
    congr 1
    push_cast
    ring_nf
  rw [hexp]
  field_simp
  rw [Complex.I_sq]
  ring_nf

/-- Term-by-term integration of the finite expansion. -/
theorem intervalIntegral_finiteExponentialPolynomial_mul_conj
    {ι : Type*} [Fintype ι] (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) :
    (∫ t : ℝ in 0..T,
        finiteExponentialPolynomial freq a t *
          conj (finiteExponentialPolynomial freq a t)) =
      ∑ r, ∑ s, a r * conj (a s) *
        (∫ t : ℝ in 0..T,
          Complex.exp (-Complex.I * ((((freq r) - freq s) * t : ℝ) : ℂ))) := by
  simp_rw [finiteExponentialPolynomial_mul_conj]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro s hs
      exact intervalIntegral.integral_const_mul _ _
    · intro s hs
      exact Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by continuity) 0 T
  · intro r hr
    apply Continuous.intervalIntegrable
    fun_prop

/-- Each integrated pair is either the diagonal contribution or the difference of the two
endpoint Hilbert-form summands. -/
theorem coefficient_mul_intervalIntegral_exp_neg_I_mul_sub
    {ι : Type} [DecidableEq ι] (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ)
    (hfreq : Function.Injective freq) (r s : ι) :
    a r * conj (a s) *
        (∫ t : ℝ in 0..T,
          Complex.exp (-Complex.I * ((((freq r - freq s) * t : ℝ)) : ℂ))) =
      if r = s then (T : ℂ) * (a r * conj (a s))
      else Complex.I *
        (endpointTwist freq a T r * conj (endpointTwist freq a T s) *
            Zeta23.MV.coef freq r s -
          a r * conj (a s) * Zeta23.MV.coef freq r s) := by
  by_cases hrs : r = s
  · subst s
    simp [intervalIntegral.integral_const]
    ring_nf
  · rw [ite_eq_right hrs, intervalIntegral_exp_neg_I_mul_sub _ _ T (hfreq.ne hrs)]
    rw [endpointTwist_mul_conj]
    simp only [Zeta23.MV.coef, ite_eq_right hrs, div_eq_mul_inv]
    ring_nf

/-- The integrated square is its diagonal term plus a difference of two Hilbert forms. -/
theorem intervalIntegral_finiteExponentialPolynomial_mul_conj_eq
    {ι : Type} [Fintype ι] [DecidableEq ι] (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ)
    (hfreq : Function.Injective freq) :
    (∫ t : ℝ in 0..T,
        finiteExponentialPolynomial freq a t *
          conj (finiteExponentialPolynomial freq a t)) =
      (T : ℂ) * ∑ r, a r * conj (a r) + Complex.I *
        (Zeta23.MV.B freq (endpointTwist freq a T) (endpointTwist freq a T) -
          Zeta23.MV.B freq a a) := by
  rw [intervalIntegral_finiteExponentialPolynomial_mul_conj]
  simp_rw [coefficient_mul_intervalIntegral_exp_neg_I_mul_sub freq a T hfreq]
  unfold Zeta23.MV.B Zeta23.MV.coef
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show (T : ℂ) * (a r * conj (a r)) =
      ∑ s, if r = s then (T : ℂ) * (a r * conj (a s)) else 0 by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hrs : r = s
  · subst s
    simp
  · simp [hrs]

/-- Endpoint twisting preserves every coefficient norm. -/
theorem norm_endpointTwist {ι : Type*} (freq : ι → ℝ) (a : ι → ℂ) (T : ℝ) (r : ι) :
    ‖endpointTwist freq a T r‖ = ‖a r‖ := by
  simp [endpointTwist, Complex.norm_exp]

/-- Endpoint twisting therefore preserves the weighted square norm used by the Hilbert
inequality. -/
theorem mvN2_endpointTwist {ι : Type} [Fintype ι] (freq δ : ι → ℝ) (a : ι → ℂ)
    (T : ℝ) :
    Zeta23.MV.N2 δ (endpointTwist freq a T) = Zeta23.MV.N2 δ a := by
  unfold Zeta23.MV.N2
  apply Finset.sum_congr rfl
  intro r hr
  rw [norm_endpointTwist]

/-- The diagonal specialization of the vendored bilinear Hilbert inequality. -/
theorem norm_mvB_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : ℝ} (hMV : Zeta23.MVHilbert C) (freq δ : ι → ℝ) (a : ι → ℂ)
    (hfreq : Function.Injective freq) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) :
    ‖Zeta23.MV.B freq a a‖ ≤ C * Zeta23.MV.N2 δ a := by
  have h := hMV ι freq δ a a hfreq hδ hsep
  rw [Zeta23.MV.sum_eq_B] at h
  change ‖Zeta23.MV.B freq a a‖ ≤
    C * Real.sqrt (Zeta23.MV.N2 δ a) * Real.sqrt (Zeta23.MV.N2 δ a) at h
  calc
    ‖Zeta23.MV.B freq a a‖ ≤
        C * Real.sqrt (Zeta23.MV.N2 δ a) * Real.sqrt (Zeta23.MV.N2 δ a) := h
    _ = C * Zeta23.MV.N2 δ a := by
      rw [mul_assoc, Real.mul_self_sqrt (Zeta23.MV.N2_nonneg hδ a)]

/-- Finite Montgomery--Vaughan mean value estimate for arbitrary admissibly spaced real
frequencies. -/
theorem finiteExponentialPolynomial_meanValue_bound
    {ι : Type} [Fintype ι] {C : ℝ} (hMV : Zeta23.MVHilbert C)
    (freq δ : ι → ℝ) (a : ι → ℂ) (T : ℝ) (hfreq : Function.Injective freq)
    (hδ : ∀ r, 0 < δ r) (hsep : ∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) :
    ‖(∫ t : ℝ in 0..T,
        finiteExponentialPolynomial freq a t *
          conj (finiteExponentialPolynomial freq a t)) -
        (T : ℂ) * ∑ r, a r * conj (a r)‖ ≤
      2 * C * Zeta23.MV.N2 δ a := by
  classical
  rw [intervalIntegral_finiteExponentialPolynomial_mul_conj_eq freq a T hfreq]
  have htwist := norm_mvB_le hMV freq δ (endpointTwist freq a T) hfreq hδ hsep
  have horiginal := norm_mvB_le hMV freq δ a hfreq hδ hsep
  rw [mvN2_endpointTwist] at htwist
  calc
    ‖(T : ℂ) * ∑ r, a r * conj (a r) +
          Complex.I *
            (Zeta23.MV.B freq (endpointTwist freq a T) (endpointTwist freq a T) -
              Zeta23.MV.B freq a a) -
        (T : ℂ) * ∑ r, a r * conj (a r)‖ =
        ‖Zeta23.MV.B freq (endpointTwist freq a T) (endpointTwist freq a T) -
          Zeta23.MV.B freq a a‖ := by
      rw [show (T : ℂ) * ∑ r, a r * conj (a r) +
          Complex.I *
            (Zeta23.MV.B freq (endpointTwist freq a T) (endpointTwist freq a T) -
              Zeta23.MV.B freq a a) -
          (T : ℂ) * ∑ r, a r * conj (a r) =
          Complex.I *
            (Zeta23.MV.B freq (endpointTwist freq a T) (endpointTwist freq a T) -
              Zeta23.MV.B freq a a) by ring]
      simp
    _ ≤ ‖Zeta23.MV.B freq (endpointTwist freq a T) (endpointTwist freq a T)‖ +
        ‖Zeta23.MV.B freq a a‖ := norm_sub_le _ _
    _ ≤ C * Zeta23.MV.N2 δ a + C * Zeta23.MV.N2 δ a :=
      add_le_add htwist horiginal
    _ = 2 * C * Zeta23.MV.N2 δ a := by ring

/-- The elementary logarithmic lower bound used to choose Dirichlet frequencies' admissible
gaps. -/
theorem inv_two_mul_le_log_one_add_inv (x : ℝ) (hx : 1 ≤ x) :
    1 / (2 * x) ≤ Real.log (1 + 1 / x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h := Real.le_log_one_add_of_nonneg (show 0 ≤ 1 / x by positivity)
  refine le_trans ?_ h
  rw [div_le_div_iff₀ (by positivity : 0 < 2 * x)
    (by positivity : 0 < 1 / x + 2)]
  field_simp
  nlinarith

theorem log_one_add_inv_eq_sub (x : ℝ) (hx : 0 < x) :
    Real.log (1 + 1 / x) = Real.log (x + 1) - Real.log x := by
  rw [← Real.log_div (by positivity : x + 1 ≠ 0) hx.ne']
  congr 1
  field_simp

/-- Frequencies `log (n + 1)` for a zero-based finite family. -/
noncomputable def dirichletFrequency (n : ℕ) : ℝ := Real.log (n + 1)

/-- A convenient admissible gap for `log (n + 1)`. -/
noncomputable def dirichletGap (n : ℕ) : ℝ := 1 / (2 * (n + 1))

theorem dirichletFrequency_injective : Function.Injective dirichletFrequency := by
  intro n m h
  unfold dirichletFrequency at h
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hm : (0 : ℝ) < m + 1 := by positivity
  have : (n + 1 : ℝ) = (m + 1 : ℝ) :=
    Real.strictMonoOn_log.injOn (Set.mem_Ioi.mpr hn) (Set.mem_Ioi.mpr hm) h
  have hnm : n + 1 = m + 1 := by exact_mod_cast this
  omega

/-- The gaps `1 / (2(n+1))` are admissible for the logarithmic frequencies. -/
theorem dirichletGap_le_abs_frequency_sub (n m : ℕ) (hnm : n ≠ m) :
    dirichletGap n ≤ |dirichletFrequency n - dirichletFrequency m| := by
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hcast : (n + 1 : ℝ) + 1 ≤ (m + 1 : ℝ) := by
      exact_mod_cast (show n + 1 + 1 ≤ m + 1 by omega)
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    have hmpos : (0 : ℝ) < m + 1 := by positivity
    have hlognm : Real.log (n + 1 : ℝ) ≤ Real.log (m + 1 : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hnpos) (Set.mem_Ioi.mpr hmpos)
        (by norm_cast; omega)
    rw [dirichletFrequency, dirichletFrequency, abs_of_nonpos (sub_nonpos.mpr hlognm)]
    calc
      dirichletGap n = 1 / (2 * (n + 1 : ℝ)) := by rfl
      _ ≤ Real.log (1 + 1 / (n + 1 : ℝ)) :=
        inv_two_mul_le_log_one_add_inv _ (by norm_num)
      _ = Real.log ((n + 1 : ℝ) + 1) - Real.log (n + 1 : ℝ) :=
        log_one_add_inv_eq_sub _ hnpos
      _ ≤ Real.log (m + 1 : ℝ) - Real.log (n + 1 : ℝ) := by
        exact sub_le_sub_right
          (Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (by positivity))
            (Set.mem_Ioi.mpr hmpos) hcast) _
      _ = -(Real.log (n + 1 : ℝ) - Real.log (m + 1 : ℝ)) := by ring
  · have hn : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by positivity
    have hn1pos : (0 : ℝ) < n + 1 := by positivity
    have hm1pos : (0 : ℝ) < m + 1 := by positivity
    have hcast : (m + 1 : ℝ) ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
    have hlogmn : Real.log (m + 1 : ℝ) ≤ Real.log (n + 1 : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hm1pos) (Set.mem_Ioi.mpr hn1pos)
        (by norm_cast; omega)
    rw [dirichletFrequency, dirichletFrequency, abs_of_nonneg (sub_nonneg.mpr hlogmn)]
    calc
      dirichletGap n = 1 / (2 * (n + 1 : ℝ)) := by rfl
      _ ≤ 1 / (2 * (n : ℝ)) := by
        gcongr
        norm_num
      _ ≤ Real.log (1 + 1 / (n : ℝ)) :=
        inv_two_mul_le_log_one_add_inv _ (by exact_mod_cast hn)
      _ = Real.log ((n : ℝ) + 1) - Real.log n := log_one_add_inv_eq_sub _ hnpos
      _ ≤ Real.log (n + 1 : ℝ) - Real.log (m + 1 : ℝ) := by
        exact sub_le_sub_left
          (Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hm1pos)
            (Set.mem_Ioi.mpr hnpos) hcast) _

/-- The infinite Dirichlet series with frequencies `log (n + 1)`.  Absolute summability of
the coefficients will be imposed by the convergence theorems below. -/
noncomputable def dirichletSeries (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' n, a n * Complex.exp
    (-Complex.I * (((dirichletFrequency n) * t : ℝ) : ℂ))

/-- The first `N` terms of `dirichletSeries`. -/
noncomputable def partialDirichletSeries (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N,
    a n * Complex.exp (-Complex.I * (((dirichletFrequency n) * t : ℝ) : ℂ))

/-- Every phase occurring in the Dirichlet series has norm one. -/
theorem norm_dirichletSeries_term (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖a n * Complex.exp
      (-Complex.I * (((dirichletFrequency n) * t : ℝ) : ℂ))‖ = ‖a n‖ := by
  simp [Complex.norm_exp]

/-- Partial Dirichlet series converge pointwise when the coefficients are absolutely
summable. -/
theorem partialDirichletSeries_tendsto (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (t : ℝ) :
    Tendsto (fun N => partialDirichletSeries a N t) atTop
      (nhds (dirichletSeries a t)) := by
  apply Summable.tendsto_sum_tsum_nat
  apply Summable.of_norm
  simpa only [norm_dirichletSeries_term] using ha

/-- The absolute coefficient sum uniformly dominates every partial Dirichlet series. -/
theorem norm_partialDirichletSeries_le_tsum (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (N : ℕ) (t : ℝ) :
    ‖partialDirichletSeries a N t‖ ≤ ∑' n, ‖a n‖ := by
  unfold partialDirichletSeries
  calc
    ‖∑ n ∈ Finset.range N,
        a n * Complex.exp (-Complex.I * (((dirichletFrequency n) * t : ℝ) : ℂ))‖ ≤
        ∑ n ∈ Finset.range N,
          ‖a n * Complex.exp
            (-Complex.I * (((dirichletFrequency n) * t : ℝ) : ℂ))‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, ‖a n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      exact norm_dirichletSeries_term a n t
    _ ≤ ∑' n, ‖a n‖ :=
      ha.sum_le_tsum _ (fun n _ => norm_nonneg _)

/-! ## Integrated endpoint-loss bounds -/

/-- The exact integral of `T ^ a` over the unit interval. -/
theorem intervalIntegral_const_rpow_eq (T : ℝ) (hT : 0 < T)
    (hlog : Real.log T ≠ 0) :
    (∫ a : ℝ in 0..1, T ^ a) = (T - 1) / Real.log T := by
  rw [show (fun a : ℝ => T ^ a) =
      fun a : ℝ => Real.exp (Real.log T * a) by
        funext a
        exact Real.rpow_def_of_pos hT a]
  rw [show (∫ a : ℝ in 0..1, Real.exp (Real.log T * a)) =
      (Real.exp (Real.log T) - 1) / Real.log T by
        exact (by
          have h := intervalIntegral.integral_comp_mul_deriv
            (a := (0 : ℝ)) (b := 1)
            (f := fun a : ℝ => Real.log T * a)
            (f' := fun _ : ℝ => Real.log T) (g := Real.exp)
            (by intro a ha
                simpa using (hasDerivAt_id a).const_mul (Real.log T))
            (by fun_prop) Real.continuous_exp
          simp only [Function.comp_apply, mul_zero, mul_one] at h
          rw [intervalIntegral.integral_mul_const, integral_exp] at h
          simpa using (eq_div_iff hlog).2 h)]
  rw [Real.exp_log hT]

/-- A Lipschitz-at-zero bound controls the absolute value on the unit interval. -/
theorem abs_le_abs_zero_add_of_lipschitzAtZero
    (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hLip : ∀ x : ℝ, |x| ≤ 1 → |f x - f 0| ≤ C * |x|)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |f a| ≤ |f 0| + C := by
  have haAbs : |a| ≤ 1 := by simpa [abs_of_nonneg ha0] using ha1
  have hCa : C * a ≤ C := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr ha1)]
  calc
    |f a| = |(f a - f 0) + f 0| := by ring_nf
    _ ≤ |f a - f 0| + |f 0| := abs_add_le _ _
    _ ≤ C * |a| + |f 0| := add_le_add (hLip a haAbs) le_rfl
    _ = C * a + |f 0| := by rw [abs_of_nonneg ha0]
    _ ≤ C + |f 0| := add_le_add hCa le_rfl
    _ = |f 0| + C := by ring

end ZetaZeros.Unconditional.PairCorrelationProof
