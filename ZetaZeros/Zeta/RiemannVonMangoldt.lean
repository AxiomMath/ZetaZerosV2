/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Zeta23.GammaFacts.Complete
import Zeta23.RvM.Statement

/-!
# The cumulative Riemann--von Mangoldt asymptotic

This file converts the Riemann--von Mangoldt estimate on dyadic windows supplied by
`Zeta23.RvM.riemannVonMangoldt` into the usual cumulative zero-counting asymptotic.
-/

noncomputable section

open Set

namespace ZetaZeros.Unconditional.RvM

/-- The antiderivative-style main term whose dyadic increment is `T / (2 * π) * ell1 T`. -/
private def mainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * (Real.log T - Real.log (2 * Real.pi) - 1)

private lemma mainTerm_double {T : ℝ} (hT : 0 < T) :
    mainTerm (2 * T) - mainTerm T = T / (2 * Real.pi) * Zeta23.ell1 T := by
  rw [mainTerm, mainTerm, Zeta23.ell1, Zeta23.l,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hT),
    Real.log_div (ne_of_gt hT) (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  ring

/-- The error after subtracting the cumulative main term. -/
private def errorTerm (T : ℝ) : ℝ := (Zeta23.Ncount 0 T : ℝ) - mainTerm T

private lemma errorTerm_double {T : ℝ} (hT : 0 < T) :
    errorTerm (2 * T) = errorTerm T +
      ((Zeta23.Ncount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T) := by
  have hcount := Zeta23.Ncount_add (a := 0) (b := T) (c := 2 * T) hT.le (by linarith)
  rw [errorTerm, errorTerm, show (Zeta23.Ncount 0 (2 * T) : ℝ) =
    (Zeta23.Ncount 0 T : ℝ) + Zeta23.Ncount T (2 * T) by exact_mod_cast hcount,
    show mainTerm (2 * T) = mainTerm T + T / (2 * Real.pi) * Zeta23.ell1 T by
      linarith [mainTerm_double hT]]
  ring

private lemma exists_dyadic_scale {R T : ℝ} (hR : 0 < R) (hRT : R ≤ T) :
    ∃ n : ℕ, R ≤ T / (2 : ℝ) ^ n ∧ T / (2 : ℝ) ^ n < 2 * R := by
  let p : ℕ → Prop := fun n => T / R < (2 : ℝ) ^ n
  have hp : ∃ n, p n := pow_unbounded_of_one_lt (T / R) (by norm_num)
  have hratio : 1 ≤ T / R := by
    exact (le_div_iff₀ hR).2 (by simpa using hRT)
  have hfind_ne : Nat.find hp ≠ 0 := by
    intro hzero
    have hspec := Nat.find_spec hp
    rw [hzero] at hspec
    simp only [p, pow_zero] at hspec
    exact (not_lt_of_ge hratio) hspec
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hfind_ne
  have hspec := Nat.find_spec hp
  rw [hn] at hspec
  simp only [p] at hspec
  have hminimal := Nat.find_min hp (show n < Nat.find hp by rw [hn]; exact Nat.lt_succ_self n)
  simp only [p, not_lt] at hminimal
  refine ⟨n, ?_, ?_⟩
  · have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
    apply (le_div_iff₀ hpow_pos).2
    have h := (le_div_iff₀ hR).1 hminimal
    nlinarith
  · have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
    apply (div_lt_iff₀ hpow_pos).2
    rw [pow_succ] at hspec
    have h := (div_lt_iff₀ hR).1 hspec
    nlinarith

private lemma errorTerm_dyadic_bound {C R η B S : ℝ}
    (hR : 1 ≤ R) (hη : 0 ≤ η) (hCR : C ≤ η * R)
    (hS : S ∈ Icc R (2 * R)) (hbase : |errorTerm S| ≤ B)
    (hwindow : ∀ x ≥ R,
      |(Zeta23.Ncount x (2 * x) : ℝ) - x / (2 * Real.pi) * Zeta23.ell1 x| ≤
        C * Real.log x) :
    ∀ n : ℕ, |errorTerm ((2 : ℝ) ^ n * S)| ≤
      B + η * ((2 : ℝ) ^ n * S) * Real.log ((2 : ℝ) ^ n * S) := by
  intro n
  induction n with
  | zero =>
      simp only [pow_zero, one_mul]
      have hS_one : 1 ≤ S := hR.trans hS.1
      have hlog : 0 ≤ Real.log S := Real.log_nonneg hS_one
      have hS_nonneg : 0 ≤ S := (by norm_num : (0 : ℝ) ≤ 1).trans hS_one
      exact hbase.trans (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hη hS_nonneg) hlog))
  | succ n ih =>
      let x := (2 : ℝ) ^ n * S
      have hpow_one : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hxR : R ≤ x := by
        dsimp [x]
        have hS_nonneg : 0 ≤ S :=
          (by linarith [hR] : (0 : ℝ) ≤ R).trans hS.1
        calc
          R ≤ S := hS.1
          _ = 1 * S := by ring
          _ ≤ 2 ^ n * S := mul_le_mul_of_nonneg_right hpow_one hS_nonneg
      have hxpos : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hR) hxR
      have hlog : 0 ≤ Real.log x := Real.log_nonneg ((hR.trans hxR))
      have hCx : C ≤ η * x := hCR.trans (mul_le_mul_of_nonneg_left hxR hη)
      have herr :
          |(Zeta23.Ncount x (2 * x) : ℝ) - x / (2 * Real.pi) * Zeta23.ell1 x| ≤
            η * x * Real.log x :=
        (hwindow x hxR).trans (mul_le_mul_of_nonneg_right hCx hlog)
      have hlog_double : Real.log x ≤ Real.log (2 * x) :=
        Real.log_le_log hxpos (by linarith)
      have hmain :
          |errorTerm (2 * x)| ≤ B + η * (2 * x) * Real.log (2 * x) := by
        rw [errorTerm_double hxpos]
        calc
          |errorTerm x +
              ((Zeta23.Ncount x (2 * x) : ℝ) -
                x / (2 * Real.pi) * Zeta23.ell1 x)|
              ≤ |errorTerm x| +
                |(Zeta23.Ncount x (2 * x) : ℝ) -
                  x / (2 * Real.pi) * Zeta23.ell1 x| := abs_add_le _ _
          _ ≤ (B + η * x * Real.log x) + η * x * Real.log x := add_le_add ih herr
          _ ≤ B + η * (2 * x) * Real.log (2 * x) := by
            have hηx : 0 ≤ η * x := mul_nonneg hη hxpos.le
            nlinarith [mul_le_mul_of_nonneg_left hlog_double hηx]
      simpa only [x, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmain

/-- The cumulative Riemann--von Mangoldt asymptotic, in the epsilon form used by the
unconditional challenge. -/
theorem ncount_asymptotic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      |(Zeta23.Ncount 0 T : ℝ) /
          (T / (2 * Real.pi) * Real.log T) - 1| < ε := by
  intro ε hε
  obtain ⟨C, Tbase, hwindow⟩ :=
    (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts).main
  let η : ℝ := ε / (12 * Real.pi)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  let R : ℝ := max 1 (max Tbase (|C| / η))
  have hR : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hbaseR : Tbase ≤ R :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hquotR : |C| / η ≤ R :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hCR : C ≤ η * R := by
    calc
      C ≤ |C| := le_abs_self C
      _ = η * (|C| / η) := by field_simp
      _ ≤ η * R := mul_le_mul_of_nonneg_left hquotR hη.le
  have hmain_cont : ContinuousOn mainTerm (Icc R (2 * R)) := by
    intro x hx
    have hxpos : 0 < x := hRpos.trans_le hx.1
    unfold mainTerm
    exact ((continuousAt_id.div_const _).mul
      (((Real.continuousAt_log hxpos.ne').sub continuousAt_const).sub
        continuousAt_const)).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hmain_cont
  let B : ℝ := (Zeta23.Ncount 0 (2 * R) : ℝ) + M
  have hbase_bound : ∀ S ∈ Icc R (2 * R), |errorTerm S| ≤ B := by
    intro S hS
    have hmono : Zeta23.Ncount 0 S ≤ Zeta23.Ncount 0 (2 * R) :=
      Zeta23.Ncount_mono le_rfl hS.2
    have hmono_real : (Zeta23.Ncount 0 S : ℝ) ≤ Zeta23.Ncount 0 (2 * R) := by
      exact_mod_cast hmono
    have hM' : |mainTerm S| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM S hS
    calc
      |errorTerm S| = |(Zeta23.Ncount 0 S : ℝ) - mainTerm S| := rfl
      _ ≤ |(Zeta23.Ncount 0 S : ℝ)| + |mainTerm S| := abs_sub _ _
      _ = (Zeta23.Ncount 0 S : ℝ) + |mainTerm S| := by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ (Zeta23.Ncount 0 (2 * R) : ℝ) + M := add_le_add hmono_real hM'
      _ = B := rfl
  let c₀ : ℝ := |Real.log (2 * Real.pi) + 1|
  let q : ℝ := max 1 (6 * c₀ / ε)
  let U : ℝ := 12 * Real.pi * (|B| + 1) / ε
  let T₀ : ℝ := max R (max (Real.exp q) U)
  refine ⟨T₀, ?_⟩
  intro T hT
  have hRT : R ≤ T := (le_max_left _ _).trans hT
  have hTpos : 0 < T := hRpos.trans_le hRT
  have hexpT : Real.exp q ≤ T :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hUT : U ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hqlog : q ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 hexpT
  have hlog_one : 1 ≤ Real.log T := (le_max_left _ _).trans hqlog
  have hlog_pos : 0 < Real.log T := zero_lt_one.trans_le hlog_one
  obtain ⟨n, hnR, hnupper⟩ := exists_dyadic_scale hRpos hRT
  let S : ℝ := T / (2 : ℝ) ^ n
  have hS : S ∈ Icc R (2 * R) := ⟨hnR, hnupper.le⟩
  have hwindowR : ∀ x ≥ R,
      |(Zeta23.Ncount x (2 * x) : ℝ) - x / (2 * Real.pi) * Zeta23.ell1 x| ≤
        C * Real.log x := by
    intro x hx
    exact hwindow x (hbaseR.trans hx)
  have hD := errorTerm_dyadic_bound hR hη.le hCR hS (hbase_bound S hS) hwindowR n
  have hrecover : (2 : ℝ) ^ n * S = T := by
    dsimp [S]
    field_simp
  rw [hrecover] at hD
  let A : ℝ := T / (2 * Real.pi) * Real.log T
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hηA : η * T * Real.log T = ε / 6 * A := by
    dsimp [η, A]
    field_simp
    ring
  have hscaled : 12 * Real.pi * (|B| + 1) ≤ ε * T := by
    calc
      12 * Real.pi * (|B| + 1) = ε * U := by
        dsimp [U]
        field_simp
      _ ≤ ε * T := mul_le_mul_of_nonneg_left hUT hε.le
  have hB_lt : B < ε / 6 * A := by
    have hden : 0 < 12 * Real.pi := by positivity
    have hBT : |B| + 1 ≤ ε * T / (12 * Real.pi) := by
      apply (le_div_iff₀ hden).2
      nlinarith [hscaled]
    have hmul_log : ε * T ≤ ε * T * Real.log T := by
      have := mul_le_mul_of_nonneg_left hlog_one (mul_nonneg hε.le hTpos.le)
      nlinarith
    calc
      B ≤ |B| := le_abs_self B
      _ < |B| + 1 := lt_add_one _
      _ ≤ ε * T / (12 * Real.pi) := hBT
      _ ≤ ε * T * Real.log T / (12 * Real.pi) :=
        div_le_div_of_nonneg_right hmul_log hden.le
      _ = ε / 6 * A := by
        dsimp [A]
        field_simp
        ring
  have hc_log : c₀ ≤ ε / 6 * Real.log T := by
    have hcq : 6 * c₀ / ε ≤ q := le_max_right _ _
    have hcT : 6 * c₀ / ε ≤ Real.log T := hcq.trans hqlog
    calc
      c₀ = (ε / 6) * (6 * c₀ / ε) := by field_simp
      _ ≤ (ε / 6) * Real.log T :=
        mul_le_mul_of_nonneg_left hcT (by positivity)
  have hmain_abs : |mainTerm T - A| = T / (2 * Real.pi) * c₀ := by
    have hTdiv : 0 < T / (2 * Real.pi) := by positivity
    dsimp [A, c₀]
    rw [mainTerm]
    have heq :
        T / (2 * Real.pi) *
              (Real.log T - Real.log (2 * Real.pi) - 1) -
            T / (2 * Real.pi) * Real.log T =
          -(T / (2 * Real.pi)) * (Real.log (2 * Real.pi) + 1) := by
      ring
    rw [heq, abs_mul, abs_neg, abs_of_pos hTdiv]
  have hmain_le : |mainTerm T - A| ≤ ε / 6 * A := by
    rw [hmain_abs]
    calc
      T / (2 * Real.pi) * c₀ ≤
          T / (2 * Real.pi) * (ε / 6 * Real.log T) :=
        mul_le_mul_of_nonneg_left hc_log (by positivity)
      _ = ε / 6 * A := by
        dsimp [A]
        ring
  have herr_lt : |errorTerm T| < ε / 3 * A := by
    calc
      |errorTerm T| ≤ B + η * T * Real.log T := hD
      _ < ε / 6 * A + ε / 6 * A := by rw [hηA]; nlinarith [hB_lt]
      _ = ε / 3 * A := by ring
  have hnum : |(Zeta23.Ncount 0 T : ℝ) - A| < ε * A := by
    have hdecomp :
        (Zeta23.Ncount 0 T : ℝ) - A = errorTerm T + (mainTerm T - A) := by
      rw [errorTerm]
      ring
    rw [hdecomp]
    calc
      |errorTerm T + (mainTerm T - A)| ≤
          |errorTerm T| + |mainTerm T - A| := abs_add_le _ _
      _ < ε / 3 * A + ε / 6 * A := add_lt_add_of_lt_of_le herr_lt hmain_le
      _ = ε / 2 * A := by ring
      _ < ε * A := by nlinarith [mul_pos hε hA]
  have hquot :
      (Zeta23.Ncount 0 T : ℝ) / A - 1 =
        ((Zeta23.Ncount 0 T : ℝ) - A) / A := by
    field_simp
  rw [hquot, abs_div, abs_of_pos hA]
  exact (div_lt_iff₀ hA).2 hnum

end ZetaZeros.Unconditional.RvM
