/-
Copyright (c) 2026 AxiomMath, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic PBC
-/
import ZetaZeros.Unconditional.PairCorrelationHighTail

/-!
# The signed boundary identity in the BGST window comparison

The endpoint argument must compare the whole-line moment of the positive-height zero
window with the moment of a symmetrically truncated full-zero sum on `(0, T]`.  Bounding
the exterior and cross terms separately loses the cancellation in Lemma 4 of
Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh.  This file records the exact signed
identity which has to be estimated before taking absolute values.
-/

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex Finset MeasureTheory Set

/-- If `B` is supported on `s`, the difference of its global second moment from that of
`A` is exactly one exterior integral plus a *signed* interior integral.  In particular,
the two cross terms remain together; no positivity or triangle inequality has been used. -/
lemma secondMoment_sub_secondMoment_eq_signed_boundary
    {A B : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    (hA : Integrable (fun t ↦ A t * (starRingEnd ℂ) (A t)))
    (hB : Integrable (fun t ↦ B t * (starRingEnd ℂ) (B t)))
    (hBzero : ∀ t ∉ s, B t = 0) :
    (∫ t, A t * (starRingEnd ℂ) (A t)) -
        ∫ t, B t * (starRingEnd ℂ) (B t) =
      (∫ t in sᶜ, A t * (starRingEnd ℂ) (A t)) +
        ∫ t in s,
          (A t - B t) * (starRingEnd ℂ) (A t) +
            B t * (starRingEnd ℂ) (A t - B t) := by
  have hBcompl : ∫ t in sᶜ,
      B t * (starRingEnd ℂ) (B t) = 0 := by
    apply integral_eq_zero_of_ae
    apply ae_restrict_of_forall_mem hs.compl
    intro t ht
    change B t * (starRingEnd ℂ) (B t) = 0
    rw [hBzero t ht, map_zero, zero_mul]
  calc
    (∫ t, A t * (starRingEnd ℂ) (A t)) -
        ∫ t, B t * (starRingEnd ℂ) (B t) =
        ((∫ t in s, A t * (starRingEnd ℂ) (A t)) +
          ∫ t in sᶜ, A t * (starRingEnd ℂ) (A t)) -
        ((∫ t in s, B t * (starRingEnd ℂ) (B t)) +
          ∫ t in sᶜ, B t * (starRingEnd ℂ) (B t)) := by
      rw [integral_add_compl hs hA, integral_add_compl hs hB]
    _ = (∫ t in sᶜ, A t * (starRingEnd ℂ) (A t)) +
        ∫ t in s,
          (A t * (starRingEnd ℂ) (A t) -
            B t * (starRingEnd ℂ) (B t)) := by
      rw [hBcompl, integral_sub hA.integrableOn hB.integrableOn]
      ring
    _ = (∫ t in sᶜ, A t * (starRingEnd ℂ) (A t)) +
        ∫ t in s,
          (A t - B t) * (starRingEnd ℂ) (A t) +
            B t * (starRingEnd ℂ) (A t - B t) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [map_sub]
      ring

/-- Exact signed boundary decomposition for Montgomery's finite window and the
phase-corrected full-zero model. -/
theorem finiteWindowSecondMoment_sub_windowedFullZeroSecondMoment_eq_signed_boundary
    (x T : ℝ) (hx : 1 ≤ x) :
    finiteWindowSecondMoment x T - windowedFullZeroSecondMoment x T =
      (∫ t in (Set.Ioc 0 T)ᶜ,
        finiteWindowLorentzianSum x T t *
          (starRingEnd ℂ) (finiteWindowLorentzianSum x T t)) +
      ∫ t in Set.Ioc 0 T,
        (finiteWindowLorentzianSum x T t - windowedFullZeroSum x T t) *
            (starRingEnd ℂ) (finiteWindowLorentzianSum x T t) +
          windowedFullZeroSum x T t * (starRingEnd ℂ)
            (finiteWindowLorentzianSum x T t - windowedFullZeroSum x T t) := by
  have hzero : ∀ t ∉ Set.Ioc (0 : ℝ) T,
      windowedFullZeroSum x T t = 0 := by
    intro t ht
    rw [windowedFullZeroSum, Set.indicator_of_notMem ht]
  simpa only [finiteWindowSecondMoment, windowedFullZeroSecondMoment] using
    secondMoment_sub_secondMoment_eq_signed_boundary
      measurableSet_Ioc
      (finiteWindowLorentzianSum_mul_conj_integrable x T)
      (integrable_windowedFullZeroSum_mul_conj x T hx) hzero

/-- On the interior window, the signed discrepancy in the preceding theorem can be
written exactly using the complementary full-zero series. -/
theorem finiteWindow_signed_discrepancy_eq_complement
    (x T t : ℝ) (hx : 1 ≤ x) (ht : t ∈ Set.Ioc (0 : ℝ) T) :
    (finiteWindowLorentzianSum x T t - windowedFullZeroSum x T t) *
          (starRingEnd ℂ) (finiteWindowLorentzianSum x T t) +
        windowedFullZeroSum x T t * (starRingEnd ℂ)
          (finiteWindowLorentzianSum x T t - windowedFullZeroSum x T t) =
      (-((x : ℂ) ^ (Complex.I * t) *
          (∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
              rho ∉ finiteZeroCarrierWindow T},
            fullZeroLorentzianSummand x t rho))) *
          (starRingEnd ℂ) (finiteWindowLorentzianSum x T t) +
        phaseCorrectedFullZeroSum x t * (starRingEnd ℂ)
          (-((x : ℂ) ^ (Complex.I * t) *
            (∑' rho : {rho : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier //
                rho ∉ finiteZeroCarrierWindow T},
              fullZeroLorentzianSummand x t rho))) := by
  rw [windowedFullZeroSum, Set.indicator_of_mem ht,
    finiteWindowLorentzianSum_sub_phaseCorrectedFullZeroSum x hx]

end ZetaZeros.Unconditional.PairCorrelationProof
