/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.ZeroCount.RiemannVonMangoldt

/-!
# The zero count on a window, and the dyadic asymptotic

The count `N(T₁, T₂) = N(T₂) - N(T₁)` of the non-trivial zeros of `ζ` on a window `(T₁, T₂]`, and
its asymptotic on the dyadic window `(T, 2T]`, a consequence of the Riemann--von Mangoldt formula
`N(T) = M(T) + O(log T)` and the identity
`M(2T) - M(T) = (T / 2π)(log (T / 2π) + 2 log 2 - 1)`.

## Main definitions

* `ZetaZeros.zeroCountWindow`: the count `N(T₁, T₂) = N(T₂) - N(T₁)` on a window.

## Main results

* `ZetaZeros.zeroCountWindow_nonneg`: the window count is non-negative.
* `ZetaZeros.mainTerm_two_mul_sub`: the dyadic main term,
  `M(2T) - M(T) = (T / 2π)(log (T / 2π) + 2 log 2 - 1)` for `T > 0`.
* `ZetaZeros.exists_abs_zeroCountWindow_sub_le`: the dyadic asymptotic
  `|N(T, 2T) - (T / 2π)(log (T / 2π) + 2 log 2 - 1)| ≤ C log T` for `T ≥ 4`.
-/

@[expose] public section

namespace ZetaZeros

/-- The **zero count on a window**, `N(T₁, T₂) = N(T₂) - N(T₁)`: for `0 ≤ T₁ ≤ T₂` this is the
number of non-trivial zeros `ρ` with `T₁ < im ρ ≤ T₂`, counted with multiplicity. The value is
real-valued, both counts being cast to `ℝ` before subtracting. -/
noncomputable def zeroCountWindow (T₁ T₂ : ℝ) : ℝ :=
  (zeroCount T₂ : ℝ) - (zeroCount T₁ : ℝ)

/-- A window with its endpoints in order carries a non-negative count. -/
theorem zeroCountWindow_nonneg {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : 0 ≤ zeroCountWindow T₁ T₂ := by
  rw [zeroCountWindow, sub_nonneg]
  exact Nat.cast_le.2 (zeroCount_mono h)

/-- **The dyadic main term.** `M(2T) - M(T) = (T / 2π)(log (T / 2π) + 2 log 2 - 1)` for `T > 0`.
-/
theorem mainTerm_two_mul_sub {T : ℝ} (hT : 0 < T) :
    mainTerm (2 * T) - mainTerm T
      = T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) + 2 * Real.log 2 - 1) := by
  have hx : T / (2 * Real.pi) ≠ 0 := div_ne_zero (ne_of_gt hT) (by positivity)
  have hlog : Real.log (2 * T / (2 * Real.pi))
      = Real.log 2 + Real.log (T / (2 * Real.pi)) := by
    rw [mul_div_assoc, Real.log_mul two_ne_zero hx]
  simp only [mainTerm, hlog]
  ring

/-- **The dyadic asymptotic.** There is a constant `C > 0` with

`|N(T, 2T) - (T / 2π)(log (T / 2π) + 2 log 2 - 1)| ≤ C log T`

for every `T ≥ 4`. -/
theorem exists_abs_zeroCountWindow_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4 ≤ T →
      |zeroCountWindow T (2 * T)
          - T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) + 2 * Real.log 2 - 1)|
        ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := exists_abs_zeroCount_sub_mainTerm_le
  have hM : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hCM : C ≤ max C 0 := le_max_left _ _
  refine ⟨3 * max C 0 + 1, by linarith, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlog2T : Real.log (2 * T) ≤ 2 * Real.log T := by
    rw [Real.log_mul two_ne_zero (ne_of_gt hT0)]
    have : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos (by linarith)
    linarith
  have hlog2T0 : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have e1 : |(zeroCount T : ℝ) - mainTerm T| ≤ max C 0 * Real.log T :=
    (hC T hT).trans (mul_le_mul_of_nonneg_right hCM hlogT)
  have e2 : |(zeroCount (2 * T) : ℝ) - mainTerm (2 * T)| ≤ 2 * max C 0 * Real.log T :=
    (hC (2 * T) (by linarith)).trans <|
      calc C * Real.log (2 * T) ≤ max C 0 * Real.log (2 * T) :=
            mul_le_mul_of_nonneg_right hCM hlog2T0
        _ ≤ max C 0 * (2 * Real.log T) := mul_le_mul_of_nonneg_left hlog2T hM
        _ = 2 * max C 0 * Real.log T := by ring
  have hid : zeroCountWindow T (2 * T)
      - T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) + 2 * Real.log 2 - 1)
      = ((zeroCount (2 * T) : ℝ) - mainTerm (2 * T)) - ((zeroCount T : ℝ) - mainTerm T) := by
    rw [zeroCountWindow, ← mainTerm_two_mul_sub hT0]
    ring
  obtain ⟨h1a, h1b⟩ := abs_le.1 e1
  obtain ⟨h2a, h2b⟩ := abs_le.1 e2
  rw [hid, abs_le]
  exact ⟨by linarith, by linarith⟩

end ZetaZeros
