/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import ZetaZeros.Meta.Attr
public import ZetaZeros.Zeta.Defs

/-!
# Good heights

A real number `T` is a *good height* when the horizontal line `im s = T` misses the non-trivial
zeros of the Riemann zeta function: there is no `ρ` with `ζ ρ = 0`, `0 < re ρ < 1` and `im ρ = T`.

## Main definitions

* `ZetaZeros.IsGoodHeight`: the predicate above, on a real height `T`.

## Main results

* `ZetaZeros.IsGoodHeight.zeta_ne_zero`: a point of the open critical strip at a good height is not
  a zero of `ζ`.
* `ZetaZeros.isGoodHeight_iff`: the same condition along the parametrisation `σ ↦ σ + T * I` of the
  horizontal line.
* `ZetaZeros.isGoodHeight_neg_iff`: the good heights are symmetric about `0`, because the zeros are
  stable under conjugation.
* `ZetaZeros.IsGoodHeight.im_lt_of_mem_nontrivialZeros`: at a good height the zeros counted by
  `N(T)` lie strictly below the height, the closed condition `im ρ ≤ T` of `nontrivialZeros`
  becoming an open one.
-/

@[expose] public section

namespace ZetaZeros

open Complex

/-- A real number `T` is a **good height** when no zero of the Riemann zeta function in the open
critical strip `0 < re s < 1` has imaginary part `T`. -/
@[zz_tag "def_good_height"]
def IsGoodHeight (T : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.im ≠ T

/-- A good height carries no zero of `ζ` in the open critical strip. -/
theorem IsGoodHeight.zeta_ne_zero {T : ℝ} (hT : IsGoodHeight T) {s : ℂ} (h₀ : 0 < s.re)
    (h₁ : s.re < 1) (hs : s.im = T) : riemannZeta s ≠ 0 :=
  fun h => hT s h h₀ h₁ hs

/-- `T` is a good height if and only if there is no zero of `ζ` in the open critical strip with
imaginary part `T`. -/
private theorem isGoodHeight_iff_not_exists {T : ℝ} :
    IsGoodHeight T ↔ ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im = T :=
  ⟨fun hT ⟨ρ, hζ, h₀, h₁, him⟩ => hT ρ hζ h₀ h₁ him,
    fun h ρ hζ h₀ h₁ him => h ⟨ρ, hζ, h₀, h₁, him⟩⟩

/-- A good height, read along the parametrisation `σ ↦ σ + T * I` of the horizontal line at
height `T`. -/
theorem isGoodHeight_iff {T : ℝ} :
    IsGoodHeight T ↔ ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ + T * I) ≠ 0 := by
  constructor
  · intro hT σ h₀ h₁
    exact hT.zeta_ne_zero (by simpa using h₀) (by simpa using h₁) (by simp)
  · intro h ρ hρ h₀ h₁ him
    refine h ρ.re h₀ h₁ ?_
    rwa [← him, re_add_im ρ]

/-- Zeros of `ζ` come in conjugate pairs, so `-T` is a good height as soon as `T` is. -/
private theorem IsGoodHeight.neg {T : ℝ} (hT : IsGoodHeight T) : IsGoodHeight (-T) := fun ρ hρ h₀ h₁
    him =>
  hT ((starRingEnd ℂ) ρ) (by rw [riemannZeta_conj, hρ, map_zero]) (by simpa using h₀)
    (by simpa using h₁) (by simp [him])

/-- The good heights are symmetric about `0`. -/
theorem isGoodHeight_neg_iff {T : ℝ} : IsGoodHeight (-T) ↔ IsGoodHeight T :=
  ⟨fun h => neg_neg T ▸ h.neg, IsGoodHeight.neg⟩

/-- At a good height `T`, every non-trivial zero counted by `N(T)` has imaginary part strictly
below `T`. -/
theorem IsGoodHeight.im_lt_of_mem_nontrivialZeros {T : ℝ} (hT : IsGoodHeight T) {ρ : ℂ}
    (hρ : ρ ∈ nontrivialZeros T) : ρ.im < T :=
  lt_of_le_of_ne hρ.2.2.2.2 (hT ρ hρ.1 hρ.2.1 hρ.2.2.1)

end ZetaZeros
