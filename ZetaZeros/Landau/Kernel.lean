/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Landau.ContourFold
public import ZetaZeros.Landau.Symmetrisation
public import ZetaZeros.Analytic.LogDerivEstimates

/-!
# The Landau kernel, and the residue identity on one rectangle

The **Landau kernel** is

`K (w) = (ζ'/ζ) (w) ⬝ x^{w - s} / (w - s)`.

Its poles are `w = s`, the pole `w = 1` of `ζ`, the non-trivial zeros `ρ ∈ 𝒩*` and the trivial
zeros `w = -2n`; this file computes the principal part of `K` at each, and proves the **residue
identity on one rectangle**: with right edge `re w = σ > 1`, left edge `re w = -(2N + 1)` and
horizontal edges at `im w = ± U`, where `U` is the ordinate of no zero,

`J (K; -(2N+1), σ, -U, U) = 2 π i ⬝ ((ζ'/ζ)(s) - x^{1-s}/(1-s)
  - ∑_{ρ ∈ 𝒩*, |im ρ| ≤ U} m_ρ x^{ρ-s}/(s-ρ) - ∑_{n=1}^{N} x^{-2n-s}/(2n+s))`.

## Main results

* `ZetaZeros.landauKernel`: the integrand `(ζ'/ζ)(w) ⬝ x^{w-s}/(w-s)`.
* `ZetaZeros.norm_landauKernel_le`: its size, `≤ A₀ x^{re (w-s)} / D` for any lower bound `D` of
  `‖w - s‖`.
* `ZetaZeros.zetaOrder`, `ZetaZeros.meromorphicOrderAt_riemannZeta_eq`: the order of `ζ` at a
  point, `-1` at the pole and the multiplicity of the zero elsewhere.
* `ZetaZeros.isBigO_mul_sub_div`: an analytic factor times a simple principal part.
* `ZetaZeros.landauResidue`, `ZetaZeros.bddAbove_landauKernel_sub`: the prescribed principal part
  of the kernel at every point, and the boundedness of the difference.
* `ZetaZeros.rectangleIntegral_landauKernel_eq`: **the residue identity on one rectangle.**
-/

@[expose] public section

namespace ZetaZeros

open Complex Filter Topology

/-! ### The integrand -/

/-- The **Landau kernel** `(ζ'/ζ) (w) ⬝ x^{w - s} / (w - s)`. -/
noncomputable def landauKernel (x : ℝ) (s : ℂ) (w : ℂ) : ℂ :=
  logDeriv riemannZeta w * ((x : ℂ) ^ (w - s) / (w - s))

/-- The Perron factor `x^{w - s} / (w - s)` is analytic away from `w = s`. -/
private theorem analyticAt_perronFactor {x : ℝ} (hx : 0 < x) {s p : ℂ} (hp : p ≠ s) :
    AnalyticAt ℂ (fun w : ℂ => (x : ℂ) ^ (w - s) / (w - s)) p := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_ne.mem_nhds hp] with v hv
  exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hx0)).div
    (by fun_prop) (sub_ne_zero.mpr hv)

/-- **The size of the kernel**: if `D` is a positive lower bound for `‖w - s‖` and `A₀` bounds
`‖ζ'/ζ (w)‖`, then `‖K (w)‖ ≤ A₀ x^{re (w - s)} / D`. -/
theorem norm_landauKernel_le {x : ℝ} (hx : 0 < x) {s w : ℂ} {A₀ D : ℝ}
    (hA : ‖deriv riemannZeta w / riemannZeta w‖ ≤ A₀) (hD : 0 < D) (hDw : D ≤ ‖w - s‖) :
    ‖landauKernel x s w‖ ≤ A₀ * x ^ (w - s).re / D := by
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) hA
  have hxr : (0 : ℝ) < x ^ (w - s).re := Real.rpow_pos_of_pos hx _
  rw [landauKernel, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, mul_div_assoc]
  refine mul_le_mul hA ?_ (by positivity) hA0
  exact div_le_div_of_nonneg_left hxr.le hD hDw

/-! ### `ζ` as a meromorphic function -/

/-- A globally differentiable function is analytic at every point. -/
private lemma analyticAt_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (p : ℂ) :
    AnalyticAt ℂ f p := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards with v using hf v

/-- `ζ` is analytic at every point other than its pole `1`. -/
theorem analyticAt_riemannZeta {p : ℂ} (hp : p ≠ 1) : AnalyticAt ℂ riemannZeta p :=
  analyticOn_riemannZeta p hp

/-- `ζ` is meromorphic at every point of the plane. -/
private theorem meromorphicAt_riemannZeta (p : ℂ) : MeromorphicAt riemannZeta p := by
  by_cases hp : p = 1
  · subst hp
    have heq : (fun z : ℂ => (z - 1)⁻¹ * riemannZeta₁ z) =ᶠ[𝓝[≠] (1 : ℂ)] riemannZeta := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (riemannZeta_eq_inv_sub_mul hz).symm
    refine MeromorphicAt.congr ?_ heq
    exact (((analyticAt_id.sub analyticAt_const).meromorphicAt).inv).mul
      (analyticAt_of_differentiable differentiable_riemannZeta₁ 1).meromorphicAt
  · exact (analyticAt_riemannZeta hp).meromorphicAt

/-- `ζ` does not vanish identically near any point. -/
private theorem analyticOrderAt_riemannZeta_ne_top {p : ℂ} (hp : p ≠ 1) :
    analyticOrderAt riemannZeta p ≠ ⊤ := by
  have hanaOn : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ := fun w hw => analyticAt_riemannZeta hw
  rw [Ne, analyticOrderAt_eq_top]
  intro hev
  have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have hEqOn := hanaOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hp hev
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num)
    (hEqOn (by norm_num : (2 : ℂ) ≠ 1))

/-- Off the pole, the meromorphic order of `ζ` is the multiplicity of the zero. -/
private theorem meromorphicOrderAt_riemannZeta_of_ne_one {p : ℂ} (hp : p ≠ 1) :
    meromorphicOrderAt riemannZeta p = ((zeroMultiplicity p : ℤ) : WithTop ℤ) := by
  rw [(analyticAt_riemannZeta hp).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannZeta_ne_top hp)]
  simp [zeroMultiplicity]

/-- **`ζ` has a simple pole at `1`.** -/
private theorem meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta 1 = ((-1 : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_eq_int_iff (meromorphicAt_riemannZeta 1)]
  refine ⟨riemannZeta₁, analyticAt_of_differentiable differentiable_riemannZeta₁ 1, ?_, ?_⟩
  · rw [riemannZeta₁_one]; exact one_ne_zero
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [smul_eq_mul, zpow_neg, zpow_one, riemannZeta_eq_inv_sub_mul hz]

/-- `ζ' / ζ` is analytic at a point which is neither the pole nor a zero. -/
private theorem analyticAt_logDeriv_riemannZeta {p : ℂ} (hp : p ≠ 1) (hz : riemannZeta p ≠ 0) :
    AnalyticAt ℂ (logDeriv riemannZeta) p := by
  have h := analyticAt_riemannZeta hp
  simpa only [logDeriv, Pi.div_def] using h.deriv.div h hz

/-- The kernel is analytic at every point which is not the pole of `ζ`, a zero of `ζ`, or `s`. -/
theorem analyticAt_landauKernel {x : ℝ} (hx : 0 < x) {s p : ℂ} (hp : p ≠ 1)
    (hz : riemannZeta p ≠ 0) (hps : p ≠ s) : AnalyticAt ℂ (landauKernel x s) p :=
  (analyticAt_logDeriv_riemannZeta hp hz).mul (analyticAt_perronFactor hx hps)

/-- **The order of `ζ` at a point**, as an integer: `-1` at the pole, and the multiplicity of the
zero elsewhere (so `0` off the zero set). -/
noncomputable def zetaOrder (p : ℂ) : ℤ := if p = 1 then -1 else (zeroMultiplicity p : ℤ)

/-- `ZetaZeros.zetaOrder` is the meromorphic order of `ζ`. -/
theorem meromorphicOrderAt_riemannZeta_eq (p : ℂ) :
    meromorphicOrderAt riemannZeta p = ((zetaOrder p : ℤ) : WithTop ℤ) := by
  by_cases hp : p = 1
  · subst hp; simpa [zetaOrder] using meromorphicOrderAt_riemannZeta_one
  · rw [meromorphicOrderAt_riemannZeta_of_ne_one hp, zetaOrder]
    simp only [hp, reduceIte]

/-! ### Simple poles of the kernel -/

/-- **Attaching an analytic factor to a simple principal part.** If `f - A / (· - p)` is bounded
near `p` and `g` is analytic at `p`, then `f ⬝ g - A ⬝ g p / (· - p)` is bounded near `p`. -/
theorem isBigO_mul_sub_div {f g : ℂ → ℂ} {p A : ℂ} (hg : AnalyticAt ℂ g p)
    (hf : (fun w : ℂ => f w - A / (w - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    (fun w : ℂ => f w * g w - A * g p / (w - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hgb : g =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hd : (fun w : ℂ => A * slope g p w) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    ((hasDerivAt_iff_tendsto_slope.1 hg.differentiableAt.hasDerivAt).const_mul A).isBigO_one ℂ
  have hprod : (fun w : ℂ => (f w - A / (w - p)) * g w) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (hf.mul hgb).congr (fun _ => rfl) (fun _ => by simp)
  refine (hprod.add hd).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hwp : w - p ≠ 0 := sub_ne_zero.mpr hw
  have hpw : p - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  rw [slope_def_field]
  field_simp
  ring

/-- **The kernel's principal part at a zero or at the pole of `ζ`.** -/
theorem isBigO_landauKernel_sub_of_ne {x : ℝ} (hx : 0 < x) {s p : ℂ} (hps : p ≠ s) :
    (fun w : ℂ => landauKernel x s w
        - (zetaOrder p : ℂ) * ((x : ℂ) ^ (p - s) / (p - s)) / (w - p))
      =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
  isBigO_mul_sub_div (analyticAt_perronFactor hx hps)
    (logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt (meromorphicAt_riemannZeta p)
      (meromorphicOrderAt_riemannZeta_eq p))

/-- **The kernel's principal part at `w = s`**: `K (w) - (ζ'/ζ)(s) / (w - s)` is bounded near
`s`. -/
private theorem isBigO_landauKernel_sub_at {x : ℝ} (hx : 0 < x) {s : ℂ} (hs1 : s ≠ 1)
    (hsz : riemannZeta s ≠ 0) :
    (fun w : ℂ => landauKernel x s w - logDeriv riemannZeta s / (w - s))
      =O[𝓝[≠] s] (1 : ℂ → ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ (w - s)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hx0)
  have hfs : (x : ℂ) ^ ((s : ℂ) - s) = 1 := by rw [sub_self, Complex.cpow_zero]
  have hf : (fun w : ℂ => (x : ℂ) ^ (w - s) / (w - s) - 1 / (w - s))
      =O[𝓝[≠] s] (1 : ℂ → ℂ) := by
    refine ((hasDerivAt_iff_tendsto_slope.1 hdiff.hasDerivAt).isBigO_one ℂ).congr'
      ?_ (EventuallyEq.refl _ _)
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwp : w - s ≠ 0 := sub_ne_zero.mpr hw
    have hsw : s - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
    rw [slope_def_field, hfs]
    field_simp
  refine (isBigO_mul_sub_div (analyticAt_logDeriv_riemannZeta hs1 hsz) hf).congr
    (fun w => ?_) (fun _ => rfl)
  simp only [landauKernel, one_mul]
  ring

/-! ### The residues -/

/-- **The residue of the kernel at `p`**: `(ζ'/ζ) (s)` at `w = s`, and
`ord_p (ζ) ⬝ x^{p - s} / (p - s)` at a zero or at the pole of `ζ`. -/
noncomputable def landauResidue (x : ℝ) (s p : ℂ) : ℂ :=
  if p = s then logDeriv riemannZeta s else (zetaOrder p : ℂ) * ((x : ℂ) ^ (p - s) / (p - s))

/-- At every point the kernel minus its prescribed simple principal part is bounded on a punctured
neighbourhood. -/
theorem bddAbove_landauKernel_sub {x : ℝ} (hx : 0 < x) {s : ℂ} (hs1 : s ≠ 1)
    (hsz : riemannZeta s ≠ 0) (p : ℂ) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (landauKernel x s
      - fun w : ℂ => landauResidue x s p / (w - p)) '' (V \ {p})) := by
  have hpi : ∀ A : ℂ, ((landauKernel x s - fun w : ℂ => A / (w - p))
      = fun w : ℂ => landauKernel x s w - A / (w - p)) := fun _ => rfl
  refine IsBigO_to_BddAbove ?_
  rw [hpi]
  by_cases hp : p = s
  · subst hp
    rw [landauResidue]
    simp only [reduceIte]
    exact isBigO_landauKernel_sub_at hx hs1 hsz
  · rw [landauResidue]
    simp only [hp, reduceIte]
    exact isBigO_landauKernel_sub_of_ne hx hp

/-! ### The bad set -/

/-- A set meeting every compact set in a finite set is closed. -/
private lemma isClosed_of_inter_compact_finite {S : Set ℂ}
    (h : ∀ K : Set ℂ, IsCompact K → (S ∩ K).Finite) : IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  have hfin := h (Metric.closedBall y 1) (isCompact_closedBall y 1)
  have hmem : (S ∩ Metric.closedBall y 1)ᶜ ∈ 𝓝 y :=
    hfin.isClosed.isOpen_compl.mem_nhds (fun hc => hy hc.1)
  filter_upwards [hmem, Metric.ball_mem_nhds y one_pos] with z hz hz1
  exact fun hzS => hz ⟨hzS, Metric.ball_subset_closedBall hz1⟩

/-- The **bad set** of the kernel: the pole of `ζ`, the point `s`, and the zeros of `ζ`. -/
def landauBad (s : ℂ) : Set ℂ := {1, s} ∪ riemannZetaZeros

/-- Removing finitely many points from the bad set leaves a closed set. -/
private lemma isClosed_landauBad_sdiff (s : ℂ) (P : Finset ℂ) :
    IsClosed (landauBad s \ (P : Set ℂ)) := by
  refine isClosed_of_inter_compact_finite fun K hK => ?_
  refine Set.Finite.subset (((Set.finite_singleton s).insert 1).union
    hK.inter_riemannZetaZeros_finite) fun z hz => ?_
  rcases hz.1.1 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨hz.2, h⟩

/-! ### The trivial zeros in the left half-plane -/

/-- `n ↦ -2n` is injective on `ℕ`. -/
private lemma neg_two_mul_natCast_injective :
    Function.Injective (fun n : ℕ => -(2 * (n : ℂ))) := fun _ _ h =>
  Nat.cast_injective (mul_left_cancel₀ two_ne_zero (neg_injective h))

/-- `ζ (-2n) = 0` for `n ≥ 1`. -/
private lemma riemannZeta_neg_two_mul_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    riemannZeta (-(2 * (n : ℂ))) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show -(2 * (((m + 1 : ℕ) : ℂ))) = -2 * ((m : ℂ) + 1) from by push_cast; ring]
  exact riemannZeta_neg_two_mul_nat_add_one m

/-- **Every trivial zero is simple**: `-2n` is a zero of `ζ` of multiplicity `1` for `n ≥ 1`. -/
private lemma zeroMultiplicity_neg_two_mul {n : ℕ} (hn : 1 ≤ n) :
    zeroMultiplicity (-(2 * (n : ℂ))) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hord : analyticOrderAt riemannZeta (-(2 * (((m + 1 : ℕ) : ℂ)))) = 1 := by
    rw [show -(2 * (((m + 1 : ℕ) : ℂ))) = -2 * ((m : ℂ) + 1) from by push_cast; ring]
    exact analyticOrderAt_riemannZeta_neg_two_mul m
  have hne : analyticOrderAt riemannZeta (-(2 * (((m + 1 : ℕ) : ℂ)))) ≠ ⊤ := by
    rw [hord]; exact ENat.natCast_ne_top 1
  have hcast := Nat.cast_analyticOrderNatAt hne
  rw [hord] at hcast
  simpa only [zeroMultiplicity, Nat.cast_eq_one] using hcast

/-- A trivial zero is not the pole of `ζ`: its real part is at most `-2`. -/
private lemma neg_two_mul_ne_one {n : ℕ} (hn : 1 ≤ n) : -(2 * (n : ℂ)) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.mul_re, Complex.one_re] at hre
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  norm_num at hre
  linarith

/-- The order of `ζ` at a trivial zero is `1`. -/
private lemma zetaOrder_neg_two_mul {n : ℕ} (hn : 1 ≤ n) : zetaOrder (-(2 * (n : ℂ))) = 1 := by
  rw [zetaOrder]
  simp only [neg_two_mul_ne_one hn, reduceIte]
  exact_mod_cast zeroMultiplicity_neg_two_mul hn

/-- The order of `ζ` at a non-trivial zero is its multiplicity. -/
private lemma zetaOrder_of_mem_allZeros {ρ : ℂ} (hρ : ρ ∈ allZeros) :
    zetaOrder ρ = (zeroMultiplicity ρ : ℤ) := by
  have hρ1 : ρ ≠ 1 := fun h => by simpa [h] using hρ.2.2
  rw [zetaOrder]
  simp only [hρ1, reduceIte]

/-! ### The residue identity on one rectangle -/

/-- The zeros in `𝒩*` of ordinate at most `U` in absolute value, as a `Finset ℂ`. -/
private noncomputable def heightWindowVal (U : ℝ) : Finset ℂ :=
  (heightWindow U).map ⟨Subtype.val, Subtype.val_injective⟩

/-- The trivial zeros `-2, -4, …, -2N` of the rectangle, as a `Finset ℂ`. -/
private noncomputable def trivialWindow (N : ℕ) : Finset ℂ :=
  (Finset.Icc 1 N).map ⟨fun n : ℕ => -(2 * (n : ℂ)), neg_two_mul_natCast_injective⟩

private lemma mem_heightWindowVal {U : ℝ} {p : ℂ} :
    p ∈ heightWindowVal U ↔ p ∈ allZeros ∧ |p.im| ≤ U := by
  simp only [heightWindowVal, Finset.mem_map, Function.Embedding.coeFn_mk, mem_heightWindow]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨ρ.2, hρ⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨p, h₁⟩, h₂, rfl⟩

private lemma mem_trivialWindow {N : ℕ} {p : ℂ} :
    p ∈ trivialWindow N ↔ ∃ n : ℕ, (1 ≤ n ∧ n ≤ N) ∧ -(2 * (n : ℂ)) = p := by
  simp only [trivialWindow, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_Icc]

/-- **The residue identity for one rectangle.** For `x > 0`, a point `s` that is neither the pole
nor a zero of `ζ`, a right abscissa `σ > 1` to the right of `s`, a left abscissa `-(2N + 1)` to its
left, and a height `U > |im s|` that is the ordinate of no zero,

`J (ζ'/ζ ⬝ x^{w-s}/(w-s)) = 2 π i ⬝ ((ζ'/ζ)(s) - x^{1-s}/(1-s) - ∑_{|im ρ| ≤ U} m_ρ x^{ρ-s}/(s-ρ)
  - ∑_{n = 1}^{N} x^{-2n-s}/(2n+s))`. -/
theorem rectangleIntegral_landauKernel_eq {x : ℝ} (hx : 0 < x) {s : ℂ} (hs1 : s ≠ 1)
    (hsz : riemannZeta s ≠ 0) {σ U : ℝ} {N : ℕ} (hσ : 1 < σ) (hσs : s.re < σ)
    (hN : -(2 * (N : ℝ) + 1) < s.re) (hU : |s.im| < U)
    (hUz : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≠ U) :
    RectangleIntegral (landauKernel x s)
        ((-(2 * (N : ℝ) + 1) : ℝ) + ((-U : ℝ) : ℂ) * I) ((σ : ℝ) + ((U : ℝ) : ℂ) * I)
      = 2 * (Real.pi : ℂ) * I * (logDeriv riemannZeta s - (x : ℂ) ^ (1 - s) / (1 - s)
          - (∑ ρ ∈ heightWindow U, landauZeroTerm x s ρ)
          - ∑ n ∈ Finset.Icc 1 N, (x : ℂ) ^ (-(2 * (n : ℂ)) - s) / (2 * (n : ℂ) + s)) := by
  have hU0 : 0 < U := lt_of_le_of_lt (abs_nonneg _) hU
  obtain ⟨hsim₁, hsim₂⟩ := abs_lt.1 hU
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hcre : ∀ n : ℕ, (-(2 * (n : ℂ))).re = -(2 * (n : ℝ)) := fun n => by simp
  have hcim : ∀ n : ℕ, (-(2 * (n : ℂ))).im = 0 := fun n => by simp
  set a : ℝ := -(2 * (N : ℝ) + 1) with ha
  have ha1 : a ≤ -1 := by rw [ha]; linarith
  have hZT : Disjoint (heightWindowVal U) (trivialWindow N) := by
    refine Finset.disjoint_left.2 fun p hpZ hpT => ?_
    obtain ⟨n, ⟨hn1, -⟩, rfl⟩ := mem_trivialWindow.1 hpT
    have hre := (mem_heightWindowVal.1 hpZ).1.2.1
    have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    rw [hcre n] at hre
    linarith
  have h1nZT : (1 : ℂ) ∉ (heightWindowVal U).disjUnion (trivialWindow N) hZT := by
    rw [Finset.mem_disjUnion]
    rintro (hp | hp)
    · exact riemannZeta_one_ne_zero (mem_heightWindowVal.1 hp).1.1
    · obtain ⟨n, ⟨hn1, -⟩, he⟩ := mem_trivialWindow.1 hp
      exact neg_two_mul_ne_one hn1 he
  have hsnP : s ∉ Finset.cons 1 ((heightWindowVal U).disjUnion (trivialWindow N) hZT) h1nZT := by
    rw [Finset.mem_cons]
    rintro (rfl | hp)
    · exact hs1 rfl
    · rw [Finset.mem_disjUnion] at hp
      rcases hp with hp | hp
      · exact hsz (mem_heightWindowVal.1 hp).1.1
      · obtain ⟨n, ⟨hn1, -⟩, rfl⟩ := mem_trivialWindow.1 hp
        exact hsz (riemannZeta_neg_two_mul_eq_zero hn1)
  set P : Finset ℂ :=
    Finset.cons s (Finset.cons 1 ((heightWindowVal U).disjUnion (trivialWindow N) hZT) h1nZT)
      hsnP with hPdef
  have hmemP : ∀ p : ℂ, p ∈ P ↔ p = s ∨ p = 1 ∨ p ∈ heightWindowVal U ∨ p ∈ trivialWindow N := by
    intro p
    simp only [hPdef, Finset.mem_cons, Finset.mem_disjUnion]
  have hP : ∀ p ∈ P, a < p.re ∧ p.re < σ ∧ -U < p.im ∧ p.im < U := by
    intro p hp
    rcases (hmemP p).1 hp with rfl | rfl | hp | hp
    · exact ⟨hN, hσs, hsim₁, hsim₂⟩
    · rw [Complex.one_re, Complex.one_im]
      exact ⟨by linarith, hσ, by linarith, hU0⟩
    · obtain ⟨⟨hz, h0, h1⟩, him⟩ := mem_heightWindowVal.1 hp
      obtain ⟨hi₁, hi₂⟩ := abs_lt.1 (lt_of_le_of_ne him (hUz p hz))
      exact ⟨by linarith, by linarith, hi₁, hi₂⟩
    · obtain ⟨n, ⟨hn1, hnN⟩, rfl⟩ := mem_trivialWindow.1 hp
      have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      rw [hcre n, hcim n, ha]
      exact ⟨by linarith, by linarith, by linarith, hU0⟩
  have hKU : {w : ℂ | a ≤ w.re ∧ w.re ≤ σ ∧ -U ≤ w.im ∧ w.im ≤ U}
      ⊆ (landauBad s \ (P : Set ℂ))ᶜ := by
    intro w hw hbad
    refine hbad.2 ?_
    rcases hbad.1 with h | h
    · rcases h with h | h
      · exact (hmemP w).2 (Or.inr (Or.inl h))
      · exact (hmemP w).2 (Or.inl (by simpa using h))
    · have hz : riemannZeta w = 0 := mem_riemannZetaZeros.1 h
      rcases le_or_gt 1 w.re with hre | hre
      · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hre)
      rcases le_or_gt w.re 0 with hre0 | hre0
      · obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hre0).1 hz
        have hw' : w = -(2 * (((n + 1 : ℕ)) : ℂ)) := by rw [hn]; push_cast; ring
        have hwre : w.re = -(2 * ((n : ℝ) + 1)) := by
          rw [hw', hcre (n + 1)]; push_cast; ring
        have hle : 2 * (n + 1) ≤ 2 * N + 1 := by
          have h1 := hw.1
          rw [hwre, ha] at h1
          have h2 : 2 * ((n : ℝ) + 1) ≤ 2 * (N : ℝ) + 1 := by linarith
          exact_mod_cast h2
        exact (hmemP w).2 (Or.inr (Or.inr (Or.inr (mem_trivialWindow.2
          ⟨n + 1, ⟨by omega, by omega⟩, hw'.symm⟩))))
      · exact (hmemP w).2 (Or.inr (Or.inr (Or.inl (mem_heightWindowVal.2
          ⟨⟨hz, hre0, hre⟩, abs_le.2 ⟨hw.2.2.1, hw.2.2.2⟩⟩))))
  have hana : AnalyticOnNhd ℂ (landauKernel x s) ((landauBad s \ (P : Set ℂ))ᶜ \ (P : Set ℂ)) := by
    intro w hw
    have hnb : w ∉ landauBad s := fun h => hw.1 ⟨h, hw.2⟩
    exact analyticAt_landauKernel hx (fun h => hnb (Or.inl (by simp [h])))
      (fun h => hnb (Or.inr (mem_riemannZetaZeros.2 h))) (fun h => hnb (Or.inl (by simp [h])))
  have hres_one : landauResidue x s 1 = -((x : ℂ) ^ (1 - s) / (1 - s)) := by
    rw [landauResidue, zetaOrder]
    simp only [Ne.symm hs1, reduceIte]
    push_cast
    ring
  have hres_Z : ∑ p ∈ heightWindowVal U, landauResidue x s p
      = ∑ ρ ∈ heightWindow U, -landauZeroTerm x s ρ := by
    rw [heightWindowVal, Finset.sum_map]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hρs : (ρ : ℂ) ≠ s := fun h => hsz (h ▸ ρ.2.1)
    rw [Function.Embedding.coeFn_mk, landauResidue, landauZeroTerm,
      zetaOrder_of_mem_allZeros ρ.2]
    simp only [hρs, reduceIte]
    set E : ℂ := (x : ℂ) ^ ((ρ : ℂ) - s) with hE
    rw [show ((ρ : ℂ) - s) = -(s - (ρ : ℂ)) from by ring, div_neg]
    push_cast
    ring
  have hres_T : ∑ p ∈ trivialWindow N, landauResidue x s p
      = ∑ n ∈ Finset.Icc 1 N, -((x : ℂ) ^ (-(2 * (n : ℂ)) - s) / (2 * (n : ℂ) + s)) := by
    rw [trivialWindow, Finset.sum_map]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.1 hn
    have hne : -(2 * (n : ℂ)) ≠ s := fun h => hsz (h ▸ riemannZeta_neg_two_mul_eq_zero hn1)
    rw [Function.Embedding.coeFn_mk, landauResidue, zetaOrder_neg_two_mul hn1]
    simp only [hne, reduceIte]
    set E : ℂ := (x : ℂ) ^ (-(2 * (n : ℂ)) - s) with hE
    rw [show (-(2 * (n : ℂ)) - s) = -(2 * (n : ℂ) + s) from by ring, div_neg]
    push_cast
    ring
  have hsum : ∑ p ∈ P, landauResidue x s p
      = logDeriv riemannZeta s - (x : ℂ) ^ (1 - s) / (1 - s)
          - (∑ ρ ∈ heightWindow U, landauZeroTerm x s ρ)
          - ∑ n ∈ Finset.Icc 1 N, (x : ℂ) ^ (-(2 * (n : ℂ)) - s) / (2 * (n : ℂ) + s) := by
    rw [hPdef, Finset.sum_cons, Finset.sum_cons, Finset.sum_disjUnion, hres_one, hres_Z, hres_T,
      Finset.sum_neg_distrib, Finset.sum_neg_distrib, landauResidue]
    simp only [reduceIte]
    ring
  rw [rectangleIntegral_eq_two_pi_I_mul_sum_residues (a := a) (b := σ) (c := -U) (d := U)
    (by linarith) (by linarith) (isClosed_landauBad_sdiff s P).isOpen_compl hKU hP hana
    (A := landauResidue x s) (fun p _ => bddAbove_landauKernel_sub hx hs1 hsz p), hsum]

end ZetaZeros
