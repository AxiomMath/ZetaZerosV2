/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeNumberTheoremAnd.RectangleArgumentPrinciple
public import ZetaZeros.Analytic.ZetaBounds
public import ZetaZeros.Analytic.Xi

/-!
# The folded contour

The argument principle and the residue theorem on a rectangle, and the fold that replaces the
boundary of the rectangle `-1 ≤ re s ≤ 2`, `0 ≤ im s ≤ T` by the half-contour
`𝒞(T) = {2 + it : 0 ≤ t ≤ T} ∪ {x + iT : 1/2 ≤ x ≤ 2}`.

The fold rests on the reflection identity `(ξ' / ξ) (1 - conj s) = - conj ((ξ' / ξ) s)`
(`ZetaZeros.logDeriv_riemannXi_one_sub_conj`): the bottom side of the rectangle contributes `0`,
the left side is minus the conjugate of the right side, and the left half of the top side is minus
the conjugate of its right half.

The boundary integral `J (h; a, b, c, d)` of a rectangle is `RectangleIntegral h (a + c i)
(b + d i)`, and the order `ord_ρ f` of a zero is `analyticOrderNatAt f ρ`.

## Main definitions

* `ZetaZeros.foldedPath`, `ZetaZeros.foldedPathIntegral`: the half-contour `𝒞(T)` and the integral
  `I(h; T) = i ∫_0^T h (2 + it) dt - ∫_{1/2}^2 h (x + iT) dx` along it.

## Main results

* `ZetaZeros.ne_one_of_mem_foldedPath`, `ZetaZeros.riemannZeta_ne_zero_of_mem_foldedPath`: on the
  half-contour at a good height, `s ≠ 1` and `ζ s ≠ 0`.
* `ZetaZeros.foldedPathIntegral_eq_sub_of_hasDerivAt`: `I(H'; T) = H (1/2 + iT) - H 2`.
* `ZetaZeros.rectangleIntegral_eq_two_pi_I_mul_sum_residues`: the residue theorem on a rectangle,
  for an integrand with prescribed simple principal parts.
* `ZetaZeros.rectangleIntegral_logDeriv_eq_sum_analyticOrderNatAt`: the argument principle on a
  rectangle, `J (f' / f) = 2 π i ∑_ρ ord_ρ f`.
* `ZetaZeros.integral_logDeriv_riemannXi_bottom_eq_zero`,
  `ZetaZeros.integral_logDeriv_riemannXi_left_eq`,
  `ZetaZeros.integral_logDeriv_riemannXi_top_left_eq`: the three pieces of the fold.
* `ZetaZeros.rectangleIntegral_logDeriv_riemannXi_eq`: the fold itself,
  `J (ξ' / ξ; -1, 2, 0, T) = 2 i im I (ξ' / ξ; T)`.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory Set

/-! ## The folded path -/

/-- The **folded path** `𝒞(T)`: the vertical segment from `2` to `2 + iT` together with the
horizontal segment from `1/2 + iT` to `2 + iT`. -/
@[zz_tag "def_path_integral"]
def foldedPath (T : ℝ) : Set ℂ :=
  {s : ℂ | s.re = 2 ∧ 0 ≤ s.im ∧ s.im ≤ T} ∪ {s : ℂ | s.im = T ∧ 1 / 2 ≤ s.re ∧ s.re ≤ 2}

/-- The **integral along the folded path**,
`I (h; T) = i ∫_0^T h (2 + it) dt - ∫_{1/2}^2 h (x + iT) dx`, the two segments of `𝒞 T` traversed
upwards and then rightwards. -/
@[zz_tag "def_path_integral"]
noncomputable def foldedPathIntegral (h : ℂ → ℂ) (T : ℝ) : ℂ :=
  I * (∫ t in (0 : ℝ)..T, h (2 + t * I)) - ∫ x in (1 / 2 : ℝ)..2, h (x + T * I)

/-- A point of the vertical segment of `𝒞 T`. -/
theorem mem_foldedPath_vertical {T t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ T) :
    (2 : ℂ) + t * I ∈ foldedPath T := Or.inl ⟨by simp, by simpa using h₀, by simpa using h₁⟩

/-- A point of the horizontal segment of `𝒞 T`. -/
theorem mem_foldedPath_horizontal {T x : ℝ} (h₀ : 1 / 2 ≤ x) (h₁ : x ≤ 2) :
    (x : ℂ) + T * I ∈ foldedPath T := Or.inr ⟨by simp, by simpa using h₀, by simpa using h₁⟩

/-- **No point of the folded path is the pole of `ζ`**, for `T > 0`. -/
@[zz_tag "lem_zeta_ne_zero_on_path"]
theorem ne_one_of_mem_foldedPath {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : s ∈ foldedPath T) : s ≠ 1 := by
  intro he
  rcases hs with h | h
  · have h2 : s.re = 2 := h.1
    rw [he] at h2
    norm_num at h2
  · have h2 : s.im = T := h.1
    rw [he] at h2
    simp only [Complex.one_im] at h2
    linarith

/-- **`ζ` does not vanish on the folded path** at a good height. -/
@[zz_tag "lem_zeta_ne_zero_on_path"]
theorem riemannZeta_ne_zero_of_mem_foldedPath {T : ℝ} (hT : IsGoodHeight T) {s : ℂ}
    (hs : s ∈ foldedPath T) : riemannZeta s ≠ 0 := by
  rcases hs with h | h
  · intro hz
    have := one_quarter_le_riemannZeta_re (s := s) (by rw [h.1])
    rw [hz] at this
    norm_num at this
  · intro hz
    rcases le_or_gt 1 s.re with hre | hre
    · exact riemannZeta_ne_zero_of_one_le_re hre hz
    · exact hT s hz (by linarith [h.2.1]) hre h.1

/-! ## A primitive along the folded path -/

/-- The fundamental theorem of calculus along a path `γ` of constant derivative `γ'`: if `H` has
derivative `h` on a set through which `γ` passes, then `∫_a^b γ' ⬝ h (γ t) dt = H (γ b) - H (γ a)`.
-/
private lemma integral_deriv_comp_of_hasDerivAt {a b : ℝ} {V : Set ℂ} {H h : ℂ → ℂ} {γ : ℝ → ℂ}
    {γ' : ℂ} (hγ : ∀ t : ℝ, HasDerivAt γ γ' t) (hcont : ContinuousOn h V)
    (hderiv : ∀ z ∈ V, HasDerivAt H (h z) z) (hmem : ∀ t ∈ uIcc a b, γ t ∈ V) :
    (∫ t in a..b, γ' * h (γ t)) = H (γ b) - H (γ a) := by
  have hγd : Differentiable ℝ γ := fun t => (hγ t).differentiableAt
  have h1 : ∀ t ∈ uIcc a b, HasDerivAt (fun t : ℝ => H (γ t)) (γ' * h (γ t)) t := by
    intro t ht
    simpa [Function.comp_def, smul_eq_mul] using (hderiv (γ t) (hmem t ht)).scomp t (hγ t)
  have h2 : IntervalIntegrable (fun t : ℝ => γ' * h (γ t)) volume a b :=
    (continuousOn_const.mul (hcont.comp hγd.continuous.continuousOn hmem)).intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt h1 h2

/-- **The folded path integral of a function with a primitive.** If `H` is analytic on a set `V`
containing `𝒞 T` and has derivative `h` there, then `I (h; T) = H (1/2 + iT) - H 2`. -/
@[zz_tag "lem_path_primitive"]
theorem foldedPathIntegral_eq_sub_of_hasDerivAt {T : ℝ} (hT : 0 < T) {V : Set ℂ}
    (hsub : foldedPath T ⊆ V) {h H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H V)
    (hderiv : ∀ z ∈ V, HasDerivAt H (h z) z) :
    foldedPathIntegral h T = H (1 / 2 + T * I) - H 2 := by
  have hcont : ContinuousOn h V :=
    (hH.deriv.continuousOn).congr fun z hz => ((hderiv z hz).deriv).symm
  have hvert : (∫ t in (0 : ℝ)..T, I * h (2 + t * I)) = H (2 + T * I) - H (2 + (0 : ℝ) * I) := by
    refine integral_deriv_comp_of_hasDerivAt (γ := fun t : ℝ => (2 : ℂ) + t * I)
      (fun t => ?_) hcont hderiv fun t ht => hsub ?_
    · simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (2 : ℂ)
    · rw [uIcc_of_le hT.le] at ht
      exact mem_foldedPath_vertical ht.1 ht.2
  have hhoriz : (∫ x in (1 / 2 : ℝ)..2, (1 : ℂ) * h (x + T * I))
      = H ((2 : ℝ) + T * I) - H ((1 / 2 : ℝ) + T * I) := by
    refine integral_deriv_comp_of_hasDerivAt (γ := fun x : ℝ => (x : ℂ) + T * I)
      (fun t => ?_) hcont hderiv fun t ht => hsub ?_
    · simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const ((T : ℂ) * I)
    · rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at ht
      exact mem_foldedPath_horizontal ht.1 ht.2
  rw [foldedPathIntegral, ← intervalIntegral.integral_const_mul, hvert]
  simp only [one_mul] at hhoriz
  rw [hhoriz]
  push_cast
  ring_nf

/-! ## The closed rectangle and its border -/

/-- For `a ≤ b` and `c ≤ d`, `Rectangle (a + c i) (b + d i)` is the set of `z` with
`a ≤ re z ≤ b` and `c ≤ im z ≤ d`. -/
private lemma rectangle_eq_setOf {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    Rectangle ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (d : ℂ) * I)
      = {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ c ≤ s.im ∧ s.im ≤ d} := by
  ext s
  simp only [Rectangle, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_add, Complex.mem_reProdIm, uIcc_of_le hab, uIcc_of_le hcd,
    mem_Icc, Set.mem_ofPred_eq]
  tauto

/-- A point of the border of a rectangle lies on one of the four sides. -/
private lemma mem_rectangleBorder_cases {a b c d : ℝ} {s : ℂ}
    (hs : s ∈ RectangleBorder ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (d : ℂ) * I)) :
    s.re = a ∨ s.re = b ∨ s.im = c ∨ s.im = d := by
  simp only [RectangleBorder, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, add_zero, zero_add, mem_union, Complex.mem_reProdIm,
    mem_singleton_iff] at hs
  tauto

/-! ## The residue theorem on a rectangle -/

/-- `-1 ≤ 0` in `WithTop ℤ`. -/
private lemma neg_one_le_zero_withTop : ((-1 : ℤ) : WithTop ℤ) ≤ 0 := by
  rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
  norm_num

/-- A non-zero simple principal part `A / (s - p)` has order exactly `-1` at `p`. -/
private lemma meromorphicOrderAt_const_div_sub_eq {A p : ℂ} (hA : A ≠ 0) :
    meromorphicOrderAt (fun s : ℂ => A / (s - p)) p = (-1 : ℤ) := by
  have hm : MeromorphicAt (fun s : ℂ => A / (s - p)) p := by fun_prop
  rw [meromorphicOrderAt_eq_int_iff hm]
  refine ⟨fun _ => A, analyticAt_const, hA, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hqp : q - p ≠ 0 := sub_ne_zero.mpr hq
  rw [smul_eq_mul, zpow_neg, zpow_one]
  field_simp

/-- A simple principal part `A / (· - p)` has order at least `-1` at `p`. -/
private lemma meromorphicOrderAt_const_div_sub (A p : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun s : ℂ => A / (s - p)) p := by
  by_cases hA : A = 0
  · have htop : meromorphicOrderAt (fun s : ℂ => A / (s - p)) p = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards with q
      simp [hA]
    rw [htop]
    exact le_top
  · rw [meromorphicOrderAt_const_div_sub_eq hA]

/-- If `h` is analytic off a finite set `P` and `h - A p / (· - p)` is bounded near `p ∈ P`, then
on a punctured neighbourhood of `p` the function `h` is an analytic function plus
`A p / (· - p)`. -/
private lemma exists_analyticAt_add_principalPart {U : Set ℂ} (hU : IsOpen U) {P : Finset ℂ}
    {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (U \ (P : Set ℂ))) {A : ℂ → ℂ} {p : ℂ} (hpU : p ∈ U)
    (hA : ∃ V ∈ nhds p, BddAbove (norm ∘ (h - fun s => A p / (s - p)) '' (V \ {p}))) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      h =ᶠ[nhdsWithin p {p}ᶜ] (g + fun s => A p / (s - p)) := by
  classical
  obtain ⟨V, hV, hbdd⟩ := hA
  obtain ⟨V₀, hV₀V, hV₀open, hpV₀⟩ := mem_nhds_iff.mp hV
  have hWopen : IsOpen (U \ ((P.erase p : Finset ℂ) : Set ℂ)) :=
    hU.sdiff (P.erase p).finite_toSet.isClosed
  have hpW : p ∈ U \ ((P.erase p : Finset ℂ) : Set ℂ) := ⟨hpU, by simp⟩
  set W : Set ℂ := V₀ ∩ (U \ ((P.erase p : Finset ℂ) : Set ℂ)) with hW
  have hWo : IsOpen W := hV₀open.inter hWopen
  have hpWm : p ∈ W := ⟨hpV₀, hpW⟩
  have hd : HolomorphicOn (h - fun s => A p / (s - p)) (W \ {p}) := by
    intro z hz
    have hzne : z ≠ p := hz.2
    have hzU : z ∈ U \ (P : Set ℂ) := by
      refine ⟨hz.1.2.1, fun hzP => ?_⟩
      exact hz.1.2.2 (by simp [hzne, hzP])
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.sub
      (hh z hzU).differentiableAt ?_)
    exact DifferentiableAt.div (differentiableAt_const _) (by fun_prop) (sub_ne_zero.mpr hzne)
  have hb : BddAbove (norm ∘ (h - fun s => A p / (s - p)) '' (W \ {p})) :=
    hbdd.mono (Set.image_mono (Set.sdiff_subset_sdiff_left
      (fun x hx => hV₀V hx.1)))
  obtain ⟨g, hgHolo, hgEq⟩ := existsDifferentiableOn_of_bddAbove (hWo.mem_nhds hpWm) hd hb
  refine ⟨g, hgHolo.analyticOnNhd hWo p hpWm, ?_⟩
  have hmem : W \ {p} ∈ nhdsWithin p {p}ᶜ := by
    rw [Set.sdiff_eq, Set.inter_comm]
    exact inter_mem_nhdsWithin _ (hWo.mem_nhds hpWm)
  filter_upwards [hmem] with z hz
  have := hgEq hz
  simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
  rw [← this]
  ring

/-- `sumResiduesIn`, a `tsum` over a subtype, as a `Finset` sum. -/
private lemma sumResiduesIn_eq_finset_sum {F : ℂ → ℂ} {S : Set ℂ} (Sfin : Finset ℂ)
    (hEq : S = (Sfin : Set ℂ)) : sumResiduesIn F S = ∑ q ∈ Sfin, residue F q := by
  rw [sumResiduesIn, hEq, tsum_fintype, ← Finset.sum_coe_sort Sfin]
  rfl

/-- **The residue theorem on a rectangle.** If `h` is analytic on an open `U` containing the closed
rectangle `K` except at the points of a finite `P` interior to `K`, and at each `p ∈ P` the
difference `h - A p / (· - p)` is bounded on a punctured neighbourhood, then
`J (h; a, b, c, d) = 2 π i ∑_{p ∈ P} A p`. -/
@[zz_tag "lem_rect_residue"]
theorem rectangleIntegral_eq_two_pi_I_mul_sum_residues {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {U : Set ℂ} (hU : IsOpen U)
    (hKU : {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ c ≤ s.im ∧ s.im ≤ d} ⊆ U) {P : Finset ℂ}
    (hP : ∀ p ∈ P, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (U \ (P : Set ℂ))) {A : ℂ → ℂ}
    (hA : ∀ p ∈ P, ∃ V ∈ nhds p, BddAbove (norm ∘ (h - fun s => A p / (s - p)) '' (V \ {p}))) :
    RectangleIntegral h ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (d : ℂ) * I) =
      2 * (Real.pi : ℂ) * I * ∑ p ∈ P, A p := by
  classical
  set z : ℂ := (a : ℂ) + (c : ℂ) * I with hz
  set w : ℂ := (b : ℂ) + (d : ℂ) * I with hw
  have hR : Rectangle z w = {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ c ≤ s.im ∧ s.im ≤ d} :=
    rectangle_eq_setOf hab.le hcd.le
  have hPR : ∀ p ∈ P, p ∈ Rectangle z w := fun p hp => by
    obtain ⟨h1, h2, h3, h4⟩ := hP p hp
    rw [hR]
    exact ⟨h1.le, h2.le, h3.le, h4.le⟩
  have hloc : ∀ p ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      h =ᶠ[nhdsWithin p {p}ᶜ] (g + fun s => A p / (s - p)) := fun p hp =>
    exists_analyticAt_add_principalPart hU hh (hKU (by rw [← hR]; exact hPR p hp)) (hA p hp)
  have hoff : ∀ q ∈ Rectangle z w, q ∉ P → AnalyticAt ℂ h q := fun q hq hqP =>
    hh q ⟨hKU (hR ▸ hq), by simpa using hqP⟩
  have hmeroP : ∀ p ∈ P, MeromorphicAt h p := by
    intro p hp
    obtain ⟨g, hg, heq⟩ := hloc p hp
    exact ((hg.meromorphicAt.add (by fun_prop)).congr heq.symm)
  have hmero : MeromorphicOn h (Rectangle z w) := by
    intro q hq
    by_cases hqP : q ∈ P
    · exact hmeroP q hqP
    · exact (hoff q hq hqP).meromorphicAt
  have hsimple : HasSimplePolesOn h (Rectangle z w) := by
    intro q hq
    by_cases hqP : q ∈ P
    · obtain ⟨g, hg, heq⟩ := hloc q hqP
      rw [meromorphicOrderAt_congr heq]
      refine le_trans ?_ (meromorphicOrderAt_add hg.meromorphicAt (by fun_prop))
      exact le_min (neg_one_le_zero_withTop.trans hg.meromorphicOrderAt_nonneg)
        (meromorphicOrderAt_const_div_sub (A q) q)
    · exact neg_one_le_zero_withTop.trans (hoff q hq hqP).meromorphicOrderAt_nonneg
  have hnonneg : ∀ q ∈ Rectangle z w, q ∉ P → ¬ meromorphicOrderAt h q < 0 := by
    intro q hq hqP
    exact not_lt_of_ge (hoff q hq hqP).meromorphicOrderAt_nonneg
  have hsub : Rectangle z w ∩ {q | meromorphicOrderAt h q < 0} ⊆ (P : Set ℂ) := by
    intro q hq
    by_contra hqP
    exact hnonneg q hq.1 (by simpa using hqP) hq.2
  have hSfin : (Rectangle z w ∩ {q | meromorphicOrderAt h q < 0}).Finite :=
    P.finite_toSet.subset hsub
  have hdisj : Disjoint (RectangleBorder z w) {q : ℂ | meromorphicOrderAt h q < 0} := by
    rw [Set.disjoint_right]
    intro q hq hqb
    have hqR : q ∈ Rectangle z w := rectangleBorder_subset_rectangle z w hqb
    refine hnonneg q hqR (fun hqP => ?_) hq
    obtain ⟨h1, h2, h3, h4⟩ := hP q hqP
    rcases mem_rectangleBorder_cases hqb with he | he | he | he
    · rw [he] at h1; exact absurd h1 (lt_irrefl a)
    · rw [he] at h2; exact absurd h2 (lt_irrefl b)
    · rw [he] at h3; exact absurd h3 (lt_irrefl c)
    · rw [he] at h4; exact absurd h4 (lt_irrefl d)
  have hres : ∀ p ∈ P, residue h p = A p := by
    intro p hp
    obtain ⟨g, hg, heq⟩ := hloc p hp
    refine residue_eq_of_tendsto ?_
    have h0 : Filter.Tendsto (fun q : ℂ => q - p) (nhdsWithin p {p}ᶜ) (nhds 0) := by
      have hc : Filter.Tendsto (fun q : ℂ => q - p) (nhds p) (nhds (p - p)) :=
        (continuous_id.sub continuous_const).tendsto p
      rw [sub_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have h1 : Filter.Tendsto (fun q : ℂ => (q - p) * g q + A p) (nhdsWithin p {p}ᶜ)
        (nhds (0 * g p + A p)) :=
      (h0.mul (hg.continuousAt.continuousWithinAt.tendsto)).add tendsto_const_nhds
    rw [zero_mul, zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [heq, self_mem_nhdsWithin] with q hq hqne
    rw [hq]
    simp only [Pi.add_apply]
    have hqp : q - p ≠ 0 := sub_ne_zero.mpr hqne
    field_simp
  have hAzero : ∀ p ∈ P, p ∉ hSfin.toFinset → A p = 0 := by
    intro p hp hpn
    by_contra hApos
    have hge : ¬ meromorphicOrderAt h p < 0 := by
      intro hlt
      exact hpn (Set.Finite.mem_toFinset _ |>.mpr ⟨hPR p hp, hlt⟩)
    obtain ⟨g, hg, heq⟩ := hloc p hp
    have hev : (fun s : ℂ => A p / (s - p)) =ᶠ[nhdsWithin p {p}ᶜ] h + (-g) := by
      filter_upwards [heq] with q hq
      simp only [Pi.add_apply, Pi.neg_apply] at hq ⊢
      rw [hq]
      ring
    have hone : meromorphicOrderAt (fun s : ℂ => A p / (s - p)) p = (-1 : ℤ) :=
      meromorphicOrderAt_const_div_sub_eq hApos
    rw [meromorphicOrderAt_congr hev] at hone
    have hle : (0 : WithTop ℤ) ≤ meromorphicOrderAt (h + (-g)) p := by
      refine le_trans (le_min (not_lt.mp hge) ?_)
        (meromorphicOrderAt_add (hmeroP p hp) hg.neg.meromorphicAt)
      exact hg.neg.meromorphicOrderAt_nonneg
    rw [hone, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
      WithTop.coe_le_coe] at hle
    norm_num at hle
  have key := RectangleIntegral'_eq_sumResiduesIn (f := h) (z := z) (w := w)
    (by simp [hz, hw, hab.le]) (by simp [hz, hw, hcd.le]) hmero hdisj hSfin hsimple
  rw [sumResiduesIn_eq_finset_sum hSfin.toFinset hSfin.coe_toFinset.symm] at key
  rw [Finset.sum_congr rfl fun q hq =>
    hres q (by simpa using hsub ((Set.Finite.mem_toFinset _).mp hq))] at key
  rw [Finset.sum_subset (fun q hq => by simpa using hsub ((Set.Finite.mem_toFinset _).mp hq))
    hAzero] at key
  rw [RectangleIntegral', smul_eq_mul] at key
  field_simp at key
  rw [key]

/-! ## The argument principle on a rectangle -/

/-- `WithTop.untop₀` of the integer image of an `ℕ∞`, which is `ENat.toNat`, junk values
included: `⊤` goes to `0` on both sides. -/
private lemma untop_zero_map_natCast (x : ℕ∞) :
    ((x.map (Nat.cast : ℕ → ℤ)).untop₀) = (x.toNat : ℤ) := by
  cases x with
  | top => simp
  | coe n => simp

/-- A function with finitely many zeros in a non-degenerate closed rectangle does not vanish
identically near any of its points. -/
private lemma not_eventually_eq_zero_of_zeros_finite {a b c d : ℝ} (hab : a < b)
    {f : ℂ → ℂ}
    (hZ : {ρ : ℂ | (a ≤ ρ.re ∧ ρ.re ≤ b ∧ c ≤ ρ.im ∧ ρ.im ≤ d) ∧ f ρ = 0}.Finite)
    {p : ℂ} (hp : a ≤ p.re ∧ p.re ≤ b ∧ c ≤ p.im ∧ p.im ≤ d) :
    ¬ ∀ᶠ z in nhds p, f z = 0 := by
  intro hev
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨σ, hσ, δ, hδ, hmem⟩ : ∃ σ : ℝ, σ ≠ 0 ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (a ≤ (p + ((σ * t : ℝ) : ℂ)).re ∧ (p + ((σ * t : ℝ) : ℂ)).re ≤ b ∧
        c ≤ (p + ((σ * t : ℝ) : ℂ)).im ∧ (p + ((σ * t : ℝ) : ℂ)).im ≤ d) ∧
      dist (p + ((σ * t : ℝ) : ℂ)) p < ε := by
    obtain ⟨h1, h2, h3, h4⟩ := hp
    rcases lt_or_ge p.re b with h | h
    · refine ⟨1, one_ne_zero, min ε (b - p.re), lt_min hε (by linarith), fun t ht ht' => ?_⟩
      have e1 : t < ε := lt_of_lt_of_le ht' (min_le_left _ _)
      have e2 : t < b - p.re := lt_of_lt_of_le ht' (min_le_right _ _)
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, one_mul, add_zero] <;>
        first | linarith | (rw [Real.norm_eq_abs, abs_of_pos ht]; linarith)
    · refine ⟨-1, by norm_num, min ε (p.re - a), lt_min hε (by linarith), fun t ht ht' => ?_⟩
      have e1 : t < ε := lt_of_lt_of_le ht' (min_le_left _ _)
      have e2 : t < p.re - a := lt_of_lt_of_le ht' (min_le_right _ _)
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, neg_one_mul, add_zero] <;>
        first | linarith | (rw [Real.norm_eq_abs, abs_of_neg (by linarith : -t < 0)]; linarith)
  have hinj : InjOn (fun t : ℝ => p + ((σ * t : ℝ) : ℂ)) (Ioo 0 δ) := by
    intro t₁ _ t₂ _ he
    have : (σ * t₁ : ℝ) = (σ * t₂ : ℝ) := by
      exact_mod_cast add_left_cancel he
    exact mul_left_cancel₀ hσ this
  refine (((Set.Ioo_infinite hδ).image hinj).mono ?_) hZ
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨(hmem t ht.1 ht.2).1, hball (hmem t ht.1 ht.2).2⟩

/-- **The argument principle on a rectangle.** For `f` analytic on a set containing the closed
rectangle `K`, non-vanishing on the border of `K` and with only finitely many zeros in `K`,
`J (f' / f; a, b, c, d) = 2 π i ∑_{ρ} ord_ρ f`, the sum over the zeros of `f` in `K`. -/
@[zz_tag "lem_rect_arg_principle"]
theorem rectangleIntegral_logDeriv_eq_sum_analyticOrderNatAt {a b c d : ℝ} (hab : a < b)
    (hcd : c < d) {U : Set ℂ} (hKU : {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ c ≤ s.im ∧ s.im ≤ d} ⊆ U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hbdry : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → c ≤ s.im → s.im ≤ d →
      s.re = a ∨ s.re = b ∨ s.im = c ∨ s.im = d → f s ≠ 0)
    (hZ : {ρ : ℂ | (a ≤ ρ.re ∧ ρ.re ≤ b ∧ c ≤ ρ.im ∧ ρ.im ≤ d) ∧ f ρ = 0}.Finite) :
    RectangleIntegral (logDeriv f) ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (d : ℂ) * I) =
      2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hZ.toFinset, (analyticOrderNatAt f ρ : ℂ) := by
  classical
  set z : ℂ := (a : ℂ) + (c : ℂ) * I with hz
  set w : ℂ := (b : ℂ) + (d : ℂ) * I with hw
  have hR : Rectangle z w = {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ c ≤ s.im ∧ s.im ≤ d} :=
    rectangle_eq_setOf hab.le hcd.le
  have hRU : Rectangle z w ⊆ U := by rw [hR]; exact hKU
  have hfR : AnalyticOnNhd ℂ f (Rectangle z w) := hf.mono hRU
  have hmero : MeromorphicOn f (Rectangle z w) := hfR.meromorphicOn
  have hlog : MeromorphicOn (logDeriv f) (Rectangle z w) := hmero.logDeriv
  have htop : ∀ p ∈ Rectangle z w, analyticOrderAt f p ≠ ⊤ := by
    intro p hp
    simp only [ne_eq, analyticOrderAt_eq_top]
    exact not_eventually_eq_zero_of_zeros_finite hab hZ (by rw [hR] at hp; exact hp)
  have hordne : ∀ p ∈ Rectangle z w, meromorphicOrderAt f p ≠ ⊤ := by
    intro p hp hcon
    rw [(hfR p hp).meromorphicOrderAt_eq] at hcon
    refine htop p hp ?_
    cases h : analyticOrderAt f p with
    | top => rfl
    | coe n => rw [h] at hcon; simp at hcon
  have hzero : ∀ p ∈ Rectangle z w, f p ≠ 0 →
      MeromorphicOn.divisor f (Rectangle z w) p = 0 := by
    intro p hp hfp
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfR hp,
      (hfR p hp).analyticOrderAt_eq_zero.2 hfp]
    simp
  have hnb : Disjoint (RectangleBorder z w)
      (MeromorphicOn.divisor f (Rectangle z w)).support := by
    rw [Set.disjoint_right]
    intro p hp hpb
    have hpR : p ∈ Rectangle z w := rectangleBorder_subset_rectangle z w hpb
    have hpK : a ≤ p.re ∧ p.re ≤ b ∧ c ≤ p.im ∧ p.im ≤ d := by rw [hR] at hpR; exact hpR
    exact hp (hzero p hpR
      (hbdry p hpK.1 hpK.2.1 hpK.2.2.1 hpK.2.2.2 (mem_rectangleBorder_cases hpb)))
  have hsupp : (MeromorphicOn.divisor f (Rectangle z w)).support
      = {ρ : ℂ | (a ≤ ρ.re ∧ ρ.re ≤ b ∧ c ≤ ρ.im ∧ ρ.im ≤ d) ∧ f ρ = 0} := by
    ext p
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · have hpR : p ∈ Rectangle z w :=
        (MeromorphicOn.divisor f (Rectangle z w)).supportWithinDomain hp
      refine ⟨by rw [hR] at hpR; exact hpR, ?_⟩
      by_contra hfp
      exact hp (hzero p hpR hfp)
    · have hpR : p ∈ Rectangle z w := by rw [hR]; exact hp.1
      have hne : analyticOrderAt f p ≠ 0 := fun h =>
        ((hfR p hpR).analyticOrderAt_eq_zero.1 h) hp.2
      intro hcon
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfR hpR, untop_zero_map_natCast] at hcon
      have hz0 : (analyticOrderAt f p).toNat = 0 := by exact_mod_cast hcon
      rcases ENat.toNat_eq_zero.mp hz0 with h | h
      · exact hne h
      · exact htop p hpR h
  have hval : ∀ p ∈ Rectangle z w,
      ((MeromorphicOn.divisor f (Rectangle z w) p : ℤ) : ℂ)
        = (analyticOrderNatAt f p : ℂ) := by
    intro p hp
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfR hp, untop_zero_map_natCast,
      analyticOrderNatAt]
    push_cast
    ring
  have key := rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt (z := z) (w := w)
    (by simp [hz, hw, hab.le]) (by simp [hz, hw, hcd.le]) hmero hlog hordne hnb
  have hfs : (divisor_support_rectangle_finite f z w).toFinset = hZ.toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, hsupp]
  rw [hfs] at key
  rw [Finset.sum_congr rfl fun p hp => hval p
    (by rw [hR]; exact ((Set.Finite.mem_toFinset _).mp hp).1)] at key
  rw [RectangleIntegral', smul_eq_mul] at key
  have hne2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp at key
  rw [key]

/-! ## The three pieces of the fold -/

/-- Conjugation commutes with the interval integral. -/
private lemma intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    (∫ x in a..b, (starRingEnd ℂ) (f x)) = (starRingEnd ℂ) (∫ x in a..b, f x) := by
  simp only [intervalIntegral, map_sub, integral_conj]

/-- `ξ' / ξ` is real at a real point. -/
private lemma conj_logDeriv_riemannXi_ofReal (x : ℝ) :
    (starRingEnd ℂ) (logDeriv riemannXi (x : ℂ)) = logDeriv riemannXi (x : ℂ) := by
  rw [logDeriv_apply, map_div₀, ← deriv_riemannXi_conj, ← riemannXi_conj, Complex.conj_ofReal]

/-- The reflection identity at a real point: `(ξ' / ξ) (1 - x) = - (ξ' / ξ) (x)`. -/
private lemma logDeriv_riemannXi_one_sub_ofReal (x : ℝ) :
    logDeriv riemannXi ((1 - x : ℝ) : ℂ) = -logDeriv riemannXi (x : ℂ) := by
  have h : (1 : ℂ) - (starRingEnd ℂ) ((x : ℝ) : ℂ) = ((1 - x : ℝ) : ℂ) := by
    rw [Complex.conj_ofReal]; push_cast; ring
  rw [← h, logDeriv_riemannXi_one_sub_conj, conj_logDeriv_riemannXi_ofReal]

/-- **The bottom side vanishes:** `∫_{-1}^{2} (ξ' / ξ) (x) dx = 0`. -/
@[zz_tag "lem_fold_bottom"]
theorem integral_logDeriv_riemannXi_bottom_eq_zero :
    (∫ x in (-1 : ℝ)..2, logDeriv riemannXi (x : ℂ)) = 0 := by
  set F : ℝ → ℂ := fun x : ℝ => logDeriv riemannXi (x : ℂ) with hF
  have hsub := intervalIntegral.integral_comp_sub_left (a := (-1 : ℝ)) (b := (2 : ℝ)) F 1
  rw [show (1 : ℝ) - 2 = -1 by norm_num, show (1 : ℝ) - (-1) = 2 by norm_num] at hsub
  have hneg : ∀ x : ℝ, F (1 - x) = -F x := fun x => logDeriv_riemannXi_one_sub_ofReal x
  rw [show (∫ x in (-1 : ℝ)..2, F (1 - x)) = -∫ x in (-1 : ℝ)..2, F x by
    simp only [hneg, intervalIntegral.integral_neg]] at hsub
  exact self_eq_neg.mp hsub.symm

/-- **The left side is minus the conjugate of the right side**, for every real `T`. -/
@[zz_tag "lem_fold_sides"]
theorem integral_logDeriv_riemannXi_left_eq (T : ℝ) :
    (∫ t in (0 : ℝ)..T, logDeriv riemannXi (-1 + t * I)) =
      -(starRingEnd ℂ) (∫ t in (0 : ℝ)..T, logDeriv riemannXi (2 + t * I)) := by
  have hpt : ∀ t : ℝ, logDeriv riemannXi (-1 + t * I)
      = (starRingEnd ℂ) (-logDeriv riemannXi (2 + t * I)) := by
    intro t
    have hc : (starRingEnd ℂ) ((2 : ℂ) + (t : ℂ) * I) = 2 - (t : ℂ) * I := by
      simp [Complex.ext_iff]
    have h : (1 : ℂ) - (starRingEnd ℂ) ((2 : ℂ) + (t : ℂ) * I) = -1 + (t : ℂ) * I := by
      rw [hc]; ring
    rw [← h, logDeriv_riemannXi_one_sub_conj, map_neg]
  simp only [hpt, intervalIntegral_conj, map_neg, intervalIntegral.integral_neg]

/-- **The two halves of the top side.** For every real `T`, the integral of `ξ' / ξ` along the
left half `[-1, 1/2] + iT` of the top side is minus the conjugate of the integral along the right
half `[1/2, 2] + iT`. -/
@[zz_tag "lem_fold_top"]
theorem integral_logDeriv_riemannXi_top_left_eq (T : ℝ) :
    (∫ x in (-1 : ℝ)..(1 / 2 : ℝ), logDeriv riemannXi (x + T * I)) =
      -(starRingEnd ℂ) (∫ x in (1 / 2 : ℝ)..2, logDeriv riemannXi (x + T * I)) := by
  set F : ℝ → ℂ := fun x : ℝ => logDeriv riemannXi ((x : ℂ) + T * I) with hF
  have hsub := intervalIntegral.integral_comp_sub_left (a := (1 / 2 : ℝ)) (b := (2 : ℝ)) F 1
  rw [show (1 : ℝ) - 2 = -1 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hsub
  have hpt : ∀ y : ℝ, F (1 - y) = (starRingEnd ℂ) (-F y) := by
    intro y
    have hc : (starRingEnd ℂ) ((y : ℂ) + (T : ℂ) * I) = (y : ℂ) - (T : ℂ) * I := by
      simp [Complex.ext_iff]
    have h : (1 : ℂ) - (starRingEnd ℂ) ((y : ℂ) + (T : ℂ) * I)
        = ((1 - y : ℝ) : ℂ) + (T : ℂ) * I := by
      rw [hc]; push_cast; ring
    simp only [hF]
    rw [← h, logDeriv_riemannXi_one_sub_conj, map_neg]
  rw [← hsub]
  simp only [hpt, intervalIntegral_conj, map_neg, intervalIntegral.integral_neg]

/-! ## Folding the boundary integral -/

/-- For complex `u` and `v`, `0 + i u - (-conj v + v) - i (-conj u) = 2 i im (i u - v)`. -/
private lemma fold_algebra (u v : ℂ) :
    (0 : ℂ) + I * u - (-(starRingEnd ℂ) v + v) - I * (-(starRingEnd ℂ) u)
      = 2 * I * (((I * u - v).im : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp [Complex.mul_re, Complex.mul_im]
  · simp [Complex.mul_re, Complex.mul_im]
    ring

/-- `ξ'` is continuous, `ξ` being entire. -/
private lemma continuous_deriv_riemannXi : Continuous (deriv riemannXi) := by
  have h : AnalyticOnNhd ℂ riemannXi univ :=
    differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ
  rw [← continuousOn_univ]
  exact h.deriv.continuousOn

/-- `ξ' / ξ` is continuous on the top side `[-1, 2] + iT` of the counting rectangle at a good
height `T ≥ 0`. -/
private lemma continuousOn_logDeriv_riemannXi_top {T : ℝ} (hT : IsGoodHeight T) (hT0 : 0 ≤ T) :
    ContinuousOn (fun x : ℝ => logDeriv riemannXi ((x : ℂ) + T * I)) (Icc (-1) 2) := by
  have hg : Continuous fun x : ℝ => ((x : ℂ) + (T : ℂ) * I) := by fun_prop
  simp only [logDeriv_apply]
  refine ContinuousOn.div ((continuous_deriv_riemannXi.comp hg).continuousOn)
    ((differentiable_riemannXi.continuous.comp hg).continuousOn) fun x hx => ?_
  refine riemannXi_ne_zero_of_mem_rectangleBoundary hT ⟨?_, ?_, ?_, ?_⟩
    (Or.inr (Or.inr (Or.inr ?_))) <;> simp [hx.1, hx.2, hT0]

/-- **Folding the boundary integral:** for a good height `T ≥ 0`,
`J (ξ' / ξ; -1, 2, 0, T) = 2 i im I (ξ' / ξ; T)`. -/
@[zz_tag "lem_rect_fold"]
theorem rectangleIntegral_logDeriv_riemannXi_eq {T : ℝ} (hT : IsGoodHeight T) (hT0 : 0 ≤ T) :
    RectangleIntegral (logDeriv riemannXi) (-1) (2 + T * I) =
      2 * I * (((foldedPathIntegral (logDeriv riemannXi) T).im : ℝ) : ℂ) := by
  have hbridge := rectangleIntegral_eq_boundary_integrals (logDeriv riemannXi) (-1) 2 0 T
  norm_num at hbridge
  have hcont := continuousOn_logDeriv_riemannXi_top hT hT0
  have hsplit : (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + T * I))
      = (∫ x in (-1 : ℝ)..(1 / 2 : ℝ), logDeriv riemannXi ((x : ℂ) + T * I))
        + ∫ x in (1 / 2 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + T * I) := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · refine (hcont.mono ?_).intervalIntegrable
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1 / 2)]
      exact Icc_subset_Icc le_rfl (by norm_num)
    · refine (hcont.mono ?_).intervalIntegrable
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
      exact Icc_subset_Icc (by norm_num) le_rfl
  rw [hbridge, hsplit, integral_logDeriv_riemannXi_bottom_eq_zero,
    integral_logDeriv_riemannXi_left_eq, integral_logDeriv_riemannXi_top_left_eq,
    foldedPathIntegral]
  exact fold_algebra _ _

end ZetaZeros
