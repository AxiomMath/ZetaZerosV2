/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import ZetaZeros.ZeroCount.Backlund
public import ZetaZeros.ZeroCount.GoodHeight

/-!
# Argument variation along a segment

The elementary estimates that turn a count of the sign changes of `re ζ` into a bound for the
variation of `arg ζ`, and the two contributions -- vertical and horizontal -- to the argument
integral along the folded contour.

If `G` is analytic and non-vanishing near a real segment `[a, b]` and `re G` has constant sign
`ε` on the interior, then `x ↦ Log (ε G(x))` is a primitive of `G'/G` on the closed segment, and
the imaginary part of `∫_a^b G'/G` is a difference of two principal arguments in `[-π/2, π/2]`,
hence at most `π` in absolute value. With `n` sign changes the bound becomes `(n + 1) π`.

## Main results

* `ZetaZeros.abs_im_integral_logDeriv_le_pi`: where `re G` has constant sign, the variation of
  `arg G` across the segment is at most `π`.
* `ZetaZeros.abs_im_integral_logDeriv_le`: with `n` sign changes it is at most `(n + 1) π`.
* `ZetaZeros.abs_im_mul_I_integral_logDeriv_riemannZeta_le_pi_div_two`: the vertical
  contribution is at most `π/2`.
* `ZetaZeros.exists_abs_im_integral_logDeriv_riemannZeta_le_mul_log`: the horizontal contribution
  is `O(log T)` at a good height.
-/

@[expose] public section

namespace ZetaZeros

open Complex MeasureTheory

/-! ### Two calculus preliminaries -/

/-- The chain rule for `Log ∘ f` for a curve `f : ℝ → ℂ` in the slit plane. -/
private lemma hasDerivAt_log_comp {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x)
    (h : f x ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℝ => Complex.log (f t)) (f' / f x) x := by
  simpa [Function.comp_def, div_eq_mul_inv] using (Complex.hasDerivAt_log h).scomp x hf

/-- `G'/G` pulled back along a curve is continuous wherever the curve is continuous, stays in the
domain of analyticity of `G`, and avoids the zeros of `G`. -/
private lemma continuousOn_logDeriv_comp {W : Set ℂ} {G : ℂ → ℂ} {γ : ℝ → ℂ} {s : Set ℝ}
    (hG : AnalyticOnNhd ℂ G W) (hγ : ContinuousOn γ s) (hmem : ∀ t ∈ s, γ t ∈ W)
    (hne : ∀ t ∈ s, G (γ t) ≠ 0) : ContinuousOn (fun t : ℝ => logDeriv G (γ t)) s := by
  have hmaps : Set.MapsTo γ s W := hmem
  exact (hG.deriv.continuousOn.comp hγ hmaps).div (hG.continuousOn.comp hγ hmaps) hne

/-- A continuous real function that does not vanish on an open interval has constant sign there,
and the sign is weak at the endpoints. -/
private lemma exists_sign_of_continuousOn {a b : ℝ} {u : ℝ → ℝ} (hab : a < b)
    (hcont : ContinuousOn u (Set.Icc a b)) (hne : ∀ x ∈ Set.Ioo a b, u x ≠ 0) :
    ∃ ε : ℝ, ε ≠ 0 ∧ ∀ x ∈ Set.Icc a b, 0 ≤ ε * u x := by
  set m : ℝ := (a + b) / 2 with hmdef
  have hm : m ∈ Set.Ioo a b := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  set ε : ℝ := if 0 < u m then 1 else -1 with hεdef
  have hεne : ε ≠ 0 := by rw [hεdef]; split_ifs <;> norm_num
  have hεm : 0 < ε * u m := by
    rw [hεdef]
    split_ifs with h
    · simpa using h
    · have h' : u m < 0 := lt_of_le_of_ne (not_lt.1 h) (hne m hm)
      simpa using h'
  set v : ℝ → ℝ := fun t => ε * u t with hvdef
  have hvcont : ContinuousOn v (Set.Icc a b) := continuousOn_const.mul hcont
  have hpos : ∀ x ∈ Set.Ioo a b, 0 < v x := by
    intro x hx
    by_contra hcon
    have hvx : v x < 0 := lt_of_le_of_ne (not_lt.1 hcon) (mul_ne_zero hεne (hne x hx))
    have hsub : Set.uIcc x m ⊆ Set.Ioo a b := Set.ordConnected_Ioo.uIcc_subset hx hm
    have hcv : ContinuousOn v (Set.uIcc x m) := hvcont.mono (hsub.trans Set.Ioo_subset_Icc_self)
    obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc hcv (Set.mem_uIcc.2 (Or.inl ⟨hvx.le, hεm.le⟩))
    exact hne c (hsub hc) ((mul_eq_zero.1 hc0).resolve_left hεne)
  refine ⟨ε, hεne, fun y hy => ?_⟩
  have hnb : (nhdsWithin y (Set.Ioo a b)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_Ioo hab.ne]; exact hy)
  exact ge_of_tendsto ((hvcont y hy).mono Set.Ioo_subset_Icc_self)
    (eventually_nhdsWithin_of_forall fun x hx => (hpos x hx).le)

/-! ### Argument variation where the real part has constant sign -/

/-- **Argument variation where the real part has constant sign.** If `G` is analytic and
non-vanishing on a set `W` containing the real segment `[a, b]`, and `re G` does not vanish on the
open interval, then the variation of `arg G` across the segment is at most `π`:
`|im ∫_a^b (G'/G)(x) dx| ≤ π`. -/
@[zz_tag "lem_arg_var_halfplane"]
theorem abs_im_integral_logDeriv_le_pi {a b : ℝ} {W : Set ℂ} {G : ℂ → ℂ} (hab : a < b)
    (hseg : ∀ x ∈ Set.Icc a b, ((x : ℝ) : ℂ) ∈ W) (hG : AnalyticOnNhd ℂ G W)
    (hGne : ∀ z ∈ W, G z ≠ 0) (hre : ∀ x ∈ Set.Ioo a b, (G (x : ℂ)).re ≠ 0) :
    |(∫ x in a..b, logDeriv G (x : ℂ)).im| ≤ Real.pi := by
  have hmaps : Set.MapsTo (fun x : ℝ => ((x : ℝ) : ℂ)) (Set.Icc a b) W := hseg
  have hGc : ContinuousOn (fun x : ℝ => G (x : ℂ)) (Set.Icc a b) :=
    hG.continuousOn.comp Complex.continuous_ofReal.continuousOn hmaps
  have hcont : ContinuousOn (fun x : ℝ => logDeriv G (x : ℂ)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact continuousOn_logDeriv_comp hG Complex.continuous_ofReal.continuousOn hseg
      fun x hx => hGne _ (hseg x hx)
  obtain ⟨ε, hεne, hsign⟩ :=
    exists_sign_of_continuousOn (u := fun x : ℝ => (G (x : ℂ)).re) hab
      (Complex.continuous_re.comp_continuousOn hGc) hre
  have hεne' : (ε : ℂ) ≠ 0 := by exact_mod_cast hεne
  have hslit : ∀ x ∈ Set.Icc a b, (ε : ℂ) * G (x : ℂ) ∈ Complex.slitPlane := by
    intro x hx
    have h1 : 0 ≤ ((ε : ℂ) * G (x : ℂ)).re := by simpa using hsign x hx
    rcases eq_or_lt_of_le h1 with h | h
    · exact Complex.mem_slitPlane_iff.2 <| Or.inr fun him =>
        mul_ne_zero hεne' (hGne _ (hseg x hx)) (Complex.ext h.symm him)
    · exact Complex.mem_slitPlane_iff.2 (Or.inl h)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log ((ε : ℂ) * G (t : ℂ))) (logDeriv G (x : ℂ)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    have hd : HasDerivAt (fun t : ℝ => G (t : ℂ)) (deriv G (x : ℂ)) x :=
      ((hG _ (hseg x hx)).differentiableAt.hasDerivAt).comp_ofReal
    have h2 := hasDerivAt_log_comp (hd.const_mul ((ε : ℂ))) (hslit x hx)
    have hGx : G (x : ℂ) ≠ 0 := hGne _ (hseg x hx)
    have hkey : (ε : ℂ) * deriv G (x : ℂ) / ((ε : ℂ) * G (x : ℂ)) = logDeriv G (x : ℂ) := by
      simp only [logDeriv, Pi.div_apply]
      field_simp
    rwa [hkey] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
    Complex.sub_im, Complex.log_im, Complex.log_im]
  have hb : |((ε : ℂ) * G (b : ℂ)).arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.2 (by simpa using hsign b (Set.right_mem_Icc.2 hab.le))
  have ha : |((ε : ℂ) * G (a : ℂ)).arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.2 (by simpa using hsign a (Set.left_mem_Icc.2 hab.le))
  calc |((ε : ℂ) * G (b : ℂ)).arg - ((ε : ℂ) * G (a : ℂ)).arg| ≤
        |((ε : ℂ) * G (b : ℂ)).arg| + |((ε : ℂ) * G (a : ℂ)).arg| := abs_sub _ _
    _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add hb ha
    _ = Real.pi := by ring

/-! ### Argument variation with finitely many sign changes -/

/-- The bound `(n + 1) π` on the argument variation, for any upper bound `n` on the number of
zeros of `re G` in the open interval. -/
private lemma abs_im_integral_logDeriv_le_aux {W : Set ℂ} {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G W)
    (hGne : ∀ z ∈ W, G z ≠ 0) :
    ∀ n : ℕ, ∀ a b : ℝ, a < b → (∀ x ∈ Set.Icc a b, ((x : ℝ) : ℂ) ∈ W) →
      {x : ℝ | x ∈ Set.Ioo a b ∧ (G (x : ℂ)).re = 0}.Finite →
      {x : ℝ | x ∈ Set.Ioo a b ∧ (G (x : ℂ)).re = 0}.ncard ≤ n →
      |(∫ x in a..b, logDeriv G (x : ℂ)).im| ≤ (n + 1) * Real.pi := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab hseg hE hEn
    set E : Set ℝ := {x : ℝ | x ∈ Set.Ioo a b ∧ (G (x : ℂ)).re = 0} with hEdef
    rcases Set.eq_empty_or_nonempty E with hemp | ⟨c, hc⟩
    · have h0 : ∀ x ∈ Set.Ioo a b, (G (x : ℂ)).re ≠ 0 := by
        intro x hx hzero
        have hxE : x ∈ E := ⟨hx, hzero⟩
        rw [hemp] at hxE
        exact Set.notMem_empty x hxE
      have hpi := abs_im_integral_logDeriv_le_pi hab hseg hG hGne h0
      nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) n]
    · obtain ⟨⟨hac, hcb⟩, hcz⟩ := hc
      set E₁ : Set ℝ := {x : ℝ | x ∈ Set.Ioo a c ∧ (G (x : ℂ)).re = 0} with hE₁def
      set E₂ : Set ℝ := {x : ℝ | x ∈ Set.Ioo c b ∧ (G (x : ℂ)).re = 0} with hE₂def
      have hs₁ : E₁ ⊆ E := fun x hx => ⟨⟨hx.1.1, hx.1.2.trans hcb⟩, hx.2⟩
      have hs₂ : E₂ ⊆ E := fun x hx => ⟨⟨hac.trans hx.1.1, hx.1.2⟩, hx.2⟩
      have hf₁ : E₁.Finite := hE.subset hs₁
      have hf₂ : E₂.Finite := hE.subset hs₂
      have hd : Disjoint E₁ E₂ :=
        Set.disjoint_left.2 fun x hx hx' => absurd (hx.1.2.trans hx'.1.1) (lt_irrefl x)
      have hdc : Disjoint (E₁ ∪ E₂) {c} := by
        refine Set.disjoint_right.2 fun x hx => ?_
        rw [Set.mem_singleton_iff] at hx
        rintro (h | h)
        · rw [hx] at h; exact absurd h.1.2 (lt_irrefl c)
        · rw [hx] at h; exact absurd h.1.1 (lt_irrefl c)
      have hsub : E₁ ∪ E₂ ∪ {c} ⊆ E := by
        refine Set.union_subset (Set.union_subset hs₁ hs₂) ?_
        rw [Set.singleton_subset_iff]
        exact ⟨⟨hac, hcb⟩, hcz⟩
      have hkey : E₁.ncard + E₂.ncard + 1 ≤ E.ncard := by
        have hu : (E₁ ∪ E₂ ∪ {c}).ncard = E₁.ncard + E₂.ncard + 1 := by
          rw [Set.ncard_union_eq hdc (hf₁.union hf₂) (Set.finite_singleton c),
            Set.ncard_union_eq hd hf₁ hf₂, Set.ncard_singleton]
        rw [← hu]
        exact Set.ncard_le_ncard hsub hE
      have hsegac : ∀ x ∈ Set.Icc a c, ((x : ℝ) : ℂ) ∈ W :=
        fun x hx => hseg x ⟨hx.1, hx.2.trans hcb.le⟩
      have hsegcb : ∀ x ∈ Set.Icc c b, ((x : ℝ) : ℂ) ∈ W :=
        fun x hx => hseg x ⟨hac.le.trans hx.1, hx.2⟩
      have hb₁ := ih _ (by omega : E₁.ncard < n) a c hac hsegac hf₁ le_rfl
      have hb₂ := ih _ (by omega : E₂.ncard < n) c b hcb hsegcb hf₂ le_rfl
      have hint₁ : IntervalIntegrable (fun x : ℝ => logDeriv G (x : ℂ)) volume a c :=
        (continuousOn_logDeriv_comp hG (Complex.continuous_ofReal.continuousOn
          (s := Set.uIcc a c)) (by rw [Set.uIcc_of_le hac.le]; exact hsegac)
          fun x hx => hGne _ (hsegac x (by rwa [Set.uIcc_of_le hac.le] at hx))).intervalIntegrable
      have hint₂ : IntervalIntegrable (fun x : ℝ => logDeriv G (x : ℂ)) volume c b :=
        (continuousOn_logDeriv_comp hG (Complex.continuous_ofReal.continuousOn
          (s := Set.uIcc c b)) (by rw [Set.uIcc_of_le hcb.le]; exact hsegcb)
          fun x hx => hGne _ (hsegcb x (by rwa [Set.uIcc_of_le hcb.le] at hx))).intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂, Complex.add_im]
      have htri := abs_add_le (∫ x in a..c, logDeriv G (x : ℂ)).im
        (∫ x in c..b, logDeriv G (x : ℂ)).im
      have hcast : (E₁.ncard : ℝ) + (E₂.ncard : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast hkey.trans hEn
      nlinarith [Real.pi_pos]

/-- **Argument variation with finitely many sign changes.** If `G` is analytic and non-vanishing on
a set `W` containing the real segment `[a, b]`, and `re G` vanishes at only finitely many points
of the open interval, then `|im ∫_a^b (G'/G)(x) dx| ≤ (n + 1) π`, where `n` is the number of those
points. -/
@[zz_tag "lem_arg_var_count"]
theorem abs_im_integral_logDeriv_le {a b : ℝ} {W : Set ℂ} {G : ℂ → ℂ} (hab : a < b)
    (hseg : ∀ x ∈ Set.Icc a b, ((x : ℝ) : ℂ) ∈ W) (hG : AnalyticOnNhd ℂ G W)
    (hGne : ∀ z ∈ W, G z ≠ 0)
    (hE : {x : ℝ | x ∈ Set.Ioo a b ∧ (G (x : ℂ)).re = 0}.Finite) :
    |(∫ x in a..b, logDeriv G (x : ℂ)).im| ≤
      ({x : ℝ | x ∈ Set.Ioo a b ∧ (G (x : ℂ)).re = 0}.ncard + 1) * Real.pi :=
  abs_im_integral_logDeriv_le_aux hG hGne _ a b hab hseg hE le_rfl

/-! ### The vertical contribution -/

/-- `ζ` is analytic away from its pole. -/
private lemma analyticOnNhd_riemannZeta : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := by
  have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  exact hd.analyticOnNhd isOpen_ne

/-- **The vertical contribution.** `|im (i ∫_0^T (ζ'/ζ)(2 + it) dt)| ≤ π/2`. -/
@[zz_tag "lem_vertical_bound"]
theorem abs_im_mul_I_integral_logDeriv_riemannZeta_le_pi_div_two (T : ℝ) :
    |(I * ∫ t in (0 : ℝ)..T, logDeriv riemannZeta (2 + (t : ℂ) * I)).im| ≤ Real.pi / 2 := by
  have hq : ∀ t : ℝ, 1 / 4 ≤ (riemannZeta ((2 : ℂ) + (t : ℂ) * I)).re :=
    fun t => one_quarter_le_riemannZeta_re (by simp)
  have hne1 : ∀ t : ℝ, (2 : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro t h
    have h2 := congrArg Complex.re h
    simp at h2
  have hpos : ∀ t : ℝ, 0 < (riemannZeta ((2 : ℂ) + (t : ℂ) * I)).re :=
    fun t => lt_of_lt_of_le (by norm_num) (hq t)
  have hzne : ∀ t : ℝ, riemannZeta ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h
    have h2 := hpos t
    rw [h] at h2
    simp at h2
  have hslit : ∀ t : ℝ, riemannZeta ((2 : ℂ) + (t : ℂ) * I) ∈ Complex.slitPlane :=
    fun t => Complex.mem_slitPlane_iff.2 (Or.inl (hpos t))
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) I t := by
    intro t
    have h1 := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I
    simpa using h1.const_add (2 : ℂ)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.log (riemannZeta (2 + (t : ℂ) * I)))
      (I * logDeriv riemannZeta (2 + (t : ℂ) * I)) t := by
    intro t
    have hz : HasDerivAt (fun t : ℝ => riemannZeta (2 + (t : ℂ) * I))
        (I • deriv riemannZeta (2 + (t : ℂ) * I)) t :=
      ((differentiableAt_riemannZeta (hne1 t)).hasDerivAt).scomp t (hγ t)
    have h2 := hasDerivAt_log_comp hz (hslit t)
    rw [smul_eq_mul] at h2
    convert h2 using 1
    simp only [logDeriv, Pi.div_apply, mul_div_assoc]
  have hcont : ContinuousOn (fun t : ℝ => logDeriv riemannZeta (2 + (t : ℂ) * I))
      (Set.uIcc 0 T) :=
    continuousOn_logDeriv_comp analyticOnNhd_riemannZeta (by fun_prop) (fun t _ => hne1 t)
      fun t _ => hzne t
  have hint : IntervalIntegrable (fun t : ℝ => I * logDeriv riemannZeta (2 + (t : ℂ) * I))
      volume 0 T := (continuousOn_const.mul hcont).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint,
    show (2 : ℂ) + ((0 : ℝ) : ℂ) * I = 2 by norm_num, Complex.sub_im, Complex.log_im,
    Complex.log_im, riemannZeta_two]
  have harg : ((Real.pi : ℂ) ^ 2 / 6).arg = 0 := by
    rw [show (Real.pi : ℂ) ^ 2 / 6 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.arg_ofReal_of_nonneg (by positivity)
  rw [harg, sub_zero]
  exact Complex.abs_arg_le_pi_div_two_iff.2 (hpos T).le

/-! ### The horizontal contribution -/

/-- For `T ≥ 4` one has `1 ≤ log T`. -/
private lemma one_le_log_of_four_le {T : ℝ} (hT : 4 ≤ T) : (1 : ℝ) ≤ Real.log T := by
  have hmono : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  nlinarith [Real.log_two_gt_d9]

/-- **The horizontal contribution.** There is a constant `C` such that for every good height
`T ≥ 4`, `|im ∫_{1/2}^2 (ζ'/ζ)(x + iT) dx| ≤ C log T`. -/
@[zz_tag "lem_horizontal_bound"]
theorem exists_abs_im_integral_logDeriv_riemannZeta_le_mul_log :
    ∃ C : ℝ, ∀ T : ℝ, IsGoodHeight T → 4 ≤ T →
      |(∫ x in (1 / 2 : ℝ)..2, logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im| ≤
        C * Real.log T := by
  obtain ⟨C₁, hC₁⟩ := exists_ncard_re_riemannZeta_eq_zero_le
  refine ⟨(C₁ + 1) * Real.pi, fun T hgood hT => ?_⟩
  obtain ⟨hSfin, hSle⟩ := hC₁ T hT
  set G : ℂ → ℂ := fun z => riemannZeta (z + (T : ℂ) * I) with hGdef
  have hVopen : IsOpen {z : ℂ | z + (T : ℂ) * I ≠ 1} :=
    isOpen_ne.preimage (by fun_prop : Continuous fun z : ℂ => z + (T : ℂ) * I)
  have hGV : AnalyticOnNhd ℂ G {z : ℂ | z + (T : ℂ) * I ≠ 1} := by
    have hd : DifferentiableOn ℂ G {z : ℂ | z + (T : ℂ) * I ≠ 1} := fun z hz =>
      ((differentiableAt_riemannZeta hz).comp z (by fun_prop)).differentiableWithinAt
    exact hd.analyticOnNhd hVopen
  set U : Set ℂ := {z : ℂ | z + (T : ℂ) * I ≠ 1 ∧ G z ≠ 0} with hUdef
  have hUopen : IsOpen U := by
    rw [isOpen_iff_eventually]
    intro z hz
    have hca : ContinuousAt G z := (hGV z hz.1).continuousAt
    filter_upwards [hca.eventually_ne hz.2, hVopen.mem_nhds hz.1] with w h1 h2
    exact ⟨h2, h1⟩
  have hseg : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, ((x : ℝ) : ℂ) ∈ U := by
    intro x hx
    obtain ⟨hx₀, hx₁⟩ := hx
    refine ⟨fun h => ?_, ?_⟩
    · have h2 := congrArg Complex.im h
      simp at h2
      linarith
    · rcases le_or_gt 1 x with h | h
      · exact riemannZeta_ne_zero_of_one_le_re (by simpa using h)
      · exact isGoodHeight_iff.1 hgood x (by linarith) h
  set E : Set ℝ := {x : ℝ | x ∈ Set.Ioo (1 / 2 : ℝ) 2 ∧ (G (x : ℂ)).re = 0} with hEdef
  set S : Set ℝ :=
    {x : ℝ | x ∈ Set.Icc (1 / 2 : ℝ) 2 ∧ (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0} with hSdef
  have hES : E ⊆ S := fun x hx => ⟨Set.Ioo_subset_Icc_self hx.1, hx.2⟩
  have hEfin : E.Finite := hSfin.subset hES
  have hEle : (E.ncard : ℝ) ≤ C₁ * Real.log T :=
    le_trans (by exact_mod_cast Set.ncard_le_ncard hES hSfin) hSle
  have hb := abs_im_integral_logDeriv_le (by norm_num : (1 / 2 : ℝ) < 2) hseg
    (hGV.mono fun z hz => hz.1) (fun z hz => hz.2) hEfin
  have hlog : ∀ x : ℝ, logDeriv G (x : ℂ) = logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I) := by
    intro x
    simp only [logDeriv, Pi.div_apply, hGdef, deriv_comp_add_const]
  simp only [hlog] at hb
  have hlogT := one_le_log_of_four_le hT
  nlinarith [Real.pi_pos, hb, hEle]

end ZetaZeros
