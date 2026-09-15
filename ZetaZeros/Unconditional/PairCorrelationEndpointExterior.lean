import ZetaZeros.Unconditional.PairCorrelationFiniteMediumEnergy

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open Complex Finset MeasureTheory Set

theorem localCount_positive_window_sum_le {Index : Type*}
    {ordinate : Index → ℝ} {multiplicity : Index → ℕ}
    {countConst height center : ℝ}
    (hcount : Zeta23.Tail.LocalCount ordinate multiplicity countConst)
    (hheight : 0 ≤ height) (zeros : Finset Index)
    (hpositive : ∀ zero ∈ zeros, 0 < ordinate zero)
    (hbounded : ∀ zero ∈ zeros, ordinate zero ≤ height)
    (hwindow : ∀ zero ∈ zeros, center < ordinate zero ∧ ordinate zero ≤ center + 1) :
    ∑ zero ∈ zeros, (multiplicity zero : ℝ) ≤ countConst * Real.log (height + 4) := by
  have hcountNonneg : 0 ≤ countConst := zero_le_one.trans hcount.one_le
  by_cases hnonempty : zeros.Nonempty
  · obtain ⟨zero, hzero⟩ := hnonempty
    have hcenterLower : -1 < center := by
      linarith [(hwindow zero hzero).2, hpositive zero hzero]
    have hcenterUpper : center < height := (hwindow zero hzero).1.trans_le
      (hbounded zero hzero)
    have habsolute : |center| ≤ height + 1 := by
      rw [abs_le]
      constructor <;> linarith
    apply (hcount.window center zeros hwindow).trans
    apply mul_le_mul_of_nonneg_left _ hcountNonneg
    exact Real.log_le_log (by positivity) (by linarith)
  · have hempty : zeros = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty, Finset.sum_empty]
    exact mul_nonneg hcountNonneg (Real.log_nonneg (by linarith))

theorem finiteWindow_shifted_lorentzian_sum_below {Index : Type*}
    {ordinate : Index → ℝ} {multiplicity : Index → ℕ}
    {countConst height time : ℝ}
    (hcount : Zeta23.Tail.LocalCount ordinate multiplicity countConst)
    (hheight : 0 ≤ height) (htime : time ≤ 0) (zeros : Finset Index)
    (hpositive : ∀ zero ∈ zeros, 0 < ordinate zero)
    (hbounded : ∀ zero ∈ zeros, ordinate zero ≤ height) :
    ∑ zero ∈ zeros, (multiplicity zero : ℝ) / (1 + (time - ordinate zero) ^ 2) ≤
      4 * (countConst * Real.log (height + 4)) / (1 - time) := by
  classical
  have hnegativeTime : 0 ≤ -time := neg_nonneg.mpr htime
  let shell : Index → ℕ := fun zero => ⌈ordinate zero⌉₊ - 1
  have hshell : ∀ zero ∈ zeros,
      (shell zero : ℝ) < ordinate zero ∧ ordinate zero ≤ (shell zero : ℝ) + 1 := by
    intro zero hzero
    have hceil : 1 ≤ ⌈ordinate zero⌉₊ := Nat.one_le_ceil_iff.mpr (hpositive zero hzero)
    have hindex : ⌈ordinate zero⌉₊ = shell zero + 1 := by
      dsimp only [shell]
      omega
    have hinterval := (Nat.ceil_eq_iff (Nat.succ_ne_zero (shell zero))).mp hindex
    push_cast at hinterval
    simpa only [add_sub_cancel_right] using hinterval
  have hmajor := shell_lorentzian_sum_le zeros multiplicity shell
    (fun zero => time - ordinate zero)
    (M := countConst * Real.log (height + 4)) (d := -time)
    (mul_nonneg (zero_le_one.trans hcount.one_le) (Real.log_nonneg (by linarith)))
    (neg_nonneg.mpr htime)
  have hbound : ∑ zero ∈ zeros,
      (multiplicity zero : ℝ) / (1 + (time - ordinate zero) ^ 2) ≤
        4 * (countConst * Real.log (height + 4)) / (1 + -time) := by
    apply hmajor
    · intro zero hzero
      have hnear : -time + (shell zero : ℝ) ≤ ordinate zero - time := by
        linarith [(hshell zero hzero).1]
      have hleft : 0 ≤ -time + (shell zero : ℝ) := by positivity
      have hright : 0 ≤ ordinate zero - time := by linarith [hpositive zero hzero]
      have hsquare : (-time + (shell zero : ℝ)) ^ 2 ≤ (ordinate zero - time) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hnear) (add_nonneg hright hleft)]
      rw [div_le_div_iff₀ (by positivity : 0 < 1 + (time - ordinate zero) ^ 2)
        (sq_pos_of_pos (by positivity : 0 < 1 + -time + (shell zero : ℝ)))]
      nlinarith [sq_nonneg (-time + (shell zero : ℝ) - 1)]
    · intro index
      apply localCount_positive_window_sum_le hcount hheight
        (zeros.filter fun zero => shell zero = index)
      · intro zero hzero
        exact hpositive zero (Finset.mem_filter.mp hzero).1
      · intro zero hzero
        exact hbounded zero (Finset.mem_filter.mp hzero).1
      · intro zero hzero
        obtain ⟨hmem, hequal⟩ := Finset.mem_filter.mp hzero
        simpa only [hequal] using hshell zero hmem
  simpa only [sub_eq_add_neg] using hbound

theorem finiteWindow_shifted_lorentzian_sum_above {Index : Type*}
    {ordinate : Index → ℝ} {multiplicity : Index → ℕ}
    {countConst height time : ℝ}
    (hcount : Zeta23.Tail.LocalCount ordinate multiplicity countConst)
    (hheight : 0 ≤ height) (htime : height ≤ time) (zeros : Finset Index)
    (hpositive : ∀ zero ∈ zeros, 0 < ordinate zero)
    (hbounded : ∀ zero ∈ zeros, ordinate zero ≤ height) :
    ∑ zero ∈ zeros, (multiplicity zero : ℝ) / (1 + (time - ordinate zero) ^ 2) ≤
      4 * (countConst * Real.log (height + 4)) / (1 + (time - height)) := by
  classical
  let shell : Index → ℕ := fun zero => ⌊height - ordinate zero⌋₊
  have hshell : ∀ zero ∈ zeros,
      height - (shell zero : ℝ) - 1 < ordinate zero ∧
        ordinate zero ≤ height - (shell zero : ℝ) := by
    intro zero hzero
    have hinterval := (Nat.floor_eq_iff (sub_nonneg.mpr (hbounded zero hzero))).mp
      (rfl : shell zero = shell zero)
    dsimp only [shell] at hinterval ⊢
    constructor <;> linarith
  apply shell_lorentzian_sum_le zeros multiplicity shell
    (fun zero => time - ordinate zero)
    (mul_nonneg (zero_le_one.trans hcount.one_le) (Real.log_nonneg (by linarith)))
    (sub_nonneg.mpr htime)
  · intro zero hzero
    have hnear : time - height + (shell zero : ℝ) ≤ time - ordinate zero := by
      linarith [(hshell zero hzero).2]
    have hleft : 0 ≤ time - height + (shell zero : ℝ) := by positivity
    have hright : 0 ≤ time - ordinate zero := by linarith [hbounded zero hzero]
    have hsquare : (time - height + (shell zero : ℝ)) ^ 2 ≤
        (time - ordinate zero) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnear) (add_nonneg hright hleft)]
    rw [div_le_div_iff₀ (by positivity : 0 < 1 + (time - ordinate zero) ^ 2)
      (sq_pos_of_pos (by positivity : 0 < 1 + (time - height) + (shell zero : ℝ)))]
    nlinarith [sq_nonneg (time - height + (shell zero : ℝ) - 1)]
  · intro index
    apply localCount_positive_window_sum_le (center := height - index - 1) hcount hheight
      (zeros.filter fun zero => shell zero = index)
    · intro zero hzero
      exact hpositive zero (Finset.mem_filter.mp hzero).1
    · intro zero hzero
      exact hbounded zero (Finset.mem_filter.mp hzero).1
    · intro zero hzero
      obtain ⟨hmem, hequal⟩ := Finset.mem_filter.mp hzero
      have hinterval := hshell zero hmem
      rw [hequal] at hinterval
      constructor <;> linarith [hinterval.1, hinterval.2]

theorem finiteWindowLorentzianSum_norm_le_weighted_ordinates
    (base height time exponent : ℝ) (hbase : 1 ≤ base)
    (hrealPart : ∀ zero ∈ finiteZeroCarrierWindow height,
      (zero : ℂ).re - 1 / 2 ≤ exponent) :
    ‖finiteWindowLorentzianSum base height time‖ ≤
      (8 / 3 : ℝ) * base ^ exponent *
        ∑ zero ∈ finiteZeroCarrierWindow height,
          (Zeta23.zeroMult zero : ℝ) / (1 + (time - (zero : ℂ).im) ^ 2) := by
  classical
  rw [← norm_fullZeroLorentzianSummand_sum_window base (zero_lt_one.trans_le hbase)]
  calc
    ‖∑ zero ∈ finiteZeroCarrierWindow height, fullZeroLorentzianSummand base time zero‖ ≤
        ∑ zero ∈ finiteZeroCarrierWindow height, ‖fullZeroLorentzianSummand base time zero‖ :=
      norm_sum_le _ _
    _ ≤ ∑ zero ∈ finiteZeroCarrierWindow height,
        (8 / 3 : ℝ) * base ^ exponent *
          ((Zeta23.zeroMult zero : ℝ) / (1 + (time - (zero : ℂ).im) ^ 2)) := by
      apply Finset.sum_le_sum
      intro zero hzero
      simpa only [mul_div_assoc] using
        fullZeroLorentzianSummand_norm_le_of_re_le base hbase time exponent zero
          (hrealPart zero hzero)
    _ = (8 / 3 : ℝ) * base ^ exponent *
        ∑ zero ∈ finiteZeroCarrierWindow height,
          (Zeta23.zeroMult zero : ℝ) / (1 + (time - (zero : ℂ).im) ^ 2) := by
      rw [Finset.mul_sum]

theorem exterior_norm_sq_integral_le_of_boundary_majorant
    (function : ℝ → ℂ) (height bound : ℝ)
    (hsquare : Integrable (fun time => ‖function time‖ ^ 2))
    (_hbound : 0 ≤ bound)
    (hbelow : ∀ time ≤ 0, ‖function time‖ ≤ bound / (1 - time))
    (habove : ∀ time, height ≤ time → ‖function time‖ ≤ bound / (1 + (time - height))) :
    (∫ time in (Ioc (0 : ℝ) height)ᶜ, ‖function time‖ ^ 2) ≤
      2 * Real.pi * bound ^ 2 := by
  have hfirst : Integrable (fun time : ℝ => (1 + time ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  have hsecond : Integrable (fun time : ℝ => (1 + (time - height) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_sub_right height
  have hmajor : Integrable (fun time : ℝ =>
      bound ^ 2 * ((1 + time ^ 2)⁻¹ + (1 + (time - height) ^ 2)⁻¹)) :=
    (hfirst.add hsecond).const_mul (bound ^ 2)
  have hpoint : ∀ time ∈ (Ioc (0 : ℝ) height)ᶜ,
      ‖function time‖ ^ 2 ≤
        bound ^ 2 * ((1 + time ^ 2)⁻¹ + (1 + (time - height) ^ 2)⁻¹) := by
    intro time htime
    by_cases hpositive : 0 < time
    · have haboveHeight : height < time := by
        by_contra! hle
        exact htime ⟨hpositive, hle⟩
      have hdenominator : 1 + (time - height) ^ 2 ≤ (1 + (time - height)) ^ 2 := by
        nlinarith
      calc
        ‖function time‖ ^ 2 ≤ (bound / (1 + (time - height))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (habove time haboveHeight.le) 2
        _ ≤ bound ^ 2 / (1 + (time - height) ^ 2) := by
          rw [div_pow]
          exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hdenominator
        _ ≤ bound ^ 2 * ((1 + time ^ 2)⁻¹ + (1 + (time - height) ^ 2)⁻¹) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (by positivity)) (sq_nonneg bound)
    · have hnonpositive : time ≤ 0 := le_of_not_gt hpositive
      have hdenominator : 1 + time ^ 2 ≤ (1 - time) ^ 2 := by nlinarith
      calc
        ‖function time‖ ^ 2 ≤ (bound / (1 - time)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hbelow time hnonpositive) 2
        _ ≤ bound ^ 2 / (1 + time ^ 2) := by
          rw [div_pow]
          exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hdenominator
        _ ≤ bound ^ 2 * ((1 + time ^ 2)⁻¹ + (1 + (time - height) ^ 2)⁻¹) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (by positivity)) (sq_nonneg bound)
  calc
    (∫ time in (Ioc (0 : ℝ) height)ᶜ, ‖function time‖ ^ 2) ≤
        ∫ time in (Ioc (0 : ℝ) height)ᶜ,
          bound ^ 2 * ((1 + time ^ 2)⁻¹ + (1 + (time - height) ^ 2)⁻¹) := by
      apply integral_mono_ae hsquare.integrableOn hmajor.integrableOn
      exact ae_restrict_of_forall_mem measurableSet_Ioc.compl hpoint
    _ ≤ ∫ time : ℝ,
        bound ^ 2 * ((1 + time ^ 2)⁻¹ + (1 + (time - height) ^ 2)⁻¹) := by
      exact setIntegral_le_integral hmajor (Filter.Eventually.of_forall (by
        intro time
        positivity))
    _ = 2 * Real.pi * bound ^ 2 := by
      rw [integral_const_mul, integral_add hfirst hsecond,
        integral_univ_inv_one_add_sq,
        integral_sub_right_eq_self (fun time : ℝ => (1 + time ^ 2)⁻¹) height,
        integral_univ_inv_one_add_sq]
      ring

theorem exists_finiteWindow_exterior_energy_bound_of_re_le :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (base height exponent : ℝ), 1 ≤ base → 0 ≤ height →
        (∀ zero ∈ finiteZeroCarrierWindow height,
          (zero : ℂ).re - 1 / 2 ≤ exponent) →
        (∫ time in (Ioc (0 : ℝ) height)ᶜ,
          ‖finiteWindowLorentzianSum base height time‖ ^ 2) ≤
            constant * (base ^ exponent) ^ 2 * (Real.log (height + 4)) ^ 2 := by
  obtain ⟨countConst, hcountConst, hlocal⟩ := Zeta23.RvM.zeta_local_zero_count
  have hcount := Zeta23.Tail.LocalCount.ofWindowCount
    (Zeta23.zetaZeros Zeta23.zetaSeam) hcountConst (fun center => by
      rw [Zeta23.zetaZeros_N]
      exact hlocal center)
  refine ⟨2 * Real.pi * ((32 / 3 : ℝ) * countConst) ^ 2, by positivity, ?_⟩
  intro base height exponent hbase hheight hrealPart
  have hbaseNonneg : 0 ≤ base := zero_le_one.trans hbase
  have hcountNonneg : 0 ≤ countConst := zero_le_one.trans hcountConst
  have hpositive : ∀ zero ∈ finiteZeroCarrierWindow height, 0 < (zero : ℂ).im := by
    intro zero hzero
    exact (mem_finiteZeroWindow.mp (mem_finiteZeroCarrierWindow.mp hzero)).2.1
  have hbounded : ∀ zero ∈ finiteZeroCarrierWindow height, (zero : ℂ).im ≤ height := by
    intro zero hzero
    exact (mem_finiteZeroWindow.mp (mem_finiteZeroCarrierWindow.mp hzero)).2.2
  have hbelow : ∀ time ≤ 0, ‖finiteWindowLorentzianSum base height time‖ ≤
      ((32 / 3 : ℝ) * countConst * base ^ exponent * Real.log (height + 4)) /
        (1 - time) := by
    intro time htime
    have hsum := finiteWindow_shifted_lorentzian_sum_below hcount hheight htime
      (finiteZeroCarrierWindow height) hpositive hbounded
    simp only [Zeta23.zetaZeros_mult] at hsum
    calc
      ‖finiteWindowLorentzianSum base height time‖ ≤
          (8 / 3 : ℝ) * base ^ exponent *
            ∑ zero ∈ finiteZeroCarrierWindow height,
              (Zeta23.zeroMult zero : ℝ) / (1 + (time - (zero : ℂ).im) ^ 2) :=
        finiteWindowLorentzianSum_norm_le_weighted_ordinates base height time exponent
          hbase hrealPart
      _ ≤ (8 / 3 : ℝ) * base ^ exponent *
          (4 * (countConst * Real.log (height + 4)) / (1 - time)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ((32 / 3 : ℝ) * countConst * base ^ exponent * Real.log (height + 4)) /
          (1 - time) := by ring
  have habove : ∀ time, height ≤ time → ‖finiteWindowLorentzianSum base height time‖ ≤
      ((32 / 3 : ℝ) * countConst * base ^ exponent * Real.log (height + 4)) /
        (1 + (time - height)) := by
    intro time htime
    have hsum := finiteWindow_shifted_lorentzian_sum_above hcount hheight htime
      (finiteZeroCarrierWindow height) hpositive hbounded
    simp only [Zeta23.zetaZeros_mult] at hsum
    calc
      ‖finiteWindowLorentzianSum base height time‖ ≤
          (8 / 3 : ℝ) * base ^ exponent *
            ∑ zero ∈ finiteZeroCarrierWindow height,
              (Zeta23.zeroMult zero : ℝ) / (1 + (time - (zero : ℂ).im) ^ 2) :=
        finiteWindowLorentzianSum_norm_le_weighted_ordinates base height time exponent
          hbase hrealPart
      _ ≤ (8 / 3 : ℝ) * base ^ exponent *
          (4 * (countConst * Real.log (height + 4)) / (1 + (time - height))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ((32 / 3 : ℝ) * countConst * base ^ exponent * Real.log (height + 4)) /
          (1 + (time - height)) := by ring
  have hsquare : Integrable (fun time => ‖finiteWindowLorentzianSum base height time‖ ^ 2) := by
    simpa only [norm_mul, Complex.norm_conj, ← pow_two] using
      (finiteWindowLorentzianSum_mul_conj_integrable base height).norm
  have hboundNonneg : 0 ≤
      (32 / 3 : ℝ) * countConst * base ^ exponent * Real.log (height + 4) := by
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have henergy := exterior_norm_sq_integral_le_of_boundary_majorant
    (finiteWindowLorentzianSum base height) height
    ((32 / 3 : ℝ) * countConst * base ^ exponent * Real.log (height + 4))
    hsquare hboundNonneg hbelow habove
  convert henergy using 1
  ring

theorem exists_finiteWindow_exterior_energy_bound_of_zeroFreeWidth :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (base height margin : ℝ), 1 ≤ base → 0 ≤ height →
        (∀ zero ∈ finiteZeroCarrierWindow height, (zero : ℂ).re ≤ 1 - margin) →
        (∫ time in (Ioc (0 : ℝ) height)ᶜ,
          ‖finiteWindowLorentzianSum base height time‖ ^ 2) ≤
            constant * base ^ (1 - 2 * margin) * (Real.log (height + 4)) ^ 2 := by
  obtain ⟨constant, hconstant, henergy⟩ := exists_finiteWindow_exterior_energy_bound_of_re_le
  refine ⟨constant, hconstant, ?_⟩
  intro base height margin hbase hheight hrealPart
  have hshift : ∀ zero ∈ finiteZeroCarrierWindow height,
      (zero : ℂ).re - 1 / 2 ≤ 1 / 2 - margin := by
    intro zero hzero
    linarith [hrealPart zero hzero]
  have hpower : (base ^ (1 / 2 - margin)) ^ 2 = base ^ (1 - 2 * margin) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (zero_le_one.trans hbase)]
    congr 1
    ring
  simpa only [hpower] using henergy base height (1 / 2 - margin) hbase hheight hshift

theorem finiteWindow_exterior_endpoint_energy_le_of_strip :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ height : ℝ, Real.exp 2 ≤ height →
        ∀ base margin : ℝ, 1 ≤ base → base ≤ height → margin ≤ 1 / 2 →
          3 * Real.log (Real.log height) ≤ 2 * margin * Real.log height →
          (∀ zero ∈ finiteZeroCarrierWindow height, (zero : ℂ).re ≤ 1 - margin) →
          (∫ time in (Ioc (0 : ℝ) height)ᶜ,
            ‖finiteWindowLorentzianSum base height time‖ ^ 2) ≤
              constant * height / Real.log height := by
  obtain ⟨constant, hconstant, henergy⟩ :=
    exists_finiteWindow_exterior_energy_bound_of_zeroFreeWidth
  refine ⟨16 * constant, by positivity, ?_⟩
  intro height hheight base margin hbase hbaseHeight hmargin hsaving hrealPart
  have hheightPos : 0 < height := (Real.exp_pos 2).trans_le hheight
  have hlogTwo : 2 ≤ Real.log height := (Real.le_log_iff_exp_le hheightPos).mpr hheight
  have hheightCutoff : height ≤ height * (Real.log height) ^ 2 := by
    have hsquare : 1 ≤ (Real.log height) ^ 2 := by nlinarith
    exact le_mul_of_one_le_right hheightPos.le hsquare
  have hlogBound : Real.log (height + 4) ≤
      Real.log (height * (Real.log height) ^ 2 + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogNonneg : 0 ≤ Real.log (height + 4) := Real.log_nonneg (by linarith)
  have hfactor : base ^ (1 - 2 * margin) * (Real.log (height + 4)) ^ 2 ≤
      16 * height / Real.log height := by
    apply le_trans _ (finiteMedium_strip_factor_le height base margin hheight hbase
      hbaseHeight hmargin hsaving)
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (zero_le_one.trans hbase) _)
    exact pow_le_pow_left₀ hlogNonneg hlogBound 2
  calc
    (∫ time in (Ioc (0 : ℝ) height)ᶜ,
        ‖finiteWindowLorentzianSum base height time‖ ^ 2) ≤
      constant * base ^ (1 - 2 * margin) * (Real.log (height + 4)) ^ 2 :=
        henergy base height margin hbase hheightPos.le hrealPart
    _ = constant * (base ^ (1 - 2 * margin) * (Real.log (height + 4)) ^ 2) := by ring
    _ ≤ constant * (16 * height / Real.log height) :=
      mul_le_mul_of_nonneg_left hfactor hconstant.le
    _ = (16 * constant) * height / Real.log height := by ring

theorem finiteWindowExteriorEnergyBound_of_strip
    (margin : ℝ → ℝ) (threshold : ℝ)
    (hmargin : ∀ height ≥ threshold, margin height ≤ 1 / 2)
    (hsaving : ∀ height ≥ threshold,
      3 * Real.log (Real.log height) ≤ 2 * margin height * Real.log height)
    (hstrip : ∀ height ≥ threshold,
      ∀ zero ∈ finiteZeroCarrierWindow height, (zero : ℂ).re ≤ 1 - margin height) :
    FiniteWindowExteriorEnergyBound := by
  obtain ⟨constant, hconstant, henergy⟩ := finiteWindow_exterior_endpoint_energy_le_of_strip
  refine ⟨constant, hconstant, max threshold (Real.exp 2), ?_⟩
  intro height hheight base hbase hbaseHeight
  have hthreshold : threshold ≤ height := (le_max_left _ _).trans hheight
  have hheightExp : Real.exp 2 ≤ height := (le_max_right _ _).trans hheight
  have hheightPos : 0 < height := (Real.exp_pos 2).trans_le hheightExp
  have hlogOne : 1 ≤ Real.log height := by
    have hlogTwo := (Real.le_log_iff_exp_le hheightPos).mpr hheightExp
    linarith
  calc
    (∫ time in (Ioc (0 : ℝ) height)ᶜ,
        ‖finiteWindowLorentzianSum base height time‖ ^ 2) ≤
      constant * height / Real.log height :=
        henergy height hheightExp base (margin height) hbase hbaseHeight
          (hmargin height hthreshold) (hsaving height hthreshold) (hstrip height hthreshold)
    _ ≤ constant * height := div_le_self (by positivity) hlogOne
    _ ≤ constant * (height + base) := by
      apply mul_le_mul_of_nonneg_left _ hconstant.le
      linarith

theorem finiteWindowExteriorEnergyBound_of_boundary_margin
    (hboundaryMargin :
      ∃ margin : ℝ → ℝ, ∃ threshold : ℝ, Real.exp 2 ≤ threshold ∧
        (∀ height ≥ threshold, margin height ≤ 1 / 2) ∧
        (∀ height ≥ threshold,
          3 * Real.log (Real.log height) ≤ 2 * margin height * Real.log height) ∧
        (∀ height ≥ threshold, ∀ zero : ℂ, Zeta23.IsNontrivialZero zero →
          |zero.im| ≤ height * (Real.log height) ^ 2 →
            |zero.re - 1 / 2| ≤ 1 / 2 - margin height)) :
    FiniteWindowExteriorEnergyBound := by
  obtain ⟨margin, threshold, hthreshold, hmargin, hsaving, hstrip⟩ :=
    hboundaryMargin
  refine finiteWindowExteriorEnergyBound_of_strip margin threshold hmargin hsaving ?_
  intro height hheight zero hzero
  have hheightExp : Real.exp 2 ≤ height := hthreshold.trans hheight
  have hheightPos : 0 < height := (Real.exp_pos 2).trans_le hheightExp
  have hlogTwo : 2 ≤ Real.log height :=
    (Real.le_log_iff_exp_le hheightPos).mpr hheightExp
  have hheightCutoff : height ≤ height * (Real.log height) ^ 2 := by
    have hsquare : 1 ≤ (Real.log height) ^ 2 := by nlinarith
    exact le_mul_of_one_le_right hheightPos.le hsquare
  have hzeroWindow := mem_finiteZeroWindow.mp (mem_finiteZeroCarrierWindow.mp hzero)
  have hzeroHeight : |(zero : ℂ).im| ≤ height * (Real.log height) ^ 2 := by
    rw [abs_of_pos hzeroWindow.2.1]
    exact hzeroWindow.2.2.trans hheightCutoff
  have hrealPart :=
    (abs_le.mp (hstrip height hheight (zero : ℂ) zero.property hzeroHeight)).2
  linarith

end ZetaZeros.Unconditional.PairCorrelationProof
