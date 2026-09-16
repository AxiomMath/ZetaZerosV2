import ErdosProblems.Erdos421.StripConstants
import ErdosProblems.Erdos421.ZetaRightHeight
import ErdosProblems.Erdos421.ZetaZeroExclusion

/-! # A zero-exclusion criterion from the proved growth envelope

The final theorem has only numerical hypotheses on its parameters. The
analytic disk bounds, local factorization, and pole estimate are all supplied
by proved results. Optimizing its parameters to obtain the prime-weighted
estimate required by the main problem is not asserted here.
-/

namespace Erdos421

open Complex Metric

theorem riemannZeta_norm_relative_to_center {s c : ℂ} {M : ℝ}
    (hc : 1 < c.re) (hM : 0 ≤ M) (hs : ‖riemannZeta s‖ ≤ M) :
    ‖riemannZeta s‖ ≤ M * (1 + 1 / (c.re - 1)) * ‖riemannZeta c‖ := by
  have hn : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_le_re hc.le
  have hq := norm_inv_riemannZeta_right_halfPlane_le hc
  have hunit : 1 ≤ (1 + 1 / (c.re - 1)) * ‖riemannZeta c‖ := by
    have h := mul_le_mul_of_nonneg_right hq (norm_nonneg (riemannZeta c))
    rwa [← norm_mul, inv_mul_cancel₀ hn, norm_one] at h
  calc
    ‖riemannZeta s‖ ≤ M := hs
    _ ≤ M * ((1 + 1 / (c.re - 1)) * ‖riemannZeta c‖) :=
      le_mul_of_one_le_right hM hunit
    _ = _ := by ring

end Erdos421
