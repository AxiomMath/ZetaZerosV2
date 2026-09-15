import ZetaZeros.Unconditional.PairCorrelationFullZeroEstimate

noncomputable section

namespace ZetaZeros.Unconditional.PairCorrelationProof

open MeasureTheory
open scoped Interval

theorem exists_fullZeroPrimeTerm_log_meanValue_bound :
    ∃ primeConst > 0, ∃ meanValueConst > 0,
      ∀ scale : ℝ, 1 ≤ scale → ∀ height : ℝ, 0 ≤ height →
      |(∫ time in 0..height, ‖fullZeroPrimeTerm scale time‖ ^ 2) -
          height * Real.log scale| ≤
        primeConst * height + meanValueConst * scale * (1 + Real.log scale) := by
  obtain ⟨diagonalConst, hdiagonalConst, hdiagonal⟩ := pairPrimeMeanSquare_bounded
  obtain ⟨meanValueConst, hmeanValueConst, hmeanValue⟩ :=
    exists_fullZeroPrimeTerm_meanValue_bound
  refine ⟨2 * diagonalConst, by positivity, meanValueConst, hmeanValueConst, ?_⟩
  intro scale hscale height hheight
  have hscaleSq : 1 ≤ scale ^ 2 := by nlinarith
  have hunit : |pairPrimeMeanSquare 1| ≤ diagonalConst := by
    simpa using hdiagonal 1 le_rfl
  have hnegative : |pairPrimeMeanSquare 1 / scale ^ 2| ≤ diagonalConst := by
    rw [abs_div, abs_of_nonneg (sq_nonneg scale)]
    exact (div_le_self (abs_nonneg _) hscaleSq).trans hunit
  have hprimeDiagonal :
      |((∑' index, ‖primePositiveCoeff scale index‖ ^ 2) +
          ∑' index, ‖primeNegativeCoeff scale index‖ ^ 2) - Real.log scale| ≤
        2 * diagonalConst := by
    rw [primePositiveCoeff_sq_tsum_eq scale hscale,
      primeNegativeCoeff_sq_tsum_eq scale hscale]
    calc
      |pairPrimeMeanSquare scale + pairPrimeMeanSquare 1 / scale ^ 2 -
          Real.log scale| =
          |(pairPrimeMeanSquare scale - Real.log scale) +
            pairPrimeMeanSquare 1 / scale ^ 2| := by congr 1; ring
      _ ≤ |pairPrimeMeanSquare scale - Real.log scale| +
          |pairPrimeMeanSquare 1 / scale ^ 2| := abs_add_le _ _
      _ ≤ diagonalConst + diagonalConst :=
        add_le_add (hdiagonal scale hscale) hnegative
      _ = 2 * diagonalConst := by ring
  calc
    |(∫ time in 0..height, ‖fullZeroPrimeTerm scale time‖ ^ 2) -
        height * Real.log scale| =
        |((∫ time in 0..height, ‖fullZeroPrimeTerm scale time‖ ^ 2) -
          height * ((∑' index, ‖primePositiveCoeff scale index‖ ^ 2) +
            ∑' index, ‖primeNegativeCoeff scale index‖ ^ 2)) +
          height * (((∑' index, ‖primePositiveCoeff scale index‖ ^ 2) +
            ∑' index, ‖primeNegativeCoeff scale index‖ ^ 2) - Real.log scale)| := by
      congr 1
      ring
    _ ≤ |(∫ time in 0..height, ‖fullZeroPrimeTerm scale time‖ ^ 2) -
          height * ((∑' index, ‖primePositiveCoeff scale index‖ ^ 2) +
            ∑' index, ‖primeNegativeCoeff scale index‖ ^ 2)| +
        |height * (((∑' index, ‖primePositiveCoeff scale index‖ ^ 2) +
          ∑' index, ‖primeNegativeCoeff scale index‖ ^ 2) - Real.log scale)| :=
      abs_add_le _ _
    _ ≤ meanValueConst * scale * (1 + Real.log scale) +
        height * (2 * diagonalConst) := by
      apply add_le_add (hmeanValue scale hscale height)
      rw [abs_mul, abs_of_nonneg hheight]
      exact mul_le_mul_of_nonneg_left hprimeDiagonal hheight
    _ = (2 * diagonalConst) * height +
        meanValueConst * scale * (1 + Real.log scale) := by ring

end ZetaZeros.Unconditional.PairCorrelationProof
