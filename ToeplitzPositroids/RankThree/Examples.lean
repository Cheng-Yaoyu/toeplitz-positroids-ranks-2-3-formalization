import ToeplitzPositroids.RankThree.Banded
import ToeplitzPositroids.RankThree.ConvexChainCriterion
import ToeplitzPositroids.RankThree.SineSequence
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Concrete rank-three examples

This file verifies the mixed-boundary `3 × 8` Toeplitz example and the
four-term golden-ratio sine example from the paper.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids Matrix
open scoped goldenRatio

noncomputable section

/-! ## The mixed-boundary example -/

/-- The coefficient vector, stored in the order `a₋₂, a₋₁, a₀, ..., a₇`. -/
def mixedBoundaryCoefficients : Fin 10 → ℝ :=
  ![0, 0, 0, 3, 9, 18, 27, 36, 48, 64]

/-- The mixed-boundary `3 × 8` Toeplitz matrix. -/
def mixedBoundaryMatrix : Matrix (Fin 3) (Fin 8) ℝ :=
  rankThreeToeplitz mixedBoundaryCoefficients

private abbrev mixedBoundaryMatrixRat : Matrix (Fin 3) (Fin 8) ℚ :=
  !![0, 3, 9, 18, 27, 36, 48, 64;
     0, 0, 3, 9, 18, 27, 36, 48;
     0, 0, 0, 3, 9, 18, 27, 36]

/-- The Toeplitz construction gives exactly the displayed numerical matrix. -/
theorem mixedBoundaryMatrix_eq :
    mixedBoundaryMatrix =
      !![0, 3, 9, 18, 27, 36, 48, 64;
         0, 0, 3, 9, 18, 27, 36, 48;
         0, 0, 0, 3, 9, 18, 27, 36] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mixedBoundaryMatrix, mixedBoundaryCoefficients, rankThreeToeplitz]

theorem mixedBoundaryCoefficients_nonneg (k : Fin 10) :
    0 ≤ mixedBoundaryCoefficients k := by
  fin_cases k <;> norm_num [mixedBoundaryCoefficients]

theorem mixedBoundaryCoefficients_pos_iff (k : Fin 10) :
    0 < mixedBoundaryCoefficients k ↔ 3 ≤ k.val := by
  fin_cases k <;> norm_num [mixedBoundaryCoefficients]

theorem mixedBoundaryCoefficients_intervalSupport :
    HasIntervalPositiveSupport mixedBoundaryCoefficients := by
  rw [hasIntervalPositiveSupport_iff]
  intro i j k hi hj hik hkj
  rw [mixedBoundaryCoefficients_pos_iff] at hi hj ⊢
  omega

theorem mixedBoundaryCoefficients_logConcave :
    DiscretelyLogConcave (n := 8) mixedBoundaryCoefficients := by
  intro k
  fin_cases k <;> norm_num [mixedBoundaryCoefficients]
  exact mul_self_nonneg _

/-- The example is totally nonnegative through order two. -/
theorem mixedBoundaryMatrix_tnUpTo_two : TNUpTo mixedBoundaryMatrix 2 := by
  rw [mixedBoundaryMatrix, rankThreeToeplitz_tnUpTo_two_iff (n := 8) (by omega)]
  exact ⟨mixedBoundaryCoefficients_nonneg,
    mixedBoundaryCoefficients_intervalSupport,
    mixedBoundaryCoefficients_logConcave⟩

/-- The first column is the unique loop column. -/
theorem mixedBoundaryMatrix_isLoop_iff (j : Fin 8) :
    IsLoop mixedBoundaryMatrix j ↔ j = 0 := by
  constructor
  · intro hj
    rw [isLoop_iff_entry_eq_zero] at hj
    have htop := hj 0
    fin_cases j <;>
      norm_num [mixedBoundaryMatrix, mixedBoundaryCoefficients, rankThreeToeplitz] at htop
    simp
  · rintro rfl
    rw [isLoop_iff_entry_eq_zero]
    intro i
    fin_cases i <;>
      norm_num [mixedBoundaryMatrix, mixedBoundaryCoefficients, rankThreeToeplitz]

/-- Columns seven and eight form the terminal positive parallel class. -/
theorem mixedBoundaryMatrix_terminalParallel :
    ColumnsParallel mixedBoundaryMatrix 6 7 := by
  constructor
  · rw [mixedBoundaryMatrix_isLoop_iff]
    decide
  · refine ⟨(4 : ℝ) / 3, by norm_num, ?_⟩
    funext i
    fin_cases i <;>
      norm_num [mixedBoundaryMatrix, mixedBoundaryCoefficients, rankThreeToeplitz,
        Matrix.col_apply, Pi.smul_apply]

/-- Among increasing nonloop pairs, only columns seven and eight are positively parallel. -/
theorem mixedBoundaryMatrix_posParallel_iff {i j : Fin 8} (hij : i < j) (hi : i ≠ 0) :
    ColumnsPositivelyParallel mixedBoundaryMatrix i j ↔ i = 6 ∧ j = 7 := by
  constructor
  · intro hp
    fin_cases i <;> fin_cases j <;> simp_all only [Fin.mk_lt_mk, Fin.ext_iff]
    all_goals try omega
    all_goals try (exfalso; apply hi; rfl)
    all_goals
      have hz := coordinateMinors_eq_zero_of_positivelyParallel hp
      norm_num [coordinateMinor12, coordinateMinor13, coordinateMinor23,
        mixedBoundaryMatrix, mixedBoundaryCoefficients, rankThreeToeplitz] at hz
  · rintro ⟨rfl, rfl⟩
    exact mixedBoundaryMatrix_terminalParallel.2

/-- The unique nontrivial parallel class is the terminal pair of columns seven and eight. -/
theorem mixedBoundaryMatrix_columnsParallel_iff {i j : Fin 8} (hij : i < j) :
    ColumnsParallel mixedBoundaryMatrix i j ↔ i = 6 ∧ j = 7 := by
  constructor
  · rintro ⟨hi, hp⟩
    apply (mixedBoundaryMatrix_posParallel_iff hij ?_).mp hp
    intro hi0
    apply hi
    rw [mixedBoundaryMatrix_isLoop_iff]
    exact hi0
  · rintro ⟨rfl, rfl⟩
    exact mixedBoundaryMatrix_terminalParallel

/-- The displayed coefficient ratios `r₂, ..., r₈`. -/
def mixedBoundaryRatio (j : Fin 7) : ℝ :=
  mixedBoundaryCoefficients ⟨j.val + 2, by omega⟩ /
    mixedBoundaryCoefficients ⟨j.val + 3, by omega⟩

theorem mixedBoundaryRatio_eq :
    mixedBoundaryRatio = ![0, (1 : ℝ) / 3, (1 : ℝ) / 2, (2 : ℝ) / 3,
      (3 : ℝ) / 4, (3 : ℝ) / 4, (3 : ℝ) / 4] := by
  funext j
  fin_cases j <;> norm_num [mixedBoundaryRatio, mixedBoundaryCoefficients]

theorem mixedBoundaryRatio_monotone : Monotone mixedBoundaryRatio := by
  rw [mixedBoundaryRatio_eq]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all only [Fin.mk_le_mk]
  all_goals try omega
  all_goals norm_num

/-- The six normalized nonloop representatives `Q₂, ..., Q₇`. -/
def mixedBoundaryPoint (j : Fin 6) : ℝ × ℝ :=
  let c : Fin 8 := ⟨j.val + 1, by omega⟩
  (mixedBoundaryMatrix 1 c / mixedBoundaryMatrix 0 c,
    mixedBoundaryMatrix 2 c / mixedBoundaryMatrix 0 c)

theorem mixedBoundaryPoint_eq :
    mixedBoundaryPoint =
      ![(0, 0), ((1 : ℝ) / 3, 0), ((1 : ℝ) / 2, (1 : ℝ) / 6),
        ((2 : ℝ) / 3, (1 : ℝ) / 3), ((3 : ℝ) / 4, (1 : ℝ) / 2),
        ((3 : ℝ) / 4, (9 : ℝ) / 16)] := by
  funext j
  fin_cases j <;>
    norm_num [mixedBoundaryPoint, mixedBoundaryMatrix, mixedBoundaryCoefficients,
      rankThreeToeplitz]

/-- An affine edge slope, with `⊤` used for a vertical edge. -/
def extendedEdgeSlope (p q : ℝ × ℝ) : WithTop ℝ :=
  if p.1 = q.1 then ⊤ else ((q.2 - p.2) / (q.1 - p.1) : ℝ)

/-- The five simplified edge slopes of the example. -/
def mixedBoundaryEdgeSlope (j : Fin 5) : WithTop ℝ :=
  extendedEdgeSlope (mixedBoundaryPoint j.castSucc)
    (mixedBoundaryPoint j.succ)

theorem mixedBoundaryEdgeSlope_eq :
    mixedBoundaryEdgeSlope = ![0, 1, 1, 2, ⊤] := by
  funext j
  fin_cases j <;>
    norm_num [mixedBoundaryEdgeSlope, extendedEdgeSlope, mixedBoundaryPoint,
      mixedBoundaryMatrix, mixedBoundaryCoefficients, rankThreeToeplitz]

theorem mixedBoundaryEdgeSlope_monotone : Monotone mixedBoundaryEdgeSlope := by
  rw [mixedBoundaryEdgeSlope_eq]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all only [Fin.mk_le_mk]
  all_goals try omega
  all_goals norm_num

/-- The explicit determinant polynomial of three selected columns. -/
def mixedBoundaryTripleDet (i j k : Fin 8) : ℝ :=
  mixedBoundaryMatrix 0 i * mixedBoundaryMatrix 1 j * mixedBoundaryMatrix 2 k -
    mixedBoundaryMatrix 0 i * mixedBoundaryMatrix 1 k * mixedBoundaryMatrix 2 j -
    mixedBoundaryMatrix 0 j * mixedBoundaryMatrix 1 i * mixedBoundaryMatrix 2 k +
    mixedBoundaryMatrix 0 j * mixedBoundaryMatrix 1 k * mixedBoundaryMatrix 2 i +
    mixedBoundaryMatrix 0 k * mixedBoundaryMatrix 1 i * mixedBoundaryMatrix 2 j -
    mixedBoundaryMatrix 0 k * mixedBoundaryMatrix 1 j * mixedBoundaryMatrix 2 i

private abbrev mixedBoundaryTripleDetRat (i j k : Fin 8) : ℚ :=
  mixedBoundaryMatrixRat 0 i * mixedBoundaryMatrixRat 1 j * mixedBoundaryMatrixRat 2 k -
    mixedBoundaryMatrixRat 0 i * mixedBoundaryMatrixRat 1 k * mixedBoundaryMatrixRat 2 j -
    mixedBoundaryMatrixRat 0 j * mixedBoundaryMatrixRat 1 i * mixedBoundaryMatrixRat 2 k +
    mixedBoundaryMatrixRat 0 j * mixedBoundaryMatrixRat 1 k * mixedBoundaryMatrixRat 2 i +
    mixedBoundaryMatrixRat 0 k * mixedBoundaryMatrixRat 1 i * mixedBoundaryMatrixRat 2 j -
    mixedBoundaryMatrixRat 0 k * mixedBoundaryMatrixRat 1 j * mixedBoundaryMatrixRat 2 i

private theorem mixedBoundaryMatrix_cast (i : Fin 3) (j : Fin 8) :
    mixedBoundaryMatrix i j = (mixedBoundaryMatrixRat i j : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [mixedBoundaryMatrix, mixedBoundaryMatrixRat, mixedBoundaryCoefficients,
      rankThreeToeplitz]

private theorem mixedBoundaryTripleDet_cast (i j k : Fin 8) :
    mixedBoundaryTripleDet i j k = (mixedBoundaryTripleDetRat i j k : ℝ) := by
  simp only [mixedBoundaryTripleDet, mixedBoundaryTripleDetRat]
  simp_rw [mixedBoundaryMatrix_cast]
  norm_cast

private theorem mixedBoundaryTripleDetRat_nonneg :
    ∀ (i j k : Fin 8), i < j → j < k → 0 ≤ mixedBoundaryTripleDetRat i j k := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all only [Fin.mk_lt_mk]
  all_goals try omega
  all_goals norm_num [mixedBoundaryTripleDetRat, mixedBoundaryMatrixRat,
    Matrix.cons_val_two]

private theorem mixedBoundaryTripleDetRat_eq_zero_iff :
    ∀ (i j k : Fin 8), i < j → j < k →
      (mixedBoundaryTripleDetRat i j k = 0 ↔
        i = 0 ∨ (j = 6 ∧ k = 7) ∨ (i = 2 ∧ j = 3 ∧ k = 4)) := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all only [Fin.mk_lt_mk]
  all_goals try omega
  all_goals norm_num [mixedBoundaryTripleDetRat, mixedBoundaryMatrixRat,
    Matrix.cons_val_two]
  all_goals simp [Fin.ext_iff]

theorem mixedBoundaryMatrix_selectedTriple_eq
    {i j k : Fin 8} (hij : i < j) (hjk : j < k) :
    orderedMinor mixedBoundaryMatrix (allRows 3)
        (selectedTripleEmbedding i j k hij hjk) = mixedBoundaryTripleDet i j k := by
  rw [orderedMinor_three]
  rfl

/-- Every increasing maximal minor of the example is nonnegative. -/
theorem mixedBoundaryMatrix_selectedTriple_nonneg
    {i j k : Fin 8} (hij : i < j) (hjk : j < k) :
    0 ≤ orderedMinor mixedBoundaryMatrix (allRows 3)
      (selectedTripleEmbedding i j k hij hjk) := by
  rw [mixedBoundaryMatrix_selectedTriple_eq hij hjk]
  rw [mixedBoundaryTripleDet_cast]
  exact_mod_cast mixedBoundaryTripleDetRat_nonneg i j k hij hjk

/-- The complete vanishing classification for increasing maximal minors. -/
theorem mixedBoundaryMatrix_selectedTriple_eq_zero_iff
    {i j k : Fin 8} (hij : i < j) (hjk : j < k) :
    orderedMinor mixedBoundaryMatrix (allRows 3)
        (selectedTripleEmbedding i j k hij hjk) = 0 ↔
      i = 0 ∨ (j = 6 ∧ k = 7) ∨ (i = 2 ∧ j = 3 ∧ k = 4) := by
  rw [mixedBoundaryMatrix_selectedTriple_eq hij hjk]
  rw [mixedBoundaryTripleDet_cast]
  norm_cast
  exact mixedBoundaryTripleDetRat_eq_zero_iff i j k hij hjk

/-- After deleting the loop and identifying the terminal parallel pair, the
only collinear increasing triple is formed by columns three, four, and five. -/
theorem mixedBoundaryMatrix_unique_collinearTriple
    {i j k : Fin 8} (hij : i < j) (hjk : j < k)
    (hi : i ≠ 0) (hterminal : ¬(j = 6 ∧ k = 7)) :
    orderedMinor mixedBoundaryMatrix (allRows 3)
        (selectedTripleEmbedding i j k hij hjk) = 0 ↔
      i = 2 ∧ j = 3 ∧ k = 4 := by
  rw [mixedBoundaryMatrix_selectedTriple_eq_zero_iff hij hjk]
  tauto

/-- The representative determinant on columns three, four, and five vanishes. -/
theorem mixedBoundaryMatrix_det_345 :
    orderedMinor mixedBoundaryMatrix (allRows 3)
      (selectedTripleEmbedding 2 3 4 (by decide) (by decide)) = 0 := by
  rw [mixedBoundaryMatrix_selectedTriple_eq]
  norm_num [mixedBoundaryTripleDet, mixedBoundaryMatrix, mixedBoundaryCoefficients,
    rankThreeToeplitz]

/-- The representative determinant on columns two, three, and four is `27`. -/
theorem mixedBoundaryMatrix_det_234 :
    orderedMinor mixedBoundaryMatrix (allRows 3)
      (selectedTripleEmbedding 1 2 3 (by decide) (by decide)) = 27 := by
  rw [mixedBoundaryMatrix_selectedTriple_eq]
  norm_num [mixedBoundaryTripleDet, mixedBoundaryMatrix, mixedBoundaryCoefficients,
    rankThreeToeplitz]

theorem mixedBoundaryMatrix_maximalMinorsNonnegative :
    MaximalMinorsNonnegative mixedBoundaryMatrix := by
  intro cols
  rw [← selectedTripleEmbedding_eq cols]
  exact mixedBoundaryMatrix_selectedTriple_nonneg
    (cols.strictMono (by decide)) (cols.strictMono (by decide))

/-- The mixed-boundary example is totally nonnegative. -/
theorem mixedBoundaryMatrix_totallyNonnegative :
    TotallyNonnegative mixedBoundaryMatrix := by
  rw [totallyNonnegative_fin_three_iff]
  exact ⟨mixedBoundaryMatrix_tnUpTo_two,
    mixedBoundaryMatrix_maximalMinorsNonnegative⟩

/-- The positive determinant `27` witnesses full row rank. -/
theorem mixedBoundaryMatrix_hasFullRowRank : HasFullRowRank mixedBoundaryMatrix := by
  refine ⟨selectedTripleEmbedding 1 2 3 (by decide) (by decide), ?_⟩
  rw [mixedBoundaryMatrix_det_234]
  norm_num

/-! ## The golden sine example -/

/-- The golden-ratio coefficient vector proportional to the `d = 3` sine base. -/
def goldenCoefficients : Fin 4 → ℝ := ![1, φ, φ, 1]

/-- The normalized golden vector gives the displayed `3 × 6` banded matrix. -/
theorem goldenBandedMatrix_eq :
    bandedMatrix goldenCoefficients =
      !![1, φ, φ, 1, 0, 0;
         0, 1, φ, φ, 1, 0;
         0, 0, 1, φ, φ, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bandedMatrix, bandCoefficient, goldenCoefficients, toeplitzMatrix,
      Matrix.cons_val_two, Int.toNat_of_nonneg,
      show Int.toNat (2 : ℤ) = 2 by rfl,
      show Int.toNat (3 : ℤ) = 3 by rfl]

/-- The `d = 3` sine base is `sin(π/5)` times the golden vector. -/
theorem sineCoefficient_three_eq_golden :
    sineCoefficient 3 = sineCoefficient 3 0 • goldenCoefficients := by
  funext t
  fin_cases t
  · norm_num [goldenCoefficients]
  · norm_num [goldenCoefficients, sineCoefficient]
    change Real.sin (2 * sineAngle 3) = Real.sin (sineAngle 3) * φ
    rw [Real.sin_two_mul]
    have hangle : sineAngle 3 = Real.pi / 5 := by norm_num [sineAngle]
    rw [hangle, Real.cos_pi_div_five]
    change 2 * Real.sin (Real.pi / 5) * ((1 + √5) / 4) =
      Real.sin (Real.pi / 5) * ((1 + √5) / 2)
    ring
  · norm_num [goldenCoefficients, sineCoefficient]
    change Real.sin (3 * sineAngle 3) = Real.sin (sineAngle 3) * φ
    have hangle : 3 * sineAngle 3 = Real.pi - 2 * sineAngle 3 := by
      norm_num [sineAngle]
      ring
    rw [hangle, Real.sin_pi_sub]
    change Real.sin (2 * sineAngle 3) = Real.sin (sineAngle 3) * φ
    rw [Real.sin_two_mul]
    have hangle' : sineAngle 3 = Real.pi / 5 := by norm_num [sineAngle]
    rw [hangle', Real.cos_pi_div_five]
    change 2 * Real.sin (Real.pi / 5) * ((1 + √5) / 4) =
      Real.sin (Real.pi / 5) * ((1 + √5) / 2)
    ring
  · simp only [goldenCoefficients, Pi.smul_apply, smul_eq_mul]
    change sineCoefficient 3 (Fin.last 3) = sineCoefficient 3 0 * 1
    rw [sineCoefficient_last, sineCoefficient_zero, mul_one]

/-- The four consecutive determinants of the golden vector are `(1,0,0,1)`. -/
theorem goldenCoefficients_consecutiveDeterminants :
    (fun t ↦ consecutiveDeterminant goldenCoefficients t) = ![1, 0, 0, 1] := by
  funext t
  fin_cases t
  · simp [goldenCoefficients]
  · rw [consecutiveDeterminant_polynomial]
    change φ ^ 3 - 2 * 1 * φ * φ + 0 * φ ^ 2 + 1 ^ 2 * 1 - 0 * φ * 1 = 0
    have hsq : (√(5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hcube : (√(5 : ℝ)) ^ 3 = 5 * √5 := by
      calc
        (√(5 : ℝ)) ^ 3 = (√5) ^ 2 * √5 := by ring
        _ = 5 * √5 := by rw [hsq]
    change ((1 + √5) / 2) ^ 3 - 2 * 1 * ((1 + √5) / 2) *
      ((1 + √5) / 2) + 0 * ((1 + √5) / 2) ^ 2 + 1 ^ 2 * 1 -
      0 * ((1 + √5) / 2) * 1 = 0
    ring_nf
    nlinarith [hsq, hcube]
  · rw [consecutiveDeterminant_polynomial]
    change φ ^ 3 - 2 * φ * φ * 1 + 1 * 1 ^ 2 + φ ^ 2 * 0 - 1 * φ * 0 = 0
    have hsq : (√(5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hcube : (√(5 : ℝ)) ^ 3 = 5 * √5 := by
      calc
        (√(5 : ℝ)) ^ 3 = (√5) ^ 2 * √5 := by ring
        _ = 5 * √5 := by rw [hsq]
    change ((1 + √5) / 2) ^ 3 - 2 * ((1 + √5) / 2) *
      ((1 + √5) / 2) * 1 + 1 * 1 ^ 2 + ((1 + √5) / 2) ^ 2 * 0 -
      1 * ((1 + √5) / 2) * 0 = 0
    ring_nf
    nlinarith [hsq, hcube]
  · simpa [goldenCoefficients] using consecutiveDeterminant_last goldenCoefficients

private theorem bandCoefficient_smul (c : ℝ) (b : Fin 4 → ℝ) (k : ℤ) :
    bandCoefficient (c • b) k = c * bandCoefficient b k := by
  unfold bandCoefficient
  split_ifs
  · simp only [Pi.smul_apply, smul_eq_mul]
  · rw [mul_zero]

/-- Consecutive determinants are homogeneous of degree three in the coefficients. -/
theorem consecutiveDeterminant_smul_four (c : ℝ) (b : Fin 4 → ℝ) (t : Fin 4) :
    consecutiveDeterminant (c • b) t = c ^ 3 * consecutiveDeterminant b t := by
  rw [consecutiveDeterminant_polynomial, consecutiveDeterminant_polynomial]
  simp_rw [bandCoefficient_smul]
  ring

/-- Before normalization, the `d = 3` sine determinants are
`sin(π/5)³ · (1,0,0,1)`. -/
theorem sineCoefficient_three_consecutiveDeterminants :
    (fun t ↦ consecutiveDeterminant (sineCoefficient 3) t) =
      sineCoefficient 3 0 ^ 3 • ![1, 0, 0, 1] := by
  let s := sineCoefficient 3 0
  have hs : sineCoefficient 3 = s • goldenCoefficients :=
    sineCoefficient_three_eq_golden
  change (fun t ↦ consecutiveDeterminant (sineCoefficient 3) t) =
    s ^ 3 • ![1, 0, 0, 1]
  rw [hs]
  funext t
  rw [consecutiveDeterminant_smul_four]
  have ht := congrFun goldenCoefficients_consecutiveDeterminants t
  rw [ht]
  fin_cases t <;> norm_num [goldenCoefficients]

end

end ToeplitzPositroids.RankThree
