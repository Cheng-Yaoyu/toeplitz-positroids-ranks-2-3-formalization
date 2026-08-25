import ToeplitzPositroids.Matrix.Configuration
import ToeplitzPositroids.RankThree.Moments
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Pascal moments for columns of three-row matrices

This file connects the coordinate identities in `RankThree.Moments` with ordered
matrix minors.  It also records the Pascal change-of-basis matrix and the
determinant-to-oriented-area identity used by the convex-chain argument.
-/

namespace ToeplitzPositroids.RankThree

open Matrix

noncomputable section

/-- The increasing embedding whose image is the ordered pair `i < j`. -/
def selectedPairEmbedding {n : ℕ} (i j : Fin n) (hij : i < j) : Fin 2 ↪o Fin n :=
  OrderEmbedding.ofStrictMono ![i, j] <| by
    intro p q hpq
    fin_cases p <;> fin_cases q
    · simp at hpq
    · exact hij
    · simp at hpq
    · simp at hpq

@[simp]
theorem selectedPairEmbedding_zero {n : ℕ} (i j : Fin n) (hij : i < j) :
    selectedPairEmbedding i j hij 0 = i :=
  rfl

@[simp]
theorem selectedPairEmbedding_one {n : ℕ} (i j : Fin n) (hij : i < j) :
    selectedPairEmbedding i j hij 1 = j :=
  rfl

/-- The increasing embedding whose image is the ordered triple `i < j < k`. -/
def selectedTripleEmbedding {n : ℕ} (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    Fin 3 ↪o Fin n :=
  OrderEmbedding.ofStrictMono ![i, j, k] <| by
    intro p q hpq
    fin_cases p <;> fin_cases q
    · simp at hpq
    · exact hij
    · exact hij.trans hjk
    · simp at hpq
    · simp at hpq
    · exact hjk
    · simp at hpq
    · simp at hpq
    · simp at hpq

@[simp]
theorem selectedTripleEmbedding_zero {n : ℕ} (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    selectedTripleEmbedding i j k hij hjk 0 = i :=
  rfl

@[simp]
theorem selectedTripleEmbedding_one {n : ℕ} (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    selectedTripleEmbedding i j k hij hjk 1 = j :=
  rfl

@[simp]
theorem selectedTripleEmbedding_two {n : ℕ} (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    selectedTripleEmbedding i j k hij hjk 2 = k :=
  rfl

/-- The ordered pair consisting of the first and second rows. -/
def rows12 : Fin 2 ↪o Fin 3 :=
  selectedPairEmbedding 0 1 (by decide)

/-- The ordered pair consisting of the first and third rows. -/
def rows13 : Fin 2 ↪o Fin 3 :=
  selectedPairEmbedding 0 2 (by decide)

/-- The ordered pair consisting of the second and third rows. -/
def rows23 : Fin 2 ↪o Fin 3 :=
  selectedPairEmbedding 1 2 (by decide)

@[simp]
theorem rows12_zero : rows12 0 = 0 :=
  rfl

@[simp]
theorem rows12_one : rows12 1 = 1 :=
  rfl

@[simp]
theorem rows13_zero : rows13 0 = 0 :=
  rfl

@[simp]
theorem rows13_one : rows13 1 = 2 :=
  rfl

@[simp]
theorem rows23_zero : rows23 0 = 1 :=
  rfl

@[simp]
theorem rows23_one : rows23 1 = 2 :=
  rfl

/-- The first coordinate minor of two selected columns is their ordered minor on rows `12`. -/
theorem coordinateMinor12_cols_eq_orderedMinor {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ)
    {i j : Fin n} (hij : i < j) :
    coordinateMinor12 (A.col i) (A.col j) =
      orderedMinor A rows12 (selectedPairEmbedding i j hij) := by
  rw [orderedMinor_two]
  simp only [coordinateMinor12, rows12_zero, rows12_one, selectedPairEmbedding_zero,
    selectedPairEmbedding_one, col_apply]
  ring

/-- The second coordinate minor of two selected columns is their ordered minor on rows `13`. -/
theorem coordinateMinor13_cols_eq_orderedMinor {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ)
    {i j : Fin n} (hij : i < j) :
    coordinateMinor13 (A.col i) (A.col j) =
      orderedMinor A rows13 (selectedPairEmbedding i j hij) := by
  rw [orderedMinor_two]
  simp only [coordinateMinor13, rows13_zero, rows13_one, selectedPairEmbedding_zero,
    selectedPairEmbedding_one, col_apply]
  ring

/-- The third coordinate minor of two selected columns is their ordered minor on rows `23`. -/
theorem coordinateMinor23_cols_eq_orderedMinor {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ)
    {i j : Fin n} (hij : i < j) :
    coordinateMinor23 (A.col i) (A.col j) =
      orderedMinor A rows23 (selectedPairEmbedding i j hij) := by
  rw [orderedMinor_two]
  simp only [coordinateMinor23, rows23_zero, rows23_one, selectedPairEmbedding_zero,
    selectedPairEmbedding_one, col_apply]
  ring

/-- Every column of a matrix that is totally nonnegative through order two is nonnegative. -/
theorem col_nonnegative_of_tnUpTo_two {n : ℕ} {A : Matrix (Fin 3) (Fin n) ℝ}
    (hA : TNUpTo A 2) (j : Fin n) :
    Nonnegative (A.col j) := by
  intro i
  exact hA.entry_nonneg (by norm_num) i j

/-- The three coordinate minors of an increasing column pair are nonnegative under `TN₂`. -/
theorem coordinateMinors_cols_nonneg_of_tnUpTo_two {n : ℕ}
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : TNUpTo A 2) {i j : Fin n} (hij : i < j) :
    0 ≤ coordinateMinor12 (A.col i) (A.col j) ∧
      0 ≤ coordinateMinor13 (A.col i) (A.col j) ∧
        0 ≤ coordinateMinor23 (A.col i) (A.col j) := by
  constructor
  · rw [coordinateMinor12_cols_eq_orderedMinor A hij]
    exact hA.orderedMinor_nonneg le_rfl rows12 (selectedPairEmbedding i j hij)
  constructor
  · rw [coordinateMinor13_cols_eq_orderedMinor A hij]
    exact hA.orderedMinor_nonneg le_rfl rows13 (selectedPairEmbedding i j hij)
  · rw [coordinateMinor23_cols_eq_orderedMinor A hij]
    exact hA.orderedMinor_nonneg le_rfl rows23 (selectedPairEmbedding i j hij)

/-- Vector-level positive parallelism agrees with the shared matrix-column predicate. -/
theorem positivelyParallel_cols_iff {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ) (i j : Fin n) :
    PositivelyParallel (A.col i) (A.col j) ↔ ColumnsPositivelyParallel A i j :=
  Iff.rfl

/-- Pascal first moments weakly increase along nonloop columns of a `TN₂` matrix. -/
theorem momentU_col_le_of_tnUpTo_two {n : ℕ} {A : Matrix (Fin 3) (Fin n) ℝ}
    (hA : TNUpTo A 2) {i j : Fin n} (hij : i < j) (hi : ¬IsLoop A i)
    (hj : ¬IsLoop A j) :
    momentU (A.col i) ≤ momentU (A.col j) := by
  have hi0 : A.col i ≠ 0 := by simpa only [IsLoop] using hi
  have hj0 : A.col j ≠ 0 := by simpa only [IsLoop] using hj
  rcases coordinateMinors_cols_nonneg_of_tnUpTo_two hA hij with ⟨h12, h13, h23⟩
  exact momentU_le_of_coordinateMinors_nonneg
    (col_nonnegative_of_tnUpTo_two hA i) hi0 (col_nonnegative_of_tnUpTo_two hA j) hj0
      h12 h13 h23

/-- Equality of first moments along nonloop columns of a `TN₂` matrix is exactly positive
parallelism of those columns. -/
theorem momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two {n : ℕ}
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : TNUpTo A 2) {i j : Fin n} (hij : i < j)
    (hi : ¬IsLoop A i) (hj : ¬IsLoop A j) :
    momentU (A.col i) = momentU (A.col j) ↔ ColumnsPositivelyParallel A i j := by
  have hi0 : A.col i ≠ 0 := by simpa only [IsLoop] using hi
  have hj0 : A.col j ≠ 0 := by simpa only [IsLoop] using hj
  rcases coordinateMinors_cols_nonneg_of_tnUpTo_two hA hij with ⟨h12, h13, h23⟩
  rw [← positivelyParallel_cols_iff]
  exact momentU_eq_iff_positivelyParallel
    (col_nonnegative_of_tnUpTo_two hA i) hi0 (col_nonnegative_of_tnUpTo_two hA j) hj0
      h12 h13 h23

/-- Pascal first moments strictly increase between distinct positive-parallel classes of a
`TN₂` matrix. -/
theorem momentU_col_lt_of_tnUpTo_two_of_not_positivelyParallel {n : ℕ}
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : TNUpTo A 2) {i j : Fin n} (hij : i < j)
    (hi : ¬IsLoop A i) (hj : ¬IsLoop A j) (hijParallel : ¬ColumnsPositivelyParallel A i j) :
    momentU (A.col i) < momentU (A.col j) := by
  have hi0 : A.col i ≠ 0 := by simpa only [IsLoop] using hi
  have hj0 : A.col j ≠ 0 := by simpa only [IsLoop] using hj
  have hnot : ¬PositivelyParallel (A.col i) (A.col j) := by
    simpa only [positivelyParallel_cols_iff] using hijParallel
  rcases coordinateMinors_cols_nonneg_of_tnUpTo_two hA hij with ⟨h12, h13, h23⟩
  exact momentU_lt_of_coordinateMinors_nonneg_of_not_positivelyParallel
    (col_nonnegative_of_tnUpTo_two hA i) hi0 (col_nonnegative_of_tnUpTo_two hA j) hj0
      h12 h13 h23 hnot

/-- The Pascal matrix sending a column to its unnormalized moment coordinates. -/
def pascalMomentMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 1; 0, 1, 2; 0, 0, 1]

/-- The Pascal moment matrix has determinant one. -/
@[simp]
theorem pascalMomentMatrix_det : pascalMomentMatrix.det = 1 := by
  norm_num [pascalMomentMatrix, Matrix.det_fin_three, Matrix.cons_val_two]

/-- Multiplication by the Pascal matrix gives the three unnormalized moment coordinates. -/
theorem pascalMomentMatrix_mulVec (c : Column) :
    pascalMomentMatrix *ᵥ c = ![momentSum c, c 1 + 2 * c 2, c 2] := by
  funext i
  fin_cases i <;> simp [pascalMomentMatrix, Matrix.mulVec, momentSum, Matrix.vecHead,
    Matrix.vecTail]
  ring

/-- The normalized Pascal image is the affine moment column `(1, u, v)`. -/
theorem normalized_pascalMomentMatrix_mulVec {c : Column} (hc : momentSum c ≠ 0) :
    (momentSum c)⁻¹ • (pascalMomentMatrix *ᵥ c) = ![1, momentU c, momentV c] := by
  rw [pascalMomentMatrix_mulVec]
  funext i
  fin_cases i
  · simp [hc]
  · simp [momentU, div_eq_inv_mul]
  · simp [momentV, div_eq_inv_mul]

/-- The square matrix having `c`, `d`, and `e` as its three columns. -/
def threeColumnMatrix (c d e : Column) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![c 0, d 0, e 0; c 1, d 1, e 1; c 2, d 2, e 2]

/-- The ordered maximal minor on `i < j < k` is the determinant of the matrix made from those
three columns. -/
theorem orderedMinor_selectedTriple_eq_threeColumnMatrix_det {n : ℕ}
    (A : Matrix (Fin 3) (Fin n) ℝ) {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) =
      (threeColumnMatrix (A.col i) (A.col j) (A.col k)).det := by
  apply congrArg Matrix.det
  ext p q
  fin_cases p <;> fin_cases q <;> rfl

/-- The affine matrix of the three moment points. -/
def momentPointMatrix (c d e : Column) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 1; momentU c, momentU d, momentU e; momentV c, momentV d, momentV e]

/-- Twice the signed affine area of the three moment points. -/
def momentOrientedArea (c d e : Column) : ℝ :=
  (momentU d - momentU c) * (momentV e - momentV d) -
    (momentV d - momentV c) * (momentU e - momentU d)

/-- The determinant of the affine moment matrix is its oriented area. -/
theorem momentPointMatrix_det (c d e : Column) :
    (momentPointMatrix c d e).det = momentOrientedArea c d e := by
  rw [Matrix.det_fin_three]
  change
    1 * momentU d * momentV e - 1 * momentU e * momentV d -
          1 * momentU c * momentV e + 1 * momentU e * momentV c +
        1 * momentU c * momentV d - 1 * momentU d * momentV c =
      momentOrientedArea c d e
  rw [momentOrientedArea]
  ring

/-- A three-column determinant is the product of the coordinate sums and the oriented area of
the corresponding moment points.  This is equation (5.8) of the paper. -/
theorem threeColumnMatrix_det_eq_momentOrientedArea {c d e : Column}
    (hc : momentSum c ≠ 0) (hd : momentSum d ≠ 0) (he : momentSum e ≠ 0) :
    (threeColumnMatrix c d e).det =
      momentSum c * momentSum d * momentSum e * momentOrientedArea c d e := by
  rw [Matrix.det_fin_three]
  change
    c 0 * d 1 * e 2 - c 0 * e 1 * d 2 - d 0 * c 1 * e 2 +
          d 0 * e 1 * c 2 + e 0 * c 1 * d 2 - e 0 * d 1 * c 2 =
      momentSum c * momentSum d * momentSum e * momentOrientedArea c d e
  rw [momentOrientedArea, momentU, momentU, momentU, momentV, momentV, momentV]
  simp only [momentSum] at hc hd he ⊢
  field_simp
  ring

/-- Equation (5.8) in its determinant-of-the-affine-moment-matrix form. -/
theorem threeColumnMatrix_det_eq_momentPointMatrix_det {c d e : Column}
    (hc : momentSum c ≠ 0) (hd : momentSum d ≠ 0) (he : momentSum e ≠ 0) :
    (threeColumnMatrix c d e).det =
      momentSum c * momentSum d * momentSum e * (momentPointMatrix c d e).det := by
  rw [momentPointMatrix_det]
  exact threeColumnMatrix_det_eq_momentOrientedArea hc hd he

/-- Equation (5.8) directly for an increasingly selected maximal minor of a three-row matrix. -/
theorem orderedMinor_selectedTriple_eq_momentOrientedArea {n : ℕ}
    (A : Matrix (Fin 3) (Fin n) ℝ) {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hi : momentSum (A.col i) ≠ 0) (hj : momentSum (A.col j) ≠ 0)
    (hk : momentSum (A.col k) ≠ 0) :
    orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) =
      momentSum (A.col i) * momentSum (A.col j) * momentSum (A.col k) *
        momentOrientedArea (A.col i) (A.col j) (A.col k) := by
  rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det A hij hjk]
  exact threeColumnMatrix_det_eq_momentOrientedArea hi hj hk

end

end ToeplitzPositroids.RankThree
