import ToeplitzPositroids.RankThree.ConvexMatrix
import ToeplitzPositroids.RankThree.Simplification
import Lean.Elab.Tactic.Omega

/-!
# The convex-chain criterion with loops and parallel columns

This file proves the full convex-chain criterion for an arbitrary three-row
matrix.  Loops are deleted and each positive-parallel class is replaced by its
least-index representative.  Total nonnegativity is then equivalent to order-two
total nonnegativity together with monotonicity of the consecutive slopes of this
canonical simplified moment chain.
-/

namespace ToeplitzPositroids.RankThree

open Matrix

noncomputable section

variable {n : ℕ} {A : Matrix (Fin 3) (Fin n) ℝ}

/-- The first coordinates of the canonical simplified moment chain. -/
def simplifiedMomentU (A : Matrix (Fin 3) (Fin n) ℝ) : ℕ → ℝ :=
  matrixMomentU (simplifiedMatrix A)

/-- The second coordinates of the canonical simplified moment chain. -/
def simplifiedMomentV (A : Matrix (Fin 3) (Fin n) ℝ) : ℕ → ℝ :=
  matrixMomentV (simplifiedMatrix A)

/-- The canonical sequence of consecutive edge slopes after deleting loops and repeated
positive-parallel classes. -/
def simplifiedEdgeSlope (A : Matrix (Fin 3) (Fin n) ℝ) (i : ℕ) : ℝ :=
  edgeSlope (simplifiedMomentU A) (simplifiedMomentV A) i

/-- The consecutive slopes of the canonical simplified moment chain are weakly increasing. -/
def SimplifiedSlopesMonotone (A : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  SlopesMonotoneUpTo (simplifiedMomentU A) (simplifiedMomentV A) (simplificationSize A)

@[simp]
theorem simplifiedEdgeSlope_eq (A : Matrix (Fin 3) (Fin n) ℝ) (i : ℕ) :
    simplifiedEdgeSlope A i =
      edgeSlope (matrixMomentU (simplifiedMatrix A))
        (matrixMomentV (simplifiedMatrix A)) i :=
  rfl

/-- When the simplification has at most two vertices, its slope monotonicity condition is
vacuous. -/
theorem simplifiedSlopesMonotone_of_size_le_two
    (A : Matrix (Fin 3) (Fin n) ℝ) (hsize : simplificationSize A ≤ 2) :
    SimplifiedSlopesMonotone A := by
  intro i j _ hj
  have hij : i = j := by omega
  subst j
  exact le_rfl

/-- The canonical simplified matrix is a simple nonloop configuration. -/
theorem simplifiedMatrix_isSimpleNonloopConfiguration
    (A : Matrix (Fin 3) (Fin n) ℝ) :
    IsSimpleNonloopConfiguration (simplifiedMatrix A) := by
  constructor
  · exact simplifiedMatrix_not_isLoop A
  · intro i j hij hpar
    exact hij.ne ((simplifiedMatrix_columnsPositivelyParallel_iff A i j).mp hpar)

/-- Canonical class numbers preserve the weak order of nonloop columns under `TN₂`. -/
theorem simplificationClassIndex_mono_of_tnUpTo_two (hA : TNUpTo A 2)
    {i j : Fin n} (hij : i ≤ j) (hi : ¬IsLoop A i) (hj : ¬IsLoop A j) :
    simplificationClassIndex A i hi ≤ simplificationClassIndex A j hj := by
  apply le_of_not_gt
  intro hji
  have hstrict := momentU_simplificationEmbedding_strictMono hA hji
  have hui :
      momentU (A.col (simplificationEmbedding A (simplificationClassIndex A i hi))) =
        momentU (A.col i) :=
    (momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two' hA
      (simplificationEmbedding_not_isLoop A _) hi).mpr
        (simplificationClassIndex_parallel A i hi)
  have huj :
      momentU (A.col (simplificationEmbedding A (simplificationClassIndex A j hj))) =
        momentU (A.col j) :=
    (momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two' hA
      (simplificationEmbedding_not_isLoop A _) hj).mpr
        (simplificationClassIndex_parallel A j hj)
  have huij := momentU_col_mono_of_tnUpTo_two hA hij hi hj
  linarith

/-- Two nonloop columns have the same canonical class number exactly when they are positively
parallel. -/
theorem simplificationClassIndex_eq_iff_columnsPositivelyParallel
    (A : Matrix (Fin 3) (Fin n) ℝ) {i j : Fin n} (hi : ¬IsLoop A i) (hj : ¬IsLoop A j) :
    simplificationClassIndex A i hi = simplificationClassIndex A j hj ↔
      ColumnsPositivelyParallel A i j := by
  constructor
  · intro hclass
    have hiPar := simplificationClassIndex_parallel A i hi
    have hjPar := simplificationClassIndex_parallel A j hj
    exact columnsPositivelyParallel_trans (columnsPositivelyParallel_symm hiPar)
      (hclass ▸ hjPar)
  · intro hij
    apply (simplificationEmbedding A).injective
    rw [simplificationEmbedding_classIndex_eq_parallelRepresentative,
      simplificationEmbedding_classIndex_eq_parallelRepresentative]
    exact parallelRepresentative_eq_iff.mpr hij

/-- The determinant of three independently rescaled columns acquires the product of the three
scalars. -/
theorem threeColumnMatrix_det_smul (a b c : ℝ) (x y z : Column) :
    (threeColumnMatrix (a • x) (b • y) (c • z)).det =
      a * b * c * (threeColumnMatrix x y z).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  change
    (a * x 0) * (b * y 1) * (c * z 2) - (a * x 0) * (c * z 1) * (b * y 2) -
          (b * y 0) * (a * x 1) * (c * z 2) + (b * y 0) * (c * z 1) * (a * x 2) +
        (c * z 0) * (a * x 1) * (b * y 2) - (c * z 0) * (b * y 1) * (a * x 2) =
      a * b * c *
        (x 0 * y 1 * z 2 - x 0 * z 1 * y 2 - y 0 * x 1 * z 2 +
            y 0 * z 1 * x 2 + z 0 * x 1 * y 2 - z 0 * y 1 * x 2)
  ring

/-- An ordered maximal minor is the determinant of the matrix made from its three columns. -/
theorem orderedMinor_allRows_eq_threeColumnMatrix_det
    (A : Matrix (Fin 3) (Fin n) ℝ) (cols : Fin 3 ↪o Fin n) :
    orderedMinor A (allRows 3) cols =
      (threeColumnMatrix (A.col (cols 0)) (A.col (cols 1)) (A.col (cols 2))).det := by
  rw [← selectedTripleEmbedding_eq cols]
  exact orderedMinor_selectedTriple_eq_threeColumnMatrix_det A
    (cols.strictMono (by decide)) (cols.strictMono (by decide))

/-- A maximal minor containing a loop is zero. -/
theorem orderedMinor_allRows_eq_zero_of_isLoop
    (A : Matrix (Fin 3) (Fin n) ℝ) (cols : Fin 3 ↪o Fin n) (p : Fin 3)
    (hp : IsLoop A (cols p)) :
    orderedMinor A (allRows 3) cols = 0 := by
  rw [orderedMinor]
  rw [IsLoop] at hp
  apply Matrix.det_eq_zero_of_column_eq_zero p
  intro i
  exact congrFun hp (allRows 3 i)

/-- A maximal minor containing two positively parallel columns is zero. -/
theorem orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel
    (A : Matrix (Fin 3) (Fin n) ℝ) (cols : Fin 3 ↪o Fin n) {p q : Fin 3}
    (hpq : p ≠ q) (hpar : ColumnsPositivelyParallel A (cols p) (cols q)) :
    orderedMinor A (allRows 3) cols = 0 := by
  rw [orderedMinor]
  rcases hpar with ⟨a, _, hcol⟩
  let M := A.submatrix (allRows 3) cols
  change M.det = 0
  have hM : M = M.updateCol q (a • M.col p) := by
    ext i j
    by_cases hjq : j = q
    · subst j
      rw [Matrix.updateCol_self]
      change A (allRows 3 i) (cols q) = a * A (allRows 3 i) (cols p)
      simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hcol (allRows 3 i)
    · rw [Matrix.updateCol_apply, if_neg hjq]
  have hzero : (M.updateCol q (M.col p)).det = 0 := by
    exact Matrix.det_updateCol_eq_zero hpq
  rw [hM, Matrix.det_updateCol_smul, hzero, mul_zero]

/-- An increasing nonloop triple in three distinct simplification classes is a positive
independent rescaling of a uniquely ordered triple of simplified columns. -/
theorem exists_ordered_simplificationTriple_and_scaledMinor (hA : TNUpTo A 2)
    {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hi : ¬IsLoop A i) (hj : ¬IsLoop A j) (hk : ¬IsLoop A k)
    (hijClass : simplificationClassIndex A i hi ≠ simplificationClassIndex A j hj)
    (hjkClass : simplificationClassIndex A j hj ≠ simplificationClassIndex A k hk) :
    ∃ (p q r : Fin (simplificationSize A)), ∃ (hpq : p < q) (hqr : q < r),
      p = simplificationClassIndex A i hi ∧
      q = simplificationClassIndex A j hj ∧
      r = simplificationClassIndex A k hk ∧
      ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
        orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) =
          a * b * c * orderedMinor (simplifiedMatrix A) (allRows 3)
            (selectedTripleEmbedding p q r hpq hqr) := by
  let p := simplificationClassIndex A i hi
  let q := simplificationClassIndex A j hj
  let r := simplificationClassIndex A k hk
  have hpq : p < q := lt_of_le_of_ne
    (simplificationClassIndex_mono_of_tnUpTo_two hA hij.le hi hj) hijClass
  have hqr : q < r := lt_of_le_of_ne
    (simplificationClassIndex_mono_of_tnUpTo_two hA hjk.le hj hk) hjkClass
  rcases simplificationClassIndex_parallel A i hi with ⟨a, ha, hcola⟩
  rcases simplificationClassIndex_parallel A j hj with ⟨b, hb, hcolb⟩
  rcases simplificationClassIndex_parallel A k hk with ⟨c, hc, hcolc⟩
  have hcola' : A.col i = a • (simplifiedMatrix A).col p := by
    simpa only [p, simplifiedMatrix_col] using hcola
  have hcolb' : A.col j = b • (simplifiedMatrix A).col q := by
    simpa only [q, simplifiedMatrix_col] using hcolb
  have hcolc' : A.col k = c • (simplifiedMatrix A).col r := by
    simpa only [r, simplifiedMatrix_col] using hcolc
  refine ⟨p, q, r, hpq, hqr, rfl, rfl, rfl, a, b, c, ha, hb, hc, ?_⟩
  rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det,
    orderedMinor_selectedTriple_eq_threeColumnMatrix_det, hcola', hcolb', hcolc']
  exact threeColumnMatrix_det_smul a b c _ _ _

/-- Nonnegativity of all maximal minors of the canonical simplification lifts through loops
and positive rescalings to the original matrix. -/
theorem maximalMinorsNonnegative_of_simplifiedMatrix (hA : TNUpTo A 2)
    (hmax : MaximalMinorsNonnegative (simplifiedMatrix A)) :
    MaximalMinorsNonnegative A := by
  intro cols
  by_cases h0 : IsLoop A (cols 0)
  · exact le_of_eq (orderedMinor_allRows_eq_zero_of_isLoop A cols 0 h0).symm
  by_cases h1 : IsLoop A (cols 1)
  · exact le_of_eq (orderedMinor_allRows_eq_zero_of_isLoop A cols 1 h1).symm
  by_cases h2 : IsLoop A (cols 2)
  · exact le_of_eq (orderedMinor_allRows_eq_zero_of_isLoop A cols 2 h2).symm
  have h01 : cols 0 < cols 1 := cols.strictMono (by decide)
  have h12 : cols 1 < cols 2 := cols.strictMono (by decide)
  let p := simplificationClassIndex A (cols 0) h0
  let q := simplificationClassIndex A (cols 1) h1
  let r := simplificationClassIndex A (cols 2) h2
  by_cases hpq : p = q
  · have hpar : ColumnsPositivelyParallel A (cols 0) (cols 1) :=
      (simplificationClassIndex_eq_iff_columnsPositivelyParallel A h0 h1).mp hpq
    exact le_of_eq
      (orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel A cols
        (by decide) hpar).symm
  by_cases hqr : q = r
  · have hpar : ColumnsPositivelyParallel A (cols 1) (cols 2) :=
      (simplificationClassIndex_eq_iff_columnsPositivelyParallel A h1 h2).mp hqr
    exact le_of_eq
      (orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel A cols
        (by decide) hpar).symm
  rcases exists_ordered_simplificationTriple_and_scaledMinor hA h01 h12 h0 h1 h2 hpq hqr with
    ⟨p', q', r', hpq', hqr', _, _, _, a, b, c, ha, hb, hc, hscale⟩
  rw [selectedTripleEmbedding_eq cols] at hscale
  rw [hscale]
  exact mul_nonneg (mul_nonneg (mul_nonneg ha.le hb.le) hc.le)
    (hmax (selectedTripleEmbedding p' q' r' hpq' hqr'))

/-- Under `TN₂`, maximal-minor nonnegativity is unchanged by canonical simplification. -/
theorem maximalMinorsNonnegative_iff_simplifiedMatrix (hA : TNUpTo A 2) :
    MaximalMinorsNonnegative A ↔ MaximalMinorsNonnegative (simplifiedMatrix A) := by
  constructor
  · intro hmax
    have hTNN : TotallyNonnegative A :=
      (totallyNonnegative_fin_three_iff A).mpr ⟨hA, hmax⟩
    have hSimplified : TotallyNonnegative (simplifiedMatrix A) :=
      hTNN.submatrix (allRows 3) (simplificationEmbedding A)
    exact ((totallyNonnegative_fin_three_iff (simplifiedMatrix A)).mp hSimplified).2
  · exact maximalMinorsNonnegative_of_simplifiedMatrix hA

/-- Canonical simplified slope monotonicity can be checked on adjacent edge slopes. -/
theorem simplifiedSlopesMonotone_iff_consecutive (hA : TNUpTo A 2) :
    SimplifiedSlopesMonotone A ↔
      ∀ i : ℕ, i + 2 < simplificationSize A →
        simplifiedEdgeSlope A i ≤ simplifiedEdgeSlope A (i + 1) := by
  exact slopesMonotoneUpTo_iff_consecutive _ _
    (matrixMomentU_strictlyIncreasingUpTo (simplifiedMatrix_tnUpTo_two hA)
      (simplifiedMatrix_isSimpleNonloopConfiguration A))

/-- The full convex-chain criterion: a three-row matrix is totally nonnegative exactly when it
is totally nonnegative through order two and the canonical simplified moment slopes are weakly
increasing.  The slope condition is automatically vacuous when the simplification has at most
two columns. -/
theorem totallyNonnegative_iff_tnUpTo_two_and_simplifiedSlopesMonotone
    (A : Matrix (Fin 3) (Fin n) ℝ) :
    TotallyNonnegative A ↔ TNUpTo A 2 ∧ SimplifiedSlopesMonotone A := by
  constructor
  · intro hA
    have hTwo : TNUpTo A 2 := hA.tnUpTo 2
    have hSimplified : TotallyNonnegative (simplifiedMatrix A) :=
      hA.submatrix (allRows 3) (simplificationEmbedding A)
    have hSlopes :
        SlopesMonotoneUpTo (matrixMomentU (simplifiedMatrix A))
          (matrixMomentV (simplifiedMatrix A)) (simplificationSize A) :=
      (totallyNonnegative_iff_momentSlopesMonotone
        (simplifiedMatrix_tnUpTo_two hTwo)
        (simplifiedMatrix_isSimpleNonloopConfiguration A)).mp hSimplified
    refine ⟨hTwo, ?_⟩
    exact hSlopes
  · rintro ⟨hTwo, hSlopes⟩
    have hSlopes' :
        SlopesMonotoneUpTo (matrixMomentU (simplifiedMatrix A))
          (matrixMomentV (simplifiedMatrix A)) (simplificationSize A) := by
      exact hSlopes
    have hSimplified : TotallyNonnegative (simplifiedMatrix A) :=
      (totallyNonnegative_iff_momentSlopesMonotone
        (simplifiedMatrix_tnUpTo_two hTwo)
        (simplifiedMatrix_isSimpleNonloopConfiguration A)).mpr hSlopes'
    have hMax : MaximalMinorsNonnegative (simplifiedMatrix A) :=
      ((totallyNonnegative_fin_three_iff (simplifiedMatrix A)).mp hSimplified).2
    exact (totallyNonnegative_fin_three_iff A).mpr
      ⟨hTwo, maximalMinorsNonnegative_of_simplifiedMatrix hTwo hMax⟩

/-- For three distinct selected simplification classes, a maximal minor vanishes exactly when
all simplified edge slopes between the first and last class are equal. -/
theorem orderedMinor_simplified_eq_zero_iff_slopesConstantBetween
    (hA : TNUpTo A 2) (hSlopes : SimplifiedSlopesMonotone A)
    {p q r : Fin (simplificationSize A)} (hpq : p < q) (hqr : q < r) :
    orderedMinor (simplifiedMatrix A) (allRows 3)
        (selectedTripleEmbedding p q r hpq hqr) = 0 ↔
      SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A) p.val r.val := by
  have hSlopes' :
      SlopesMonotoneUpTo (matrixMomentU (simplifiedMatrix A))
        (matrixMomentV (simplifiedMatrix A)) (simplificationSize A) := by
    exact hSlopes
  simpa only [simplifiedMomentU, simplifiedMomentV] using
    (orderedMinor_selectedTriple_eq_zero_iff_slopesConstantBetween
      (simplifiedMatrix_tnUpTo_two hA)
      (simplifiedMatrix_isSimpleNonloopConfiguration A) hSlopes' hpq hqr)

/-- The exact zero criterion for an arbitrary increasing nonloop triple in three distinct
simplification classes.  Positive rescaling back to the original columns does not change
whether the determinant vanishes. -/
theorem orderedMinor_selectedTriple_eq_zero_iff_simplifiedSlopesConstantBetween
    (hA : TNUpTo A 2) (hSlopes : SimplifiedSlopesMonotone A)
    {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hi : ¬IsLoop A i) (hj : ¬IsLoop A j) (hk : ¬IsLoop A k)
    (hijClass : simplificationClassIndex A i hi ≠ simplificationClassIndex A j hj)
    (hjkClass : simplificationClassIndex A j hj ≠ simplificationClassIndex A k hk) :
    orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) = 0 ↔
      SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A)
        (simplificationClassIndex A i hi).val (simplificationClassIndex A k hk).val := by
  rcases exists_ordered_simplificationTriple_and_scaledMinor hA hij hjk hi hj hk
      hijClass hjkClass with
    ⟨p, q, r, hpq, hqr, rfl, rfl, rfl, a, b, c, ha, hb, hc, hscale⟩
  rw [hscale, mul_eq_zero]
  simp only [mul_ne_zero (mul_ne_zero ha.ne' hb.ne') hc.ne', false_or]
  exact orderedMinor_simplified_eq_zero_iff_slopesConstantBetween hA hSlopes hpq hqr

end

end ToeplitzPositroids.RankThree
