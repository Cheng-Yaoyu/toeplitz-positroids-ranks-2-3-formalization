import ToeplitzPositroids.Geometry.ConvexChain
import ToeplitzPositroids.Matrix.ThreeRows
import ToeplitzPositroids.RankThree.MomentMatrix
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Convex chains attached to simple three-row configurations

This file connects the discrete convex-chain results to three-row matrices via
the Pascal moment coordinates.  It proves the core form of the paper's
convex-chain criterion under the explicit assumptions that every column is
nonzero and no increasing pair of columns is positively parallel.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- Every column is nonzero and no two distinct ordered columns are positively parallel. -/
def IsSimpleNonloopConfiguration {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  (∀ j, ¬IsLoop A j) ∧
    ∀ {i j : Fin n}, i < j → ¬ColumnsPositivelyParallel A i j

/-- The first Pascal moments of a finite matrix, extended by zero outside its column range. -/
def matrixMomentU {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then momentU (A.col ⟨i, hi⟩) else 0

/-- The second Pascal moments of a finite matrix, extended by zero outside its column range. -/
def matrixMomentV {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then momentV (A.col ⟨i, hi⟩) else 0

@[simp]
theorem matrixMomentU_apply_of_lt {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ) {i : ℕ}
    (hi : i < n) :
    matrixMomentU A i = momentU (A.col ⟨i, hi⟩) := by
  simp [matrixMomentU, hi]

@[simp]
theorem matrixMomentV_apply_of_lt {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ) {i : ℕ}
    (hi : i < n) :
    matrixMomentV A i = momentV (A.col ⟨i, hi⟩) := by
  simp [matrixMomentV, hi]

@[simp]
theorem matrixMomentU_apply_fin {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ) (i : Fin n) :
    matrixMomentU A i.val = momentU (A.col i) := by
  simp [matrixMomentU]

@[simp]
theorem matrixMomentV_apply_fin {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ) (i : Fin n) :
    matrixMomentV A i.val = momentV (A.col i) := by
  simp [matrixMomentV]

/-- Under `TN₂`, the first moment coordinates of a simple nonloop configuration strictly
increase in column order. -/
theorem matrixMomentU_strictlyIncreasingUpTo {n : ℕ}
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : TNUpTo A 2)
    (hsimple : IsSimpleNonloopConfiguration A) :
    StrictlyIncreasingUpTo (matrixMomentU A) n := by
  intro i j hij hjn
  have hin : i < n := hij.trans hjn
  let i' : Fin n := ⟨i, hin⟩
  let j' : Fin n := ⟨j, hjn⟩
  have hij' : i' < j' := by
    simpa [i', j'] using hij
  have hlt := momentU_col_lt_of_tnUpTo_two_of_not_positivelyParallel hA hij'
    (hsimple.1 i') (hsimple.1 j') (hsimple.2 hij')
  simpa [matrixMomentU, hin, hjn, i', j'] using hlt

/-- An increasingly selected triple is determined by the images of `0`, `1`, and `2`. -/
theorem selectedTripleEmbedding_eq {n : ℕ} (cols : Fin 3 ↪o Fin n) :
    selectedTripleEmbedding (cols 0) (cols 1) (cols 2)
      (cols.strictMono (by decide)) (cols.strictMono (by decide)) = cols := by
  apply RelEmbedding.ext
  intro i
  fin_cases i <;> rfl

/-- The matrix moment area agrees with the natural-number-indexed oriented area. -/
theorem momentOrientedArea_eq_orientedArea_matrixMoments {n : ℕ}
    (A : Matrix (Fin 3) (Fin n) ℝ) (i j k : Fin n) :
    momentOrientedArea (A.col i) (A.col j) (A.col k) =
      orientedArea (matrixMomentU A) (matrixMomentV A) i.val j.val k.val := by
  simp only [momentOrientedArea, orientedArea, matrixMomentU_apply_fin,
    matrixMomentV_apply_fin]

/-- For an increasing triple of nonloop columns of a `TN₂` matrix, nonnegativity of the
maximal minor is equivalent to nonnegativity of the corresponding moment area. -/
theorem orderedMinor_selectedTriple_nonneg_iff_momentOrientedArea_nonneg {n : ℕ}
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : TNUpTo A 2) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (hi : ¬IsLoop A i) (hj : ¬IsLoop A j)
    (hk : ¬IsLoop A k) :
    0 ≤ orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) ↔
      0 ≤ momentOrientedArea (A.col i) (A.col j) (A.col k) := by
  have hi0 : A.col i ≠ 0 := by simpa only [IsLoop] using hi
  have hj0 : A.col j ≠ 0 := by simpa only [IsLoop] using hj
  have hk0 : A.col k ≠ 0 := by simpa only [IsLoop] using hk
  have hsi : 0 < momentSum (A.col i) :=
    momentSum_pos (col_nonnegative_of_tnUpTo_two hA i) hi0
  have hsj : 0 < momentSum (A.col j) :=
    momentSum_pos (col_nonnegative_of_tnUpTo_two hA j) hj0
  have hsk : 0 < momentSum (A.col k) :=
    momentSum_pos (col_nonnegative_of_tnUpTo_two hA k) hk0
  rw [orderedMinor_selectedTriple_eq_momentOrientedArea A hij hjk hsi.ne' hsj.ne' hsk.ne']
  exact mul_nonneg_iff_of_pos_left (mul_pos (mul_pos hsi hsj) hsk)

/-- For an increasing triple of nonloop columns of a `TN₂` matrix, vanishing of the maximal
minor is equivalent to vanishing of its moment area. -/
theorem orderedMinor_selectedTriple_eq_zero_iff_momentOrientedArea_eq_zero {n : ℕ}
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : TNUpTo A 2) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (hi : ¬IsLoop A i) (hj : ¬IsLoop A j)
    (hk : ¬IsLoop A k) :
    orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) = 0 ↔
      momentOrientedArea (A.col i) (A.col j) (A.col k) = 0 := by
  have hi0 : A.col i ≠ 0 := by simpa only [IsLoop] using hi
  have hj0 : A.col j ≠ 0 := by simpa only [IsLoop] using hj
  have hk0 : A.col k ≠ 0 := by simpa only [IsLoop] using hk
  have hsi : 0 < momentSum (A.col i) :=
    momentSum_pos (col_nonnegative_of_tnUpTo_two hA i) hi0
  have hsj : 0 < momentSum (A.col j) :=
    momentSum_pos (col_nonnegative_of_tnUpTo_two hA j) hj0
  have hsk : 0 < momentSum (A.col k) :=
    momentSum_pos (col_nonnegative_of_tnUpTo_two hA k) hk0
  rw [orderedMinor_selectedTriple_eq_momentOrientedArea A hij hjk hsi.ne' hsj.ne' hsk.ne']
  simp [hsi.ne', hsj.ne', hsk.ne']

/-- Maximal-minor nonnegativity of a simple nonloop `TN₂` configuration is exactly
nonnegativity of all ordered areas in its moment chain. -/
theorem maximalMinorsNonnegative_iff_areasNonnegativeUpTo {n : ℕ}
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : TNUpTo A 2)
    (hsimple : IsSimpleNonloopConfiguration A) :
    MaximalMinorsNonnegative A ↔
      AreasNonnegativeUpTo (matrixMomentU A) (matrixMomentV A) n := by
  constructor
  · intro hmax i j k hij hjk hkn
    have hin : i < n := hij.trans (hjk.trans hkn)
    have hjn : j < n := hjk.trans hkn
    let i' : Fin n := ⟨i, hin⟩
    let j' : Fin n := ⟨j, hjn⟩
    let k' : Fin n := ⟨k, hkn⟩
    have hij' : i' < j' := by simpa [i', j'] using hij
    have hjk' : j' < k' := by simpa [j', k'] using hjk
    have hminor := hmax (selectedTripleEmbedding i' j' k' hij' hjk')
    have harea :=
      (orderedMinor_selectedTriple_nonneg_iff_momentOrientedArea_nonneg hA hij' hjk'
        (hsimple.1 i') (hsimple.1 j') (hsimple.1 k')).mp hminor
    simpa [momentOrientedArea_eq_orientedArea_matrixMoments, i', j', k'] using harea
  · intro hareas cols
    have h01 : cols 0 < cols 1 := cols.strictMono (by decide)
    have h12 : cols 1 < cols 2 := cols.strictMono (by decide)
    have harea :
        0 ≤ momentOrientedArea (A.col (cols 0)) (A.col (cols 1)) (A.col (cols 2)) := by
      rw [momentOrientedArea_eq_orientedArea_matrixMoments]
      exact hareas h01 h12 (cols 2).isLt
    have hminor :=
      (orderedMinor_selectedTriple_nonneg_iff_momentOrientedArea_nonneg hA h01 h12
        (hsimple.1 (cols 0)) (hsimple.1 (cols 1)) (hsimple.1 (cols 2))).mpr harea
    rw [selectedTripleEmbedding_eq cols] at hminor
    exact hminor

/-- Core convex-chain criterion for a simple nonloop three-row configuration: all maximal
minors are nonnegative exactly when the consecutive moment slopes are weakly increasing. -/
theorem maximalMinorsNonnegative_iff_momentSlopesMonotone {n : ℕ}
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : TNUpTo A 2)
    (hsimple : IsSimpleNonloopConfiguration A) :
    MaximalMinorsNonnegative A ↔
      SlopesMonotoneUpTo (matrixMomentU A) (matrixMomentV A) n := by
  rw [maximalMinorsNonnegative_iff_areasNonnegativeUpTo hA hsimple,
    areasNonnegativeUpTo_iff_slopesMonotoneUpTo _ _
      (matrixMomentU_strictlyIncreasingUpTo hA hsimple)]

/-- The no-loop/no-parallel form of the paper's convex-chain criterion. -/
theorem totallyNonnegative_iff_momentSlopesMonotone {n : ℕ}
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : TNUpTo A 2)
    (hsimple : IsSimpleNonloopConfiguration A) :
    TotallyNonnegative A ↔
      SlopesMonotoneUpTo (matrixMomentU A) (matrixMomentV A) n := by
  rw [totallyNonnegative_fin_three_iff, and_iff_right hA,
    maximalMinorsNonnegative_iff_momentSlopesMonotone hA hsimple]

/-- Under the convexity condition, a selected maximal minor vanishes exactly when every
intervening moment edge has the same slope. -/
theorem orderedMinor_selectedTriple_eq_zero_iff_slopesConstantBetween {n : ℕ}
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : TNUpTo A 2)
    (hsimple : IsSimpleNonloopConfiguration A)
    (hσ : SlopesMonotoneUpTo (matrixMomentU A) (matrixMomentV A) n)
    {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) = 0 ↔
      SlopesConstantBetween (matrixMomentU A) (matrixMomentV A) i.val k.val := by
  rw [orderedMinor_selectedTriple_eq_zero_iff_momentOrientedArea_eq_zero hA hij hjk
    (hsimple.1 i) (hsimple.1 j) (hsimple.1 k),
    momentOrientedArea_eq_orientedArea_matrixMoments]
  exact orientedArea_eq_zero_iff_slopesConstantBetween _ _
    (matrixMomentU_strictlyIncreasingUpTo hA hsimple) hσ
      (by simpa using hij) (by simpa using hjk) k.isLt

end

end ToeplitzPositroids.RankThree
