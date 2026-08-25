import ToeplitzPositroids.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rank-two finite Toeplitz matrices

This file fixes a finite coefficient convention for two-row Toeplitz matrices and proves the
projective formula for their maximal minors.  It also records a small positive counterexample to
the literal statement of Corollary 4 of the paper: positivity of the entries alone does not force
parallel classes to be intervals.  The missing hypothesis is total nonnegativity.
-/

namespace ToeplitzPositroids

variable {R K κ : Type*} {n : ℕ}

/-- The two-row Toeplitz matrix associated with the shifted finite coefficient vector
`(a₋₁, a₀, …, aₙ₋₁)`.  Thus column `j` is `(a (j + 1), a j)` in the finite indexing
used by this definition. -/
def shiftedRankTwoToeplitz (a : Fin (n + 1) → R) : Matrix (Fin 2) (Fin n) R :=
  fun i j ↦ Fin.cases (a j.succ) (fun _ ↦ a j.castSucc) i

@[simp]
theorem shiftedRankTwoToeplitz_zero (a : Fin (n + 1) → R) (j : Fin n) :
    shiftedRankTwoToeplitz a 0 j = a j.succ :=
  rfl

@[simp]
theorem shiftedRankTwoToeplitz_one (a : Fin (n + 1) → R) (j : Fin n) :
    shiftedRankTwoToeplitz a 1 j = a j.castSucc :=
  rfl

/-- The determinant of two ordered columns of a two-row matrix. -/
def orderedPairMinor [Ring R] (A : Matrix (Fin 2) κ R) (i j : κ) : R :=
  A 0 i * A 1 j - A 0 j * A 1 i

@[simp]
theorem orderedPairMinor_shiftedRankTwoToeplitz [Ring R] (a : Fin (n + 1) → R)
    (i j : Fin n) :
    orderedPairMinor (shiftedRankTwoToeplitz a) i j =
      a i.succ * a j.castSucc - a j.succ * a i.castSucc :=
  rfl

/-- The affine projective coordinate of a column whose first entry is nonzero. -/
def rankTwoProjectiveParameter [Field K] (a : Fin (n + 1) → K) (j : Fin n) : K :=
  a j.castSucc / a j.succ

/-- The ordered pair minor is the product of the first coordinates times the difference of the
projective parameters.  This is equation (3.3) of the paper in zero-based finite indexing. -/
theorem orderedPairMinor_eq_projectiveDifference [Field K] (a : Fin (n + 1) → K)
    (i j : Fin n) (hi : a i.succ ≠ 0) (hj : a j.succ ≠ 0) :
    orderedPairMinor (shiftedRankTwoToeplitz a) i j =
      a i.succ * a j.succ *
        (rankTwoProjectiveParameter a j - rankTwoProjectiveParameter a i) := by
  rw [orderedPairMinor_shiftedRankTwoToeplitz]
  simp only [rankTwoProjectiveParameter]
  field_simp

/-- Two columns are positively parallel when the second is a positive scalar multiple of the
first. -/
def PositivelyParallel [Zero R] [LT R] [SMul R R] (A : Matrix (Fin 2) κ R) (i j : κ) : Prop :=
  ∃ r : R, 0 < r ∧ A.col j = r • A.col i

/-- A direct ordered formulation of the assertion that positive parallel classes are intervals. -/
def ParallelClassesAreIntervals [Zero R] [LT R] [SMul R R] [Preorder κ]
    (A : Matrix (Fin 2) κ R) : Prop :=
  ∀ i j k : κ, i ≤ j → j ≤ k → PositivelyParallel A i k → PositivelyParallel A i j

theorem orderedPairMinor_eq_zero_of_column_eq_smul [CommRing R]
    (A : Matrix (Fin 2) κ R) (i j : κ) (r : R) (h : A.col j = r • A.col i) :
    orderedPairMinor A i j = 0 := by
  have h₀ := congrFun h (0 : Fin 2)
  have h₁ := congrFun h (1 : Fin 2)
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at h₀ h₁
  unfold orderedPairMinor
  rw [h₀, h₁]
  ring

/-- A nonzero ordered pair minor certifies that the two rows are linearly independent. -/
theorem linearIndependent_rows_of_orderedPairMinor_ne_zero [Field R]
    (A : Matrix (Fin 2) κ R) (i j : κ) (hminor : orderedPairMinor A i j ≠ 0) :
    LinearIndependent R A.row := by
  rw [Fintype.linearIndependent_iff]
  intro g hg r
  have hi : g 0 * A 0 i + g 1 * A 1 i = 0 := by
    simpa [Fin.sum_univ_two] using congrFun hg i
  have hj : g 0 * A 0 j + g 1 * A 1 j = 0 := by
    simpa [Fin.sum_univ_two] using congrFun hg j
  have hg₀minor : g 0 * orderedPairMinor A i j = 0 := by
    calc
      g 0 * orderedPairMinor A i j =
          A 1 j * (g 0 * A 0 i + g 1 * A 1 i) -
            A 1 i * (g 0 * A 0 j + g 1 * A 1 j) := by
              simp only [orderedPairMinor]
              ring
      _ = 0 := by rw [hi, hj]; ring
  have hg₁minor : g 1 * orderedPairMinor A i j = 0 := by
    calc
      g 1 * orderedPairMinor A i j =
          A 0 i * (g 0 * A 0 j + g 1 * A 1 j) -
            A 0 j * (g 0 * A 0 i + g 1 * A 1 i) := by
              simp only [orderedPairMinor]
              ring
      _ = 0 := by rw [hi, hj]; ring
  have hg₀ : g 0 = 0 := (mul_eq_zero.mp hg₀minor).resolve_right hminor
  have hg₁ : g 1 = 0 := (mul_eq_zero.mp hg₁minor).resolve_right hminor
  fin_cases r
  · simpa using hg₀
  · simpa using hg₁

section Counterexample

/-- The coefficient vector `(a₋₁, a₀, a₁, a₂) = (1, 1, 2, 2)`. -/
def rankTwoCounterexampleCoefficients : Fin 4 → ℚ :=
  fun i ↦ if i.val < 2 then 1 else 2

@[simp]
theorem rankTwoCounterexampleCoefficients_zero : rankTwoCounterexampleCoefficients 0 = 1 :=
  by norm_num [rankTwoCounterexampleCoefficients]

@[simp]
theorem rankTwoCounterexampleCoefficients_one : rankTwoCounterexampleCoefficients 1 = 1 :=
  by norm_num [rankTwoCounterexampleCoefficients]

@[simp]
theorem rankTwoCounterexampleCoefficients_two : rankTwoCounterexampleCoefficients 2 = 2 :=
  by norm_num [rankTwoCounterexampleCoefficients]

@[simp]
theorem rankTwoCounterexampleCoefficients_three : rankTwoCounterexampleCoefficients 3 = 2 :=
  by norm_num [rankTwoCounterexampleCoefficients]

/-- The resulting positive `2 × 3` Toeplitz matrix.  Its rows are `(1, 2, 2)` and `(1, 1, 2)`. -/
def rankTwoCounterexample : Matrix (Fin 2) (Fin 3) ℚ :=
  shiftedRankTwoToeplitz rankTwoCounterexampleCoefficients

/-- Every entry of the counterexample is strictly positive. -/
theorem rankTwoCounterexample_entry_pos (i : Fin 2) (j : Fin 3) :
    0 < rankTwoCounterexample i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rankTwoCounterexample, rankTwoCounterexampleCoefficients]

/-- The first two columns give a nonzero maximal minor. -/
theorem rankTwoCounterexample_pairMinor_zero_one :
    orderedPairMinor rankTwoCounterexample 0 1 = -1 := by
  norm_num [rankTwoCounterexample, rankTwoCounterexampleCoefficients, orderedPairMinor]

theorem rankTwoCounterexample_pairMinor_zero_one_ne_zero :
    orderedPairMinor rankTwoCounterexample 0 1 ≠ 0 := by
  rw [rankTwoCounterexample_pairMinor_zero_one]
  norm_num

/-- The negative first maximal minor shows exactly why the total-nonnegativity hypothesis is
essential. -/
theorem rankTwoCounterexample_not_totallyNonnegative :
    ¬TotallyNonnegative rankTwoCounterexample := by
  intro hA
  have hminor := hA.orderedMinor_nonneg (OrderIso.refl (Fin 2)).toOrderEmbedding
    (Fin.castLEOrderEmb (show 2 ≤ 3 by norm_num))
  rw [orderedMinor_two] at hminor
  norm_num [rankTwoCounterexample, rankTwoCounterexampleCoefficients] at hminor

/-- The nonzero minor witnesses full row rank. -/
theorem rankTwoCounterexample_rank : rankTwoCounterexample.rank = 2 := by
  simpa using (linearIndependent_rows_of_orderedPairMinor_ne_zero rankTwoCounterexample 0 1
    rankTwoCounterexample_pairMinor_zero_one_ne_zero).rank_matrix

/-- Columns one and three in the paper's one-based indexing are positively parallel. -/
theorem rankTwoCounterexample_outer_parallel :
    PositivelyParallel rankTwoCounterexample 0 2 := by
  refine ⟨2, by norm_num, ?_⟩
  ext i
  fin_cases i <;>
    norm_num [rankTwoCounterexample, rankTwoCounterexampleCoefficients]

/-- The middle column is not parallel to the first column. -/
theorem rankTwoCounterexample_middle_not_parallel :
    ¬PositivelyParallel rankTwoCounterexample 0 1 := by
  rintro ⟨r, -, h⟩
  have hz := orderedPairMinor_eq_zero_of_column_eq_smul rankTwoCounterexample 0 1 r h
  exact rankTwoCounterexample_pairMinor_zero_one_ne_zero hz

/-- Positivity and full row rank alone do not force parallel classes to be consecutive. -/
theorem rankTwoCounterexample_parallelClasses_not_intervals :
    ¬ParallelClassesAreIntervals rankTwoCounterexample := by
  intro h
  have h₀₁ : (0 : Fin 3) ≤ 1 := Nat.zero_le 1
  have h₁₂ : (1 : Fin 3) ≤ 2 := Nat.succ_le_succ (Nat.zero_le 1)
  exact rankTwoCounterexample_middle_not_parallel
    (h 0 1 2 h₀₁ h₁₂ rankTwoCounterexample_outer_parallel)

end Counterexample

end ToeplitzPositroids
