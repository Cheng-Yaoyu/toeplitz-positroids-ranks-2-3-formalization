import ToeplitzPositroids.Matrix.Positroid
import ToeplitzPositroids.RankTwo.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A positroidal counterexample to the literal rank-two corollary

The positive Toeplitz matrix with coefficient tuple `(1, 1, 2, 2)` has a non-interval positive
parallel class.  This file strengthens the existing correctness finding by showing that its
column matroid is nevertheless a genuine positroid: a second real matrix has the same column
matroid and all of its ordered maximal minors are nonnegative.
-/

namespace ToeplitzPositroids

noncomputable section

/-- The real coefficient tuple `(a₋₁, a₀, a₁, a₂) = (1, 1, 2, 2)`. -/
def realRankTwoCounterexampleCoefficients : Fin 4 → ℝ :=
  fun i ↦ if i.val < 2 then 1 else 2

/-- The real positive Toeplitz counterexample. -/
def realRankTwoCounterexample : Matrix (Fin 2) (Fin 3) ℝ :=
  shiftedRankTwoToeplitz realRankTwoCounterexampleCoefficients

/-- Explicit form of the real counterexample. -/
theorem realRankTwoCounterexample_eq :
    realRankTwoCounterexample = !![(1 : ℝ), 2, 2; 1, 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realRankTwoCounterexample, realRankTwoCounterexampleCoefficients]

/-- Every entry of the real counterexample is positive. -/
theorem realRankTwoCounterexample_entry_pos (i : Fin 2) (j : Fin 3) :
    0 < realRankTwoCounterexample i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [realRankTwoCounterexample, realRankTwoCounterexampleCoefficients]

/-- Its first two columns form a basis. -/
theorem realRankTwoCounterexample_fullRowRank :
    HasFullRowRank realRankTwoCounterexample := by
  refine ⟨Fin.castSuccOrderEmb, ?_⟩
  rw [orderedMinor_two]
  norm_num [allRows, realRankTwoCounterexample, realRankTwoCounterexampleCoefficients]

/-- Its first and last columns are positively parallel. -/
theorem realRankTwoCounterexample_outer_parallel :
    PositivelyParallel realRankTwoCounterexample 0 2 := by
  refine ⟨2, by norm_num, ?_⟩
  ext i
  fin_cases i <;>
    norm_num [realRankTwoCounterexample, realRankTwoCounterexampleCoefficients]

/-- Its middle column is not parallel to the first. -/
theorem realRankTwoCounterexample_middle_not_parallel :
    ¬PositivelyParallel realRankTwoCounterexample 0 1 := by
  rintro ⟨c, hc, hcol⟩
  have hzero := orderedPairMinor_eq_zero_of_column_eq_smul
    realRankTwoCounterexample 0 1 c hcol
  norm_num [realRankTwoCounterexample, realRankTwoCounterexampleCoefficients,
    orderedPairMinor] at hzero

/-- Thus its positive parallel classes do not form ordinary intervals. -/
theorem realRankTwoCounterexample_parallelClasses_not_intervals :
    ¬ParallelClassesAreIntervals realRankTwoCounterexample := by
  intro hinterval
  exact realRankTwoCounterexample_middle_not_parallel
    (hinterval 0 1 2 (by decide) (by decide) realRankTwoCounterexample_outer_parallel)

/-- A second rank-two realization of the same matroid.  The last column is a negative multiple
of the first, making both nonzero ordered basis minors positive. -/
def counterexamplePositroidMatrix : Matrix (Fin 2) (Fin 3) ℝ :=
  !![(1 : ℝ), 0, -1; 0, 1, 0]

/-- The comparison matrix has nonnegative ordered maximal minors. -/
theorem counterexamplePositroidMatrix_maximalMinorsNonnegative :
    MaximalMinorsNonnegative counterexamplePositroidMatrix := by
  intro cols
  rw [orderedMinor_two]
  generalize h0 : cols 0 = i
  generalize h1 : cols 1 = j
  fin_cases i <;> fin_cases j <;>
    norm_num [allRows, counterexamplePositroidMatrix]
  all_goals
    have hstrict := cols.strictMono (show (0 : Fin 2) < 1 by decide)
    simp_all

/-- The first two columns also witness full row rank of the comparison matrix. -/
theorem counterexamplePositroidMatrix_fullRowRank :
    HasFullRowRank counterexamplePositroidMatrix := by
  refine ⟨Fin.castSuccOrderEmb, ?_⟩
  rw [orderedMinor_two]
  norm_num [allRows, counterexamplePositroidMatrix]

/-- The comparison matrix is a genuine positroid representation. -/
def counterexamplePositroidRepresentation : PositroidRepresentation 2 3 where
  matrix := counterexamplePositroidMatrix
  isPositroidRepresentation :=
    ⟨counterexamplePositroidMatrix_fullRowRank,
      counterexamplePositroidMatrix_maximalMinorsNonnegative⟩

/-- The two matrices have the same support of ordered maximal minors. -/
theorem realCounterexample_minor_ne_zero_iff_comparison
    (cols : Fin 2 ↪o Fin 3) :
    orderedMinor realRankTwoCounterexample (allRows 2) cols ≠ 0 ↔
      orderedMinor counterexamplePositroidMatrix (allRows 2) cols ≠ 0 := by
  rw [orderedMinor_two, orderedMinor_two]
  generalize h0 : cols 0 = i
  generalize h1 : cols 1 = j
  fin_cases i <;> fin_cases j <;>
    norm_num [allRows, realRankTwoCounterexample, realRankTwoCounterexampleCoefficients,
      counterexamplePositroidMatrix]

/-- For a full-rank two-row matrix, every matroid basis is the range of an increasing pair of
columns with nonzero ordered minor. -/
theorem columnMatroid_isBase_iff_exists_orderedPair
    (A : Matrix (Fin 2) (Fin 3) ℝ) (hfull : HasFullRowRank A) (B : Set (Fin 3)) :
    (columnMatroid A).IsBase B ↔
      ∃ cols : Fin 2 ↪o Fin 3,
        Set.range cols = B ∧ orderedMinor A (allRows 2) cols ≠ 0 := by
  constructor
  · intro hB
    obtain ⟨baseCols, hbaseCols⟩ :=
      (hasFullRowRank_iff_exists_columnMatroid_isBase A).mp hfull
    have hBcard : B.ncard = 2 := by
      rw [hB.ncard_eq_ncard_of_isBase hbaseCols,
        Set.ncard_range_of_injective baseCols.injective]
      simp
    let hBfinite : B.Finite := Set.toFinite B
    let s : Finset (Fin 3) := hBfinite.toFinset
    have hsCard : s.card = 2 := by
      rw [← Set.ncard_eq_toFinset_card B hBfinite]
      exact hBcard
    let cols : Fin 2 ↪o Fin 3 := s.orderEmbOfFin hsCard
    have hcolsRange : Set.range cols = B := by
      dsimp only [cols]
      rw [Finset.range_orderEmbOfFin]
      exact hBfinite.coe_toFinset
    refine ⟨cols, hcolsRange, ?_⟩
    exact (columnMatroid_isBase_range_iff A cols).mp (hcolsRange ▸ hB)
  · rintro ⟨cols, rfl, hminor⟩
    exact (columnMatroid_isBase_range_iff A cols).mpr hminor

/-- The positive Toeplitz counterexample and the positroid representation have equal column
matroids. -/
theorem realRankTwoCounterexample_columnMatroid_eq_positroid :
    columnMatroid realRankTwoCounterexample = counterexamplePositroidRepresentation.matroid := by
  apply Matroid.ext_isBase
  · simp [PositroidRepresentation.matroid]
  · intro B hB
    rw [columnMatroid_isBase_iff_exists_orderedPair realRankTwoCounterexample
      realRankTwoCounterexample_fullRowRank B]
    change (∃ cols : Fin 2 ↪o Fin 3,
      Set.range cols = B ∧ orderedMinor realRankTwoCounterexample (allRows 2) cols ≠ 0) ↔
      (columnMatroid counterexamplePositroidMatrix).IsBase B
    rw [columnMatroid_isBase_iff_exists_orderedPair counterexamplePositroidMatrix
      counterexamplePositroidMatrix_fullRowRank B]
    constructor <;> rintro ⟨cols, hcols, hminor⟩
    · exact ⟨cols, hcols, (realCounterexample_minor_ne_zero_iff_comparison cols).mp hminor⟩
    · exact ⟨cols, hcols, (realCounterexample_minor_ne_zero_iff_comparison cols).mpr hminor⟩

/-- Strengthened correctness finding: positivity and full row rank do not imply the literal
Corollary 4, even when the underlying column matroid is represented by a nonnegative maximal-minor
matrix and hence is a genuine positroid. -/
theorem literal_corollary_four_fails_for_genuine_positroid :
    (∀ i j, 0 < realRankTwoCounterexample i j) ∧
      HasFullRowRank realRankTwoCounterexample ∧
      ¬ParallelClassesAreIntervals realRankTwoCounterexample ∧
      ∃ P : PositroidRepresentation 2 3,
        columnMatroid realRankTwoCounterexample = P.matroid := by
  refine ⟨realRankTwoCounterexample_entry_pos,
    realRankTwoCounterexample_fullRowRank,
    realRankTwoCounterexample_parallelClasses_not_intervals,
    counterexamplePositroidRepresentation, ?_⟩
  exact realRankTwoCounterexample_columnMatroid_eq_positroid

end

end ToeplitzPositroids
