import ToeplitzPositroids.RankTwo.Classification

/-!
# The corrected positive rank-two corollary

Corollary 4 of the manuscript requires the standing total-nonnegativity
hypothesis.  This file states the corrected matrix-level conclusion explicitly;
`RankTwo.Basic` contains a positive counterexample when that hypothesis is
omitted.
-/

namespace ToeplitzPositroids

/-- A matrix with strictly positive entries has no loop columns. -/
theorem not_isLoop_of_entry_pos {n : ℕ} {A : Matrix (Fin 2) (Fin n) ℝ}
    (hA : ∀ i j, 0 < A i j) (j : Fin n) : ¬IsLoop A j := by
  intro hj
  have hzero := (isLoop_iff_entry_eq_zero.mp hj) 0
  exact (ne_of_gt (hA 0 j)) hzero

/-- Corrected Corollary 4: for a positive totally nonnegative rank-two Toeplitz
matrix, every parallel class is an ordinary interval; full row rank guarantees
at least two such classes. -/
theorem positive_rankTwoToeplitz_parallelClasses_form_composition
    {n : ℕ} (a : Fin (n + 1) → ℝ)
    (hpos : ∀ i j, 0 < rankTwoToeplitz a i j)
    (hTN : TotallyNonnegative (rankTwoToeplitz a))
    (hfull : HasFullRowRank (rankTwoToeplitz a)) :
    (∀ i : Fin n,
        Set.OrdConnected {j | ColumnsPositivelyParallel (rankTwoToeplitz a) i j}) ∧
      ∃ i j : Fin n, i < j ∧
        ¬ColumnsPositivelyParallel (rankTwoToeplitz a) i j := by
  constructor
  · intro i
    exact rankTwoToeplitz_parallelClasses_ordConnected a hTN
      (not_isLoop_of_entry_pos hpos i)
  · obtain ⟨i, j, hij, -, -, hparallel⟩ :=
      hasFullRowRank_exists_nonparallel_columns hfull
    exact ⟨i, j, hij, hparallel⟩

end ToeplitzPositroids
