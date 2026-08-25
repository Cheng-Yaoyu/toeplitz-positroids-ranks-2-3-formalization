import ToeplitzPositroids.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Consecutive maximal minors do not suffice before simplification

This file formalizes Remark 6 of *Toeplitz Positroids in Ranks Two and Three*.
It gives a `3 × 4` matrix that is totally nonnegative through order two and whose
consecutive maximal minors vanish, but which has two negative nonconsecutive
maximal minors.
-/

namespace ToeplitzPositroids

open Matrix

/-- The `3 × 4` counterexample from Remark 6. -/
def consecutiveCounterexample : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 1, 1, 0; 1, 1, 1, 1; 0, 1, 1, 1]

/-- Every entry of the counterexample is nonnegative. -/
theorem consecutiveCounterexample_entry_nonneg (i : Fin 3) (j : Fin 4) :
    0 ≤ consecutiveCounterexample i j := by
  fin_cases i <;> fin_cases j <;> norm_num [consecutiveCounterexample]

/-- An increasing pair in `Fin 3` is one of the three explicitly listed pairs. -/
private theorem finTwo_orderEmbedding_finThree_cases (rows : Fin 2 ↪o Fin 3) :
    (rows 0 = 0 ∧ rows 1 = 1) ∨
      (rows 0 = 0 ∧ rows 1 = 2) ∨
      rows 0 = 1 ∧ rows 1 = 2 := by
  have hrows : rows 0 < rows 1 := rows.lt_iff_lt.mpr (by decide)
  omega

/-- An increasing pair in `Fin 4` is one of the six explicitly listed pairs. -/
private theorem finTwo_orderEmbedding_finFour_cases (cols : Fin 2 ↪o Fin 4) :
    (cols 0 = 0 ∧ cols 1 = 1) ∨
      (cols 0 = 0 ∧ cols 1 = 2) ∨
      (cols 0 = 0 ∧ cols 1 = 3) ∨
      (cols 0 = 1 ∧ cols 1 = 2) ∨
      (cols 0 = 1 ∧ cols 1 = 3) ∨
      cols 0 = 2 ∧ cols 1 = 3 := by
  have hcols : cols 0 < cols 1 := cols.lt_iff_lt.mpr (by decide)
  omega

/-- Every ordered minor of order two is nonnegative. -/
theorem consecutiveCounterexample_orderTwo_nonneg (rows : Fin 2 ↪o Fin 3)
    (cols : Fin 2 ↪o Fin 4) :
    0 ≤ orderedMinor consecutiveCounterexample rows cols := by
  rw [orderedMinor_two]
  rcases finTwo_orderEmbedding_finThree_cases rows with hr | hr | hr <;>
    rcases finTwo_orderEmbedding_finFour_cases cols with hc | hc | hc | hc | hc | hc <;>
    norm_num [consecutiveCounterexample, hr.1, hr.2, hc.1, hc.2,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The counterexample is totally nonnegative through order two. -/
theorem consecutiveCounterexample_tnUpTo_two :
    TNUpTo consecutiveCounterexample 2 := by
  intro k hk rows cols
  interval_cases k
  · simp
  · rw [orderedMinor_one]
    exact consecutiveCounterexample_entry_nonneg _ _
  · exact consecutiveCounterexample_orderTwo_nonneg rows cols

/-- The first consecutive maximal minor, on columns `123`, vanishes. -/
theorem consecutiveCounterexample_minor_123 :
    orderedMinor consecutiveCounterexample (OrderIso.refl (Fin 3)).toOrderEmbedding
      (Fin.succAboveOrderEmb 3) = 0 := by
  change
    (consecutiveCounterexample.submatrix (OrderIso.refl (Fin 3)).toOrderEmbedding
      (Fin.succAboveOrderEmb 3)).det = 0
  have hmatrix :
      consecutiveCounterexample.submatrix (OrderIso.refl (Fin 3)).toOrderEmbedding
        (Fin.succAboveOrderEmb 3) = !![1, 1, 1; 1, 1, 1; 0, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hmatrix]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

/-- The second consecutive maximal minor, on columns `234`, vanishes. -/
theorem consecutiveCounterexample_minor_234 :
    orderedMinor consecutiveCounterexample (OrderIso.refl (Fin 3)).toOrderEmbedding
      (Fin.succAboveOrderEmb 0) = 0 := by
  change
    (consecutiveCounterexample.submatrix (OrderIso.refl (Fin 3)).toOrderEmbedding
      (Fin.succAboveOrderEmb 0)).det = 0
  have hmatrix :
      consecutiveCounterexample.submatrix (OrderIso.refl (Fin 3)).toOrderEmbedding
        (Fin.succAboveOrderEmb 0) = !![1, 1, 0; 1, 1, 1; 1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hmatrix]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

/-- The nonconsecutive maximal minor on columns `124` equals `-1`. -/
theorem consecutiveCounterexample_minor_124 :
    orderedMinor consecutiveCounterexample (OrderIso.refl (Fin 3)).toOrderEmbedding
      (Fin.succAboveOrderEmb 2) = -1 := by
  change
    (consecutiveCounterexample.submatrix (OrderIso.refl (Fin 3)).toOrderEmbedding
      (Fin.succAboveOrderEmb 2)).det = -1
  have hmatrix :
      consecutiveCounterexample.submatrix (OrderIso.refl (Fin 3)).toOrderEmbedding
        (Fin.succAboveOrderEmb 2) = !![1, 1, 0; 1, 1, 1; 0, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hmatrix]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

/-- The nonconsecutive maximal minor on columns `134` equals `-1`. -/
theorem consecutiveCounterexample_minor_134 :
    orderedMinor consecutiveCounterexample (OrderIso.refl (Fin 3)).toOrderEmbedding
      (Fin.succAboveOrderEmb 1) = -1 := by
  change
    (consecutiveCounterexample.submatrix (OrderIso.refl (Fin 3)).toOrderEmbedding
      (Fin.succAboveOrderEmb 1)).det = -1
  have hmatrix :
      consecutiveCounterexample.submatrix (OrderIso.refl (Fin 3)).toOrderEmbedding
        (Fin.succAboveOrderEmb 1) = !![1, 1, 0; 1, 1, 1; 0, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hmatrix]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

/-- The middle two columns of the counterexample are equal, hence parallel. -/
theorem consecutiveCounterexample_middle_columns_eq :
    (fun i ↦ consecutiveCounterexample i 1) =
      fun i ↦ consecutiveCounterexample i 2 := by
  funext i
  fin_cases i <;> rfl

/-- A negative maximal minor prevents the counterexample from being totally nonnegative. -/
theorem consecutiveCounterexample_not_totallyNonnegative :
    ¬ TotallyNonnegative consecutiveCounterexample := by
  intro htnn
  have hminor :
      0 ≤ orderedMinor consecutiveCounterexample (OrderIso.refl (Fin 3)).toOrderEmbedding
        (Fin.succAboveOrderEmb 2) :=
    htnn.orderedMinor_nonneg (OrderIso.refl (Fin 3)).toOrderEmbedding
      (Fin.succAboveOrderEmb 2)
  rw [consecutiveCounterexample_minor_124] at hminor
  norm_num at hminor

/-- Remark 6 in one statement. -/
theorem consecutiveCounterexample_spec :
    TNUpTo consecutiveCounterexample 2 ∧
      orderedMinor consecutiveCounterexample (OrderIso.refl (Fin 3)).toOrderEmbedding
          (Fin.succAboveOrderEmb 3) = 0 ∧
      orderedMinor consecutiveCounterexample (OrderIso.refl (Fin 3)).toOrderEmbedding
          (Fin.succAboveOrderEmb 0) = 0 ∧
      orderedMinor consecutiveCounterexample (OrderIso.refl (Fin 3)).toOrderEmbedding
          (Fin.succAboveOrderEmb 2) = -1 ∧
      orderedMinor consecutiveCounterexample (OrderIso.refl (Fin 3)).toOrderEmbedding
          (Fin.succAboveOrderEmb 1) = -1 ∧
      (fun i ↦ consecutiveCounterexample i 1) =
          (fun i ↦ consecutiveCounterexample i 2) ∧
      ¬ TotallyNonnegative consecutiveCounterexample := by
  exact ⟨consecutiveCounterexample_tnUpTo_two,
    consecutiveCounterexample_minor_123,
    consecutiveCounterexample_minor_234,
    consecutiveCounterexample_minor_124,
    consecutiveCounterexample_minor_134,
    consecutiveCounterexample_middle_columns_eq,
    consecutiveCounterexample_not_totallyNonnegative⟩

end ToeplitzPositroids
