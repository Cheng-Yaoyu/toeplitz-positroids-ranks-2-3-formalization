import ToeplitzPositroids.Matrix.ColumnMatroid
import ToeplitzPositroids.Matrix.Toeplitz
import Mathlib.Data.Finset.Sort

/-!
# Positroids represented by finite matrices

This file packages a full-row-rank real matrix with nonnegative maximal minors and associates to
it the genuine column matroid constructed in `ToeplitzPositroids.Matrix.ColumnMatroid`. Its bases
are characterized by positive ordered maximal minors. We also isolate the stronger condition used
in the paper: a full-row-rank finite Toeplitz matrix that is totally nonnegative in every minor
order.
-/

namespace ToeplitzPositroids

open Set

variable {r n : ℕ}

/-- A bundled real matrix representation of a positroid. -/
structure PositroidRepresentation (r n : ℕ) where
  /-- The representing matrix. -/
  matrix : Matrix (Fin r) (Fin n) ℝ
  /-- Full row rank and nonnegativity of all maximal minors. -/
  isPositroidRepresentation : IsPositroidRepresentation matrix

namespace PositroidRepresentation

/-- The genuine matroid represented by the columns of a bundled positroid representation. -/
noncomputable def matroid (P : PositroidRepresentation r n) : Matroid (Fin n) :=
  columnMatroid P.matrix

/-- The representing matrix has full row rank. -/
theorem fullRowRank (P : PositroidRepresentation r n) : HasFullRowRank P.matrix :=
  P.isPositroidRepresentation.1

/-- Every maximal minor of the representing matrix is nonnegative. -/
theorem maximalMinorsNonnegative (P : PositroidRepresentation r n) :
    MaximalMinorsNonnegative P.matrix :=
  P.isPositroidRepresentation.2

/-- The represented positroid has the full column-index set as its ground set. -/
@[simp]
theorem matroid_ground (P : PositroidRepresentation r n) : P.matroid.E = Set.univ := by
  exact columnMatroid_ground P.matrix

/-- An increasingly selected maximal-size set is a basis exactly when its maximal minor is
positive. -/
theorem isBase_range_iff_orderedMinor_pos (P : PositroidRepresentation r n)
    (cols : Fin r ↪o Fin n) :
    P.matroid.IsBase (Set.range cols) ↔ 0 < orderedMinor P.matrix (allRows r) cols :=
  columnMatroid_isBase_range_iff_orderedMinor_pos P.maximalMinorsNonnegative cols

/-- A positroid representation has at least one positive ordered maximal minor, and its column
set is a basis of the represented matroid. -/
theorem exists_positive_orderedBasis (P : PositroidRepresentation r n) :
    ∃ cols : Fin r ↪o Fin n,
      P.matroid.IsBase (Set.range cols) ∧ 0 < orderedMinor P.matrix (allRows r) cols := by
  obtain ⟨cols, hcols⟩ := P.fullRowRank
  have hpos : 0 < orderedMinor P.matrix (allRows r) cols :=
    lt_of_le_of_ne (P.maximalMinorsNonnegative cols) hcols.symm
  exact ⟨cols, (P.isBase_range_iff_orderedMinor_pos cols).2 hpos, hpos⟩

/-- Every basis, not merely an already-enumerated one, is the range of an increasing
selection whose ordered maximal minor is positive. -/
theorem isBase_iff_exists_positive_orderedMinor (P : PositroidRepresentation r n)
    (B : Set (Fin n)) :
    P.matroid.IsBase B ↔
      ∃ cols : Fin r ↪o Fin n,
        Set.range cols = B ∧ 0 < orderedMinor P.matrix (allRows r) cols := by
  constructor
  · intro hB
    obtain ⟨baseCols, hbase, _⟩ := P.exists_positive_orderedBasis
    have hBcard : B.ncard = r := by
      rw [hB.ncard_eq_ncard_of_isBase hbase,
        Set.ncard_range_of_injective baseCols.injective]
      simp
    let hBfin : B.Finite := Set.toFinite B
    let s : Finset (Fin n) := hBfin.toFinset
    have hsCard : s.card = r := by
      rw [← Set.ncard_eq_toFinset_card B hBfin]
      exact hBcard
    let cols : Fin r ↪o Fin n := s.orderEmbOfFin hsCard
    have hcolsRange : Set.range cols = B := by
      dsimp only [cols]
      rw [Finset.range_orderEmbOfFin]
      dsimp only [s]
      exact hBfin.coe_toFinset
    refine ⟨cols, hcolsRange, ?_⟩
    exact (P.isBase_range_iff_orderedMinor_pos cols).1 (hcolsRange ▸ hB)
  · rintro ⟨cols, rfl, hpos⟩
    exact (P.isBase_range_iff_orderedMinor_pos cols).2 hpos

/-- Matrix loops and matroid loops agree for a bundled positroid representation. -/
theorem isLoop_iff (P : PositroidRepresentation r n) (j : Fin n) :
    IsLoop P.matrix j ↔ P.matroid.IsLoop j :=
  isLoop_iff_columnMatroid_isLoop P.matrix j

end PositroidRepresentation

/-- Total nonnegativity in all minor orders implies nonnegativity of the maximal minors. -/
theorem TotallyNonnegative.maximalMinorsNonnegative
    {A : Matrix (Fin r) (Fin n) ℝ} (hA : TotallyNonnegative A) :
    MaximalMinorsNonnegative A := by
  intro cols
  exact hA.orderedMinor_nonneg (allRows r) cols

/-- A finite matrix has Toeplitz form when it is obtained from a coefficient vector through the
common finite Toeplitz constructor. -/
def HasFiniteToeplitzForm (A : Matrix (Fin r) (Fin n) ℝ) : Prop :=
  ∃ a : Fin (n + r - 1) → ℝ, A = finiteToeplitz a

/-- The condition on a coefficient vector saying that its finite Toeplitz section is full-row-rank
and totally nonnegative in all minor orders. -/
def AllMinorTNToeplitzCoefficients (a : Fin (n + r - 1) → ℝ) : Prop :=
  HasFullRowRank (finiteToeplitz a) ∧ TotallyNonnegative (finiteToeplitz a)

/-- A matrix is a strong Toeplitz positroid representation when it has finite Toeplitz form, has
full row rank, and is totally nonnegative in every minor order. -/
def IsAllMinorTNToeplitzRepresentation (A : Matrix (Fin r) (Fin n) ℝ) : Prop :=
  HasFiniteToeplitzForm A ∧ HasFullRowRank A ∧ TotallyNonnegative A

/-- The coefficient-centered and matrix-centered formulations of a strong Toeplitz representation
agree on a finite Toeplitz section. -/
theorem isAllMinorTNToeplitzRepresentation_finiteToeplitz_iff
    (a : Fin (n + r - 1) → ℝ) :
    IsAllMinorTNToeplitzRepresentation (finiteToeplitz a) ↔
      AllMinorTNToeplitzCoefficients a := by
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨⟨a, rfl⟩, h⟩

/-- A strong all-minor-TN Toeplitz representation is, in particular, a positroid
representation. -/
theorem IsAllMinorTNToeplitzRepresentation.isPositroidRepresentation
    {A : Matrix (Fin r) (Fin n) ℝ} (hA : IsAllMinorTNToeplitzRepresentation A) :
    IsPositroidRepresentation A :=
  ⟨hA.2.1, hA.2.2.maximalMinorsNonnegative⟩

/-- Bundle a strong all-minor-TN Toeplitz representation as a positroid representation. -/
def IsAllMinorTNToeplitzRepresentation.toPositroidRepresentation
    {A : Matrix (Fin r) (Fin n) ℝ} (hA : IsAllMinorTNToeplitzRepresentation A) :
    PositroidRepresentation r n :=
  ⟨A, hA.isPositroidRepresentation⟩

section ParallelColumns

variable {A : Matrix (Fin r) (Fin n) ℝ} {i j : Fin n}

/-- Distinct positively parallel nonzero columns form a dependent pair in the column matroid. -/
theorem ColumnsParallel.pair_dep (hpar : ColumnsParallel A i j) (hij : i ≠ j) :
    (columnMatroid A).Dep {i, j} := by
  have hnot : ¬(columnMatroid A).Indep {i, j} := by
    rw [columnMatroid_indep_iff]
    intro hlin
    have hlin' : LinearIndepOn ℝ A.col (insert j {i}) := by
      simpa [Set.pair_comm] using hlin
    have hjNotSpan := (linearIndepOn_insert (f := A.col) (by simpa using hij.symm)).mp hlin' |>.2
    obtain ⟨c, _, hcol⟩ := hpar.2
    apply hjNotSpan
    rw [hcol]
    exact Submodule.smul_mem _ c
      (Submodule.subset_span (by simp : A.col i ∈ A.col '' ({i} : Set (Fin n))))
  exact ⟨hnot, by simp⟩

/-- Distinct positively parallel columns form a two-element circuit in the column matroid. -/
theorem ColumnsParallel.pair_isCircuit (hpar : ColumnsParallel A i j) (hij : i ≠ j) :
    (columnMatroid A).IsCircuit {i, j} := by
  rw [Matroid.isCircuit_iff_dep_forall_diff_singleton_indep]
  refine ⟨hpar.pair_dep hij, ?_⟩
  intro e he
  rcases he with rfl | rfl
  · rw [Set.pair_diff_left hij, columnMatroid_indep_iff]
    exact LinearIndepOn.singleton (by simpa [IsLoop] using (columnsParallel_symm hpar).1)
  · rw [Set.pair_diff_right hij, columnMatroid_indep_iff]
    exact LinearIndepOn.singleton (by simpa [IsLoop] using hpar.1)

/-- No basis of the column matroid contains two distinct positively parallel columns. -/
theorem ColumnsParallel.not_both_mem_isBase (hpar : ColumnsParallel A i j) (hij : i ≠ j)
    {B : Set (Fin n)} (hB : (columnMatroid A).IsBase B) :
    ¬(i ∈ B ∧ j ∈ B) := by
  rintro ⟨hiB, hjB⟩
  exact (hpar.pair_dep hij).not_indep
    (hB.indep.subset (by simpa [Set.pair_subset_iff] using ⟨hiB, hjB⟩))

/-- Under all-minor total nonnegativity, a two-element circuit is exactly a pair of positively
parallel columns. -/
theorem columnsParallel_iff_pair_isCircuit_of_totallyNonnegative
    (hA : TotallyNonnegative A) (hij : i ≠ j) :
    ColumnsParallel A i j ↔ (columnMatroid A).IsCircuit {i, j} := by
  refine ⟨fun h ↦ h.pair_isCircuit hij, fun hcir ↦ ?_⟩
  have hiInd : (columnMatroid A).Indep {i} := by
    have h := hcir.diff_singleton_indep (show j ∈ ({i, j} : Set (Fin n)) by simp)
    simpa [Set.pair_diff_right hij] using h
  have hjInd : (columnMatroid A).Indep {j} := by
    have h := hcir.diff_singleton_indep (show i ∈ ({i, j} : Set (Fin n)) by simp)
    simpa [Set.pair_diff_left hij] using h
  have hiLin := (columnMatroid_indep_iff A {i}).mp hiInd
  have hjLin := (columnMatroid_indep_iff A {j}).mp hjInd
  have hi0 : A.col i ≠ 0 := hiLin.ne_zero (by simp)
  have hj0 : A.col j ≠ 0 := hjLin.ne_zero (by simp)
  have hpairNotIndep : ¬LinearIndepOn ℝ A.col {i, j} :=
    (columnMatroid_indep_iff A {i, j}).not.mp hcir.not_indep
  rw [linearIndepOn_pair_iff A.col hij hi0] at hpairNotIndep
  simp only [not_forall, not_ne_iff] at hpairNotIndep
  obtain ⟨c, hc⟩ := hpairNotIndep
  obtain ⟨row, hrowNe⟩ := Function.ne_iff.mp hi0
  have hrowNonneg : 0 ≤ A row i := hA.entry_nonneg row i
  have hrowPos : 0 < A row i := lt_of_le_of_ne hrowNonneg hrowNe.symm
  have hcRow : c * A row i = A row j := by
    simpa using congrFun hc row
  have hmulNonneg : 0 ≤ c * A row i := by
    rw [hcRow]
    exact hA.entry_nonneg row j
  have hcNonneg : 0 ≤ c := (mul_nonneg_iff_of_pos_right hrowPos).mp hmulNonneg
  have hc0 : c ≠ 0 := by
    intro hcZero
    apply hj0
    rw [← hc, hcZero, zero_smul]
  exact ⟨by simpa [IsLoop] using hi0, c, lt_of_le_of_ne hcNonneg hc0.symm, hc.symm⟩

/-- For a strong Toeplitz representation, matrix parallelism agrees with the represented
matroid's two-element circuits. -/
theorem IsAllMinorTNToeplitzRepresentation.columnsParallel_iff_pair_isCircuit
    (hA : IsAllMinorTNToeplitzRepresentation A) (hij : i ≠ j) :
    ColumnsParallel A i j ↔ (columnMatroid A).IsCircuit {i, j} :=
  columnsParallel_iff_pair_isCircuit_of_totallyNonnegative hA.2.2 hij

end ParallelColumns

end ToeplitzPositroids
