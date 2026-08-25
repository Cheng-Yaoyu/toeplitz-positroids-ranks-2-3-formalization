import ToeplitzPositroids.Matrix.Configuration
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Column matroids of finite matrices

This file constructs the matroid represented by the columns of a matrix over a field. Its
independent sets are exactly the sets indexing linearly independent columns. For matrices with
`Fin r` rows, a set of `r` increasingly selected columns is a matroid basis exactly when the
corresponding ordered maximal minor is nonzero.
-/

namespace ToeplitzPositroids

open Set

variable {K V ι m n : Type*}

private theorem linearIndepOn_augment [Field K] [AddCommGroup V] [Module K V]
    (v : ι → V) {I J : Set ι} (hIfin : I.Finite) (hJfin : J.Finite)
    (hI : LinearIndepOn K v I) (hJ : LinearIndepOn K v J) (hcard : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn K v (insert e I) := by
  by_contra haug
  have himage : v '' J ⊆ Submodule.span K (v '' I) := by
    rintro _ ⟨e, heJ, rfl⟩
    by_cases heI : e ∈ I
    · exact Submodule.subset_span (mem_image_of_mem v heI)
    · by_contra heSpan
      exact haug ⟨e, heJ, heI, hI.insert heSpan⟩
  have hspan : Submodule.span K (v '' J) ≤ Submodule.span K (v '' I) :=
    Submodule.span_le.mpr himage
  letI := hIfin.fintype
  letI := hJfin.fintype
  have hrangeI : Set.range (fun x : I ↦ v x) = v '' I := by
    ext x
    simp
  have hrangeJ : Set.range (fun x : J ↦ v x) = v '' J := by
    ext x
    simp
  have hrankI : Module.finrank K (Submodule.span K (v '' I)) = I.ncard := by
    rw [← hrangeI, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact finrank_span_eq_card hI
  have hrankJ : Module.finrank K (Submodule.span K (v '' J)) = J.ncard := by
    rw [← hrangeJ, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact finrank_span_eq_card hJ
  letI : Module.Finite K (Submodule.span K (v '' I)) :=
    FiniteDimensional.span_of_finite K (hIfin.image v)
  have hrank := Submodule.finrank_mono hspan
  rw [hrankJ, hrankI] at hrank
  exact (Nat.not_le_of_lt hcard) hrank

/-- The independence-based presentation of the matroid represented by the columns of `A`. -/
private noncomputable def columnIndepMatroid [Field K] [Finite n] (A : Matrix m n K) :
    IndepMatroid n :=
  IndepMatroid.ofFinite Set.finite_univ (fun I ↦ LinearIndepOn K A.col I)
    (linearIndepOn_empty K A.col)
    (fun {_ _} hJ hIJ ↦ LinearIndepOn.mono hJ hIJ)
    (fun {_ _} hI hJ hcard ↦
      linearIndepOn_augment A.col (Set.toFinite _) (Set.toFinite _) hI hJ hcard)
    (fun {_} _ ↦ subset_univ _)

/-- The finite matroid represented by the columns of `A` over `K`. -/
noncomputable def columnMatroid [Field K] [Finite n] (A : Matrix m n K) : Matroid n :=
  (columnIndepMatroid A).matroid

/-- Every column index belongs to the ground set of the column matroid. -/
@[simp]
theorem columnMatroid_ground [Field K] [Finite n] (A : Matrix m n K) :
    (columnMatroid A).E = Set.univ := by
  rfl

/-- Independence in the column matroid is linear independence of the indexed columns. -/
@[simp]
theorem columnMatroid_indep_iff [Field K] [Finite n] (A : Matrix m n K) (I : Set n) :
    (columnMatroid A).Indep I ↔ LinearIndepOn K A.col I := by
  rfl

/-- Finset independence in the column matroid is linear independence of the corresponding
subtype-indexed family of columns. -/
theorem columnMatroid_indep_finset_iff [Field K] [Finite n] (A : Matrix m n K)
    (I : Finset n) :
    (columnMatroid A).Indep (I : Set n) ↔
      LinearIndependent K (fun j : I ↦ A.col j) := by
  rfl

/-- An increasingly enumerated column set is independent exactly when the enumerated column
family is linearly independent. -/
theorem columnMatroid_indep_range_iff [Field K] [LinearOrder n] [Finite n]
    (A : Matrix m n K) {k : ℕ}
    (cols : Fin k ↪o n) :
    (columnMatroid A).Indep (Set.range cols) ↔
      LinearIndependent K (fun j : Fin k ↦ A.col (cols j)) := by
  rw [columnMatroid_indep_iff, linearIndepOn_range_iff cols.injective]
  rfl

/-- A column index is a matroid loop exactly when its column vector is zero. -/
theorem columnMatroid_isLoop_iff [Field K] [Finite n] (A : Matrix m n K) (j : n) :
    (columnMatroid A).IsLoop j ↔ A.col j = 0 := by
  rw [← (columnMatroid A).singleton_not_indep (by simp), columnMatroid_indep_iff]
  simp

/-- The matrix-level loop predicate agrees with the loop predicate of the represented matroid. -/
theorem isLoop_iff_columnMatroid_isLoop {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℝ)
    (j : Fin c) :
    IsLoop A j ↔ (columnMatroid A).IsLoop j := by
  rw [IsLoop, columnMatroid_isLoop_iff]

section MaximalMinors

variable [Field K] {r c : ℕ}

/-- A nonzero ordered maximal minor is equivalent to linear independence of its selected
columns. -/
theorem orderedMinor_ne_zero_iff_linearIndependent_columns
    (A : Matrix (Fin r) (Fin c) K) (cols : Fin r ↪o Fin c) :
    orderedMinor A (allRows r) cols ≠ 0 ↔
      LinearIndependent K (fun j : Fin r ↦ A.col (cols j)) := by
  change (A.submatrix (allRows r) cols).det ≠ 0 ↔ _
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_cols_iff_isUnit]
  rfl

/-- A set of as many selected columns as there are rows is a basis of the column matroid exactly
when its ordered maximal minor is nonzero. -/
theorem columnMatroid_isBase_range_iff (A : Matrix (Fin r) (Fin c) K)
    (cols : Fin r ↪o Fin c) :
    (columnMatroid A).IsBase (Set.range cols) ↔
      orderedMinor A (allRows r) cols ≠ 0 := by
  constructor
  · intro hbase
    rw [orderedMinor_ne_zero_iff_linearIndependent_columns]
    exact columnMatroid_indep_range_iff A cols |>.mp hbase.indep
  · intro hminor
    have hI : (columnMatroid A).Indep (Set.range cols) :=
      columnMatroid_indep_range_iff A cols |>.mpr
        ((orderedMinor_ne_zero_iff_linearIndependent_columns A cols).mp hminor)
    apply hI.isBase_of_maximal
    intro J hJ hIJ
    apply Set.eq_of_subset_of_ncard_le hIJ
    have hJlin : LinearIndependent K (fun j : J ↦ A.col j) :=
      (columnMatroid_indep_iff A J).mp hJ
    letI := Fintype.ofFinite J
    have hcard := hJlin.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at hcard
    have hJcard : J.ncard ≤ r := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      simpa using hcard
    simpa [Set.ncard_range_of_injective cols.injective] using hJcard

/-- When maximal minors are nonnegative, the bases are exactly the column selections with
positive maximal minor. -/
theorem columnMatroid_isBase_range_iff_orderedMinor_pos
    {A : Matrix (Fin r) (Fin c) ℝ} (hA : MaximalMinorsNonnegative A)
    (cols : Fin r ↪o Fin c) :
    (columnMatroid A).IsBase (Set.range cols) ↔
      0 < orderedMinor A (allRows r) cols := by
  rw [columnMatroid_isBase_range_iff]
  exact ⟨fun hne ↦ lt_of_le_of_ne (hA cols) hne.symm, ne_of_gt⟩

/-- The matrix-level column-basis predicate agrees with the basis predicate of the represented
column matroid. -/
theorem isColumnBasis_iff_columnMatroid_isBase (A : Matrix (Fin r) (Fin c) ℝ)
    (cols : Fin r ↪o Fin c) :
    IsColumnBasis A cols ↔ (columnMatroid A).IsBase (Set.range cols) := by
  rw [IsColumnBasis, columnMatroid_isBase_range_iff]

/-- Full row rank is equivalent to the existence of an increasingly enumerated basis of maximal
size in the column matroid. -/
theorem hasFullRowRank_iff_exists_columnMatroid_isBase (A : Matrix (Fin r) (Fin c) ℝ) :
    HasFullRowRank A ↔
      ∃ cols : Fin r ↪o Fin c, (columnMatroid A).IsBase (Set.range cols) := by
  simp only [HasFullRowRank, columnMatroid_isBase_range_iff]

end MaximalMinors

end ToeplitzPositroids
