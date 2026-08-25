import ToeplitzPositroids.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Ordered column configurations

This file records the matrix-level notions of loops, positive parallelism, full
row rank, and nonnegative maximal minors used in the paper.  These definitions
deliberately precede the construction of a column matroid: most of the low-rank
arguments only depend on determinant support.
-/

namespace ToeplitzPositroids

open Matrix

variable {m n : ℕ}

/-- A column is a loop when it is the zero vector. -/
def IsLoop (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : Prop :=
  A.col j = 0

theorem isLoop_iff_entry_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} {j : Fin n} :
    IsLoop A j ↔ ∀ i, A i j = 0 := by
  change (fun i => A i j) = (0 : Fin m → ℝ) ↔ ∀ i, A i j = 0
  constructor
  · intro h i
    simpa using congrFun h i
  · intro h
    funext i
    simpa using h i

/-- The second column is a positive scalar multiple of the first.

This raw proportionality predicate also holds for two zero columns.  The paper's
notion of a parallel pair, which explicitly excludes loops, is `ColumnsParallel`.
-/
def ColumnsPositivelyParallel (A : Matrix (Fin m) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ∃ c : ℝ, 0 < c ∧ A.col j = c • A.col i

/-- Two columns are parallel in the sense of the paper: they are nonzero and one
is a positive scalar multiple of the other. -/
def ColumnsParallel (A : Matrix (Fin m) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ¬IsLoop A i ∧ ColumnsPositivelyParallel A i j

theorem columnsPositivelyParallel_refl (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    ColumnsPositivelyParallel A i i := by
  refine ⟨1, zero_lt_one, ?_⟩
  simp

theorem columnsPositivelyParallel_symm {A : Matrix (Fin m) (Fin n) ℝ} {i j : Fin n}
    (h : ColumnsPositivelyParallel A i j) : ColumnsPositivelyParallel A j i := by
  obtain ⟨c, hc, hcol⟩ := h
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  rw [hcol, smul_smul]
  simp [hc.ne']

theorem columnsPositivelyParallel_trans {A : Matrix (Fin m) (Fin n) ℝ} {i j k : Fin n}
    (hij : ColumnsPositivelyParallel A i j) (hjk : ColumnsPositivelyParallel A j k) :
    ColumnsPositivelyParallel A i k := by
  obtain ⟨c, hc, hcij⟩ := hij
  obtain ⟨d, hd, hdjk⟩ := hjk
  refine ⟨d * c, mul_pos hd hc, ?_⟩
  rw [hdjk, hcij, smul_smul]

theorem columnsParallel_refl {A : Matrix (Fin m) (Fin n) ℝ} {i : Fin n}
    (hi : ¬IsLoop A i) : ColumnsParallel A i i :=
  ⟨hi, columnsPositivelyParallel_refl A i⟩

theorem columnsParallel_symm {A : Matrix (Fin m) (Fin n) ℝ} {i j : Fin n}
    (h : ColumnsParallel A i j) : ColumnsParallel A j i := by
  rcases h with ⟨hi, hij⟩
  have hj : ¬IsLoop A j := by
    intro hj
    rcases hij with ⟨c, hc, hcol⟩
    apply hi
    rw [IsLoop] at hi hj ⊢
    rw [hcol] at hj
    have hc0 : c ≠ 0 := hc.ne'
    exact (smul_eq_zero.mp hj).resolve_left hc0
  exact ⟨hj, columnsPositivelyParallel_symm hij⟩

theorem columnsParallel_trans {A : Matrix (Fin m) (Fin n) ℝ} {i j k : Fin n}
    (hij : ColumnsParallel A i j) (hjk : ColumnsParallel A j k) :
    ColumnsParallel A i k :=
  ⟨hij.1, columnsPositivelyParallel_trans hij.2 hjk.2⟩

/-- The increasing embedding containing every row of a square maximal minor. -/
def allRows (m : ℕ) : Fin m ↪o Fin m :=
  (OrderIso.refl (Fin m)).toOrderEmbedding

/-- A full-row-rank witness is a nonzero ordered maximal minor. -/
def HasFullRowRank (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ cols : Fin m ↪o Fin n, orderedMinor A (allRows m) cols ≠ 0

/-- Every ordered maximal minor is nonnegative. -/
def MaximalMinorsNonnegative (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ cols : Fin m ↪o Fin n, 0 ≤ orderedMinor A (allRows m) cols

/-- The support predicate of the ordered maximal minor indexed by `cols`. -/
def IsColumnBasis (A : Matrix (Fin m) (Fin n) ℝ) (cols : Fin m ↪o Fin n) : Prop :=
  orderedMinor A (allRows m) cols ≠ 0

theorem hasFullRowRank_iff_exists_isColumnBasis (A : Matrix (Fin m) (Fin n) ℝ) :
    HasFullRowRank A ↔ ∃ cols, IsColumnBasis A cols :=
  Iff.rfl

/-- A matrix-level positroid representation has full row rank and nonnegative maximal minors. -/
def IsPositroidRepresentation (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  HasFullRowRank A ∧ MaximalMinorsNonnegative A

end ToeplitzPositroids
