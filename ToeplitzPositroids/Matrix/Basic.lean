import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic

/-!
# Finite Toeplitz matrices and their minors

This file develops the common matrix-theoretic definitions used throughout the
formalization.
-/

namespace ToeplitzPositroids

variable {R m n m' n' : Type*}

/-- The order embedding selecting a single element. -/
def singletonOrderEmbedding [Preorder m] (i : m) : Fin 1 ↪o m :=
  OrderEmbedding.ofMapLEIff (fun _ => i) fun a b => by simp [Subsingleton.elim a b]

section OrderedMinors

variable [CommRing R] [Preorder m] [Preorder n]

/-- The minor of `A` on the increasingly enumerated rows `rows` and columns `cols`.

Using order embeddings fixes the sign of the determinant canonically. In particular, the
definition does not permit an arbitrary permutation of the selected rows or columns. -/
def orderedMinor (A : Matrix m n R) {k : ℕ} (rows : Fin k ↪o m) (cols : Fin k ↪o n) : R :=
  (A.submatrix rows cols).det

/-- The unique minor of order zero is one. -/
@[simp]
theorem orderedMinor_zero (A : Matrix m n R) (rows : Fin 0 ↪o m) (cols : Fin 0 ↪o n) :
    orderedMinor A rows cols = 1 := by
  simp [orderedMinor]

/-- An ordered minor of order one is the corresponding matrix entry. -/
@[simp]
theorem orderedMinor_one (A : Matrix m n R) (rows : Fin 1 ↪o m) (cols : Fin 1 ↪o n) :
    orderedMinor A rows cols = A (rows 0) (cols 0) := by
  simp [orderedMinor]

/-- The explicit determinant formula for an ordered minor of order two. -/
theorem orderedMinor_two (A : Matrix m n R) (rows : Fin 2 ↪o m) (cols : Fin 2 ↪o n) :
    orderedMinor A rows cols =
      A (rows 0) (cols 0) * A (rows 1) (cols 1) -
        A (rows 0) (cols 1) * A (rows 1) (cols 0) := by
  simpa [orderedMinor] using Matrix.det_fin_two (A.submatrix rows cols)

/-- The explicit determinant formula for an ordered minor of order three. -/
theorem orderedMinor_three (A : Matrix m n R) (rows : Fin 3 ↪o m) (cols : Fin 3 ↪o n) :
    orderedMinor A rows cols =
      A (rows 0) (cols 0) * A (rows 1) (cols 1) * A (rows 2) (cols 2) -
        A (rows 0) (cols 0) * A (rows 1) (cols 2) * A (rows 2) (cols 1) -
        A (rows 0) (cols 1) * A (rows 1) (cols 0) * A (rows 2) (cols 2) +
        A (rows 0) (cols 1) * A (rows 1) (cols 2) * A (rows 2) (cols 0) +
        A (rows 0) (cols 2) * A (rows 1) (cols 0) * A (rows 2) (cols 1) -
        A (rows 0) (cols 2) * A (rows 1) (cols 1) * A (rows 2) (cols 0) := by
  simpa [orderedMinor] using Matrix.det_fin_three (A.submatrix rows cols)

/-- Transposition exchanges the row and column selections of an ordered minor. -/
@[simp]
theorem orderedMinor_transpose (A : Matrix m n R) {k : ℕ} (rows : Fin k ↪o m)
    (cols : Fin k ↪o n) :
    orderedMinor A.transpose cols rows = orderedMinor A rows cols := by
  simp [orderedMinor, ← Matrix.transpose_submatrix]

/-- Taking an ordered minor after an order-preserving restriction composes the row and column
selections. -/
theorem orderedMinor_submatrix [Preorder m'] [Preorder n'] (A : Matrix m n R)
    (rowMap : m' ↪o m) (colMap : n' ↪o n) {k : ℕ} (rows : Fin k ↪o m')
    (cols : Fin k ↪o n') :
    orderedMinor (A.submatrix rowMap colMap) rows cols =
      orderedMinor A (rows.trans rowMap) (cols.trans colMap) := by
  simp [orderedMinor, Matrix.submatrix_submatrix]

end OrderedMinors

section TotalNonnegativity

variable [CommRing R] [PartialOrder R] [LinearOrder m] [LinearOrder n]

/-- `TNUpTo A k` means that every ordered minor of `A` of order at most `k` is
nonnegative. This is the paper's condition `TN_k`. -/
def TNUpTo (A : Matrix m n R) (k : ℕ) : Prop :=
  ∀ l : ℕ, l ≤ k → ∀ (rows : Fin l ↪o m) (cols : Fin l ↪o n),
    0 ≤ orderedMinor A rows cols

/-- A matrix is totally nonnegative when every ordered minor is nonnegative. -/
def TotallyNonnegative (A : Matrix m n R) : Prop :=
  ∀ k : ℕ, ∀ (rows : Fin k ↪o m) (cols : Fin k ↪o n), 0 ≤ orderedMinor A rows cols

/-- A matrix is totally positive when every ordered minor is positive. -/
def TotallyPositive (A : Matrix m n R) : Prop :=
  ∀ k : ℕ, ∀ (rows : Fin k ↪o m) (cols : Fin k ↪o n), 0 < orderedMinor A rows cols

/-- Extract nonnegativity of a particular minor from a bounded total-nonnegativity hypothesis. -/
theorem TNUpTo.orderedMinor_nonneg {A : Matrix m n R} {k l : ℕ} (hA : TNUpTo A k)
    (hlk : l ≤ k) (rows : Fin l ↪o m) (cols : Fin l ↪o n) :
    0 ≤ orderedMinor A rows cols :=
  hA l hlk rows cols

/-- Extract nonnegativity of a particular minor from total nonnegativity. -/
theorem TotallyNonnegative.orderedMinor_nonneg {A : Matrix m n R} (hA : TotallyNonnegative A)
    {k : ℕ} (rows : Fin k ↪o m) (cols : Fin k ↪o n) :
    0 ≤ orderedMinor A rows cols :=
  hA k rows cols

/-- Extract positivity of a particular minor from total positivity. -/
theorem TotallyPositive.orderedMinor_pos {A : Matrix m n R} (hA : TotallyPositive A)
    {k : ℕ} (rows : Fin k ↪o m) (cols : Fin k ↪o n) :
    0 < orderedMinor A rows cols :=
  hA k rows cols

/-- Total nonnegativity supplies nonnegativity through every fixed order. -/
theorem TotallyNonnegative.tnUpTo {A : Matrix m n R} (hA : TotallyNonnegative A) (k : ℕ) :
    TNUpTo A k := by
  intro l _ rows cols
  exact hA l rows cols

/-- The conditions `TNUpTo A k` become weaker as `k` decreases. -/
theorem TNUpTo.mono {A : Matrix m n R} {k l : ℕ} (hA : TNUpTo A k) (hlk : l ≤ k) :
    TNUpTo A l := by
  intro d hdl rows cols
  exact hA d (hdl.trans hlk) rows cols

/-- Every matrix is totally nonnegative through order zero when `0 ≤ 1`. -/
theorem tnUpTo_zero [ZeroLEOneClass R] (A : Matrix m n R) : TNUpTo A 0 := by
  intro l hl rows cols
  obtain rfl := Nat.eq_zero_of_le_zero hl
  simp

/-- Total nonnegativity through order one is exactly entrywise nonnegativity. -/
theorem tnUpTo_one_iff_entries_nonneg [ZeroLEOneClass R] (A : Matrix m n R) :
    TNUpTo A 1 ↔ ∀ i j, 0 ≤ A i j := by
  constructor
  · intro hA i j
    simpa using hA 1 le_rfl (singletonOrderEmbedding i) (singletonOrderEmbedding j)
  · intro hA l hl rows cols
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl with rfl | rfl
    · simp
    · simpa using hA (rows 0) (cols 0)

/-- A totally positive matrix is totally nonnegative. -/
theorem TotallyPositive.totallyNonnegative {A : Matrix m n R} (hA : TotallyPositive A) :
    TotallyNonnegative A := by
  intro k rows cols
  exact (hA k rows cols).le

/-- Total positivity implies nonnegativity of all minors through any fixed order. -/
theorem TotallyPositive.tnUpTo {A : Matrix m n R} (hA : TotallyPositive A) (k : ℕ) :
    TNUpTo A k :=
  hA.totallyNonnegative.tnUpTo k

/-- Total nonnegativity is equivalent to satisfying every finite-order condition. -/
theorem totallyNonnegative_iff_forall_tnUpTo (A : Matrix m n R) :
    TotallyNonnegative A ↔ ∀ k : ℕ, TNUpTo A k := by
  constructor
  · intro hA k
    exact hA.tnUpTo k
  · intro hA k rows cols
    exact hA k k le_rfl rows cols

/-- A `TNUpTo` hypothesis of order at least one makes every entry nonnegative. -/
theorem TNUpTo.entry_nonneg {A : Matrix m n R} {k : ℕ} (hA : TNUpTo A k) (hk : 1 ≤ k)
    (i : m) (j : n) :
    0 ≤ A i j := by
  simpa using hA 1 hk (singletonOrderEmbedding i) (singletonOrderEmbedding j)

/-- Every entry of a totally nonnegative matrix is nonnegative. -/
theorem TotallyNonnegative.entry_nonneg {A : Matrix m n R} (hA : TotallyNonnegative A)
    (i : m) (j : n) :
    0 ≤ A i j := by
  simpa using hA 1 (singletonOrderEmbedding i) (singletonOrderEmbedding j)

/-- Every entry of a totally positive matrix is positive. -/
theorem TotallyPositive.entry_pos {A : Matrix m n R} (hA : TotallyPositive A) (i : m) (j : n) :
    0 < A i j := by
  simpa using hA 1 (singletonOrderEmbedding i) (singletonOrderEmbedding j)

/-- Transposition preserves total nonnegativity. -/
theorem TotallyNonnegative.transpose {A : Matrix m n R} (hA : TotallyNonnegative A) :
    TotallyNonnegative A.transpose := by
  intro k rows cols
  simpa using hA k cols rows

/-- Transposition preserves total positivity. -/
theorem TotallyPositive.transpose {A : Matrix m n R} (hA : TotallyPositive A) :
    TotallyPositive A.transpose := by
  intro k rows cols
  simpa using hA k cols rows

/-- Transposition preserves total nonnegativity through a fixed order. -/
theorem TNUpTo.transpose {A : Matrix m n R} {k : ℕ} (hA : TNUpTo A k) :
    TNUpTo A.transpose k := by
  intro l hl rows cols
  simpa using hA l hl cols rows

/-- An order-preserving submatrix of a totally nonnegative matrix is totally nonnegative. -/
theorem TotallyNonnegative.submatrix [LinearOrder m'] [LinearOrder n'] {A : Matrix m n R}
    (hA : TotallyNonnegative A) (rowMap : m' ↪o m) (colMap : n' ↪o n) :
    TotallyNonnegative (A.submatrix rowMap colMap) := by
  intro k rows cols
  rw [orderedMinor_submatrix]
  exact hA k (rows.trans rowMap) (cols.trans colMap)

/-- An order-preserving submatrix of a totally positive matrix is totally positive. -/
theorem TotallyPositive.submatrix [LinearOrder m'] [LinearOrder n'] {A : Matrix m n R}
    (hA : TotallyPositive A) (rowMap : m' ↪o m) (colMap : n' ↪o n) :
    TotallyPositive (A.submatrix rowMap colMap) := by
  intro k rows cols
  rw [orderedMinor_submatrix]
  exact hA k (rows.trans rowMap) (cols.trans colMap)

/-- An order-preserving submatrix preserves bounded total nonnegativity. -/
theorem TNUpTo.submatrix [LinearOrder m'] [LinearOrder n'] {A : Matrix m n R} {k : ℕ}
    (hA : TNUpTo A k) (rowMap : m' ↪o m) (colMap : n' ↪o n) :
    TNUpTo (A.submatrix rowMap colMap) k := by
  intro l hl rows cols
  rw [orderedMinor_submatrix]
  exact hA l hl (rows.trans rowMap) (cols.trans colMap)

end TotalNonnegativity

end ToeplitzPositroids
