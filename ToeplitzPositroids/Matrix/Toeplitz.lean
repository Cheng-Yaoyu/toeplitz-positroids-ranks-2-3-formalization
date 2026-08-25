import ToeplitzPositroids.Matrix.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Finite Toeplitz matrix sections

This file defines the finite Toeplitz sections used in the rank-two and rank-three
parts of the paper.  A coefficient vector for an `r × n` section is stored in
increasing order of its integer labels

`1 - r, 2 - r, ..., n - 1`.

Thus its entry in row `i` and column `j` has vector index `j + (r - 1 - i)`.
We also provide an integer-indexed version and a zero extension relating the two
conventions.
-/

namespace ToeplitzPositroids

universe u

variable {R : Type u}
variable {r n : ℕ}

/-- The coefficient index of entry `(i, j)` in a finite `r × n` Toeplitz section.

The coefficient vector is ordered by the integer labels `1 - r, ..., n - 1`.
-/
def finiteToeplitzIndex (i : Fin r) (j : Fin n) : Fin (n + r - 1) :=
  ⟨j + (r - 1 - i), by omega⟩

@[simp]
theorem finiteToeplitzIndex_val (i : Fin r) (j : Fin n) :
    (finiteToeplitzIndex i j : ℕ) = j + (r - 1 - i) :=
  rfl

/-- Simultaneously reversing the row and column indices reverses the coefficient index. -/
@[simp]
theorem finiteToeplitzIndex_rev (i : Fin r) (j : Fin n) :
    finiteToeplitzIndex i.rev j.rev = (finiteToeplitzIndex i j).rev := by
  apply Fin.ext
  simp only [finiteToeplitzIndex_val, Fin.val_rev]
  omega

/-- A finite `r × n` Toeplitz section whose coefficient vector is indexed in
increasing order from coefficient `1 - r` to coefficient `n - 1`. -/
def finiteToeplitz (a : Fin (n + r - 1) → R) : Matrix (Fin r) (Fin n) R :=
  fun i j ↦ a (finiteToeplitzIndex i j)

@[simp]
theorem finiteToeplitz_apply (a : Fin (n + r - 1) → R) (i : Fin r) (j : Fin n) :
    finiteToeplitz a i j = a (finiteToeplitzIndex i j) :=
  rfl

/-- Reversing both matrix axes of a finite Toeplitz section reverses its coefficients. -/
theorem finiteToeplitz_submatrix_rev (a : Fin (n + r - 1) → R) :
    (finiteToeplitz a).submatrix Fin.rev Fin.rev =
      finiteToeplitz (a ∘ Fin.rev) := by
  ext i j
  simp

/-- The integer-indexed `r × n` Toeplitz section associated to `a`. -/
def toeplitzMatrix (r n : ℕ) (a : ℤ → R) : Matrix (Fin r) (Fin n) R :=
  fun i j ↦ a (j - i)

@[simp]
theorem toeplitzMatrix_apply (a : ℤ → R) (i : Fin r) (j : Fin n) :
    toeplitzMatrix r n a i j = a (j - i) :=
  rfl

/-- Translate the labels of an integer-indexed coefficient sequence. -/
def shiftCoefficients (a : ℤ → R) (s : ℤ) : ℤ → R :=
  fun k ↦ a (k + s)

@[simp]
theorem shiftCoefficients_apply (a : ℤ → R) (s k : ℤ) :
    shiftCoefficients a s k = a (k + s) :=
  rfl

/-- Deleting the first row shifts all coefficient labels down by one. -/
theorem toeplitzMatrix_succ_rows (a : ℤ → R) :
    (toeplitzMatrix (r + 1) n a).submatrix Fin.succ id =
      toeplitzMatrix r n (shiftCoefficients a (-1)) := by
  ext i j
  simp only [Matrix.submatrix_apply, toeplitzMatrix_apply, shiftCoefficients_apply,
    id_eq, Fin.val_succ]
  congr 1
  omega

/-- Deleting the first column shifts all coefficient labels up by one. -/
theorem toeplitzMatrix_succ_cols (a : ℤ → R) :
    (toeplitzMatrix r (n + 1) a).submatrix id Fin.succ =
      toeplitzMatrix r n (shiftCoefficients a 1) := by
  ext i j
  simp only [Matrix.submatrix_apply, toeplitzMatrix_apply, shiftCoefficients_apply,
    id_eq, Fin.val_succ]
  congr 1
  omega

/-- Moving one row and one column southeast leaves a Toeplitz entry unchanged. -/
@[simp]
theorem toeplitzMatrix_succ_succ (a : ℤ → R) (i : Fin r) (j : Fin n) :
    toeplitzMatrix (r + 1) (n + 1) a i.succ j.succ = toeplitzMatrix r n a i j := by
  simp only [toeplitzMatrix_apply, Fin.val_succ]
  congr 1
  omega

/-- Reverse the coefficient labels appropriate to reversing an `r × n` section. -/
def reverseCoefficients (r n : ℕ) (a : ℤ → R) : ℤ → R :=
  fun k ↦ a (n - r - k)

@[simp]
theorem reverseCoefficients_apply (a : ℤ → R) (k : ℤ) :
    reverseCoefficients r n a k = a (n - r - k) :=
  rfl

/-- Reversing both axes of an integer-indexed Toeplitz section reverses and translates
the coefficient labels. -/
theorem toeplitzMatrix_submatrix_rev (a : ℤ → R) :
    (toeplitzMatrix r n a).submatrix Fin.rev Fin.rev =
      toeplitzMatrix r n (reverseCoefficients r n a) := by
  ext i j
  simp only [Matrix.submatrix_apply, toeplitzMatrix_apply, reverseCoefficients_apply,
    Fin.val_rev]
  congr 1
  omega

/-- Extend a finite coefficient vector by zero to all integer coefficient labels. -/
def zeroExtendCoefficients [Zero R] (a : Fin (n + r - 1) → R) : ℤ → R :=
  fun k ↦
    if h : 0 ≤ k + (r - 1 : ℕ) ∧
        k + (r - 1 : ℕ) < (n + r - 1 : ℕ) then
      a ⟨(k + (r - 1 : ℕ)).toNat, by omega⟩
    else
      0

/-- The zero extension recovers each stored coefficient at its integer label. -/
@[simp]
theorem zeroExtendCoefficients_at_index [Zero R] (a : Fin (n + r - 1) → R)
    (k : Fin (n + r - 1)) :
    zeroExtendCoefficients a (k - (r - 1 : ℕ)) = a k := by
  simp only [zeroExtendCoefficients]
  split_ifs with h
  · congr 1
    apply Fin.ext
    rw [← Int.ofNat_inj, Int.toNat_of_nonneg (by omega)]
    omega
  · exfalso
    apply h
    constructor <;> omega

/-- The zero extension agrees with the finite coefficient vector on every matrix entry. -/
@[simp]
theorem zeroExtendCoefficients_entry [Zero R] (a : Fin (n + r - 1) → R)
    (i : Fin r) (j : Fin n) :
    zeroExtendCoefficients a (j - i) = a (finiteToeplitzIndex i j) := by
  simp only [zeroExtendCoefficients]
  split_ifs with h
  · congr 1
    apply Fin.ext
    simp only [finiteToeplitzIndex_val]
    omega
  · exfalso
    apply h
    constructor <;> omega

/-- A finite Toeplitz section is the section of the zero-extended integer sequence. -/
theorem toeplitzMatrix_zeroExtendCoefficients [Zero R]
    (a : Fin (n + r - 1) → R) :
    toeplitzMatrix r n (zeroExtendCoefficients a) = finiteToeplitz a := by
  ext i j
  simp

/-- The rank-two Toeplitz matrix from coefficients indexed by `-1, 0, ..., n - 1`. -/
def rankTwoToeplitz (a : Fin (n + 1) → R) : Matrix (Fin 2) (Fin n) R :=
  fun i j ↦ a ⟨j + (1 - i), by omega⟩

@[simp]
theorem rankTwoToeplitz_apply (a : Fin (n + 1) → R) (i : Fin 2) (j : Fin n) :
    rankTwoToeplitz a i j = a ⟨j + (1 - i), by omega⟩ :=
  rfl

@[simp]
theorem rankTwoToeplitz_row_zero (a : Fin (n + 1) → R) (j : Fin n) :
    rankTwoToeplitz a 0 j = a j.succ := by
  rfl

@[simp]
theorem rankTwoToeplitz_row_one (a : Fin (n + 1) → R) (j : Fin n) :
    rankTwoToeplitz a 1 j = a j.castSucc := by
  rfl

/-- The exact formula for a column of a rank-two Toeplitz matrix. -/
theorem rankTwoToeplitz_column (a : Fin (n + 1) → R) (j : Fin n) :
    (fun i ↦ rankTwoToeplitz a i j) = ![a j.succ, a j.castSucc] := by
  funext i
  fin_cases i <;> rfl

/-- The rank-two wrapper is the generic finite Toeplitz construction. -/
theorem rankTwoToeplitz_eq_finiteToeplitz (a : Fin (n + 1) → R) :
    rankTwoToeplitz a = finiteToeplitz (r := 2) a := by
  rfl

/-- The rank-two wrapper agrees with the integer-indexed wrapper after zero extension. -/
theorem rankTwoToeplitz_eq_toeplitzMatrix [Zero R] (a : Fin (n + 1) → R) :
    rankTwoToeplitz a = toeplitzMatrix 2 n (zeroExtendCoefficients (r := 2) a) := by
  rw [toeplitzMatrix_zeroExtendCoefficients]
  exact rankTwoToeplitz_eq_finiteToeplitz a

/-- Reversing rows and columns of a rank-two section reverses its coefficient vector. -/
theorem rankTwoToeplitz_submatrix_rev (a : Fin (n + 1) → R) :
    (rankTwoToeplitz a).submatrix Fin.rev Fin.rev =
      rankTwoToeplitz (a ∘ Fin.rev) := by
  rw [rankTwoToeplitz_eq_finiteToeplitz, finiteToeplitz_submatrix_rev,
    rankTwoToeplitz_eq_finiteToeplitz]
  rfl

/-- The rank-three Toeplitz matrix from coefficients indexed by `-2, -1, ..., n - 1`. -/
def rankThreeToeplitz (a : Fin (n + 2) → R) : Matrix (Fin 3) (Fin n) R :=
  fun i j ↦ a ⟨j + (2 - i), by omega⟩

@[simp]
theorem rankThreeToeplitz_apply (a : Fin (n + 2) → R) (i : Fin 3) (j : Fin n) :
    rankThreeToeplitz a i j = a ⟨j + (2 - i), by omega⟩ :=
  rfl

@[simp]
theorem rankThreeToeplitz_row_zero (a : Fin (n + 2) → R) (j : Fin n) :
    rankThreeToeplitz a 0 j = a j.succ.succ := by
  rfl

@[simp]
theorem rankThreeToeplitz_row_one (a : Fin (n + 2) → R) (j : Fin n) :
    rankThreeToeplitz a 1 j = a j.succ.castSucc := by
  rfl

@[simp]
theorem rankThreeToeplitz_row_two (a : Fin (n + 2) → R) (j : Fin n) :
    rankThreeToeplitz a 2 j = a j.castSucc.castSucc := by
  rfl

/-- The exact formula for a column of a rank-three Toeplitz matrix. -/
theorem rankThreeToeplitz_column (a : Fin (n + 2) → R) (j : Fin n) :
    (fun i ↦ rankThreeToeplitz a i j) =
      ![a j.succ.succ, a j.succ.castSucc, a j.castSucc.castSucc] := by
  funext i
  fin_cases i <;> rfl

/-- The rank-three wrapper is the generic finite Toeplitz construction. -/
theorem rankThreeToeplitz_eq_finiteToeplitz (a : Fin (n + 2) → R) :
    rankThreeToeplitz a = finiteToeplitz (r := 3) a := by
  rfl

/-- The rank-three wrapper agrees with the integer-indexed wrapper after zero extension. -/
theorem rankThreeToeplitz_eq_toeplitzMatrix [Zero R] (a : Fin (n + 2) → R) :
    rankThreeToeplitz a = toeplitzMatrix 3 n (zeroExtendCoefficients (r := 3) a) := by
  rw [toeplitzMatrix_zeroExtendCoefficients]
  exact rankThreeToeplitz_eq_finiteToeplitz a

/-- The top two rows of a rank-three Toeplitz matrix form the rank-two section of
the coefficient vector with its first entry removed. -/
theorem rankThreeToeplitz_top_two_rows (a : Fin (n + 2) → R) :
    (rankThreeToeplitz a).submatrix Fin.castSucc id =
      rankTwoToeplitz (a ∘ Fin.succ) := by
  ext i j
  fin_cases i <;> rfl

/-- The bottom two rows of a rank-three Toeplitz matrix form the rank-two section of
the coefficient vector with its last entry removed. -/
theorem rankThreeToeplitz_bottom_two_rows (a : Fin (n + 2) → R) :
    (rankThreeToeplitz a).submatrix Fin.succ id =
      rankTwoToeplitz (a ∘ Fin.castSucc) := by
  ext i j
  fin_cases i <;> rfl

/-- Reversing rows and columns of a rank-three section reverses its coefficient vector. -/
theorem rankThreeToeplitz_submatrix_rev (a : Fin (n + 2) → R) :
    (rankThreeToeplitz a).submatrix Fin.rev Fin.rev =
      rankThreeToeplitz (a ∘ Fin.rev) := by
  rw [rankThreeToeplitz_eq_finiteToeplitz, finiteToeplitz_submatrix_rev,
    rankThreeToeplitz_eq_finiteToeplitz]
  rfl

end ToeplitzPositroids
