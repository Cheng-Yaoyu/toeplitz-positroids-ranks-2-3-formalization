import ToeplitzPositroids.Matrix.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Determinant identities at parallel-class endpoints

This file isolates the polynomial identities used in the proofs of Theorem 10
and Lemma 11 of *Toeplitz Positroids in Ranks Two and Three*.  The identities
are stated over an arbitrary commutative ring; order assumptions occur only in
the sign corollaries.
-/

namespace ToeplitzPositroids

open Matrix

section ParallelTrap

variable {R : Type*} [CommRing R]

/-- The unscaled three-column matrix in the internal-parallel trap calculation.

The columns correspond to `cₚ₋₁`, `cₚ`, and `c_{q+1}` after removing their
common factor `c`.  The natural number `L` is the length of the parallel run in
the paper.  The identity below is valid without the paper's restriction `2 ≤ L`.
-/
def internalParallelTrapCore (lambda e f : R) (L : ℕ) : Matrix (Fin 3) (Fin 3) R :=
  !![lambda, lambda ^ 2, f;
    1, lambda, lambda ^ (L + 1);
    e, 1, lambda ^ L]

/-- The exponent-generic internal-parallel trap factorization. -/
theorem internalParallelTrapCore_det (lambda e f : R) (L : ℕ) :
    (internalParallelTrapCore lambda e f L).det =
      (lambda ^ (L + 2) - f) * (e * lambda - 1) := by
  rw [Matrix.det_fin_three]
  simp [internalParallelTrapCore, Matrix.cons_val_two, pow_succ]
  ring

/-- The actual trap matrix, including the common coefficient factor `c` in every column. -/
def internalParallelTrapMatrix (c lambda e f : R) (L : ℕ) :
    Matrix (Fin 3) (Fin 3) R :=
  !![c * lambda, c * lambda ^ 2, c * f;
    c, c * lambda, c * lambda ^ (L + 1);
    c * e, c, c * lambda ^ L]

/-- The trap matrix is obtained by scaling every entry of its core matrix by `c`. -/
theorem internalParallelTrapMatrix_eq_smul (c lambda e f : R) (L : ℕ) :
    internalParallelTrapMatrix c lambda e f L =
      c • internalParallelTrapCore lambda e f L := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [internalParallelTrapMatrix, internalParallelTrapCore]

/-- Formula (6.4), with a natural run length and no positivity assumptions. -/
theorem internalParallelTrapMatrix_det (c lambda e f : R) (L : ℕ) :
    (internalParallelTrapMatrix c lambda e f L).det =
      c ^ 3 * (lambda ^ (L + 2) - f) * (e * lambda - 1) := by
  rw [internalParallelTrapMatrix_eq_smul, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [internalParallelTrapCore_det]
  ring

/-- The end inequalities in Theorem 10 force the trap determinant to be nonpositive. -/
theorem internalParallelTrapMatrix_det_nonpos [LinearOrder R] [IsStrictOrderedRing R]
    {c lambda e f : R} {L : ℕ} (hc : 0 ≤ c) (he : e * lambda ≤ 1)
    (hf : f ≤ lambda ^ (L + 2)) :
    (internalParallelTrapMatrix c lambda e f L).det ≤ 0 := by
  rw [internalParallelTrapMatrix_det]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (pow_nonneg hc _) (sub_nonneg.mpr hf)) (sub_nonpos.mpr he)

end ParallelTrap

section EndpointProtection

variable {R : Type*} [CommRing R]

/-- The normalized endpoint-protection matrix from formula (6.5). -/
def endpointProtectionCore (radius t w : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, t, w; radius, 1, t; radius ^ 2, radius, 1]

/-- The endpoint-protection determinant is independent of `w`. -/
theorem endpointProtectionCore_det (radius t w : R) :
    (endpointProtectionCore radius t w).det = (1 - radius * t) ^ 2 := by
  rw [Matrix.det_fin_three]
  simp [endpointProtectionCore, Matrix.cons_val_two]
  ring

/-- The endpoint-protection matrix with the common column factor `A0`. -/
def endpointProtectionMatrix (A0 radius t w : R) : Matrix (Fin 3) (Fin 3) R :=
  !![A0, A0 * t, A0 * w;
    A0 * radius, A0, A0 * t;
    A0 * radius ^ 2, A0 * radius, A0]

/-- The scaled endpoint matrix is `A0` times its normalized core. -/
theorem endpointProtectionMatrix_eq_smul (A0 radius t w : R) :
    endpointProtectionMatrix A0 radius t w = A0 • endpointProtectionCore radius t w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [endpointProtectionMatrix, endpointProtectionCore]

/-- Formula (6.5): `A0³ * (1 - radius * t)²`, independently of `w`. -/
theorem endpointProtectionMatrix_det (A0 radius t w : R) :
    (endpointProtectionMatrix A0 radius t w).det =
      A0 ^ 3 * (1 - radius * t) ^ 2 := by
  rw [endpointProtectionMatrix_eq_smul, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [endpointProtectionCore_det]

/-- Changing `w` does not change the endpoint-protection determinant. -/
theorem endpointProtectionMatrix_det_independent (A0 radius t w₁ w₂ : R) :
    (endpointProtectionMatrix A0 radius t w₁).det =
      (endpointProtectionMatrix A0 radius t w₂).det := by
  rw [endpointProtectionMatrix_det, endpointProtectionMatrix_det]

/-- Under the strict endpoint inequality, the endpoint-protection determinant is positive. -/
theorem endpointProtectionMatrix_det_pos [LinearOrder R] [IsStrictOrderedRing R]
    {A0 radius t w : R} (hA0 : 0 < A0) (hrt : radius * t < 1) :
    0 < (endpointProtectionMatrix A0 radius t w).det := by
  rw [endpointProtectionMatrix_det]
  exact mul_pos (pow_pos hA0 _) (pow_pos (sub_pos.mpr hrt) _)

end EndpointProtection

section Boundary

variable {R : Type*} [CommRing R]

/-- The triangular matrix formed by the first three nonloop columns at a left support boundary. -/
def leftBoundaryTriple (b0 b1 b2 : R) : Matrix (Fin 3) (Fin 3) R :=
  !![b0, b1, b2; 0, b0, b1; 0, 0, b0]

/-- The triangular boundary determinant is the cube of its nonzero boundary coefficient. -/
theorem leftBoundaryTriple_det (b0 b1 b2 : R) :
    (leftBoundaryTriple b0 b1 b2).det = b0 ^ 3 := by
  rw [Matrix.det_fin_three]
  simp [leftBoundaryTriple, Matrix.cons_val_two]
  ring

/-- A positive boundary coefficient makes the triangular boundary determinant positive. -/
theorem leftBoundaryTriple_det_pos [LinearOrder R] [IsStrictOrderedRing R]
    {b0 b1 b2 : R} (hb0 : 0 < b0) :
    0 < (leftBoundaryTriple b0 b1 b2).det := by
  rw [leftBoundaryTriple_det]
  exact pow_pos hb0 _

end Boundary

section Reversal

variable {R : Type*}

/-- Reverse both row and column orders of a `3 × 3` matrix. -/
def reverseThree (A : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix Fin.revPerm Fin.revPerm

/-- Reversing both orders writes the entries in the opposite order in each direction. -/
theorem reverseThree_eq (A : Matrix (Fin 3) (Fin 3) R) :
    reverseThree A =
      !![A 2 2, A 2 1, A 2 0; A 1 2, A 1 1, A 1 0; A 0 2, A 0 1, A 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable [CommRing R]

/-- The two reversal signs cancel, so reversing both orders preserves a `3 × 3` determinant. -/
@[simp]
theorem reverseThree_det (A : Matrix (Fin 3) (Fin 3) R) :
    (reverseThree A).det = A.det := by
  simp [reverseThree]

/-- The reversal sign cancellation written as an explicit polynomial identity. -/
theorem det_reverse_three_explicit (a b c d e f g h i : R) :
    Matrix.det !![i, h, g; f, e, d; c, b, a] =
      Matrix.det !![a, b, c; d, e, f; g, h, i] := by
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  simp [Matrix.cons_val_two]
  ring

end Reversal

end ToeplitzPositroids
