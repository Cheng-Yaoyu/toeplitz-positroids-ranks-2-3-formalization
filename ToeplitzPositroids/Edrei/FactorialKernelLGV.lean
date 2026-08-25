import ToeplitzPositroids.Edrei.ExponentialMinor
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# Reciprocal-factorial minors and Pascal determinants

This file proves the arbitrary-order first-row-block case of the reciprocal-factorial kernel.
After positive diagonal scaling, the minor is a consecutive-degree Pascal determinant; falling
factorials identify that determinant with a Vandermonde determinant.
-/

namespace ToeplitzPositroids

noncomputable section

/-- The first `r` natural row indices. -/
def firstNaturalRows (r : ℕ) : Fin r ↪o ℕ := Fin.valOrderEmb r

/-- The Pascal evaluation matrix on increasingly selected natural arguments. -/
def pascalEvaluationMatrix {r : ℕ} (cols : Fin r ↪o ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j ↦ Nat.choose (cols j) i

/-- The falling-factorial evaluation matrix is the transpose Pascal matrix followed by positive
column scaling by factorials. -/
theorem descPochhammerEvaluation_eq_pascalTranspose_mul_diagonal {r : ℕ}
    (cols : Fin r ↪o ℕ) :
    Matrix.of (fun i j : Fin r ↦
      (descPochhammer ℝ j).eval (cols i : ℝ)) =
      (pascalEvaluationMatrix cols).transpose *
        Matrix.diagonal (fun j : Fin r ↦ ((j : ℕ).factorial : ℝ)) := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [Matrix.transpose_apply, pascalEvaluationMatrix]
  change (descPochhammer ℝ (j : ℕ)).eval (cols i : ℝ) = _
  rw [descPochhammer_eval_eq_descFactorial]
  norm_cast
  simpa [mul_comm] using Nat.descFactorial_eq_factorial_mul_choose (cols i) (j : ℕ)

/-- The Pascal determinant times the product of column factorials is a Vandermonde determinant. -/
theorem pascal_det_mul_prod_factorial_eq_vandermonde {r : ℕ}
    (cols : Fin r ↪o ℕ) :
    (pascalEvaluationMatrix cols).det * (∏ i : Fin r, ((i : ℕ).factorial : ℝ)) =
      (Matrix.vandermonde fun j : Fin r ↦ (cols j : ℝ)).det := by
  have heval := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun j : Fin r ↦ (cols j : ℝ))
    (fun i : Fin r ↦ descPochhammer ℝ i)
    (fun i ↦ descPochhammer_natDegree ℝ i)
    (fun i ↦ monic_descPochhammer ℝ i)
  rw [descPochhammerEvaluation_eq_pascalTranspose_mul_diagonal,
    Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at heval
  exact heval.symm

/-- Increasing Pascal evaluation points give a strictly positive determinant. -/
theorem pascalEvaluationMatrix_det_pos {r : ℕ} (cols : Fin r ↪o ℕ) :
    0 < (pascalEvaluationMatrix cols).det := by
  have hvand : 0 < (Matrix.vandermonde fun j : Fin r ↦ (cols j : ℝ)).det := by
    rw [Matrix.det_vandermonde]
    apply Finset.prod_pos
    intro j hj
    apply Finset.prod_pos
    intro i hi
    have hji : j < i := Finset.mem_Ioi.mp hi
    have hcols : cols j < cols i := cols.strictMono hji
    have hcols' : (cols j : ℝ) < cols i := by exact_mod_cast hcols
    linarith
  have hfactorial : 0 < ∏ i : Fin r, ((i : ℕ).factorial : ℝ) := by
    apply Finset.prod_pos
    intro i hi
    positivity
  have heq := pascal_det_mul_prod_factorial_eq_vandermonde cols
  rw [← heq] at hvand
  exact (mul_pos_iff_of_pos_right hfactorial).mp hvand

/-- Entrywise scaling of the first-row reciprocal-factorial matrix to the Pascal matrix. -/
theorem firstRows_factorialKernelMatrix_eq_diagonal_mul_pascal_mul_diagonal
    {r : ℕ} (cols : Fin r ↪o ℕ) :
    oneSidedToeplitzMinorMatrix factorialKernelCoefficient (firstNaturalRows r) cols =
      Matrix.diagonal (fun i : Fin r ↦ ((i : ℕ).factorial : ℝ)) *
        pascalEvaluationMatrix cols *
          Matrix.diagonal (fun j : Fin r ↦ ((cols j).factorial : ℝ)⁻¹) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [firstNaturalRows, pascalEvaluationMatrix]
  change factorialKernelCoefficient ((cols j : ℤ) - (i.val : ℤ)) = _
  by_cases hij : i.val ≤ cols j
  · have hnonneg : (0 : ℤ) ≤ (cols j : ℤ) - (i.val : ℤ) := by omega
    rw [factorialKernelCoefficient, if_pos hnonneg, Int.toNat_sub]
    have hchoose := Nat.choose_mul_factorial_mul_factorial hij
    have hchooseR :
        ((Nat.choose (cols j) i.val : ℕ) : ℝ) * (i.val.factorial : ℝ) *
          ((cols j - i.val).factorial : ℝ) = ((cols j).factorial : ℝ) := by
      exact_mod_cast hchoose
    have hfac : ((cols j).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith [hchooseR]
  · have hneg : (cols j : ℤ) - (i.val : ℤ) < 0 := by omega
    rw [factorialKernelCoefficient_eq_zero_of_neg hneg]
    have hchoose : Nat.choose (cols j) i.val = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hchoose]
    norm_num

/-- Every reciprocal-factorial minor on the first `r` rows is strictly positive. Componentwise
admissibility is automatic for an increasing embedding `Fin r ↪o ℕ`. -/
theorem factorialKernelMinor_firstRows_pos {r : ℕ} (cols : Fin r ↪o ℕ) :
    0 < factorialKernelMinor (firstNaturalRows r) cols := by
  rw [factorialKernelMinor, oneSidedToeplitzMinor,
    firstRows_factorialKernelMatrix_eq_diagonal_mul_pascal_mul_diagonal cols,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  have hrow : 0 < ∏ i : Fin r, ((i : ℕ).factorial : ℝ) := by
    apply Finset.prod_pos
    intro i hi
    positivity
  have hcol : 0 < ∏ j : Fin r, ((cols j).factorial : ℝ)⁻¹ := by
    apply Finset.prod_pos
    intro j hj
    positivity
  exact mul_pos (mul_pos hrow (pascalEvaluationMatrix_det_pos cols)) hcol

/-- Hence every componentwise-allowed exponential minor on the first row block is strictly
positive for `gamma > 0`. -/
theorem exponentialToeplitzMinor_firstRows_pos {r : ℕ} {gamma : ℝ} (hgamma : 0 < gamma)
    (cols : Fin r ↪o ℕ) :
    0 < exponentialToeplitzMinor gamma (firstNaturalRows r) cols :=
  (exponentialToeplitzMinor_pos_iff_factorialKernelMinor_pos hgamma _ _).2
    (factorialKernelMinor_firstRows_pos cols)

/-- A consecutive block of `r` natural row indices beginning at `offset`. -/
def consecutiveNaturalRows (offset r : ℕ) : Fin r ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun i : Fin r ↦ offset + i.val) (by
    intro i j hij
    exact Nat.add_lt_add_left hij offset)

/-- Subtract a common lower bound from an increasing natural tuple. -/
def subtractFromOrderEmbedding {r : ℕ} (cols : Fin r ↪o ℕ) (offset : ℕ)
    (hoffset : ∀ j, offset ≤ cols j) : Fin r ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun j ↦ cols j - offset) (by
    intro i j hij
    exact Nat.sub_lt_sub_right (hoffset i) (cols.strictMono hij))

/-- Translating a consecutive row block and its allowed columns reduces it to the first-row
block. -/
theorem factorialKernelMinor_consecutiveRows_eq_firstRows {r offset : ℕ}
    (cols : Fin r ↪o ℕ) (hallowed : ∀ i, offset + i.val ≤ cols i) :
    factorialKernelMinor (consecutiveNaturalRows offset r) cols =
      factorialKernelMinor (firstNaturalRows r)
        (subtractFromOrderEmbedding cols offset (fun j ↦ (Nat.le_add_right offset j.val).trans
          (hallowed j))) := by
  unfold factorialKernelMinor oneSidedToeplitzMinor
  congr 1
  ext i j
  simp only [oneSidedToeplitzMinorMatrix_apply, consecutiveNaturalRows,
    subtractFromOrderEmbedding, firstNaturalRows, Fin.valOrderEmb_apply,
    OrderEmbedding.coe_ofStrictMono]
  apply congrArg factorialKernelCoefficient
  have hjoff : offset ≤ cols j :=
    (Nat.le_add_right offset j.val).trans (hallowed j)
  have hcast : ((cols j - offset : ℕ) : ℤ) = (cols j : ℤ) - offset := by
    omega
  rw [hcast]
  push_cast
  ring

/-- Every componentwise-allowed reciprocal-factorial minor on consecutive rows is strictly
positive. -/
theorem factorialKernelMinor_consecutiveRows_pos {r offset : ℕ}
    (cols : Fin r ↪o ℕ) (hallowed : ∀ i, offset + i.val ≤ cols i) :
    0 < factorialKernelMinor (consecutiveNaturalRows offset r) cols := by
  rw [factorialKernelMinor_consecutiveRows_eq_firstRows cols hallowed]
  exact factorialKernelMinor_firstRows_pos _

/-- Every componentwise-allowed exponential minor on consecutive rows is strictly positive. -/
theorem exponentialToeplitzMinor_consecutiveRows_pos {r offset : ℕ} {gamma : ℝ}
    (hgamma : 0 < gamma) (cols : Fin r ↪o ℕ)
    (hallowed : ∀ i, offset + i.val ≤ cols i) :
    0 < exponentialToeplitzMinor gamma (consecutiveNaturalRows offset r) cols :=
  (exponentialToeplitzMinor_pos_iff_factorialKernelMinor_pos hgamma _ _).2
    (factorialKernelMinor_consecutiveRows_pos cols hallowed)

end

end ToeplitzPositroids
