import ToeplitzPositroids.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A corner-minor obstruction

This file formalizes Proposition 2 of *Toeplitz Positroids in Ranks Two and Three*.
The symmetric Toeplitz matrix considered there has positive entries and positive
corner minors, but a negative leading principal minor of order two.
-/

namespace ToeplitzPositroids

open Matrix

/-- The `3 × 3` symmetric Toeplitz matrix used in the corner obstruction. -/
def cornerObstructionMatrix (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, a, b; a, 1, a; b, a, 1]

/-- The upper-right corner submatrix of order two. -/
def cornerObstructionUpperRight (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (cornerObstructionMatrix a b).submatrix Fin.castSucc Fin.succ

/-- The lower-left corner submatrix of order two. -/
def cornerObstructionLowerLeft (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (cornerObstructionMatrix a b).submatrix Fin.succ Fin.castSucc

/-- The leading principal submatrix of order two. -/
def cornerObstructionLeadingPrincipal (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (cornerObstructionMatrix a b).submatrix Fin.castSucc Fin.castSucc

/-- The upper-right corner has the explicit form displayed in the paper. -/
@[simp]
theorem cornerObstructionUpperRight_eq (a b : ℝ) :
    cornerObstructionUpperRight a b = !![a, b; 1, a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The lower-left corner is the transpose of the displayed upper-right corner. -/
@[simp]
theorem cornerObstructionLowerLeft_eq (a b : ℝ) :
    cornerObstructionLowerLeft a b = !![a, 1; b, a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The leading principal submatrix has diagonal entries one and off-diagonal entries `a`. -/
@[simp]
theorem cornerObstructionLeadingPrincipal_eq (a b : ℝ) :
    cornerObstructionLeadingPrincipal a b = !![1, a; a, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Every entry of the obstruction matrix is positive under the paper's hypotheses. -/
theorem cornerObstructionMatrix_entry_pos {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (i j : Fin 3) : 0 < cornerObstructionMatrix a b i j := by
  fin_cases i <;> fin_cases j <;> simp [cornerObstructionMatrix] <;> linarith

/-- The two corner entries, which are the corner minors of order one, equal `b`. -/
theorem cornerObstructionMatrix_orderOneCorners (a b : ℝ) :
    cornerObstructionMatrix a b 0 2 = b ∧ cornerObstructionMatrix a b 2 0 = b := by
  simp [cornerObstructionMatrix]

/-- The upper-right corner determinant is `a² - b`. -/
theorem cornerObstructionUpperRight_det (a b : ℝ) :
    (cornerObstructionUpperRight a b).det = a ^ 2 - b := by
  rw [cornerObstructionUpperRight_eq]
  simp
  ring

/-- The lower-left corner determinant is `a² - b`. -/
theorem cornerObstructionLowerLeft_det (a b : ℝ) :
    (cornerObstructionLowerLeft a b).det = a ^ 2 - b := by
  rw [cornerObstructionLowerLeft_eq]
  simp
  ring

/-- The full determinant has the factorization stated in Proposition 2. -/
theorem cornerObstructionMatrix_det (a b : ℝ) :
    (cornerObstructionMatrix a b).det = (b - 1) * (2 * a ^ 2 - b - 1) := by
  rw [Matrix.det_fin_three]
  simp [cornerObstructionMatrix]
  ring

/-- The leading principal determinant is `1 - a²`. -/
theorem cornerObstructionLeadingPrincipal_det (a b : ℝ) :
    (cornerObstructionLeadingPrincipal a b).det = 1 - a ^ 2 := by
  rw [cornerObstructionLeadingPrincipal_eq]
  simp
  ring

/-- Both corner minors of order two are positive under `b < a²`. -/
theorem cornerObstruction_orderTwoCorners_pos {a b : ℝ} (hb : b < a ^ 2) :
    0 < (cornerObstructionUpperRight a b).det ∧
      0 < (cornerObstructionLowerLeft a b).det := by
  rw [cornerObstructionUpperRight_det, cornerObstructionLowerLeft_det]
  constructor <;> linarith

/-- The full determinant is positive under the hypotheses of Proposition 2. -/
theorem cornerObstructionMatrix_det_pos {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hab : b < a ^ 2) : 0 < (cornerObstructionMatrix a b).det := by
  rw [cornerObstructionMatrix_det]
  have hfirst : 0 < b - 1 := by linarith
  have hsquare : 1 < a ^ 2 := by nlinarith only [ha]
  have hsecond : 0 < 2 * a ^ 2 - b - 1 := by linarith only [hab, hsquare]
  exact mul_pos hfirst hsecond

/-- Every corner minor (of orders one, two, and three) is positive. -/
theorem cornerObstruction_cornerMinors_pos {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hab : b < a ^ 2) :
    (0 < cornerObstructionMatrix a b 0 2 ∧ 0 < cornerObstructionMatrix a b 2 0) ∧
      (0 < (cornerObstructionUpperRight a b).det ∧
        0 < (cornerObstructionLowerLeft a b).det) ∧
      0 < (cornerObstructionMatrix a b).det := by
  refine ⟨?_, cornerObstruction_orderTwoCorners_pos hab, ?_⟩
  · constructor <;> simp [cornerObstructionMatrix] <;> linarith
  · exact cornerObstructionMatrix_det_pos ha hb hab

/-- The leading principal minor of order two is negative when `1 < a`. -/
theorem cornerObstructionLeadingPrincipal_det_neg {a b : ℝ} (ha : 1 < a) :
    (cornerObstructionLeadingPrincipal a b).det < 0 := by
  rw [cornerObstructionLeadingPrincipal_det]
  nlinarith

/-- The leading principal determinant expressed through the shared ordered-minor API. -/
theorem cornerObstruction_leadingPrincipal_orderedMinor (a b : ℝ) :
    orderedMinor (cornerObstructionMatrix a b) Fin.castSuccOrderEmb
      Fin.castSuccOrderEmb = 1 - a ^ 2 := by
  change (cornerObstructionLeadingPrincipal a b).det = 1 - a ^ 2
  exact cornerObstructionLeadingPrincipal_det a b

/-- The obstruction matrix is not totally nonnegative when `1 < a`. -/
theorem cornerObstructionMatrix_not_totallyNonnegative {a b : ℝ} (ha : 1 < a) :
    ¬ TotallyNonnegative (cornerObstructionMatrix a b) := by
  intro htnn
  have hnonneg :
      0 ≤ orderedMinor (cornerObstructionMatrix a b) Fin.castSuccOrderEmb
        Fin.castSuccOrderEmb :=
    htnn.orderedMinor_nonneg Fin.castSuccOrderEmb Fin.castSuccOrderEmb
  rw [cornerObstruction_leadingPrincipal_orderedMinor] at hnonneg
  nlinarith

/-- Proposition 2: positive entries and corner minors do not imply total nonnegativity. -/
theorem cornerObstruction {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (hab : b < a ^ 2) :
    (∀ i j, 0 < cornerObstructionMatrix a b i j) ∧
      ((0 < cornerObstructionMatrix a b 0 2 ∧
          0 < cornerObstructionMatrix a b 2 0) ∧
        (0 < (cornerObstructionUpperRight a b).det ∧
          0 < (cornerObstructionLowerLeft a b).det) ∧
        0 < (cornerObstructionMatrix a b).det) ∧
      ¬ TotallyNonnegative (cornerObstructionMatrix a b) := by
  exact ⟨cornerObstructionMatrix_entry_pos ha hb,
    cornerObstruction_cornerMinors_pos ha hb hab,
    cornerObstructionMatrix_not_totallyNonnegative ha⟩

/-- The small integral instance highlighted immediately after Proposition 2. -/
def cornerObstructionExample : Matrix (Fin 3) (Fin 3) ℝ :=
  cornerObstructionMatrix 2 2

/-- The numerical obstruction matrix written out entry by entry. -/
@[simp]
theorem cornerObstructionExample_eq :
    cornerObstructionExample = !![1, 2, 2; 2, 1, 2; 2, 2, 1] := by
  rfl

/-- Every entry of the numerical example is positive. -/
theorem cornerObstructionExample_entry_pos (i j : Fin 3) :
    0 < cornerObstructionExample i j := by
  exact cornerObstructionMatrix_entry_pos (by norm_num) (by norm_num) i j

/-- Every corner minor of the numerical example is positive. -/
theorem cornerObstructionExample_cornerMinors_pos :
    (0 < cornerObstructionExample 0 2 ∧ 0 < cornerObstructionExample 2 0) ∧
      (0 < (cornerObstructionUpperRight 2 2).det ∧
        0 < (cornerObstructionLowerLeft 2 2).det) ∧
      0 < cornerObstructionExample.det := by
  exact cornerObstruction_cornerMinors_pos (by norm_num) (by norm_num) (by norm_num)

/-- The numerical example has a negative leading principal minor of order two. -/
theorem cornerObstructionExample_leadingPrincipal_det_neg :
    (cornerObstructionLeadingPrincipal 2 2).det < 0 := by
  exact cornerObstructionLeadingPrincipal_det_neg (by norm_num)

/-- The four relevant determinants of the numerical example have small integral values. -/
theorem cornerObstructionExample_determinants :
    (cornerObstructionUpperRight 2 2).det = 2 ∧
      (cornerObstructionLowerLeft 2 2).det = 2 ∧
      cornerObstructionExample.det = 5 ∧
      (cornerObstructionLeadingPrincipal 2 2).det = -3 := by
  constructor
  · norm_num [cornerObstructionUpperRight_det]
  constructor
  · norm_num [cornerObstructionLowerLeft_det]
  constructor
  · norm_num [cornerObstructionExample, cornerObstructionMatrix_det]
  · norm_num [cornerObstructionLeadingPrincipal_det]

/-- The numerical example is not totally nonnegative. -/
theorem cornerObstructionExample_not_totallyNonnegative :
    ¬ TotallyNonnegative cornerObstructionExample := by
  exact cornerObstructionMatrix_not_totallyNonnegative (by norm_num)

/-- The full assertion of Proposition 2 for the numerical instance `(a, b) = (2, 2)`. -/
theorem cornerObstructionExample_spec :
    (∀ i j, 0 < cornerObstructionExample i j) ∧
      ((0 < cornerObstructionExample 0 2 ∧ 0 < cornerObstructionExample 2 0) ∧
        (0 < (cornerObstructionUpperRight 2 2).det ∧
          0 < (cornerObstructionLowerLeft 2 2).det) ∧
        0 < cornerObstructionExample.det) ∧
      ¬ TotallyNonnegative cornerObstructionExample := by
  exact cornerObstruction (by norm_num) (by norm_num) (by norm_num)

end ToeplitzPositroids
