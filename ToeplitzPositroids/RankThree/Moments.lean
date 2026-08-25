import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pascal moments for three-dimensional nonnegative columns

This file formalizes the Pascal moment coordinates used for rank-three Toeplitz
matrices.  The main result is the summand-separation identity: the change of the
first moment is a positive linear combination of the three coordinate minors.
-/

namespace ToeplitzPositroids.RankThree

noncomputable section

/-- A rank-three column, indexed from top to bottom by `0`, `1`, and `2`. -/
abbrev Column := Fin 3 → ℝ

/-- A column is coordinatewise nonnegative. -/
def Nonnegative (c : Column) : Prop :=
  ∀ i, 0 ≤ c i

/-- The sum of the coordinates of a rank-three column. -/
def momentSum (c : Column) : ℝ :=
  c 0 + c 1 + c 2

/-- The first Pascal moment of a nonzero column. -/
def momentU (c : Column) : ℝ :=
  (c 1 + 2 * c 2) / momentSum c

/-- The second Pascal moment of a nonzero column. -/
def momentV (c : Column) : ℝ :=
  c 2 / momentSum c

/-- The coordinate minor on rows zero and one of the two columns `c` and `d`. -/
def coordinateMinor12 (c d : Column) : ℝ :=
  c 0 * d 1 - c 1 * d 0

/-- The coordinate minor on rows zero and two of the two columns `c` and `d`. -/
def coordinateMinor13 (c d : Column) : ℝ :=
  c 0 * d 2 - c 2 * d 0

/-- The coordinate minor on rows one and two of the two columns `c` and `d`. -/
def coordinateMinor23 (c d : Column) : ℝ :=
  c 1 * d 2 - c 2 * d 1

/-- Two columns are positively parallel if the second is a positive scalar multiple of the
first. -/
def PositivelyParallel (c d : Column) : Prop :=
  ∃ a : ℝ, 0 < a ∧ d = a • c

/-- A nonnegative nonzero column has strictly positive coordinate sum. -/
theorem momentSum_pos {c : Column} (hc : Nonnegative c) (hc0 : c ≠ 0) :
    0 < momentSum c := by
  have h0 : 0 ≤ c 0 := hc 0
  have h1 : 0 ≤ c 1 := hc 1
  have h2 : 0 ≤ c 2 := hc 2
  by_contra hs
  have hs' : momentSum c ≤ 0 := le_of_not_gt hs
  have hc0' : c 0 = 0 := by
    simp only [momentSum] at hs'
    linarith
  have hc1' : c 1 = 0 := by
    simp only [momentSum] at hs'
    linarith
  have hc2' : c 2 = 0 := by
    simp only [momentSum] at hs'
    linarith
  apply hc0
  funext i
  fin_cases i <;> simp_all

/-- A nonnegative nonzero column has nonzero coordinate sum. -/
theorem momentSum_ne_zero {c : Column} (hc : Nonnegative c) (hc0 : c ≠ 0) :
    momentSum c ≠ 0 :=
  (momentSum_pos hc hc0).ne'

/-- Scaling a column scales its coordinate sum by the same factor. -/
@[simp]
theorem momentSum_smul (a : ℝ) (c : Column) : momentSum (a • c) = a * momentSum c := by
  simp only [momentSum, Pi.smul_apply, smul_eq_mul]
  ring

/-- The first Pascal moment is invariant under nonzero rescaling. -/
theorem momentU_smul {a : ℝ} (ha : a ≠ 0) {c : Column} (hc : momentSum c ≠ 0) :
    momentU (a • c) = momentU c := by
  rw [momentU, momentU, momentSum_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- The second Pascal moment is invariant under nonzero rescaling. -/
theorem momentV_smul {a : ℝ} (ha : a ≠ 0) {c : Column} (hc : momentSum c ≠ 0) :
    momentV (a • c) = momentV c := by
  rw [momentV, momentV, momentSum_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- The exact separation of the first-moment difference into coordinate minors. -/
theorem momentU_summand_separation {c d : Column} (hc : momentSum c ≠ 0)
    (hd : momentSum d ≠ 0) :
    momentSum c * momentSum d * (momentU d - momentU c) =
      coordinateMinor12 c d + 2 * coordinateMinor13 c d + coordinateMinor23 c d := by
  rw [momentU, momentU]
  field_simp
  simp only [momentSum, coordinateMinor12, coordinateMinor13, coordinateMinor23]
  ring

/-- The summand-separation identity for nonnegative nonzero columns. -/
theorem momentU_summand_separation_of_nonnegative {c d : Column} (hc : Nonnegative c)
    (hc0 : c ≠ 0) (hd : Nonnegative d) (hd0 : d ≠ 0) :
    momentSum c * momentSum d * (momentU d - momentU c) =
      coordinateMinor12 c d + 2 * coordinateMinor13 c d + coordinateMinor23 c d :=
  momentU_summand_separation (momentSum_ne_zero hc hc0) (momentSum_ne_zero hd hd0)

/-- Nonnegative coordinate minors make the first Pascal moment weakly increasing. -/
theorem momentU_le_of_coordinateMinors_nonneg {c d : Column} (hc : Nonnegative c)
    (hc0 : c ≠ 0)
    (hd : Nonnegative d) (hd0 : d ≠ 0) (h12 : 0 ≤ coordinateMinor12 c d)
    (h13 : 0 ≤ coordinateMinor13 c d) (h23 : 0 ≤ coordinateMinor23 c d) :
    momentU c ≤ momentU d := by
  have hsum :
      0 ≤ coordinateMinor12 c d + 2 * coordinateMinor13 c d + coordinateMinor23 c d := by
    positivity
  have hprod : 0 < momentSum c * momentSum d :=
    mul_pos (momentSum_pos hc hc0) (momentSum_pos hd hd0)
  have hmul : 0 ≤ momentSum c * momentSum d * (momentU d - momentU c) := by
    rw [momentU_summand_separation (momentSum_ne_zero hc hc0) (momentSum_ne_zero hd hd0)]
    exact hsum
  have hdiff : 0 ≤ momentU d - momentU c := nonneg_of_mul_nonneg_right hmul hprod
  linarith

/-- Equality of first moments forces each nonnegative coordinate minor to vanish. -/
theorem coordinateMinors_eq_zero_of_momentU_eq {c d : Column} (hc : Nonnegative c)
    (hc0 : c ≠ 0)
    (hd : Nonnegative d) (hd0 : d ≠ 0) (h12 : 0 ≤ coordinateMinor12 c d)
    (h13 : 0 ≤ coordinateMinor13 c d) (h23 : 0 ≤ coordinateMinor23 c d)
    (hu : momentU c = momentU d) :
    coordinateMinor12 c d = 0 ∧ coordinateMinor13 c d = 0 ∧ coordinateMinor23 c d = 0 := by
  have hsum :
      coordinateMinor12 c d + 2 * coordinateMinor13 c d + coordinateMinor23 c d = 0 := by
    rw [← momentU_summand_separation (momentSum_ne_zero hc hc0)
      (momentSum_ne_zero hd hd0), hu]
    ring
  constructor
  · linarith
  constructor <;> linarith

/-- Vanishing of all coordinate minors forces equality of first moments. -/
theorem momentU_eq_of_coordinateMinors_eq_zero {c d : Column} (hc : Nonnegative c)
    (hc0 : c ≠ 0)
    (hd : Nonnegative d) (hd0 : d ≠ 0) (h12 : coordinateMinor12 c d = 0)
    (h13 : coordinateMinor13 c d = 0) (h23 : coordinateMinor23 c d = 0) :
    momentU c = momentU d := by
  have hsep := momentU_summand_separation_of_nonnegative hc hc0 hd hd0
  rw [h12, h13, h23] at hsep
  have hprod : momentSum c * momentSum d ≠ 0 :=
    mul_ne_zero (momentSum_ne_zero hc hc0) (momentSum_ne_zero hd hd0)
  have hdiff : momentU d - momentU c = 0 :=
    (mul_eq_zero.mp (by simpa using hsep)).resolve_left hprod
  exact (sub_eq_zero.mp hdiff).symm

/-- Under nonnegativity of the coordinate minors, equality of first moments is equivalent to
the simultaneous vanishing of all three minors. -/
theorem momentU_eq_iff_coordinateMinors_eq_zero {c d : Column} (hc : Nonnegative c)
    (hc0 : c ≠ 0)
    (hd : Nonnegative d) (hd0 : d ≠ 0) (h12 : 0 ≤ coordinateMinor12 c d)
    (h13 : 0 ≤ coordinateMinor13 c d) (h23 : 0 ≤ coordinateMinor23 c d) :
    momentU c = momentU d ↔
      coordinateMinor12 c d = 0 ∧ coordinateMinor13 c d = 0 ∧ coordinateMinor23 c d = 0 := by
  constructor
  · exact coordinateMinors_eq_zero_of_momentU_eq hc hc0 hd hd0 h12 h13 h23
  · rintro ⟨h12', h13', h23'⟩
    exact momentU_eq_of_coordinateMinors_eq_zero hc hc0 hd hd0 h12' h13' h23'

/-- Positive parallelism makes all three coordinate minors vanish. -/
theorem coordinateMinors_eq_zero_of_positivelyParallel {c d : Column}
    (hcd : PositivelyParallel c d) :
    coordinateMinor12 c d = 0 ∧ coordinateMinor13 c d = 0 ∧
      coordinateMinor23 c d = 0 := by
  rcases hcd with ⟨a, _, rfl⟩
  simp only [coordinateMinor12, coordinateMinor13, coordinateMinor23, Pi.smul_apply,
    smul_eq_mul]
  constructor
  · ring
  constructor <;> ring

/-- Positively parallel columns have the same two Pascal moments. -/
theorem moments_eq_of_positivelyParallel {c d : Column} (hc : momentSum c ≠ 0)
    (hcd : PositivelyParallel c d) :
    momentU c = momentU d ∧ momentV c = momentV d := by
  rcases hcd with ⟨a, ha, rfl⟩
  constructor
  · exact (momentU_smul ha.ne' hc).symm
  · exact (momentV_smul ha.ne' hc).symm

/-- For nonnegative nonzero columns, simultaneous vanishing of the coordinate minors gives a
positive scalar multiple. -/
theorem positivelyParallel_of_coordinateMinors_eq_zero {c d : Column} (hc : Nonnegative c)
    (hc0 : c ≠ 0) (hd : Nonnegative d) (hd0 : d ≠ 0)
    (h12 : coordinateMinor12 c d = 0) (h13 : coordinateMinor13 c d = 0)
    (h23 : coordinateMinor23 c d = 0) :
    PositivelyParallel c d := by
  have hcoord0 : momentSum c * d 0 = momentSum d * c 0 := by
    simp only [momentSum, coordinateMinor12, coordinateMinor13] at h12 h13 ⊢
    nlinarith
  have hcoord1 : momentSum c * d 1 = momentSum d * c 1 := by
    simp only [momentSum, coordinateMinor12, coordinateMinor23] at h12 h23 ⊢
    nlinarith
  have hcoord2 : momentSum c * d 2 = momentSum d * c 2 := by
    simp only [momentSum, coordinateMinor13, coordinateMinor23] at h13 h23 ⊢
    nlinarith
  refine ⟨momentSum d / momentSum c, div_pos (momentSum_pos hd hd0) (momentSum_pos hc hc0), ?_⟩
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
  apply (eq_div_iff (momentSum_ne_zero hc hc0)).2
  fin_cases i
  · simpa [mul_comm] using hcoord0
  · simpa [mul_comm] using hcoord1
  · simpa [mul_comm] using hcoord2

/-- For nonnegative nonzero columns, positive parallelism is exactly simultaneous vanishing of
the three coordinate minors. -/
theorem positivelyParallel_iff_coordinateMinors_eq_zero {c d : Column} (hc : Nonnegative c)
    (hc0 : c ≠ 0) (hd : Nonnegative d) (hd0 : d ≠ 0) :
    PositivelyParallel c d ↔
      coordinateMinor12 c d = 0 ∧ coordinateMinor13 c d = 0 ∧
        coordinateMinor23 c d = 0 := by
  constructor
  · exact coordinateMinors_eq_zero_of_positivelyParallel
  · rintro ⟨h12, h13, h23⟩
    exact positivelyParallel_of_coordinateMinors_eq_zero hc hc0 hd hd0 h12 h13 h23

/-- Under nonnegative coordinate minors, equality of the first Pascal moments is exactly
positive parallelism. -/
theorem momentU_eq_iff_positivelyParallel {c d : Column} (hc : Nonnegative c) (hc0 : c ≠ 0)
    (hd : Nonnegative d) (hd0 : d ≠ 0) (h12 : 0 ≤ coordinateMinor12 c d)
    (h13 : 0 ≤ coordinateMinor13 c d) (h23 : 0 ≤ coordinateMinor23 c d) :
    momentU c = momentU d ↔ PositivelyParallel c d := by
  rw [momentU_eq_iff_coordinateMinors_eq_zero hc hc0 hd hd0 h12 h13 h23,
    ← positivelyParallel_iff_coordinateMinors_eq_zero hc hc0 hd hd0]

/-- If the columns are not positively parallel, nonnegative coordinate minors make the first
Pascal moment strictly increase. -/
theorem momentU_lt_of_coordinateMinors_nonneg_of_not_positivelyParallel {c d : Column}
    (hc : Nonnegative c) (hc0 : c ≠ 0) (hd : Nonnegative d) (hd0 : d ≠ 0)
    (h12 : 0 ≤ coordinateMinor12 c d) (h13 : 0 ≤ coordinateMinor13 c d)
    (h23 : 0 ≤ coordinateMinor23 c d) (hcd : ¬PositivelyParallel c d) :
    momentU c < momentU d := by
  apply lt_of_le_of_ne (momentU_le_of_coordinateMinors_nonneg hc hc0 hd hd0 h12 h13 h23)
  intro hu
  exact hcd ((momentU_eq_iff_positivelyParallel hc hc0 hd hd0 h12 h13 h23).mp hu)

end

end ToeplitzPositroids.RankThree
