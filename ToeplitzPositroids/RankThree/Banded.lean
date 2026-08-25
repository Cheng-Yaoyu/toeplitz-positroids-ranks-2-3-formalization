import ToeplitzPositroids.RankThree.ConvexMatrix
import ToeplitzPositroids.RankThree.OrderTwo
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Banded three-row Toeplitz matrices

This file develops the banded matrix `C(b)` from Section 9.  Its coefficient
vector `b_0, ..., b_d` is extended by zero outside `0, ..., d`.  We define the
consecutive determinants `D_t`, compute their endpoint values and five-term
polynomial expansion, and connect them exactly to consecutive Pascal-moment
slope differences.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

variable {d : ℕ}

/-- Extend `b_0, ..., b_d` by zero to every integer coefficient index. -/
def bandCoefficient (b : Fin (d + 1) → ℝ) (k : ℤ) : ℝ :=
  if h : 0 ≤ k ∧ k ≤ d then b ⟨k.toNat, by omega⟩ else 0

@[simp]
theorem bandCoefficient_apply_fin (b : Fin (d + 1) → ℝ) (k : Fin (d + 1)) :
    bandCoefficient b k = b k := by
  have hk : (0 : ℤ) ≤ k ∧ (k : ℤ) ≤ d := by omega
  simp only [bandCoefficient, dif_pos hk]
  congr 1

@[simp]
theorem bandCoefficient_zero (b : Fin (d + 1) → ℝ) : bandCoefficient b 0 = b 0 := by
  simpa using bandCoefficient_apply_fin b (0 : Fin (d + 1))

theorem bandCoefficient_eq_zero_of_neg (b : Fin (d + 1) → ℝ) {k : ℤ} (hk : k < 0) :
    bandCoefficient b k = 0 := by
  simp [bandCoefficient, not_le.mpr hk]

theorem bandCoefficient_eq_zero_of_lt (b : Fin (d + 1) → ℝ) {k : ℤ} (hk : d < k) :
    bandCoefficient b k = 0 := by
  simp [bandCoefficient, not_le.mpr hk]

@[simp]
theorem bandCoefficient_neg_one (b : Fin (d + 1) → ℝ) : bandCoefficient b (-1) = 0 := by
  exact bandCoefficient_eq_zero_of_neg b (by omega)

@[simp]
theorem bandCoefficient_neg_two (b : Fin (d + 1) → ℝ) : bandCoefficient b (-2) = 0 := by
  exact bandCoefficient_eq_zero_of_neg b (by omega)

@[simp]
theorem bandCoefficient_succ_last (b : Fin (d + 1) → ℝ) :
    bandCoefficient b (d + 1) = 0 := by
  exact bandCoefficient_eq_zero_of_lt b (by omega)

@[simp]
theorem bandCoefficient_succ_succ_last (b : Fin (d + 1) → ℝ) :
    bandCoefficient b (d + 2) = 0 := by
  exact bandCoefficient_eq_zero_of_lt b (by omega)

/-- Every displayed band coefficient is positive. -/
def PositiveBandCoefficients (b : Fin (d + 1) → ℝ) : Prop :=
  ∀ t, 0 < b t

/-- Strict log-concavity with the zero boundary convention of Section 9. -/
def StrictlyLogConcaveWithZeroBoundary (b : Fin (d + 1) → ℝ) : Prop :=
  PositiveBandCoefficients b ∧
    ∀ t : Fin (d + 1),
      bandCoefficient b (t - 1) * bandCoefficient b (t + 1) < b t ^ 2

/-- The zero-extended coefficient is nonnegative when all displayed coefficients
are nonnegative. -/
theorem bandCoefficient_nonneg {b : Fin (d + 1) → ℝ} (hb : ∀ t, 0 ≤ b t) (k : ℤ) :
    0 ≤ bandCoefficient b k := by
  rw [bandCoefficient]
  split_ifs
  · exact hb _
  · exact le_rfl

/-- Under positivity of `b`, the zero extension is positive exactly on `0, ..., d`. -/
theorem bandCoefficient_pos_iff {b : Fin (d + 1) → ℝ} (hb : PositiveBandCoefficients b)
    (k : ℤ) :
    0 < bandCoefficient b k ↔ 0 ≤ k ∧ k ≤ d := by
  rw [bandCoefficient]
  split_ifs with hk
  · exact iff_of_true (hb _) hk
  · simp only [lt_self_iff_false, false_iff]
    exact hk

/-- The finite coefficient vector for `C(b)`, ordered from integer label `-2`
through label `d+2`. -/
def bandCoefficientVector (b : Fin (d + 1) → ℝ) : Fin (d + 5) → ℝ :=
  fun k ↦ bandCoefficient b (k - 2)

@[simp]
theorem bandCoefficientVector_left (b : Fin (d + 1) → ℝ) (k : Fin (d + 3)) :
    bandCoefficientVector b k.castSucc.castSucc = bandCoefficient b (k - 2) := by
  unfold bandCoefficientVector
  congr 1

@[simp]
theorem bandCoefficientVector_center (b : Fin (d + 1) → ℝ) (k : Fin (d + 3)) :
    bandCoefficientVector b k.succ.castSucc = bandCoefficient b (k - 1) := by
  unfold bandCoefficientVector
  congr 1
  simp only [Fin.val_succ, Fin.val_castSucc]
  omega

@[simp]
theorem bandCoefficientVector_right (b : Fin (d + 1) → ℝ) (k : Fin (d + 3)) :
    bandCoefficientVector b k.succ.succ = bandCoefficient b k := by
  unfold bandCoefficientVector
  congr 1
  simp only [Fin.val_succ]
  omega

/-- The `3 × (d+3)` banded Toeplitz matrix `C(b)` from Section 9. -/
def bandedMatrix (b : Fin (d + 1) → ℝ) : Matrix (Fin 3) (Fin (d + 3)) ℝ :=
  toeplitzMatrix 3 (d + 3) (bandCoefficient b)

@[simp]
theorem bandedMatrix_apply (b : Fin (d + 1) → ℝ) (i : Fin 3) (j : Fin (d + 3)) :
    bandedMatrix b i j = bandCoefficient b (j - i) :=
  rfl

/-- The exact coefficient formula for a column of `C(b)`. -/
theorem bandedMatrix_column (b : Fin (d + 1) → ℝ) (j : Fin (d + 3)) :
    (bandedMatrix b).col j =
      ![bandCoefficient b j, bandCoefficient b (j - 1), bandCoefficient b (j - 2)] := by
  funext i
  fin_cases i <;> rfl

/-- The integer-indexed and padded finite constructions of `C(b)` agree. -/
theorem bandedMatrix_eq_rankThreeToeplitz (b : Fin (d + 1) → ℝ) :
    bandedMatrix b = rankThreeToeplitz (bandCoefficientVector b) := by
  ext i j
  rw [bandedMatrix_apply, rankThreeToeplitz_apply]
  unfold bandCoefficientVector
  congr 1
  change (j.val : ℤ) - i.val = ((j.val + (2 - i.val) : ℕ) : ℤ) - 2
  omega

/-- The padded coefficient vector is nonnegative when `b` is positive. -/
theorem bandCoefficientVector_nonneg {b : Fin (d + 1) → ℝ}
    (hb : PositiveBandCoefficients b) (k : Fin (d + 5)) :
    0 ≤ bandCoefficientVector b k :=
  bandCoefficient_nonneg (fun t ↦ (hb t).le) _

/-- Positivity of `b` makes the positive support of the padded coefficient vector
the interval of positions `2, ..., d+2`. -/
theorem bandCoefficientVector_hasIntervalPositiveSupport {b : Fin (d + 1) → ℝ}
    (hb : PositiveBandCoefficients b) :
    HasIntervalPositiveSupport (bandCoefficientVector b) := by
  rw [hasIntervalPositiveSupport_iff]
  intro i j k hi hj hik hkj
  change 0 < bandCoefficient b (i - 2) at hi
  change 0 < bandCoefficient b (j - 2) at hj
  change 0 < bandCoefficient b (k - 2)
  rw [bandCoefficient_pos_iff hb] at hi hj ⊢
  constructor <;> omega

/-- Strict log-concavity with zero boundary implies weak discrete log-concavity
of the padded coefficient vector. -/
theorem bandCoefficientVector_discretelyLogConcave {b : Fin (d + 1) → ℝ}
    (hb : StrictlyLogConcaveWithZeroBoundary b) :
    DiscretelyLogConcave (n := d + 3) (bandCoefficientVector b) := by
  intro k
  rw [bandCoefficientVector_left, bandCoefficientVector_center,
    bandCoefficientVector_right]
  by_cases hk : (0 : ℤ) ≤ (k : ℤ) - 1 ∧ (k : ℤ) - 1 ≤ d
  · let t : Fin (d + 1) := ⟨((k : ℤ) - 1).toNat, by omega⟩
    have ht : (t : ℤ) = (k : ℤ) - 1 := by
      simp only [t]
      rw [Int.toNat_of_nonneg hk.1]
    have hleft : (k : ℤ) - 2 = (t : ℤ) - 1 := by omega
    have hright : (k : ℤ) = (t : ℤ) + 1 := by omega
    calc
      bandCoefficient b (k - 2) * bandCoefficient b k =
          bandCoefficient b (t - 1) * bandCoefficient b (t + 1) := by
            rw [hleft, hright]
      _ ≤ b t ^ 2 := (hb.2 t).le
      _ = bandCoefficient b (k - 1) * bandCoefficient b (k - 1) := by
        rw [pow_two]
        have hcenter : bandCoefficient b (k - 1) = b t := by
          rw [← ht]
          exact bandCoefficient_apply_fin b t
        rw [hcenter]
  · have hkcase : k.val = 0 ∨ k.val = d + 2 := by omega
    rcases hkcase with hkzero | hklast
    · have : k = 0 := Fin.ext hkzero
      subst k
      change bandCoefficient b (-1) * bandCoefficient b (-1) ≥
        bandCoefficient b (-2) * bandCoefficient b 0
      simp
    · have hkm1 : (k : ℤ) - 1 = d + 1 := by omega
      have hkm2 : (k : ℤ) - 2 = d := by omega
      have hkval : (k : ℤ) = d + 2 := by omega
      rw [hkm1, hkm2, hkval]
      simp

/-- Positive strict log-concavity with zero boundary makes `C(b)` totally
nonnegative through order two. -/
theorem bandedMatrix_tnUpTo_two_of_strictLogConcave
    {b : Fin (d + 1) → ℝ} (hb : StrictlyLogConcaveWithZeroBoundary b) :
    TNUpTo (bandedMatrix b) 2 := by
  rw [bandedMatrix_eq_rankThreeToeplitz,
    rankThreeToeplitz_tnUpTo_two_iff (n := d + 3) (by omega)]
  exact ⟨bandCoefficientVector_nonneg hb.1,
    bandCoefficientVector_hasIntervalPositiveSupport hb.1,
    bandCoefficientVector_discretelyLogConcave hb⟩

/-- The column index `t + s`, for `0 ≤ t ≤ d` and `s ∈ {0,1,2}`. -/
def consecutiveColumnIndex (t : Fin (d + 1)) (s : Fin 3) : Fin (d + 3) :=
  ⟨t + s, by omega⟩

@[simp]
theorem consecutiveColumnIndex_val (t : Fin (d + 1)) (s : Fin 3) :
    (consecutiveColumnIndex t s : ℕ) = t + s :=
  rfl

/-- The consecutive maximal minor `D_t(b)`. -/
def consecutiveDeterminant (b : Fin (d + 1) → ℝ) (t : Fin (d + 1)) : ℝ :=
  (threeColumnMatrix
    ((bandedMatrix b).col (consecutiveColumnIndex t 0))
    ((bandedMatrix b).col (consecutiveColumnIndex t 1))
    ((bandedMatrix b).col (consecutiveColumnIndex t 2))).det

/-- The determinant defining `D_t` has the coefficient layout displayed in Section 9. -/
theorem consecutiveDeterminant_eq_det (b : Fin (d + 1) → ℝ) (t : Fin (d + 1)) :
    consecutiveDeterminant b t =
      (!![bandCoefficient b t, bandCoefficient b (t + 1), bandCoefficient b (t + 2);
          bandCoefficient b (t - 1), bandCoefficient b t, bandCoefficient b (t + 1);
          bandCoefficient b (t - 2), bandCoefficient b (t - 1),
            bandCoefficient b t] : Matrix (Fin 3) (Fin 3) ℝ).det := by
  apply congrArg Matrix.det
  ext i j
  fin_cases i <;> fin_cases j <;>
    change bandCoefficient b _ = bandCoefficient b _ <;> congr 1 <;>
      simp only [consecutiveColumnIndex_val] <;> omega

/-- The determinant expansion underlying the five-term formula. -/
theorem det_three_by_three_toeplitz (am2 am1 a0 a1 a2 : ℝ) :
    (!![a0, a1, a2; am1, a0, a1; am2, am1, a0] :
      Matrix (Fin 3) (Fin 3) ℝ).det =
      a0 ^ 3 - 2 * am1 * a0 * a1 + am2 * a1 ^ 2 +
        am1 ^ 2 * a2 - am2 * a0 * a2 := by
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]
  ring

/-- The five-term polynomial expansion of a consecutive determinant. -/
theorem consecutiveDeterminant_polynomial (b : Fin (d + 1) → ℝ) (t : Fin (d + 1)) :
    consecutiveDeterminant b t =
      bandCoefficient b t ^ 3 -
        2 * bandCoefficient b (t - 1) * bandCoefficient b t * bandCoefficient b (t + 1) +
        bandCoefficient b (t - 2) * bandCoefficient b (t + 1) ^ 2 +
        bandCoefficient b (t - 1) ^ 2 * bandCoefficient b (t + 2) -
        bandCoefficient b (t - 2) * bandCoefficient b t * bandCoefficient b (t + 2) := by
  rw [consecutiveDeterminant_eq_det]
  exact det_three_by_three_toeplitz _ _ _ _ _

/-- The first consecutive determinant is `b_0^3`. -/
@[simp]
theorem consecutiveDeterminant_zero (b : Fin (d + 1) → ℝ) :
    consecutiveDeterminant b 0 = b 0 ^ 3 := by
  rw [consecutiveDeterminant_polynomial]
  change bandCoefficient b 0 ^ 3 -
      2 * bandCoefficient b (-1) * bandCoefficient b 0 * bandCoefficient b 1 +
      bandCoefficient b (-2) * bandCoefficient b 1 ^ 2 +
      bandCoefficient b (-1) ^ 2 * bandCoefficient b 2 -
      bandCoefficient b (-2) * bandCoefficient b 0 * bandCoefficient b 2 = b 0 ^ 3
  rw [bandCoefficient_zero, bandCoefficient_neg_one, bandCoefficient_neg_two]
  ring

/-- The last consecutive determinant is `b_d^3`. -/
@[simp]
theorem consecutiveDeterminant_last (b : Fin (d + 1) → ℝ) :
    consecutiveDeterminant b (Fin.last d) = b (Fin.last d) ^ 3 := by
  rw [consecutiveDeterminant_polynomial]
  simp only [bandCoefficient_apply_fin]
  have h₁ : bandCoefficient b ((Fin.last d : ℕ) + 1) = 0 := by
    simp
  have h₂ : bandCoefficient b ((Fin.last d : ℕ) + 2) = 0 := by
    simp
  rw [h₁, h₂]
  ring

/-- The positive projective weight `ω_j`, namely the coordinate sum of column `j`. -/
def bandMomentWeight (b : Fin (d + 1) → ℝ) (j : Fin (d + 3)) : ℝ :=
  momentSum ((bandedMatrix b).col j)

/-- The first Pascal moment of column `j`. -/
def bandMomentU (b : Fin (d + 1) → ℝ) (j : Fin (d + 3)) : ℝ :=
  momentU ((bandedMatrix b).col j)

/-- The second Pascal moment of column `j`. -/
def bandMomentV (b : Fin (d + 1) → ℝ) (j : Fin (d + 3)) : ℝ :=
  momentV ((bandedMatrix b).col j)

/-- The edge slope `σ_j` between consecutive Pascal moment points. -/
def bandMomentSlope (b : Fin (d + 1) → ℝ) (j : Fin (d + 2)) : ℝ :=
  (bandMomentV b j.succ - bandMomentV b j.castSucc) /
    (bandMomentU b j.succ - bandMomentU b j.castSucc)

/-- The slope index `t + s`, where `s` is zero or one. -/
def consecutiveSlopeIndex (t : Fin (d + 1)) (s : Fin 2) : Fin (d + 2) :=
  ⟨t + s, by omega⟩

/-- The factor `κ_t` in the determinant--slope identity. -/
def consecutiveSlopeFactor (b : Fin (d + 1) → ℝ) (t : Fin (d + 1)) : ℝ :=
  bandMomentWeight b (consecutiveColumnIndex t 0) *
    bandMomentWeight b (consecutiveColumnIndex t 1) *
    bandMomentWeight b (consecutiveColumnIndex t 2) *
    (bandMomentU b (consecutiveColumnIndex t 1) -
      bandMomentU b (consecutiveColumnIndex t 0)) *
    (bandMomentU b (consecutiveColumnIndex t 2) -
      bandMomentU b (consecutiveColumnIndex t 1))

/-- The oriented area of three moment points is their two horizontal increments
times the difference of the consecutive slopes. -/
theorem momentOrientedArea_eq_slopeDifference {c₀ c₁ c₂ : Column}
    (h₀₁ : momentU c₁ ≠ momentU c₀) (h₁₂ : momentU c₂ ≠ momentU c₁) :
    momentOrientedArea c₀ c₁ c₂ =
      (momentU c₁ - momentU c₀) * (momentU c₂ - momentU c₁) *
        ((momentV c₂ - momentV c₁) / (momentU c₂ - momentU c₁) -
          (momentV c₁ - momentV c₀) / (momentU c₁ - momentU c₀)) := by
  rw [momentOrientedArea]
  field_simp [sub_ne_zero.mpr h₀₁, sub_ne_zero.mpr h₁₂]

/-- A three-column determinant is the positive-weighted moment slope difference. -/
theorem threeColumnMatrix_det_eq_slopeDifference {c₀ c₁ c₂ : Column}
    (hw₀ : momentSum c₀ ≠ 0) (hw₁ : momentSum c₁ ≠ 0) (hw₂ : momentSum c₂ ≠ 0)
    (h₀₁ : momentU c₁ ≠ momentU c₀) (h₁₂ : momentU c₂ ≠ momentU c₁) :
    (threeColumnMatrix c₀ c₁ c₂).det =
      momentSum c₀ * momentSum c₁ * momentSum c₂ *
        (momentU c₁ - momentU c₀) * (momentU c₂ - momentU c₁) *
          ((momentV c₂ - momentV c₁) / (momentU c₂ - momentU c₁) -
            (momentV c₁ - momentV c₀) / (momentU c₁ - momentU c₀)) := by
  rw [threeColumnMatrix_det_eq_momentOrientedArea hw₀ hw₁ hw₂,
    momentOrientedArea_eq_slopeDifference h₀₁ h₁₂]
  ring

/-- The exact bridge `D_t = κ_t (σ_{t+1} - σ_t)`. -/
theorem consecutiveDeterminant_eq_slopeDifference (b : Fin (d + 1) → ℝ)
    (t : Fin (d + 1))
    (hweight : ∀ s : Fin 3, bandMomentWeight b (consecutiveColumnIndex t s) ≠ 0)
    (hu₀₁ : bandMomentU b (consecutiveColumnIndex t 1) ≠
      bandMomentU b (consecutiveColumnIndex t 0))
    (hu₁₂ : bandMomentU b (consecutiveColumnIndex t 2) ≠
      bandMomentU b (consecutiveColumnIndex t 1)) :
    consecutiveDeterminant b t =
      consecutiveSlopeFactor b t *
        (bandMomentSlope b (consecutiveSlopeIndex t 1) -
          bandMomentSlope b (consecutiveSlopeIndex t 0)) := by
  let c₀ := consecutiveColumnIndex t 0
  let c₁ := consecutiveColumnIndex t 1
  let c₂ := consecutiveColumnIndex t 2
  let s₀ := consecutiveSlopeIndex t 0
  let s₁ := consecutiveSlopeIndex t 1
  have hs₀left : s₀.castSucc = c₀ := by
    apply Fin.ext
    simp [s₀, c₀, consecutiveSlopeIndex, consecutiveColumnIndex]
  have hs₀right : s₀.succ = c₁ := by
    apply Fin.ext
    simp [s₀, c₁, consecutiveSlopeIndex, consecutiveColumnIndex]
  have hs₁left : s₁.castSucc = c₁ := by
    apply Fin.ext
    simp [s₁, c₁, consecutiveSlopeIndex, consecutiveColumnIndex]
  have hs₁right : s₁.succ = c₂ := by
    apply Fin.ext
    simp [s₁, c₂, consecutiveSlopeIndex, consecutiveColumnIndex]
  have hσ₀ : bandMomentSlope b s₀ =
      (bandMomentV b c₁ - bandMomentV b c₀) /
        (bandMomentU b c₁ - bandMomentU b c₀) := by
    unfold bandMomentSlope
    rw [hs₀left, hs₀right]
  have hσ₁ : bandMomentSlope b s₁ =
      (bandMomentV b c₂ - bandMomentV b c₁) /
        (bandMomentU b c₂ - bandMomentU b c₁) := by
    unfold bandMomentSlope
    rw [hs₁left, hs₁right]
  simp only [bandMomentU, bandMomentV] at hσ₀ hσ₁
  have hdet := threeColumnMatrix_det_eq_slopeDifference
    (c₀ := (bandedMatrix b).col c₀) (c₁ := (bandedMatrix b).col c₁)
    (c₂ := (bandedMatrix b).col c₂) (hweight 0) (hweight 1) (hweight 2)
    hu₀₁ hu₁₂
  change (threeColumnMatrix ((bandedMatrix b).col c₀) ((bandedMatrix b).col c₁)
    ((bandedMatrix b).col c₂)).det = _
  rw [hdet, ← hσ₁, ← hσ₀]
  unfold consecutiveSlopeFactor bandMomentWeight bandMomentU
  change _ =
    (momentSum ((bandedMatrix b).col c₀) * momentSum ((bandedMatrix b).col c₁) *
      momentSum ((bandedMatrix b).col c₂) *
      (momentU ((bandedMatrix b).col c₁) - momentU ((bandedMatrix b).col c₀)) *
      (momentU ((bandedMatrix b).col c₂) - momentU ((bandedMatrix b).col c₁))) * _
  ring

/-- Under positive weights and strict increase of adjacent first moments, `κ_t`
is strictly positive. -/
theorem consecutiveSlopeFactor_pos (b : Fin (d + 1) → ℝ) (t : Fin (d + 1))
    (hweight : ∀ s : Fin 3, 0 < bandMomentWeight b (consecutiveColumnIndex t s))
    (hu₀₁ : bandMomentU b (consecutiveColumnIndex t 0) <
      bandMomentU b (consecutiveColumnIndex t 1))
    (hu₁₂ : bandMomentU b (consecutiveColumnIndex t 1) <
      bandMomentU b (consecutiveColumnIndex t 2)) :
    0 < consecutiveSlopeFactor b t := by
  unfold consecutiveSlopeFactor
  exact mul_pos (mul_pos (mul_pos (mul_pos (hweight 0) (hweight 1)) (hweight 2))
    (sub_pos.mpr hu₀₁)) (sub_pos.mpr hu₁₂)

/-- A `TN₂` simple banded configuration has positive moment weights. -/
theorem bandMomentWeight_pos_of_tnUpTo_two
    {b : Fin (d + 1) → ℝ} (hC : TNUpTo (bandedMatrix b) 2)
    (hsimple : IsSimpleNonloopConfiguration (bandedMatrix b)) (j : Fin (d + 3)) :
    0 < bandMomentWeight b j := by
  apply momentSum_pos (col_nonnegative_of_tnUpTo_two hC j)
  simpa only [IsLoop] using hsimple.1 j

/-- A `TN₂` simple banded configuration has strictly increasing adjacent first moments. -/
theorem bandMomentU_lt_succ_of_tnUpTo_two
    {b : Fin (d + 1) → ℝ} (hC : TNUpTo (bandedMatrix b) 2)
    (hsimple : IsSimpleNonloopConfiguration (bandedMatrix b)) (j : Fin (d + 2)) :
    bandMomentU b j.castSucc < bandMomentU b j.succ := by
  have hj : j.castSucc < j.succ := by
    change j.val < j.val + 1
    omega
  exact momentU_col_lt_of_tnUpTo_two_of_not_positivelyParallel hC hj
    (hsimple.1 j.castSucc) (hsimple.1 j.succ) (hsimple.2 hj)

/-- The determinant--slope bridge with its positive factor, under the `TN₂`
and no-loop/no-parallel hypotheses supplied by strict log-concavity in the banded setting. -/
theorem consecutiveDeterminant_eq_positiveFactor_mul_slopeDifference
    {b : Fin (d + 1) → ℝ} (hC : TNUpTo (bandedMatrix b) 2)
    (hsimple : IsSimpleNonloopConfiguration (bandedMatrix b)) (t : Fin (d + 1)) :
    consecutiveDeterminant b t =
        consecutiveSlopeFactor b t *
          (bandMomentSlope b (consecutiveSlopeIndex t 1) -
            bandMomentSlope b (consecutiveSlopeIndex t 0)) ∧
      0 < consecutiveSlopeFactor b t := by
  have hw : ∀ s : Fin 3, 0 < bandMomentWeight b (consecutiveColumnIndex t s) :=
    fun s ↦ bandMomentWeight_pos_of_tnUpTo_two hC hsimple _
  have hu₀₁ : bandMomentU b (consecutiveColumnIndex t 0) <
      bandMomentU b (consecutiveColumnIndex t 1) := by
    simpa [bandMomentU, consecutiveColumnIndex, consecutiveSlopeIndex] using
      bandMomentU_lt_succ_of_tnUpTo_two hC hsimple (consecutiveSlopeIndex t 0)
  have hu₁₂ : bandMomentU b (consecutiveColumnIndex t 1) <
      bandMomentU b (consecutiveColumnIndex t 2) := by
    simpa [bandMomentU, consecutiveColumnIndex, consecutiveSlopeIndex] using
      bandMomentU_lt_succ_of_tnUpTo_two hC hsimple (consecutiveSlopeIndex t 1)
  exact ⟨consecutiveDeterminant_eq_slopeDifference b t (fun s ↦ (hw s).ne')
      hu₀₁.ne' hu₁₂.ne',
    consecutiveSlopeFactor_pos b t hw hu₀₁ hu₁₂⟩

/-- The paper's strict-log-concavity/no-parallel specialization of the positive
determinant--slope bridge. -/
theorem consecutiveDeterminant_eq_positiveFactor_mul_slopeDifference_of_strictLogConcave
    {b : Fin (d + 1) → ℝ} (hb : StrictlyLogConcaveWithZeroBoundary b)
    (hsimple : IsSimpleNonloopConfiguration (bandedMatrix b)) (t : Fin (d + 1)) :
    consecutiveDeterminant b t =
        consecutiveSlopeFactor b t *
          (bandMomentSlope b (consecutiveSlopeIndex t 1) -
            bandMomentSlope b (consecutiveSlopeIndex t 0)) ∧
      0 < consecutiveSlopeFactor b t :=
  consecutiveDeterminant_eq_positiveFactor_mul_slopeDifference
    (bandedMatrix_tnUpTo_two_of_strictLogConcave hb) hsimple t

/-- A consecutive determinant is nonnegative exactly when the corresponding two
moment slopes are weakly increasing. -/
theorem consecutiveDeterminant_nonneg_iff_slope_le
    {b : Fin (d + 1) → ℝ} (hb : StrictlyLogConcaveWithZeroBoundary b)
    (hsimple : IsSimpleNonloopConfiguration (bandedMatrix b)) (t : Fin (d + 1)) :
    0 ≤ consecutiveDeterminant b t ↔
      bandMomentSlope b (consecutiveSlopeIndex t 0) ≤
        bandMomentSlope b (consecutiveSlopeIndex t 1) := by
  obtain ⟨hdet, hfactor⟩ :=
    consecutiveDeterminant_eq_positiveFactor_mul_slopeDifference_of_strictLogConcave
      hb hsimple t
  rw [hdet, mul_nonneg_iff_of_pos_left hfactor, sub_nonneg]

/-- A consecutive determinant vanishes exactly when its two adjacent moment
slopes agree. -/
theorem consecutiveDeterminant_eq_zero_iff_slope_eq
    {b : Fin (d + 1) → ℝ} (hb : StrictlyLogConcaveWithZeroBoundary b)
    (hsimple : IsSimpleNonloopConfiguration (bandedMatrix b)) (t : Fin (d + 1)) :
    consecutiveDeterminant b t = 0 ↔
      bandMomentSlope b (consecutiveSlopeIndex t 0) =
        bandMomentSlope b (consecutiveSlopeIndex t 1) := by
  obtain ⟨hdet, hfactor⟩ :=
    consecutiveDeterminant_eq_positiveFactor_mul_slopeDifference_of_strictLogConcave
      hb hsimple t
  rw [hdet, mul_eq_zero]
  simp only [ne_of_gt hfactor, false_or, sub_eq_zero]
  exact eq_comm

end

end ToeplitzPositroids.RankThree
