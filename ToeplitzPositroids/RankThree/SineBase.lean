import ToeplitzPositroids.RankThree.Banded
import ToeplitzPositroids.RankThree.ConvexChainCriterion
import ToeplitzPositroids.RankThree.OrderTwoEquality
import ToeplitzPositroids.RankThree.SineSequence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The rank-three sine base point

This file formalizes the sine base point of Lemma 18.  For `d ≥ 2`, its displayed
coefficients are positive and strictly log-concave with zero boundary.  The associated banded
Toeplitz matrix is totally nonnegative through order two, its interior consecutive maximal
minors vanish, and its endpoint consecutive minors are positive.  The determinant--slope bridge
then gives a convex moment chain and hence full total nonnegativity.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids Matrix

noncomputable section

variable {d : ℕ}

/-- The sine vector is positive coefficientwise. -/
theorem sinePositiveBandCoefficients (d : ℕ) :
    PositiveBandCoefficients (sineCoefficient d) :=
  sineCoefficient_pos d

/-- The sine vector is strictly log-concave, including both structural zero boundaries. -/
theorem sineStrictlyLogConcaveWithZeroBoundary (d : ℕ) :
    StrictlyLogConcaveWithZeroBoundary (sineCoefficient d) := by
  refine ⟨sineCoefficient_pos d, ?_⟩
  intro t
  by_cases ht0 : t.val = 0
  · have ht : t = 0 := Fin.ext ht0
    subst t
    have hleft : bandCoefficient (sineCoefficient d) ((0 : Fin (d + 1)) - 1) = 0 := by
      apply bandCoefficient_eq_zero_of_neg
      omega
    rw [hleft, zero_mul]
    exact sq_pos_of_pos (sineCoefficient_pos d 0)
  · by_cases htd : t.val = d
    · have hright : bandCoefficient (sineCoefficient d) ((t : ℤ) + 1) = 0 := by
        apply bandCoefficient_eq_zero_of_lt
        omega
      rw [hright, mul_zero]
      exact sq_pos_of_pos (sineCoefficient_pos d t)
    · have htpos : 0 < t.val := by omega
      have htsucc : t.val + 1 < d + 1 := by omega
      let tm : Fin (d + 1) := ⟨t.val - 1, by omega⟩
      let tp : Fin (d + 1) := ⟨t.val + 1, by omega⟩
      have hleft : bandCoefficient (sineCoefficient d) ((t : ℤ) - 1) =
          sineCoefficient d tm := by
        rw [← bandCoefficient_apply_fin (sineCoefficient d) tm]
        congr 1
        simp [tm]
        omega
      have hright : bandCoefficient (sineCoefficient d) ((t : ℤ) + 1) =
          sineCoefficient d tp := by
        rw [← bandCoefficient_apply_fin (sineCoefficient d) tp]
        congr 1
      rw [hleft, hright]
      have hdefect := sineCoefficient_logConcavity_defect d htpos htsucc
      change sineCoefficient d tm * sineCoefficient d tp < sineCoefficient d t ^ 2
      have hsin : 0 < Real.sin (sineAngle d) ^ 2 := sq_pos_of_pos (by
        exact Real.sin_pos_of_pos_of_lt_pi (sineAngle_pos d) (sineAngle_lt_pi d))
      dsimp only [tm, tp]
      nlinarith

/-- The sine banded matrix is totally nonnegative through order two. -/
theorem sineBandedMatrix_tnUpTo_two (d : ℕ) :
    TNUpTo (bandedMatrix (sineCoefficient d)) 2 :=
  bandedMatrix_tnUpTo_two_of_strictLogConcave
    (sineStrictlyLogConcaveWithZeroBoundary d)

/-- At every three-term positive window of the padded sine vector, adjacent coefficient ratios
decrease strictly. -/
theorem sineCoefficientRatio_succ_lt (d : ℕ) (k : Fin (d + 3))
    (hleft : 0 < bandCoefficientVector (sineCoefficient d) k.castSucc.castSucc)
    (hcenter : 0 < bandCoefficientVector (sineCoefficient d) k.succ.castSucc) :
    coefficientRatio (bandCoefficientVector (sineCoefficient d)) k.succ <
      coefficientRatio (bandCoefficientVector (sineCoefficient d)) k.castSucc := by
  have hcenterBand : 0 < bandCoefficient (sineCoefficient d) ((k : ℤ) - 1) := by
    simpa only [bandCoefficientVector_center] using hcenter
  have hk := (bandCoefficient_pos_iff (sinePositiveBandCoefficients d) ((k : ℤ) - 1)).mp
    hcenterBand
  let t : Fin (d + 1) := ⟨((k : ℤ) - 1).toNat, by omega⟩
  have ht : (t : ℤ) = (k : ℤ) - 1 := by
    simp only [t]
    rw [Int.toNat_of_nonneg hk.1]
  have hstrict := (sineStrictlyLogConcaveWithZeroBoundary d).2 t
  have hcenterEq : sineCoefficient d t =
      bandCoefficient (sineCoefficient d) ((k : ℤ) - 1) := by
    rw [← bandCoefficient_apply_fin (sineCoefficient d) t, ht]
  have hleftEq : bandCoefficient (sineCoefficient d) ((t : ℤ) - 1) =
      bandCoefficient (sineCoefficient d) ((k : ℤ) - 2) := by
    congr 1
    omega
  have hrightEq : bandCoefficient (sineCoefficient d) ((t : ℤ) + 1) =
      bandCoefficient (sineCoefficient d) k := by
    congr 1
    omega
  rw [hleftEq, hrightEq, hcenterEq] at hstrict
  rw [coefficientRatio_apply, coefficientRatio_apply]
  have hmiddle : k.castSucc.succ = k.succ.castSucc := by
    apply Fin.ext
    rfl
  rw [hmiddle]
  rw [bandCoefficientVector_right, bandCoefficientVector_center,
    bandCoefficientVector_left]
  apply (div_lt_div_iff₀ (by simpa only [bandCoefficientVector_center] using hcenter)
    (by simpa only [bandCoefficientVector_left] using hleft)).2
  nlinarith

/-- Every nonstructural order-two minor of the sine banded matrix is strictly positive. -/
theorem sineBandedMatrix_nonstructural_twoMinor_pos (hd : 2 ≤ d)
    (i₀ i₁ : Fin 3) (hi : i₀ < i₁) (j₀ j₁ : Fin (d + 3)) (hj : j₀ < j₁)
    (hminor : IsNonstructuralTwoMinor (bandCoefficientVector (sineCoefficient d))
      i₀ i₁ j₀ j₁) :
    0 < orderedMinor (bandedMatrix (sineCoefficient d))
      (twoPointOrderEmbedding i₀ i₁ hi) (twoPointOrderEmbedding j₀ j₁ hj) := by
  let a := bandCoefficientVector (sineCoefficient d)
  have hstrict := sineStrictlyLogConcaveWithZeroBoundary d
  have hnonnegCoeff : ∀ k, 0 ≤ a k := bandCoefficientVector_nonneg hstrict.1
  have hsupport : HasIntervalPositiveSupport a :=
    bandCoefficientVector_hasIntervalPositiveSupport hstrict.1
  have hlog : DiscretelyLogConcave a := bandCoefficientVector_discretelyLogConcave hstrict
  have hnonneg := (sineBandedMatrix_tnUpTo_two d).orderedMinor_nonneg le_rfl
    (twoPointOrderEmbedding i₀ i₁ hi) (twoPointOrderEmbedding j₀ j₁ hj)
  by_contra hnot
  have hzero : orderedMinor (bandedMatrix (sineCoefficient d))
      (twoPointOrderEmbedding i₀ i₁ hi) (twoPointOrderEmbedding j₀ j₁ hj) = 0 :=
    le_antisymm (not_lt.mp hnot) hnonneg
  have hzero' : orderedMinor (rankThreeToeplitz a)
      (twoPointOrderEmbedding i₀ i₁ hi) (twoPointOrderEmbedding j₀ j₁ hj) = 0 := by
    simpa [a, bandedMatrix_eq_rankThreeToeplitz] using hzero
  have hconst := (rankThreeToeplitz_nonstructural_minor_eq_zero_iff_ratio_const
    hnonnegCoeff hsupport hlog i₀ i₁ hi j₀ j₁ hj hminor).mp hzero'
  let s := minorRatioStart i₀ i₁ hi j₀
  let e := finiteToeplitzIndex i₀ j₁
  have hgap : s.val + 2 ≤ e.val := by
    simp only [s, e, minorRatioStart_val, finiteToeplitzIndex_val]
    omega
  let k : Fin (d + 3) := ⟨s.val, by omega⟩
  have hs : s = k.castSucc := by
    apply Fin.ext
    rfl
  have hlowerIndex : (finiteToeplitzIndex i₁ j₀) = k.castSucc.castSucc := by
    apply Fin.ext
    change (finiteToeplitzIndex i₁ j₀).val = s.val
    rfl
  have hleft : 0 < a k.castSucc.castSucc := by
    rw [← hlowerIndex]
    exact hminor.2.2.1
  have hcenter : 0 < a k.succ.castSucc := by
    apply (hasIntervalPositiveSupport_iff a).mp hsupport
      (finiteToeplitzIndex i₁ j₀) (finiteToeplitzIndex i₀ j₁)
        k.succ.castSucc hminor.2.2.1 hminor.2.1
    · change (finiteToeplitzIndex i₁ j₀).val ≤ k.val + 1
      simp only [k, s, minorRatioStart_val]
      omega
    · change k.val + 1 ≤ (finiteToeplitzIndex i₀ j₁).val
      simp only [k]
      omega
  have hratioStrict := sineCoefficientRatio_succ_lt d k hleft hcenter
  have hratioEq : coefficientRatio a k.succ = coefficientRatio a s := hconst k.succ (by
    change s.val ≤ k.val + 1
    simp [k]) (by
    change k.val + 1 < e.val
    simp only [k]
    omega)
  rw [hs] at hratioEq
  exact (ne_of_lt hratioStrict) hratioEq

/-- Entry positivity in the sine band is exactly membership of its coefficient index in
`0, …, d`. -/
theorem sineBandedMatrix_entry_pos_iff (d : ℕ) (i : Fin 3) (j : Fin (d + 3)) :
    0 < bandedMatrix (sineCoefficient d) i j ↔
      (0 : ℤ) ≤ (j : ℤ) - i ∧ (j : ℤ) - i ≤ d := by
  rw [bandedMatrix_apply, bandCoefficient_pos_iff (sinePositiveBandCoefficients d)]

/-- For `d ≥ 2`, the sine band has no loops and no distinct positively parallel columns. -/
theorem sineBandedMatrix_isSimpleNonloopConfiguration (hd : 2 ≤ d) :
    IsSimpleNonloopConfiguration (bandedMatrix (sineCoefficient d)) := by
  let C := bandedMatrix (sineCoefficient d)
  have hC := sineBandedMatrix_tnUpTo_two d
  constructor
  · intro j hloop
    rw [isLoop_iff_entry_eq_zero] at hloop
    by_cases hj : j.val ≤ d
    · have hpos : 0 < C 0 j := by
        rw [sineBandedMatrix_entry_pos_iff]
        constructor <;> omega
      exact hpos.ne' (hloop 0)
    · have hpos : 0 < C 2 j := by
        rw [sineBandedMatrix_entry_pos_iff]
        constructor <;> omega
      exact hpos.ne' (hloop 2)
  · intro i j hij hparallel
    obtain ⟨c, hc, hcol⟩ := hparallel
    have hposiff : ∀ r : Fin 3, 0 < C r i ↔ 0 < C r j := by
      intro r
      change 0 < bandedMatrix (sineCoefficient d) r i ↔
        0 < bandedMatrix (sineCoefficient d) r j
      have hcoord := congrFun hcol r
      simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hcoord
      constructor
      · intro hi
        rw [hcoord]
        exact mul_pos hc hi
      · intro hj
        have hinonneg := hC.entry_nonneg (by omega) r i
        rw [hcoord] at hj
        nlinarith
    have h₀ := hposiff 0
    have h₁ := hposiff 1
    have h₂ := hposiff 2
    simp only [C, sineBandedMatrix_entry_pos_iff] at h₀ h₁ h₂
    have hinterior : 2 ≤ i.val ∧ j.val ≤ d := by omega
    have hminor : IsNonstructuralTwoMinor (bandCoefficientVector (sineCoefficient d))
        (0 : Fin 3) 1 i j := by
      have h00 : 0 < C 0 i := by
        rw [sineBandedMatrix_entry_pos_iff]
        constructor <;> omega
      have h01 : 0 < C 0 j := by
        rw [sineBandedMatrix_entry_pos_iff]
        constructor <;> omega
      have h10 : 0 < C 1 i := by
        rw [sineBandedMatrix_entry_pos_iff]
        constructor <;> omega
      have h11 : 0 < C 1 j := by
        rw [sineBandedMatrix_entry_pos_iff]
        constructor <;> omega
      dsimp only [C] at h00 h01 h10 h11
      rw [bandedMatrix_eq_rankThreeToeplitz] at h00 h01 h10 h11
      exact ⟨h00, h01, h10, h11⟩
    have hposminor := sineBandedMatrix_nonstructural_twoMinor_pos hd
      (0 : Fin 3) 1 (by decide) i j hij hminor
    have hzero : orderedMinor C (twoPointOrderEmbedding (0 : Fin 3) 1 (by decide))
        (twoPointOrderEmbedding i j hij) = 0 := by
      rw [orderedMinor_two]
      simp only [twoPointOrderEmbedding_zero, twoPointOrderEmbedding_one]
      dsimp only [C]
      have hc₀ := congrFun hcol (0 : Fin 3)
      have hc₁ := congrFun hcol (1 : Fin 3)
      simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hc₀ hc₁
      rw [hc₀, hc₁]
      ring
    exact hposminor.ne' hzero

/-- The zero-extended sine coefficients satisfy the second-order recurrence throughout the
middle band, including its two structural boundary terms. -/
theorem sineBandCoefficient_recurrence (hd : 2 ≤ d) (j : ℕ)
    (hj0 : 1 ≤ j) (hjd : j ≤ d + 1) :
    bandCoefficient (sineCoefficient d) j =
      2 * Real.cos (sineAngle d) * bandCoefficient (sineCoefficient d) (j - 1) -
        bandCoefficient (sineCoefficient d) (j - 2) := by
  rcases eq_or_lt_of_le hjd with hjlast | hjlt
  · have hj : j = d + 1 := by omega
    subst j
    have htrig := sin_add_eq_two_cos_mul_sin_sub_sin_sub
      (((d : ℝ) + 1) * sineAngle d) (sineAngle d)
    have hplus : (((d : ℝ) + 1) * sineAngle d) + sineAngle d = Real.pi := by
      unfold sineAngle
      field_simp
      ring
    have hminus : (((d : ℝ) + 1) * sineAngle d) - sineAngle d =
        (d : ℝ) * sineAngle d := by ring
    rw [hplus, Real.sin_pi, hminus] at htrig
    have htopzero : bandCoefficient (sineCoefficient d) ((d + 1 : ℕ) : ℤ) = 0 := by
      apply bandCoefficient_eq_zero_of_lt
      omega
    rw [htopzero]
    have hcenter : bandCoefficient (sineCoefficient d) ((d + 1 : ℕ) - 1) =
        sineCoefficient d (Fin.last d) := by
      rw [← bandCoefficient_apply_fin (sineCoefficient d) (Fin.last d)]
      congr 1
      simp
    let dm : Fin (d + 1) := ⟨d - 1, by omega⟩
    have hleft : bandCoefficient (sineCoefficient d) ((d + 1 : ℕ) - 2) =
        sineCoefficient d dm := by
      rw [← bandCoefficient_apply_fin (sineCoefficient d) dm]
      congr 1
      change ((d + 1 : ℕ) : ℤ) - 2 = ((d - 1 : ℕ) : ℤ)
      simpa using (Int.ofNat_sub (by omega : 2 ≤ d + 1)).symm
    rw [hcenter, hleft]
    unfold sineCoefficient
    have hdmCast : ((d - 1 : ℕ) : ℝ) + 1 = d := by
      norm_num only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      ring
    rw [hdmCast]
    simpa [dm, mul_comm, mul_left_comm, mul_assoc] using htrig
  · by_cases hjone : j = 1
    · subst j
      have htrig := sin_add_eq_two_cos_mul_sin_sub_sin_sub
        (sineAngle d) (sineAngle d)
      rw [sub_self, Real.sin_zero] at htrig
      have hzero : bandCoefficient (sineCoefficient d) ((1 : ℕ) - 2) = 0 := by
        change bandCoefficient (sineCoefficient d) (-1) = 0
        simp
      rw [hzero, sub_zero]
      have hcenter : bandCoefficient (sineCoefficient d) (((1 : ℕ) : ℤ) - 1) =
          sineCoefficient d 0 := by
        rw [← bandCoefficient_apply_fin (sineCoefficient d) (0 : Fin (d + 1))]
        congr 1
      have hOne : bandCoefficient (sineCoefficient d) (1 : ℕ) =
          sineCoefficient d ⟨1, by omega⟩ := by
        rw [← bandCoefficient_apply_fin (sineCoefficient d) ⟨1, by omega⟩]
      rw [hOne, hcenter]
      unfold sineCoefficient
      norm_num
      rw [show (2 : ℝ) * sineAngle d = sineAngle d + sineAngle d by ring]
      simpa [mul_comm, mul_left_comm, mul_assoc] using htrig
    · have hjtwo : 2 ≤ j := by omega
      let u : ℕ := j - 2
      have hu : u + 2 < d + 1 := by omega
      have hrec := sineCoefficient_recurrence d hu
      let jt : Fin (d + 1) := ⟨j, by omega⟩
      let jm : Fin (d + 1) := ⟨j - 1, by omega⟩
      let jmm : Fin (d + 1) := ⟨j - 2, by omega⟩
      have hjband : bandCoefficient (sineCoefficient d) j = sineCoefficient d jt := by
        rw [← bandCoefficient_apply_fin (sineCoefficient d) jt]
      have hjmband : bandCoefficient (sineCoefficient d) (j - 1) = sineCoefficient d jm := by
        rw [← bandCoefficient_apply_fin (sineCoefficient d) jm]
        congr 1
        simpa using (Int.ofNat_sub (by omega : 1 ≤ j)).symm
      have hjmmband : bandCoefficient (sineCoefficient d) (j - 2) = sineCoefficient d jmm := by
        rw [← bandCoefficient_apply_fin (sineCoefficient d) jmm]
        congr 1
        simpa using (Int.ofNat_sub (by omega : 2 ≤ j)).symm
      rw [hjband, hjmband, hjmmband]
      have ejt : jt = ⟨u + 2, hu⟩ := by
        apply Fin.ext
        change j = u + 2
        dsimp only [u]
        omega
      have ejm : jm = ⟨u + 1, by omega⟩ := by
        apply Fin.ext
        change j - 1 = u + 1
        dsimp only [u]
        omega
      have ejmm : jmm = ⟨u, by omega⟩ := by
        apply Fin.ext
        change j - 2 = u
        rfl
      rw [ejt, ejm, ejmm]
      exact hrec

/-- Every middle column of the sine band lies in the recurrence plane
`x - 2 cos(θ) y + z = 0`. -/
theorem sineBandedMatrix_middleColumn_plane (hd : 2 ≤ d) (j : Fin (d + 3))
    (hj0 : 1 ≤ j.val) (hjd : j.val ≤ d + 1) :
    bandedMatrix (sineCoefficient d) 0 j -
        2 * Real.cos (sineAngle d) * bandedMatrix (sineCoefficient d) 1 j +
      bandedMatrix (sineCoefficient d) 2 j = 0 := by
  rw [bandedMatrix_apply, bandedMatrix_apply, bandedMatrix_apply]
  have hrec := sineBandCoefficient_recurrence hd j.val hj0 hjd
  change bandCoefficient (sineCoefficient d) j.val -
      2 * Real.cos (sineAngle d) * bandCoefficient (sineCoefficient d) (j.val - 1) +
        bandCoefficient (sineCoefficient d) (j.val - 2) = 0
  linarith

/-- Three columns lying in one plane through the origin have zero determinant. -/
theorem threeColumnMatrix_det_eq_zero_of_common_plane {n : ℕ}
    (A : Matrix (Fin 3) (Fin n) ℝ) (i j k : Fin n) (q : ℝ)
    (hi : A 0 i - q * A 1 i + A 2 i = 0)
    (hj : A 0 j - q * A 1 j + A 2 j = 0)
    (hk : A 0 k - q * A 1 k + A 2 k = 0) :
    (threeColumnMatrix (A.col i) (A.col j) (A.col k)).det = 0 := by
  rw [Matrix.det_fin_three]
  norm_num [threeColumnMatrix, Matrix.cons_val_two]
  linear_combination
    (A 1 j * A 2 k - A 2 j * A 1 k) * hi -
    (A 1 i * A 2 k - A 2 i * A 1 k) * hj +
    (A 1 i * A 2 j - A 2 i * A 1 j) * hk

/-- Every interior consecutive maximal minor vanishes at the sine point. -/
theorem sineConsecutiveDeterminant_eq_zero (hd : 2 ≤ d) (t : Fin (d + 1))
    (ht0 : 0 < t.val) (htd : t.val < d) :
    consecutiveDeterminant (sineCoefficient d) t = 0 := by
  let C := bandedMatrix (sineCoefficient d)
  let j₀ := consecutiveColumnIndex t 0
  let j₁ := consecutiveColumnIndex t 1
  let j₂ := consecutiveColumnIndex t 2
  have hp₀ := sineBandedMatrix_middleColumn_plane hd j₀ (by
    change 1 ≤ t.val
    omega) (by
    change t.val ≤ d + 1
    omega)
  have hp₁ := sineBandedMatrix_middleColumn_plane hd j₁ (by
    change 1 ≤ t.val + 1
    omega) (by
    change t.val + 1 ≤ d + 1
    omega)
  have hp₂ := sineBandedMatrix_middleColumn_plane hd j₂ (by
    change 1 ≤ t.val + 2
    omega) (by
    change t.val + 2 ≤ d + 1
    omega)
  unfold consecutiveDeterminant
  exact threeColumnMatrix_det_eq_zero_of_common_plane C j₀ j₁ j₂
    (2 * Real.cos (sineAngle d)) hp₀ hp₁ hp₂

/-- The left endpoint consecutive determinant is positive. -/
theorem sineConsecutiveDeterminant_zero_pos (d : ℕ) :
    0 < consecutiveDeterminant (sineCoefficient d) 0 := by
  rw [consecutiveDeterminant_zero]
  exact pow_pos (sineCoefficient_pos d 0) 3

/-- The right endpoint consecutive determinant is positive. -/
theorem sineConsecutiveDeterminant_last_pos (d : ℕ) :
    0 < consecutiveDeterminant (sineCoefficient d) (Fin.last d) := by
  rw [consecutiveDeterminant_last]
  exact pow_pos (sineCoefficient_pos d (Fin.last d)) 3

/-- Every consecutive determinant at the sine point is nonnegative. -/
theorem sineConsecutiveDeterminant_nonneg (hd : 2 ≤ d) (t : Fin (d + 1)) :
    0 ≤ consecutiveDeterminant (sineCoefficient d) t := by
  by_cases ht0 : t.val = 0
  · have ht : t = 0 := Fin.ext ht0
    subst t
    exact (sineConsecutiveDeterminant_zero_pos d).le
  · by_cases htd : t.val = d
    · have ht : t = Fin.last d := Fin.ext htd
      subst t
      exact (sineConsecutiveDeterminant_last_pos d).le
    · rw [sineConsecutiveDeterminant_eq_zero hd t (by omega) (by omega)]

/-- The banded slope notation agrees with the edge slopes of the matrix moment chain. -/
theorem bandMomentSlope_eq_edgeSlope (b : Fin (d + 1) → ℝ) (j : Fin (d + 2)) :
    bandMomentSlope b j =
      edgeSlope (matrixMomentU (bandedMatrix b)) (matrixMomentV (bandedMatrix b)) j.val := by
  unfold bandMomentSlope edgeSlope chordSlope bandMomentU bandMomentV
  change
    (momentV ((bandedMatrix b).col j.succ) - momentV ((bandedMatrix b).col j.castSucc)) /
        (momentU ((bandedMatrix b).col j.succ) - momentU ((bandedMatrix b).col j.castSucc)) =
      (matrixMomentV (bandedMatrix b) j.succ.val -
          matrixMomentV (bandedMatrix b) j.castSucc.val) /
        (matrixMomentU (bandedMatrix b) j.succ.val -
          matrixMomentU (bandedMatrix b) j.castSucc.val)
  rw [matrixMomentU_apply_fin, matrixMomentU_apply_fin,
    matrixMomentV_apply_fin, matrixMomentV_apply_fin]

/-- Every adjacent pair of sine moment slopes is weakly increasing. -/
theorem sineBandMomentSlope_mono (hd : 2 ≤ d) (t : Fin (d + 1)) :
    bandMomentSlope (sineCoefficient d) (consecutiveSlopeIndex t 0) ≤
      bandMomentSlope (sineCoefficient d) (consecutiveSlopeIndex t 1) := by
  have hbridge := consecutiveDeterminant_eq_positiveFactor_mul_slopeDifference
    (sineBandedMatrix_tnUpTo_two d) (sineBandedMatrix_isSimpleNonloopConfiguration hd) t
  have hdet := sineConsecutiveDeterminant_nonneg hd t
  rw [hbridge.1] at hdet
  nlinarith [hbridge.2]

/-- The two endpoint slope comparisons are strict. -/
theorem sineBandMomentSlope_zero_lt (hd : 2 ≤ d) :
    bandMomentSlope (sineCoefficient d) (consecutiveSlopeIndex 0 0) <
      bandMomentSlope (sineCoefficient d) (consecutiveSlopeIndex 0 1) := by
  have hbridge := consecutiveDeterminant_eq_positiveFactor_mul_slopeDifference
    (sineBandedMatrix_tnUpTo_two d) (sineBandedMatrix_isSimpleNonloopConfiguration hd)
      (0 : Fin (d + 1))
  have hdet := sineConsecutiveDeterminant_zero_pos d
  rw [hbridge.1] at hdet
  nlinarith [hbridge.2]

theorem sineBandMomentSlope_last_lt (hd : 2 ≤ d) :
    bandMomentSlope (sineCoefficient d) (consecutiveSlopeIndex (Fin.last d) 0) <
      bandMomentSlope (sineCoefficient d) (consecutiveSlopeIndex (Fin.last d) 1) := by
  have hbridge := consecutiveDeterminant_eq_positiveFactor_mul_slopeDifference
    (sineBandedMatrix_tnUpTo_two d) (sineBandedMatrix_isSimpleNonloopConfiguration hd)
      (Fin.last d)
  have hdet := sineConsecutiveDeterminant_last_pos d
  rw [hbridge.1] at hdet
  nlinarith [hbridge.2]

/-- The complete sine moment-slope chain is weakly increasing. -/
theorem sineBandedMatrix_momentSlopesMonotone (hd : 2 ≤ d) :
    SlopesMonotoneUpTo (matrixMomentU (bandedMatrix (sineCoefficient d)))
      (matrixMomentV (bandedMatrix (sineCoefficient d))) (d + 3) := by
  have hC := sineBandedMatrix_tnUpTo_two d
  have hsimple := sineBandedMatrix_isSimpleNonloopConfiguration hd
  apply (slopesMonotoneUpTo_iff_consecutive _ _
    (matrixMomentU_strictlyIncreasingUpTo hC hsimple)).mpr
  intro i hi
  let t : Fin (d + 1) := ⟨i, by omega⟩
  have hslope := sineBandMomentSlope_mono hd t
  rw [bandMomentSlope_eq_edgeSlope, bandMomentSlope_eq_edgeSlope] at hslope
  change edgeSlope (matrixMomentU (bandedMatrix (sineCoefficient d)))
    (matrixMomentV (bandedMatrix (sineCoefficient d))) i ≤
      edgeSlope (matrixMomentU (bandedMatrix (sineCoefficient d)))
        (matrixMomentV (bandedMatrix (sineCoefficient d))) (i + 1)
  simpa [t, consecutiveSlopeIndex] using hslope

/-- The sine banded matrix is totally nonnegative. -/
theorem sineBandedMatrix_totallyNonnegative (hd : 2 ≤ d) :
    TotallyNonnegative (bandedMatrix (sineCoefficient d)) :=
  (totallyNonnegative_iff_momentSlopesMonotone
    (sineBandedMatrix_tnUpTo_two d) (sineBandedMatrix_isSimpleNonloopConfiguration hd)).mpr
      (sineBandedMatrix_momentSlopesMonotone hd)

/-- The positive left endpoint determinant witnesses full row rank. -/
theorem sineBandedMatrix_hasFullRowRank (hd : 2 ≤ d) :
    HasFullRowRank (bandedMatrix (sineCoefficient d)) := by
  let i : Fin (d + 3) := ⟨0, by omega⟩
  let j : Fin (d + 3) := ⟨1, by omega⟩
  let k : Fin (d + 3) := ⟨2, by omega⟩
  have hij : i < j := by simp [i, j]
  have hjk : j < k := by
    change (1 : ℕ) < 2
    omega
  refine ⟨selectedTripleEmbedding i j k hij hjk, ?_⟩
  rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det]
  change consecutiveDeterminant (sineCoefficient d) 0 ≠ 0
  exact (sineConsecutiveDeterminant_zero_pos d).ne'

/-- Lemma 18, packaged with all of its asserted conclusions. -/
theorem sineBasePoint (hd : 2 ≤ d) :
    TotallyNonnegative (bandedMatrix (sineCoefficient d)) ∧
      HasFullRowRank (bandedMatrix (sineCoefficient d)) ∧
      (∀ (i₀ i₁ : Fin 3) (hi : i₀ < i₁) (j₀ j₁ : Fin (d + 3)) (hj : j₀ < j₁),
        IsNonstructuralTwoMinor (bandCoefficientVector (sineCoefficient d)) i₀ i₁ j₀ j₁ →
          0 < orderedMinor (bandedMatrix (sineCoefficient d))
            (twoPointOrderEmbedding i₀ i₁ hi) (twoPointOrderEmbedding j₀ j₁ hj)) ∧
      0 < consecutiveDeterminant (sineCoefficient d) 0 ∧
      (∀ t : Fin (d + 1), 0 < t.val → t.val < d →
        consecutiveDeterminant (sineCoefficient d) t = 0) ∧
      0 < consecutiveDeterminant (sineCoefficient d) (Fin.last d) :=
  ⟨sineBandedMatrix_totallyNonnegative hd, sineBandedMatrix_hasFullRowRank hd,
    fun i₀ i₁ hi j₀ j₁ hj ↦ sineBandedMatrix_nonstructural_twoMinor_pos hd i₀ i₁ hi j₀ j₁ hj,
    sineConsecutiveDeterminant_zero_pos d, sineConsecutiveDeterminant_eq_zero hd,
    sineConsecutiveDeterminant_last_pos d⟩

end

end ToeplitzPositroids.RankThree
