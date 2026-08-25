import ToeplitzPositroids.RankThree.CollinearIntervals
import ToeplitzPositroids.RankThree.OneSidedRealization
import ToeplitzPositroids.RankThree.OrderTwo
import Mathlib.Tactic

/-!
# Assembly of one-sided Toeplitz realizations

This file turns finite synthesized ratio chains into finite Toeplitz coefficient
vectors.  It isolates the positive, unprotected endpoint chart used as the core
of the one-sided construction.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- Freeze a synthesized ratio sequence after its final required value. -/
def finiteSynthesizedRatio {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) (j : ℕ) : ℝ :=
  synthesizedRatio s ε (min j (N + 1))

/-- Before the final cutoff, the frozen ratio sequence agrees with the original synthesis. -/
theorem finiteSynthesizedRatio_eq {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) {j : ℕ}
    (hj : j ≤ N + 1) :
    finiteSynthesizedRatio s ε j = synthesizedRatio s ε j := by
  simp [finiteSynthesizedRatio, min_eq_left hj]

/-- Every frozen synthesized ratio is positive. -/
theorem finiteSynthesizedRatio_pos {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : ℕ) :
    0 < finiteSynthesizedRatio s ε j := by
  apply synthesizedRatio_pos_of_lt hε
  omega

/-- Freezing preserves weak increase of the ratios. -/
theorem finiteSynthesizedRatio_mono_succ {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : ℕ) :
    finiteSynthesizedRatio s ε j ≤ finiteSynthesizedRatio s ε (j + 1) := by
  by_cases hj : j < N + 1
  · rw [finiteSynthesizedRatio_eq s ε hj.le,
      finiteSynthesizedRatio_eq s ε (by omega)]
    exact (synthesizedRatio_strictMonoOn hε (Nat.lt_succ_self j) (by omega)).le
  · have hj' : N + 1 ≤ j := Nat.le_of_not_gt hj
    simp [finiteSynthesizedRatio, min_eq_right hj', min_eq_right (by omega : N + 1 ≤ j + 1)]

/-- The coefficient vector recovered from a finite synthesized ratio chain. -/
def synthesizedCoefficientVector {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) :
    Fin (N + 3) → ℝ :=
  fun k ↦ recoveredCoefficient (finiteSynthesizedRatio s ε) k.val

/-- Every synthesized coefficient is positive. -/
theorem synthesizedCoefficientVector_pos {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (k : Fin (N + 3)) :
    0 < synthesizedCoefficientVector s ε k := by
  exact recoveredCoefficient_pos (finiteSynthesizedRatio_pos hε) k.val

/-- Positivity makes the coefficient support the whole stored interval. -/
theorem synthesizedCoefficientVector_intervalSupport {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) :
    HasIntervalPositiveSupport (synthesizedCoefficientVector s ε) := by
  rw [hasIntervalPositiveSupport_iff]
  intro i j k hi hj hik hkj
  exact synthesizedCoefficientVector_pos hε k

/-- The recovered finite coefficient vector is discretely log-concave. -/
theorem synthesizedCoefficientVector_logConcave {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) :
    DiscretelyLogConcave (n := N + 1) (synthesizedCoefficientVector s ε) := by
  intro k
  simpa [synthesizedCoefficientVector, pow_two, mul_comm] using
    (recoveredCoefficient_logConcave (finiteSynthesizedRatio_pos hε)
      (finiteSynthesizedRatio_mono_succ hε) k.val)

/-- The positive synthesized Toeplitz section is totally nonnegative through order two. -/
theorem synthesizedToeplitz_tnUpTo_two {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hN : 2 ≤ N) (hε : IsAdmissibleSynthesisEpsilon s ε) :
    TNUpTo (rankThreeToeplitz (synthesizedCoefficientVector s ε)) 2 := by
  rw [rankThreeToeplitz_tnUpTo_two_iff (n := N + 1) (by omega)]
  exact ⟨fun k ↦ (synthesizedCoefficientVector_pos hε k).le,
    synthesizedCoefficientVector_intervalSupport hε,
    synthesizedCoefficientVector_logConcave hε⟩

/-- A recovered coefficient equals its inverse ratio times the following coefficient. -/
theorem recoveredCoefficient_eq_ratio_mul_succ {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (j : ℕ) :
    recoveredCoefficient r j = r j * recoveredCoefficient r (j + 1) := by
  have hratio := recoveredCoefficient_div_succ hr j
  have hnext := (recoveredCoefficient_pos hr (j + 1)).ne'
  field_simp at hratio
  nlinarith

/-- Each Toeplitz column is a positive multiple of its affine ratio point. -/
theorem synthesizedToeplitz_column {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : Fin (N + 1)) :
    (rankThreeToeplitz (synthesizedCoefficientVector s ε)).col j =
      synthesizedCoefficientVector s ε j.succ.succ •
        ![1, ratioPointX (finiteSynthesizedRatio s ε) j.val,
          ratioPointY (finiteSynthesizedRatio s ε) j.val] := by
  let r := finiteSynthesizedRatio s ε
  have hr : ∀ t, 0 < r t := finiteSynthesizedRatio_pos hε
  have h₁ := recoveredCoefficient_eq_ratio_mul_succ hr (j.val + 1)
  have h₀ := recoveredCoefficient_eq_ratio_mul_succ hr j.val
  change (fun i ↦ rankThreeToeplitz (synthesizedCoefficientVector s ε) i j) = _
  rw [rankThreeToeplitz_column]
  funext i
  fin_cases i
  · simp [synthesizedCoefficientVector]
  · simp only [Pi.smul_apply, smul_eq_mul]
    change recoveredCoefficient r (j.val + 1) =
      recoveredCoefficient r (j.val + 2) * r (j.val + 1)
    nlinarith [h₁]
  · simp only [Pi.smul_apply, smul_eq_mul]
    change recoveredCoefficient r j.val =
      recoveredCoefficient r (j.val + 2) * (r j.val * r (j.val + 1))
    rw [h₀, h₁]
    ring

/-- The determinant of three affine ratio columns is their oriented area. -/
theorem ratioPoint_threeColumnMatrix_det (r : ℕ → ℝ) (i j k : ℕ) :
    (threeColumnMatrix
      ![1, ratioPointX r i, ratioPointY r i]
      ![1, ratioPointX r j, ratioPointY r j]
      ![1, ratioPointX r k, ratioPointY r k]).det =
        orientedArea (ratioPointX r) (ratioPointY r) i j k := by
  norm_num [threeColumnMatrix, Matrix.det_fin_three, Matrix.cons_val_two, orientedArea]
  ring

/-- Selected maximal minors are positive scale factors times oriented areas of ratio points. -/
theorem synthesizedToeplitz_minor_eq_area {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) {i j k : Fin (N + 1)}
    (hij : i < j) (hjk : j < k) :
    orderedMinor (rankThreeToeplitz (synthesizedCoefficientVector s ε)) (allRows 3)
        (selectedTripleEmbedding i j k hij hjk) =
      synthesizedCoefficientVector s ε i.succ.succ *
        synthesizedCoefficientVector s ε j.succ.succ *
        synthesizedCoefficientVector s ε k.succ.succ *
          orientedArea (ratioPointX (finiteSynthesizedRatio s ε))
            (ratioPointY (finiteSynthesizedRatio s ε)) i.val j.val k.val := by
  rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det,
    synthesizedToeplitz_column hε, synthesizedToeplitz_column hε,
    synthesizedToeplitz_column hε, threeColumnMatrix_det_smul,
    ratioPoint_threeColumnMatrix_det]

/-- The frozen ratio points retain every prescribed synthesized edge slope. -/
theorem finiteSynthesizedRatio_edgeSlope {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : Fin N) :
    edgeSlope (ratioPointX (finiteSynthesizedRatio s ε))
      (ratioPointY (finiteSynthesizedRatio s ε)) j.val = s j := by
  rw [ratioPoint_edgeSlope]
  rw [finiteSynthesizedRatio_eq s ε (by omega),
    finiteSynthesizedRatio_eq s ε (by omega),
    finiteSynthesizedRatio_eq s ε (by omega)]
  rw [← ratioPoint_edgeSlope (synthesizedRatio s ε) j.val]
  exact synthesizedPoint_edgeSlope hε j

/-- The finite ratio-point abscissae strictly increase. -/
theorem finiteSynthesizedRatio_pointX_strict {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) :
    StrictlyIncreasingUpTo (ratioPointX (finiteSynthesizedRatio s ε)) (N + 1) := by
  intro i j hij hjN
  simp only [ratioPointX]
  rw [finiteSynthesizedRatio_eq s ε (by omega),
    finiteSynthesizedRatio_eq s ε (by omega)]
  exact synthesizedRatio_strictMonoOn hε (by omega) (by omega)

/-- Monotonicity of the target slopes transfers to the finite ratio-point chain. -/
theorem finiteSynthesizedRatio_slopesMonotone {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (hs : Monotone s) :
    SlopesMonotoneUpTo (ratioPointX (finiteSynthesizedRatio s ε))
      (ratioPointY (finiteSynthesizedRatio s ε)) (N + 1) := by
  intro i j hij hjN
  have hiN : i < N := by omega
  have hjN' : j < N := by omega
  rw [finiteSynthesizedRatio_edgeSlope hε ⟨i, hiN⟩,
    finiteSynthesizedRatio_edgeSlope hε ⟨j, hjN'⟩]
  exact hs (by simpa using hij)

/-- Every oriented area in the finite positive ratio chain is nonnegative. -/
theorem finiteSynthesizedRatio_areasNonnegative {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (hs : Monotone s) :
    AreasNonnegativeUpTo (ratioPointX (finiteSynthesizedRatio s ε))
      (ratioPointY (finiteSynthesizedRatio s ε)) (N + 1) :=
  areasNonnegativeUpTo_of_slopesMonotoneUpTo _ _
    (finiteSynthesizedRatio_pointX_strict hε)
    (finiteSynthesizedRatio_slopesMonotone hε hs)

/-- All maximal minors of the positive synthesized Toeplitz section are nonnegative. -/
theorem synthesizedToeplitz_maximalMinorsNonnegative {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (hs : Monotone s) :
    MaximalMinorsNonnegative
      (rankThreeToeplitz (synthesizedCoefficientVector s ε)) := by
  intro cols
  have h01 : cols 0 < cols 1 := cols.strictMono (by decide)
  have h12 : cols 1 < cols 2 := cols.strictMono (by decide)
  have harea := finiteSynthesizedRatio_areasNonnegative hε hs
    (show (cols 0).val < (cols 1).val from h01)
    (show (cols 1).val < (cols 2).val from h12) (cols 2).isLt
  have hminor := synthesizedToeplitz_minor_eq_area hε h01 h12
  rw [selectedTripleEmbedding_eq cols] at hminor
  rw [hminor]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (synthesizedCoefficientVector_pos hε _).le
        (synthesizedCoefficientVector_pos hε _).le)
      (synthesizedCoefficientVector_pos hε _).le) harea

/-- A positive weakly increasing target family yields a totally nonnegative positive Toeplitz
section. -/
theorem synthesizedToeplitz_totallyNonnegative {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hN : 2 ≤ N) (hε : IsAdmissibleSynthesisEpsilon s ε)
    (hs : Monotone s) :
    TotallyNonnegative (rankThreeToeplitz (synthesizedCoefficientVector s ε)) := by
  rw [totallyNonnegative_fin_three_iff]
  exact ⟨synthesizedToeplitz_tnUpTo_two hN hε,
    synthesizedToeplitz_maximalMinorsNonnegative hε hs⟩

/-- A strict adjacent target-slope comparison supplies an explicit positive maximal minor. -/
theorem synthesizedToeplitz_hasFullRowRank_of_strictSlope {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) {t : ℕ} (ht : t + 1 < N)
    (hstrict : s ⟨t, by omega⟩ < s ⟨t + 1, ht⟩) :
    HasFullRowRank (rankThreeToeplitz (synthesizedCoefficientVector s ε)) := by
  let i : Fin (N + 1) := ⟨t, by omega⟩
  let j : Fin (N + 1) := ⟨t + 1, by omega⟩
  let k : Fin (N + 1) := ⟨t + 2, by omega⟩
  have hij : i < j := by simp [i, j]
  have hjk : j < k := by simp [j, k]
  have hx₁ := finiteSynthesizedRatio_pointX_strict hε hij (by simp [j]; omega)
  have hx₂ := finiteSynthesizedRatio_pointX_strict hε hjk (by simp [k]; omega)
  have harea : 0 < orientedArea (ratioPointX (finiteSynthesizedRatio s ε))
      (ratioPointY (finiteSynthesizedRatio s ε)) t (t + 1) (t + 2) := by
    rw [orientedArea_consecutive _ _ (ne_of_gt hx₁) (ne_of_gt hx₂)]
    rw [finiteSynthesizedRatio_edgeSlope hε ⟨t, by omega⟩,
      finiteSynthesizedRatio_edgeSlope hε ⟨t + 1, ht⟩]
    exact mul_pos (mul_pos (sub_pos.mpr hx₁) (sub_pos.mpr hx₂))
      (sub_pos.mpr hstrict)
  refine ⟨selectedTripleEmbedding i j k hij hjk, ?_⟩
  rw [synthesizedToeplitz_minor_eq_area hε hij hjk]
  exact ne_of_gt (mul_pos
    (mul_pos
      (mul_pos (synthesizedCoefficientVector_pos hε _)
        (synthesizedCoefficientVector_pos hε _))
      (synthesizedCoefficientVector_pos hε _)) (by simpa [i, j, k] using harea))

namespace CompatibleSlopePattern

/-- Compatibility and the exclusion of a whole-ground-set interval force at least one strict
break in the canonical target-slope sequence. -/
theorem exists_unprescribedEquality {n : ℕ} (D : CompatibleRankThreeData n) :
    ∃ t : Fin (D.simplifiedSize - 2), ¬IsPrescribedEquality D t.val := by
  classical
  by_contra hnone
  have hall : ∀ t : Fin (D.simplifiedSize - 2), IsPrescribedEquality D t.val := by
    intro t
    by_contra ht
    exact hnone ⟨t, ht⟩
  have hsize : 0 < D.simplifiedSize - 2 := by
    have hm := D.simplifiedSize_ge_three
    omega
  let z : Fin (D.simplifiedSize - 2) := ⟨0, hsize⟩
  have hz := hall z
  change IsPrescribedEquality D 0 at hz
  obtain ⟨H₀, hH₀, hH₀left, hH₀right⟩ := hz
  have hleftZero : H₀.left.val = 0 := by omega
  have hreach : ∀ q : ℕ, q < D.simplifiedSize - 2 →
      ∃ H ∈ D.intervals, H = H₀ ∧ H.left.val ≤ q ∧ q + 2 ≤ H.right.val := by
    intro q hq
    induction q with
    | zero => exact ⟨H₀, hH₀, rfl, hH₀left, hH₀right⟩
    | succ q ih =>
        obtain ⟨Hprev, hHprev, hprevEq, hprevLeft, hprevRight⟩ := ih (by omega)
        have hnext := hall ⟨q + 1, by omega⟩
        change IsPrescribedEquality D (q + 1) at hnext
        obtain ⟨Hnext, hHnext, hnextLeft, hnextRight⟩ := hnext
        let x : Fin D.simplifiedSize := ⟨q + 1, by omega⟩
        let y : Fin D.simplifiedSize := ⟨q + 2, by omega⟩
        have hxPrev : x ∈ Hprev.points := by
          rw [SimplifiedInterval.mem_points]
          change Hprev.left.val ≤ q + 1 ∧ q + 1 ≤ Hprev.right.val
          omega
        have hyPrev : y ∈ Hprev.points := by
          rw [SimplifiedInterval.mem_points]
          change Hprev.left.val ≤ q + 2 ∧ q + 2 ≤ Hprev.right.val
          omega
        have hxNext : x ∈ Hnext.points := by
          rw [SimplifiedInterval.mem_points]
          change Hnext.left.val ≤ q + 1 ∧ q + 1 ≤ Hnext.right.val
          omega
        have hyNext : y ∈ Hnext.points := by
          rw [SimplifiedInterval.mem_points]
          change Hnext.left.val ≤ q + 2 ∧ q + 2 ≤ Hnext.right.val
          omega
        have hEq : Hprev = Hnext :=
          D.interval_eq_of_two_common hHprev hHnext (by simp [x, y])
            hxPrev hxNext hyPrev hyNext
        refine ⟨Hnext, hHnext, ?_, hnextLeft, hnextRight⟩
        exact hEq.symm.trans hprevEq
  have hlastIndex : D.simplifiedSize - 3 < D.simplifiedSize - 2 := by omega
  obtain ⟨Hlast, hHlast, hlastEq, hlastLeft, hlastRight⟩ :=
    hreach (D.simplifiedSize - 3) hlastIndex
  have hrightLast : H₀.right.val + 1 = D.simplifiedSize := by
    rw [hlastEq] at hlastRight
    have hrightBound := H₀.right.isLt
    omega
  rcases D.interval_not_whole H₀ hH₀ with hleft | hright
  · exact hleft hleftZero
  · exact hright hrightLast

/-- Hence the canonical target family contains a strict adjacent comparison. -/
theorem exists_targetSlope_strict {n : ℕ} (D : CompatibleRankThreeData n) :
    ∃ t : Fin (D.simplifiedSize - 2),
      targetSlope D (comparisonLeft D t) < targetSlope D (comparisonRight D t) := by
  obtain ⟨t, ht⟩ := exists_unprescribedEquality D
  have hindex : comparisonLeft D t ≤ comparisonRight D t := by
    apply Fin.mk_le_mk.mpr
    exact Nat.le_succ _
  refine ⟨t, lt_of_le_of_ne (targetSlope_monotone D hindex) ?_⟩
  exact (targetSlope_castSucc_eq_succ_iff D t).not.mpr ht

end CompatibleSlopePattern

/-- Every compatible datum admits a positive Toeplitz realization of its simplified slope
pattern.  Endpoint plateaux and loop translations are added after this core construction. -/
theorem exists_simplifiedPositiveCoreRealization {n : ℕ} (D : CompatibleRankThreeData n) :
    ∃ a : Fin ((D.simplifiedSize - 1) + 3) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧ HasFullRowRank (rankThreeToeplitz a) := by
  let s := CompatibleSlopePattern.targetSlope D
  have hs : IsPositiveMonotoneSlopeFamily s :=
    CompatibleSlopePattern.targetSlope_isPositiveMonotone D
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hN : 2 ≤ D.simplifiedSize - 1 := by
    have hm := D.simplifiedSize_ge_three
    omega
  have htnn : TotallyNonnegative
      (rankThreeToeplitz (synthesizedCoefficientVector s ε)) :=
    synthesizedToeplitz_totallyNonnegative hN hε hs.2
  obtain ⟨t, ht⟩ := CompatibleSlopePattern.exists_targetSlope_strict D
  have htBound : t.val + 1 < D.simplifiedSize - 1 := by omega
  have hstrict : s ⟨t.val, by omega⟩ < s ⟨t.val + 1, htBound⟩ := by
    simpa [s, CompatibleSlopePattern.comparisonLeft,
      CompatibleSlopePattern.comparisonRight] using ht
  have hrank : HasFullRowRank
      (rankThreeToeplitz (synthesizedCoefficientVector s ε)) :=
    synthesizedToeplitz_hasFullRowRank_of_strictSlope hε htBound hstrict
  exact ⟨synthesizedCoefficientVector s ε, htnn, hrank⟩

/-- The positive core realizes exactly the prescribed adjacent equality pattern, so its maximal
constant-slope runs are the interval blocks encoded by the compatible datum. -/
theorem exists_simplifiedPositiveCoreRealization_withPattern {n : ℕ}
    (D : CompatibleRankThreeData n) :
    ∃ ε : ℝ,
      IsAdmissibleSynthesisEpsilon (CompatibleSlopePattern.targetSlope D) ε ∧
        TotallyNonnegative
          (rankThreeToeplitz
            (synthesizedCoefficientVector (CompatibleSlopePattern.targetSlope D) ε)) ∧
        HasFullRowRank
          (rankThreeToeplitz
            (synthesizedCoefficientVector (CompatibleSlopePattern.targetSlope D) ε)) ∧
        ∀ t : Fin (D.simplifiedSize - 2),
          edgeSlope
              (ratioPointX
                (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε))
              (ratioPointY
                (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε)) t.val =
            edgeSlope
              (ratioPointX
                (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε))
              (ratioPointY
                (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε)) (t.val + 1) ↔
              CompatibleSlopePattern.IsPrescribedEquality D t.val := by
  let s := CompatibleSlopePattern.targetSlope D
  have hs : IsPositiveMonotoneSlopeFamily s :=
    CompatibleSlopePattern.targetSlope_isPositiveMonotone D
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hN : 2 ≤ D.simplifiedSize - 1 := by
    have hm := D.simplifiedSize_ge_three
    omega
  have htnn := synthesizedToeplitz_totallyNonnegative hN hε hs.2
  obtain ⟨t, ht⟩ := CompatibleSlopePattern.exists_targetSlope_strict D
  have htBound : t.val + 1 < D.simplifiedSize - 1 := by omega
  have hstrict : s ⟨t.val, by omega⟩ < s ⟨t.val + 1, htBound⟩ := by
    simpa [s, CompatibleSlopePattern.comparisonLeft,
      CompatibleSlopePattern.comparisonRight] using ht
  have hrank := synthesizedToeplitz_hasFullRowRank_of_strictSlope hε htBound hstrict
  refine ⟨ε, hε, htnn, hrank, ?_⟩
  intro u
  have hu₀ : u.val < D.simplifiedSize - 1 := by omega
  have hu₁ : u.val + 1 < D.simplifiedSize - 1 := by omega
  rw [finiteSynthesizedRatio_edgeSlope hε ⟨u.val, hu₀⟩,
    finiteSynthesizedRatio_edgeSlope hε ⟨u.val + 1, hu₁⟩]
  simpa [s, CompatibleSlopePattern.comparisonLeft,
    CompatibleSlopePattern.comparisonRight] using
      (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D u)

end

end ToeplitzPositroids.RankThree
