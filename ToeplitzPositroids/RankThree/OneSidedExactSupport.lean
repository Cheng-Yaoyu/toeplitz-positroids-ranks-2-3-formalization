import ToeplitzPositroids.RankThree.OneSidedRawRealization
import ToeplitzPositroids.RankThree.SupportUniqueness
import Mathlib.Tactic

/-!
# Exact support for one-sided realizations

This file adds the positive endpoint-plateau cases and packages exact maximal-minor support.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

namespace CompatibleBoundaryTargets

/-- Remove only the terminal protected edge. -/
def beforeRightProtection {n : ℕ} (D : CompatibleRankThreeData n) :
    Fin (D.simplifiedSize - 2) → ℝ :=
  fun i ↦ CompatibleSlopePattern.targetSlope D ⟨i.val, by omega⟩

theorem beforeRightProtection_isPositiveMonotone {n : ℕ}
    (D : CompatibleRankThreeData n) :
    IsPositiveMonotoneSlopeFamily (beforeRightProtection D) := by
  constructor
  · exact fun i ↦ CompatibleSlopePattern.targetSlope_pos D _
  · intro i j hij
    exact CompatibleSlopePattern.targetSlope_monotone D
      (Fin.mk_le_mk.mpr (show i.val ≤ j.val from hij))

end CompatibleBoundaryTargets

/-- Extend a positive synthesized coefficient vector through `q` terminal-class columns by
freezing its final ratio. -/
def positiveCoefficientVectorExtra {N : ℕ} (q : ℕ) (s : Fin N → ℝ) (ε : ℝ) :
    Fin ((N + 1 + q) + 2) → ℝ :=
  fun k ↦ recoveredCoefficient (finiteSynthesizedRatio s ε) k.val

/-- Every point from the positive terminal cutoff onward is the same. -/
theorem finiteSynthesizedRatio_terminalPoint_eq {N : ℕ} (s : Fin N → ℝ) (ε : ℝ)
    {j : ℕ} (hj : N + 1 ≤ j) :
    (ratioPointX (finiteSynthesizedRatio s ε) j,
      ratioPointY (finiteSynthesizedRatio s ε) j) =
      (synthesizedRatio s ε (N + 1), synthesizedRatio s ε (N + 1) ^ 2) := by
  simp only [ratioPointX, ratioPointY, finiteSynthesizedRatio]
  rw [min_eq_right hj, min_eq_right (by omega : N + 1 ≤ j + 1)]
  simp [pow_two]

/-- The frozen positive terminal point is vertically above the preceding point. -/
theorem finiteSynthesizedRatio_terminalVertical {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) :
    ratioPointX (finiteSynthesizedRatio s ε) N =
        ratioPointX (finiteSynthesizedRatio s ε) (N + 1) ∧
      ratioPointY (finiteSynthesizedRatio s ε) N <
        ratioPointY (finiteSynthesizedRatio s ε) (N + 1) := by
  have hR : 0 < finiteSynthesizedRatio s ε (N + 1) :=
    finiteSynthesizedRatio_pos hε _
  have hprev : finiteSynthesizedRatio s ε N < finiteSynthesizedRatio s ε (N + 1) := by
    rw [finiteSynthesizedRatio_eq s ε (by omega), finiteSynthesizedRatio_eq s ε (by omega)]
    exact synthesizedRatio_strictMonoOn hε (by omega) (by omega)
  simp only [ratioPointX, ratioPointY]
  have hfreeze : finiteSynthesizedRatio s ε (N + 2) =
      finiteSynthesizedRatio s ε (N + 1) := by simp [finiteSynthesizedRatio]
  rw [hfreeze]
  exact ⟨rfl, mul_lt_mul_of_pos_right hprev hR⟩

/-- The positive chain with repeated terminal points has nonnegative oriented areas. -/
theorem finiteSynthesizedRatio_extendedAreasNonnegative {N q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (hs : Monotone s) :
    AreasNonnegativeUpTo (ratioPointX (finiteSynthesizedRatio s ε))
      (ratioPointY (finiteSynthesizedRatio s ε)) (N + 1 + q) := by
  intro i j k hij hjk hk
  by_cases hkBase : k < N + 1
  · exact finiteSynthesizedRatio_areasNonnegative hε hs hij hjk hkBase
  by_cases hjTerminal : N + 1 ≤ j
  · have hjPoint := finiteSynthesizedRatio_terminalPoint_eq s ε hjTerminal
    have hkPoint := finiteSynthesizedRatio_terminalPoint_eq s ε (by omega : N + 1 ≤ k)
    have hx := congrArg Prod.fst (hjPoint.trans hkPoint.symm)
    have hy := congrArg Prod.snd (hjPoint.trans hkPoint.symm)
    change ratioPointX (finiteSynthesizedRatio s ε) j =
      ratioPointX (finiteSynthesizedRatio s ε) k at hx
    change ratioPointY (finiteSynthesizedRatio s ε) j =
      ratioPointY (finiteSynthesizedRatio s ε) k at hy
    rw [orientedArea, hx, hy]
    ring_nf
    exact le_rfl
  · have hkPoint := finiteSynthesizedRatio_terminalPoint_eq s ε (by omega : N + 1 ≤ k)
    have hstarPoint := finiteSynthesizedRatio_terminalPoint_eq s ε
      (show N + 1 ≤ N + 1 by omega)
    have hkx := congrArg Prod.fst (hkPoint.trans hstarPoint.symm)
    have hky := congrArg Prod.snd (hkPoint.trans hstarPoint.symm)
    change ratioPointX (finiteSynthesizedRatio s ε) k =
      ratioPointX (finiteSynthesizedRatio s ε) (N + 1) at hkx
    change ratioPointY (finiteSynthesizedRatio s ε) k =
      ratioPointY (finiteSynthesizedRatio s ε) (N + 1) at hky
    rw [orientedArea, hkx, hky, ← orientedArea]
    by_cases hjLast : j = N
    · subst j
      have hv := finiteSynthesizedRatio_terminalVertical hε
      rw [orientedArea, hv.1]
      have hxPos : 0 < ratioPointX (finiteSynthesizedRatio s ε) N -
          ratioPointX (finiteSynthesizedRatio s ε) i :=
        sub_pos.mpr (finiteSynthesizedRatio_pointX_strict hε hij (by omega))
      have hp := mul_pos hxPos (sub_pos.mpr hv.2)
      nlinarith
    · have hjStrict : j < N := by omega
      rw [orientedArea_vertical_replace _ _ (finiteSynthesizedRatio_terminalVertical hε).1.symm]
      exact add_nonneg
        (finiteSynthesizedRatio_areasNonnegative hε hs hij hjStrict (by omega))
        (mul_nonneg
          (sub_pos.mpr (finiteSynthesizedRatio_pointX_strict hε hij (by omega))).le
          (sub_pos.mpr (finiteSynthesizedRatio_terminalVertical hε).2).le)

/-- The positive extended coefficient vector remains `TN₂`. -/
theorem positiveToeplitzExtra_tnUpTo_two {N q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hsize : 3 ≤ N + 1 + q) (hε : IsAdmissibleSynthesisEpsilon s ε) :
    TNUpTo (rankThreeToeplitz (positiveCoefficientVectorExtra q s ε)) 2 := by
  rw [rankThreeToeplitz_tnUpTo_two_iff hsize]
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact (recoveredCoefficient_pos (finiteSynthesizedRatio_pos hε) k.val).le
  · rw [hasIntervalPositiveSupport_iff]
    intro i j k hi hj hik hkj
    exact recoveredCoefficient_pos (finiteSynthesizedRatio_pos hε) k.val
  · intro k
    simpa [positiveCoefficientVectorExtra, pow_two, mul_comm] using
      (recoveredCoefficient_logConcave (finiteSynthesizedRatio_pos hε)
        (finiteSynthesizedRatio_mono_succ hε) k.val)

/-- Positive extended columns retain the ratio-point normalization. -/
theorem positiveToeplitzExtra_column {N q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : Fin (N + 1 + q)) :
    (rankThreeToeplitz (positiveCoefficientVectorExtra q s ε)).col j =
      positiveCoefficientVectorExtra q s ε j.succ.succ •
        ![1, ratioPointX (finiteSynthesizedRatio s ε) j.val,
          ratioPointY (finiteSynthesizedRatio s ε) j.val] := by
  let r := finiteSynthesizedRatio s ε
  have hr : ∀ t, 0 < r t := finiteSynthesizedRatio_pos hε
  have h₁ := recoveredCoefficient_eq_ratio_mul_succ hr (j.val + 1)
  have h₀ := recoveredCoefficient_eq_ratio_mul_succ hr j.val
  change (fun i ↦ rankThreeToeplitz (positiveCoefficientVectorExtra q s ε) i j) = _
  rw [rankThreeToeplitz_column]
  funext i
  fin_cases i
  · simp [positiveCoefficientVectorExtra]
  · simp only [Pi.smul_apply, smul_eq_mul]
    change recoveredCoefficient r (j.val + 1) =
      recoveredCoefficient r (j.val + 2) * r (j.val + 1)
    nlinarith [h₁]
  · simp only [Pi.smul_apply, smul_eq_mul]
    change recoveredCoefficient r j.val =
      recoveredCoefficient r (j.val + 2) * (r j.val * r (j.val + 1))
    rw [h₀, h₁]
    ring

/-- Positive extended maximal minors factor through extended ratio-point areas. -/
theorem positiveToeplitzExtra_minor_eq_area {N q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) {i j k : Fin (N + 1 + q)}
    (hij : i < j) (hjk : j < k) :
    orderedMinor (rankThreeToeplitz (positiveCoefficientVectorExtra q s ε)) (allRows 3)
        (selectedTripleEmbedding i j k hij hjk) =
      positiveCoefficientVectorExtra q s ε i.succ.succ *
        positiveCoefficientVectorExtra q s ε j.succ.succ *
        positiveCoefficientVectorExtra q s ε k.succ.succ *
          orientedArea (ratioPointX (finiteSynthesizedRatio s ε))
            (ratioPointY (finiteSynthesizedRatio s ε)) i.val j.val k.val := by
  rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det,
    positiveToeplitzExtra_column hε, positiveToeplitzExtra_column hε,
    positiveToeplitzExtra_column hε, threeColumnMatrix_det_smul,
    ratioPoint_threeColumnMatrix_det]

/-- The positive terminal-plateau extension is totally nonnegative. -/
theorem positiveToeplitzExtra_totallyNonnegative {N q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hsize : 3 ≤ N + 1 + q) (hε : IsAdmissibleSynthesisEpsilon s ε)
    (hs : Monotone s) :
    TotallyNonnegative (rankThreeToeplitz (positiveCoefficientVectorExtra q s ε)) := by
  rw [totallyNonnegative_fin_three_iff]
  refine ⟨positiveToeplitzExtra_tnUpTo_two hsize hε, ?_⟩
  intro cols
  have h01 : cols 0 < cols 1 := cols.strictMono (by decide)
  have h12 : cols 1 < cols 2 := cols.strictMono (by decide)
  have harea := finiteSynthesizedRatio_extendedAreasNonnegative (q := q) hε hs
    (show (cols 0).val < (cols 1).val from h01)
    (show (cols 1).val < (cols 2).val from h12) (cols 2).isLt
  have hminor := positiveToeplitzExtra_minor_eq_area hε h01 h12
  rw [selectedTripleEmbedding_eq cols] at hminor
  rw [hminor]
  have htop : ∀ j : Fin (N + 1 + q),
      0 < positiveCoefficientVectorExtra q s ε j.succ.succ := by
    intro j
    exact recoveredCoefficient_pos (finiteSynthesizedRatio_pos hε) (j.val + 2)
  exact mul_nonneg (mul_nonneg (mul_nonneg (htop (cols 0)).le (htop (cols 1)).le)
    (htop (cols 2)).le) harea

/-- A nonempty finite-slope chain followed by a terminal vertical point is full row rank. -/
theorem positiveToeplitzExtra_hasFullRowRank {N q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hN : 1 ≤ N) (hq : 1 ≤ q) (hε : IsAdmissibleSynthesisEpsilon s ε) :
    HasFullRowRank (rankThreeToeplitz (positiveCoefficientVectorExtra q s ε)) := by
  let i : Fin (N + 1 + q) := ⟨0, by omega⟩
  let j : Fin (N + 1 + q) := ⟨N, by omega⟩
  let k : Fin (N + 1 + q) := ⟨N + 1, by omega⟩
  have hij : i < j := Fin.mk_lt_mk.mpr hN
  have hjk : j < k := Fin.mk_lt_mk.mpr (Nat.lt_succ_self N)
  have hv := finiteSynthesizedRatio_terminalVertical hε
  have hx : 0 < ratioPointX (finiteSynthesizedRatio s ε) N -
      ratioPointX (finiteSynthesizedRatio s ε) 0 :=
    sub_pos.mpr (finiteSynthesizedRatio_pointX_strict hε (by omega) (by omega))
  have harea : 0 < orientedArea (ratioPointX (finiteSynthesizedRatio s ε))
      (ratioPointY (finiteSynthesizedRatio s ε)) 0 N (N + 1) := by
    rw [orientedArea, hv.1]
    have hp := mul_pos hx (sub_pos.mpr hv.2)
    nlinarith
  refine ⟨selectedTripleEmbedding i j k hij hjk, ?_⟩
  rw [positiveToeplitzExtra_minor_eq_area hε hij hjk]
  exact ne_of_gt (mul_pos
    (mul_pos
      (mul_pos
        (recoveredCoefficient_pos (finiteSynthesizedRatio_pos hε) (i.val + 2))
        (recoveredCoefficient_pos (finiteSynthesizedRatio_pos hε) (j.val + 2)))
      (recoveredCoefficient_pos (finiteSynthesizedRatio_pos hε) (k.val + 2)))
    (by simpa [i, j, k] using harea))

/-- Loop-free compatible data with a singleton initial class and nontrivial terminal class have
the intended terminal-plateau TNN full-rank model. -/
theorem exists_noLoop_singletonInitial_terminalPlateau {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : D.initialParallelSize = 1)
    (hq : 1 < D.terminalParallelSize) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧ HasFullRowRank (rankThreeToeplitz a) := by
  let s := CompatibleBoundaryTargets.beforeRightProtection D
  have hs := CompatibleBoundaryTargets.beforeRightProtection_isPositiveMonotone D
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hN : 1 ≤ D.simplifiedSize - 2 := by
    have hm := D.simplifiedSize_ge_three
    omega
  have hsizeMatrix : 3 ≤ (D.simplifiedSize - 2) + 1 + D.terminalParallelSize := by omega
  have hsize : (D.simplifiedSize - 2) + 1 + D.terminalParallelSize = n := by
    have hg := D.groundSize_eq
    have hm := D.simplifiedSize_ge_three
    omega
  let a₀ := positiveCoefficientVectorExtra D.terminalParallelSize s ε
  let a : Fin (n + 2) → ℝ := castRankThreeCoefficients hsize a₀
  refine ⟨a, ?_, ?_⟩
  · rw [show rankThreeToeplitz a = castColumnCount hsize (rankThreeToeplitz a₀) by
      exact rankThreeToeplitz_castRankThreeCoefficients hsize a₀]
    exact TotallyNonnegative.castColumnCount
      (positiveToeplitzExtra_totallyNonnegative hsizeMatrix hε hs.2)
  · rw [show rankThreeToeplitz a = castColumnCount hsize (rankThreeToeplitz a₀) by
      exact rankThreeToeplitz_castRankThreeCoefficients hsize a₀]
    exact HasFullRowRank.castColumnCount
      (positiveToeplitzExtra_hasFullRowRank hN hq.le hε)

/-- Freeze an initial-plateau ratio construction after its last required finite ratio. -/
def finiteInitialPlateauRatio {N : ℕ} (p : ℕ) (s : Fin N → ℝ) (ε : ℝ) (j : ℕ) : ℝ :=
  initialPlateauRatio p s ε (min j (p + N + 1))

theorem finiteInitialPlateauRatio_eq {N : ℕ} (p : ℕ) (s : Fin N → ℝ) (ε : ℝ)
    {j : ℕ} (hj : j ≤ p + N + 1) :
    finiteInitialPlateauRatio p s ε j = initialPlateauRatio p s ε j := by
  simp [finiteInitialPlateauRatio, min_eq_left hj]

/-- The explicit simplified point sequence: one plateau vertex, then the synthesized tail. -/
def initialSimplifiedX {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) : ℕ → ℝ
  | 0 => ε
  | j + 1 => synthesizedPointX s ε j

def initialSimplifiedY {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) : ℕ → ℝ
  | 0 => ε ^ 2
  | j + 1 => synthesizedPointY s ε j

/-- The explicit simplified initial-plateau chain has strictly increasing abscissae. -/
theorem initialSimplifiedX_strict {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) :
    StrictlyIncreasingUpTo (initialSimplifiedX s ε) (N + 2) := by
  intro i j hij hjN
  rcases i with _ | i
  · rcases j with _ | j
    · omega
    · simp only [initialSimplifiedX, synthesizedPointX]
      exact synthesizedRatio_strictMonoOn hε (by omega) (by omega)
  · rcases j with _ | j
    · omega
    · simp only [initialSimplifiedX]
      exact synthesizedRatio_strictMonoOn hε (by omega) (by omega)

/-- The first simplified edge has slope `ε`; all later edges have the prescribed slopes. -/
theorem initialSimplified_edgeSlope_zero {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) :
    edgeSlope (initialSimplifiedX s ε) (initialSimplifiedY s ε) 0 = ε := by
  norm_num [edgeSlope, chordSlope, initialSimplifiedX, initialSimplifiedY,
    synthesizedPointX, synthesizedPointY, synthesizedRatio]
  field_simp [hε.1.ne']

theorem initialSimplified_edgeSlope_succ {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : Fin N) :
    edgeSlope (initialSimplifiedX s ε) (initialSimplifiedY s ε) (j.val + 1) = s j := by
  rw [edgeSlope, chordSlope]
  simp only [initialSimplifiedX, initialSimplifiedY]
  exact synthesizedPoint_edgeSlope hε j

/-- The initial simplified chain is convex. -/
theorem initialSimplified_slopesMonotone {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (hs : IsPositiveMonotoneSlopeFamily s) :
    SlopesMonotoneUpTo (initialSimplifiedX s ε) (initialSimplifiedY s ε) (N + 2) := by
  intro i j hij hjN
  rcases i with _ | i
  · rw [initialSimplified_edgeSlope_zero hε]
    by_cases hj0 : j = 0
    · subst j
      exact le_of_eq (initialSimplified_edgeSlope_zero hε).symm
    · let q : Fin N := ⟨j - 1, by omega⟩
      have hjEq : j = q.val + 1 := by simp [q]; omega
      rw [hjEq, initialSimplified_edgeSlope_succ hε q]
      have hsmall := hε.2 q
      have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith [hε.1]
  · let p : Fin N := ⟨i, by omega⟩
    let q : Fin N := ⟨j - 1, by omega⟩
    rw [show i + 1 = p.val + 1 by rfl, initialSimplified_edgeSlope_succ hε p]
    rw [show j = q.val + 1 by simp [q]; omega, initialSimplified_edgeSlope_succ hε q]
    apply hs.2
    apply Fin.mk_le_mk.mpr
    change i ≤ j - 1
    omega

theorem initialSimplified_areasNonnegative {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (hs : IsPositiveMonotoneSlopeFamily s) :
    AreasNonnegativeUpTo (initialSimplifiedX s ε) (initialSimplifiedY s ε) (N + 2) :=
  areasNonnegativeUpTo_of_slopesMonotoneUpTo _ _
    (initialSimplifiedX_strict hε) (initialSimplified_slopesMonotone hε hs)

/-- Raw initial-plateau points map to the explicit simplified point sequence. -/
theorem finiteInitialPlateauRatio_point_eq_simplified {N p : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    {j : ℕ} (hj : j < p + N + 1) :
    (ratioPointX (finiteInitialPlateauRatio p s ε) j,
      ratioPointY (finiteInitialPlateauRatio p s ε) j) =
      if j < p then (initialSimplifiedX s ε 0, initialSimplifiedY s ε 0)
      else (initialSimplifiedX s ε (j - p + 1), initialSimplifiedY s ε (j - p + 1)) := by
  by_cases hjp : j < p
  · rw [if_pos hjp]
    have hpoint := initialPlateau_point_eq s ε hjp
    rw [ratioPointX, ratioPointY,
      finiteInitialPlateauRatio_eq p s ε hj.le,
      finiteInitialPlateauRatio_eq p s ε (by omega)]
    simpa [initialSimplifiedX, initialSimplifiedY] using hpoint
  · rw [if_neg hjp]
    have hjle : j ≤ p + N + 1 := hj.le
    have hj1le : j + 1 ≤ p + N + 1 := by omega
    rw [ratioPointX, ratioPointY,
      finiteInitialPlateauRatio_eq p s ε hjle,
      finiteInitialPlateauRatio_eq p s ε hj1le]
    have hjform : j = p + (j - p) := by omega
    rw [hjform, initialPlateauRatio_add, show p + (j - p) + 1 = p + (j - p + 1) by omega,
      initialPlateauRatio_add]
    simp [initialSimplifiedX, initialSimplifiedY, synthesizedPointX, synthesizedPointY]

/-- Before a terminal vertical append, all raw initial-plateau areas are nonnegative. -/
theorem finiteInitialPlateauRatio_baseAreasNonnegative {N p : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε)
    (hs : IsPositiveMonotoneSlopeFamily s) :
    AreasNonnegativeUpTo (ratioPointX (finiteInitialPlateauRatio p s ε))
      (ratioPointY (finiteInitialPlateauRatio p s ε)) (p + N + 1) := by
  intro i j k hij hjk hk
  by_cases hjp : j < p
  · have hip : i < p := hij.trans hjp
    have hiPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := i)
      (hij.trans (hjk.trans hk))
    have hjPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := j)
      (hjk.trans hk)
    rw [if_pos hip] at hiPoint
    rw [if_pos hjp] at hjPoint
    have hx := congrArg Prod.fst (hiPoint.trans hjPoint.symm)
    have hy := congrArg Prod.snd (hiPoint.trans hjPoint.symm)
    change ratioPointX (finiteInitialPlateauRatio p s ε) i =
      ratioPointX (finiteInitialPlateauRatio p s ε) j at hx
    change ratioPointY (finiteInitialPlateauRatio p s ε) i =
      ratioPointY (finiteInitialPlateauRatio p s ε) j at hy
    rw [orientedArea, hx, hy]
    ring_nf
    exact le_rfl
  · have hjge : p ≤ j := Nat.le_of_not_gt hjp
    have hkge : p ≤ k := hjge.trans (hjk.le)
    let I := if i < p then 0 else i - p + 1
    let J := j - p + 1
    let K := k - p + 1
    have hiPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := i)
      (hij.trans (hjk.trans hk))
    have hjPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := j)
      (hjk.trans hk)
    have hkPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := k) hk
    rw [if_neg hjp] at hjPoint
    rw [if_neg (not_lt_of_ge hkge)] at hkPoint
    have hiPointI : (ratioPointX (finiteInitialPlateauRatio p s ε) i,
        ratioPointY (finiteInitialPlateauRatio p s ε) i) =
          (initialSimplifiedX s ε I, initialSimplifiedY s ε I) := by
      by_cases hip : i < p
      · simpa [I, hip] using hiPoint
      · simpa [I, hip] using hiPoint
    change (ratioPointX (finiteInitialPlateauRatio p s ε) j,
      ratioPointY (finiteInitialPlateauRatio p s ε) j) =
        (initialSimplifiedX s ε J, initialSimplifiedY s ε J) at hjPoint
    change (ratioPointX (finiteInitialPlateauRatio p s ε) k,
      ratioPointY (finiteInitialPlateauRatio p s ε) k) =
        (initialSimplifiedX s ε K, initialSimplifiedY s ε K) at hkPoint
    have hIJ : I < J := by
      dsimp [I, J]
      split_ifs <;> omega
    have hJK : J < K := by dsimp [J, K]; omega
    have hK : K < N + 2 := by dsimp [K]; omega
    have harea := initialSimplified_areasNonnegative hε hs hIJ hJK hK
    rw [orientedArea]
    rw [show ratioPointX (finiteInitialPlateauRatio p s ε) i = initialSimplifiedX s ε I by
      exact congrArg Prod.fst hiPointI,
      show ratioPointY (finiteInitialPlateauRatio p s ε) i = initialSimplifiedY s ε I by
        exact congrArg Prod.snd hiPointI,
      show ratioPointX (finiteInitialPlateauRatio p s ε) j = initialSimplifiedX s ε J by
        exact congrArg Prod.fst hjPoint,
      show ratioPointY (finiteInitialPlateauRatio p s ε) j = initialSimplifiedY s ε J by
        exact congrArg Prod.snd hjPoint,
      show ratioPointX (finiteInitialPlateauRatio p s ε) k = initialSimplifiedX s ε K by
        exact congrArg Prod.fst hkPoint,
      show ratioPointY (finiteInitialPlateauRatio p s ε) k = initialSimplifiedY s ε K by
        exact congrArg Prod.snd hkPoint]
    simpa [orientedArea] using harea

/-- The finite initial-plateau ratios are positive. -/
theorem finiteInitialPlateauRatio_pos {N p : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : ℕ) :
    0 < finiteInitialPlateauRatio p s ε j := by
  unfold finiteInitialPlateauRatio initialPlateauRatio
  split_ifs
  · exact hε.1
  · apply synthesizedRatio_pos_of_lt hε
    omega

/-- The finite initial-plateau ratios are weakly increasing. -/
theorem finiteInitialPlateauRatio_mono_succ {N p : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : ℕ) :
    finiteInitialPlateauRatio p s ε j ≤ finiteInitialPlateauRatio p s ε (j + 1) := by
  by_cases hjCut : j < p + N + 1
  · rw [finiteInitialPlateauRatio_eq p s ε hjCut.le,
      finiteInitialPlateauRatio_eq p s ε (by omega)]
    by_cases hjp : j < p
    · simp [initialPlateauRatio, hjp.le, (Nat.succ_le_iff).2 hjp]
    · have hjge : p ≤ j := Nat.le_of_not_gt hjp
      rw [show j = p + (j - p) by omega,
        show p + (j - p) + 1 = p + (j - p + 1) by omega,
        initialPlateauRatio_add, initialPlateauRatio_add]
      exact (synthesizedRatio_strictMonoOn hε (by omega) (by omega)).le
  · have hjge : p + N + 1 ≤ j := Nat.le_of_not_gt hjCut
    simp [finiteInitialPlateauRatio, min_eq_right hjge,
      min_eq_right (by omega : p + N + 1 ≤ j + 1)]

/-- All raw points at or after the initial construction cutoff are the same terminal point. -/
theorem finiteInitialPlateauRatio_terminalPoint_eq {N p : ℕ}
    (s : Fin N → ℝ) (ε : ℝ) {j : ℕ} (hj : p + N + 1 ≤ j) :
    (ratioPointX (finiteInitialPlateauRatio p s ε) j,
      ratioPointY (finiteInitialPlateauRatio p s ε) j) =
      (initialPlateauRatio p s ε (p + N + 1),
        initialPlateauRatio p s ε (p + N + 1) ^ 2) := by
  simp only [ratioPointX, ratioPointY, finiteInitialPlateauRatio]
  rw [min_eq_right hj, min_eq_right (by omega : p + N + 1 ≤ j + 1)]
  simp [pow_two]

/-- The terminal point is vertically above the final point of the initial simplified chain. -/
theorem finiteInitialPlateauRatio_terminalVertical {N p : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) :
    ratioPointX (finiteInitialPlateauRatio p s ε) (p + N) =
        ratioPointX (finiteInitialPlateauRatio p s ε) (p + N + 1) ∧
      ratioPointY (finiteInitialPlateauRatio p s ε) (p + N) <
        ratioPointY (finiteInitialPlateauRatio p s ε) (p + N + 1) := by
  have hR := finiteInitialPlateauRatio_pos (p := p) hε (p + N + 1)
  have hprev : finiteInitialPlateauRatio p s ε (p + N) <
      finiteInitialPlateauRatio p s ε (p + N + 1) := by
    rw [finiteInitialPlateauRatio_eq p s ε (by omega),
      finiteInitialPlateauRatio_eq p s ε (by omega),
      initialPlateauRatio_add,
      show p + N + 1 = p + (N + 1) by omega, initialPlateauRatio_add]
    exact synthesizedRatio_strictMonoOn hε (by omega) (by omega)
  simp only [ratioPointX, ratioPointY]
  have hfreeze : finiteInitialPlateauRatio p s ε (p + N + 2) =
      finiteInitialPlateauRatio p s ε (p + N + 1) := by
    simp [finiteInitialPlateauRatio]
  rw [hfreeze]
  exact ⟨rfl, mul_lt_mul_of_pos_right hprev hR⟩

/-- Raw initial and terminal plateaux preserve nonnegativity of every oriented area. -/
theorem finiteInitialPlateauRatio_extendedAreasNonnegative {N p q : ℕ}
    {s : Fin N → ℝ} {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon s ε)
    (hs : IsPositiveMonotoneSlopeFamily s) :
    AreasNonnegativeUpTo (ratioPointX (finiteInitialPlateauRatio p s ε))
      (ratioPointY (finiteInitialPlateauRatio p s ε)) (p + N + 1 + q) := by
  intro i j k hij hjk hk
  by_cases hkBase : k < p + N + 1
  · exact finiteInitialPlateauRatio_baseAreasNonnegative hε hs hij hjk hkBase
  by_cases hjTerminal : p + N + 1 ≤ j
  · have hjPoint := finiteInitialPlateauRatio_terminalPoint_eq (p := p) s ε
      (j := j) hjTerminal
    have hkPoint := finiteInitialPlateauRatio_terminalPoint_eq (p := p) s ε
      (j := k) (by omega)
    have hx := congrArg Prod.fst (hjPoint.trans hkPoint.symm)
    have hy := congrArg Prod.snd (hjPoint.trans hkPoint.symm)
    change ratioPointX (finiteInitialPlateauRatio p s ε) j =
      ratioPointX (finiteInitialPlateauRatio p s ε) k at hx
    change ratioPointY (finiteInitialPlateauRatio p s ε) j =
      ratioPointY (finiteInitialPlateauRatio p s ε) k at hy
    rw [orientedArea, hx, hy]
    ring_nf
    exact le_rfl
  · have hkPoint := finiteInitialPlateauRatio_terminalPoint_eq (p := p) s ε
      (j := k) (by omega)
    have hsPoint := finiteInitialPlateauRatio_terminalPoint_eq (p := p) s ε
      (j := p + N + 1) (le_rfl)
    have hkx := congrArg Prod.fst (hkPoint.trans hsPoint.symm)
    have hky := congrArg Prod.snd (hkPoint.trans hsPoint.symm)
    change ratioPointX (finiteInitialPlateauRatio p s ε) k =
      ratioPointX (finiteInitialPlateauRatio p s ε) (p + N + 1) at hkx
    change ratioPointY (finiteInitialPlateauRatio p s ε) k =
      ratioPointY (finiteInitialPlateauRatio p s ε) (p + N + 1) at hky
    rw [orientedArea, hkx, hky, ← orientedArea]
    have hrMono : Monotone (finiteInitialPlateauRatio p s ε) :=
      monotone_nat_of_le_succ (finiteInitialPlateauRatio_mono_succ hε)
    have hxMono : Monotone (ratioPointX (finiteInitialPlateauRatio p s ε)) := by
      intro a b hab
      exact hrMono (Nat.add_le_add_right hab 1)
    by_cases hjLast : j = p + N
    · subst j
      have hv := finiteInitialPlateauRatio_terminalVertical (p := p) hε
      rw [orientedArea, hv.1]
      have hxNonneg : 0 ≤ ratioPointX (finiteInitialPlateauRatio p s ε) (p + N) -
          ratioPointX (finiteInitialPlateauRatio p s ε) i :=
        sub_nonneg.mpr (hxMono hij.le)
      nlinarith [mul_nonneg hxNonneg (sub_pos.mpr hv.2).le]
    · have hjBase : j < p + N := by omega
      rw [orientedArea_vertical_replace _ _
        (finiteInitialPlateauRatio_terminalVertical (p := p) hε).1.symm]
      exact add_nonneg
        (finiteInitialPlateauRatio_baseAreasNonnegative hε hs hij hjBase (by omega))
        (mul_nonneg (sub_nonneg.mpr (hxMono hij.le))
          (sub_pos.mpr (finiteInitialPlateauRatio_terminalVertical (p := p) hε).2).le)

/-- Coefficients recovered from an initial plateau and optional terminal plateau. -/
def initialCoefficientVectorExtra {N : ℕ} (p q : ℕ) (s : Fin N → ℝ) (ε : ℝ) :
    Fin ((p + N + 1 + q) + 2) → ℝ :=
  fun k ↦ recoveredCoefficient (finiteInitialPlateauRatio p s ε) k.val

/-- The combined endpoint-plateau coefficient vector is `TN₂`. -/
theorem initialToeplitzExtra_tnUpTo_two {N p q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hsize : 3 ≤ p + N + 1 + q) (hε : IsAdmissibleSynthesisEpsilon s ε) :
    TNUpTo (rankThreeToeplitz (initialCoefficientVectorExtra p q s ε)) 2 := by
  rw [rankThreeToeplitz_tnUpTo_two_iff hsize]
  refine ⟨?_, ?_, ?_⟩
  · exact fun k ↦ (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) k.val).le
  · rw [hasIntervalPositiveSupport_iff]
    exact fun i j k hi hj hik hkj ↦ recoveredCoefficient_pos
      (finiteInitialPlateauRatio_pos hε) k.val
  · intro k
    simpa [initialCoefficientVectorExtra, pow_two, mul_comm] using
      (recoveredCoefficient_logConcave (finiteInitialPlateauRatio_pos hε)
        (finiteInitialPlateauRatio_mono_succ hε) k.val)

/-- Combined endpoint-plateau columns retain their ratio-point normalization. -/
theorem initialToeplitzExtra_column {N p q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : Fin (p + N + 1 + q)) :
    (rankThreeToeplitz (initialCoefficientVectorExtra p q s ε)).col j =
      initialCoefficientVectorExtra p q s ε j.succ.succ •
        ![1, ratioPointX (finiteInitialPlateauRatio p s ε) j.val,
          ratioPointY (finiteInitialPlateauRatio p s ε) j.val] := by
  let r := finiteInitialPlateauRatio p s ε
  have hr : ∀ t, 0 < r t := finiteInitialPlateauRatio_pos hε
  have h₁ := recoveredCoefficient_eq_ratio_mul_succ hr (j.val + 1)
  have h₀ := recoveredCoefficient_eq_ratio_mul_succ hr j.val
  change (fun i ↦ rankThreeToeplitz (initialCoefficientVectorExtra p q s ε) i j) = _
  rw [rankThreeToeplitz_column]
  funext i
  fin_cases i
  · simp [initialCoefficientVectorExtra]
  · simp only [Pi.smul_apply, smul_eq_mul]
    change recoveredCoefficient r (j.val + 1) = recoveredCoefficient r (j.val + 2) * r (j.val + 1)
    nlinarith [h₁]
  · simp only [Pi.smul_apply, smul_eq_mul]
    change recoveredCoefficient r j.val =
      recoveredCoefficient r (j.val + 2) * (r j.val * r (j.val + 1))
    rw [h₀, h₁]
    ring

theorem initialToeplitzExtra_minor_eq_area {N p q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) {i j k : Fin (p + N + 1 + q)}
    (hij : i < j) (hjk : j < k) :
    orderedMinor (rankThreeToeplitz (initialCoefficientVectorExtra p q s ε)) (allRows 3)
        (selectedTripleEmbedding i j k hij hjk) =
      initialCoefficientVectorExtra p q s ε i.succ.succ *
        initialCoefficientVectorExtra p q s ε j.succ.succ *
        initialCoefficientVectorExtra p q s ε k.succ.succ *
          orientedArea (ratioPointX (finiteInitialPlateauRatio p s ε))
            (ratioPointY (finiteInitialPlateauRatio p s ε)) i.val j.val k.val := by
  rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det,
    initialToeplitzExtra_column hε, initialToeplitzExtra_column hε,
    initialToeplitzExtra_column hε, threeColumnMatrix_det_smul,
    ratioPoint_threeColumnMatrix_det]

/-- Every combined endpoint-plateau Toeplitz matrix is totally nonnegative. -/
theorem initialToeplitzExtra_totallyNonnegative {N p q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hsize : 3 ≤ p + N + 1 + q) (hε : IsAdmissibleSynthesisEpsilon s ε)
    (hs : IsPositiveMonotoneSlopeFamily s) :
    TotallyNonnegative (rankThreeToeplitz (initialCoefficientVectorExtra p q s ε)) := by
  rw [totallyNonnegative_fin_three_iff]
  refine ⟨initialToeplitzExtra_tnUpTo_two hsize hε, ?_⟩
  intro cols
  have h01 : cols 0 < cols 1 := cols.strictMono (by decide)
  have h12 : cols 1 < cols 2 := cols.strictMono (by decide)
  have harea := finiteInitialPlateauRatio_extendedAreasNonnegative (p := p) (q := q) hε hs
    (show (cols 0).val < (cols 1).val from h01)
    (show (cols 1).val < (cols 2).val from h12) (cols 2).isLt
  have hminor := initialToeplitzExtra_minor_eq_area hε h01 h12
  rw [selectedTripleEmbedding_eq cols] at hminor
  rw [hminor]
  have htop : ∀ j : Fin (p + N + 1 + q),
      0 < initialCoefficientVectorExtra p q s ε j.succ.succ := by
    exact fun j ↦ recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) (j.val + 2)
  exact mul_nonneg (mul_nonneg (mul_nonneg (htop (cols 0)).le (htop (cols 1)).le)
    (htop (cols 2)).le) harea

/-- Without a terminal plateau, the first two simplified edges give a positive basis. -/
theorem initialToeplitz_hasFullRowRank {N p : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hN : 1 ≤ N) (hp : 1 ≤ p) (hε : IsAdmissibleSynthesisEpsilon s ε) :
    HasFullRowRank (rankThreeToeplitz (initialCoefficientVectorExtra p 0 s ε)) := by
  let i : Fin (p + N + 1) := ⟨p - 1, by omega⟩
  let j : Fin (p + N + 1) := ⟨p, by omega⟩
  let k : Fin (p + N + 1) := ⟨p + 1, by omega⟩
  have hij : i < j := Fin.mk_lt_mk.mpr (by omega)
  have hjk : j < k := Fin.mk_lt_mk.mpr (by omega)
  have hareaSimple : 0 < orientedArea (initialSimplifiedX s ε)
      (initialSimplifiedY s ε) 0 1 2 := by
    rw [orientedArea_consecutive _ _
      (ne_of_gt (initialSimplifiedX_strict hε (by omega) (by omega)))
      (ne_of_gt (initialSimplifiedX_strict hε (by omega) (by omega)))]
    rw [initialSimplified_edgeSlope_zero hε,
      initialSimplified_edgeSlope_succ hε ⟨0, hN⟩]
    have hsmall := hε.2 ⟨0, hN⟩
    have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact mul_pos
      (mul_pos
        (sub_pos.mpr (initialSimplifiedX_strict hε (by omega) (by omega)))
        (sub_pos.mpr (initialSimplifiedX_strict hε (by omega) (by omega))))
      (by nlinarith [hε.1])
  have hiPoint := finiteInitialPlateauRatio_point_eq_simplified
    (p := p) (s := s) (ε := ε) (j := i.val) (by simp [i]; omega)
  have hjPoint := finiteInitialPlateauRatio_point_eq_simplified
    (p := p) (s := s) (ε := ε) (j := j.val) (by simp [j])
  have hkPoint := finiteInitialPlateauRatio_point_eq_simplified
    (p := p) (s := s) (ε := ε) (j := k.val) (by simp [k]; omega)
  have hip : i.val < p := by simp [i]; omega
  have hjp : ¬j.val < p := by simp [j]
  have hkp : ¬k.val < p := by simp [k]
  rw [if_pos hip] at hiPoint
  rw [if_neg hjp] at hjPoint
  rw [if_neg hkp] at hkPoint
  have hjIndex : j.val - p + 1 = 1 := by simp [j]
  have hkIndex : k.val - p + 1 = 2 := by simp [k]
  rw [hjIndex] at hjPoint
  rw [hkIndex] at hkPoint
  change (ratioPointX (finiteInitialPlateauRatio p s ε) i.val,
      ratioPointY (finiteInitialPlateauRatio p s ε) i.val) =
    (initialSimplifiedX s ε 0, initialSimplifiedY s ε 0) at hiPoint
  change (ratioPointX (finiteInitialPlateauRatio p s ε) j.val,
      ratioPointY (finiteInitialPlateauRatio p s ε) j.val) =
    (initialSimplifiedX s ε 1, initialSimplifiedY s ε 1) at hjPoint
  change (ratioPointX (finiteInitialPlateauRatio p s ε) k.val,
      ratioPointY (finiteInitialPlateauRatio p s ε) k.val) =
    (initialSimplifiedX s ε 2, initialSimplifiedY s ε 2) at hkPoint
  have hareaRaw : 0 < orientedArea (ratioPointX (finiteInitialPlateauRatio p s ε))
      (ratioPointY (finiteInitialPlateauRatio p s ε)) i.val j.val k.val := by
    rw [orientedArea]
    rw [show ratioPointX (finiteInitialPlateauRatio p s ε) i.val = initialSimplifiedX s ε 0 by
        exact congrArg Prod.fst hiPoint,
      show ratioPointY (finiteInitialPlateauRatio p s ε) i.val = initialSimplifiedY s ε 0 by
        exact congrArg Prod.snd hiPoint,
      show ratioPointX (finiteInitialPlateauRatio p s ε) j.val = initialSimplifiedX s ε 1 by
        exact congrArg Prod.fst hjPoint,
      show ratioPointY (finiteInitialPlateauRatio p s ε) j.val = initialSimplifiedY s ε 1 by
        exact congrArg Prod.snd hjPoint,
      show ratioPointX (finiteInitialPlateauRatio p s ε) k.val = initialSimplifiedX s ε 2 by
        exact congrArg Prod.fst hkPoint,
      show ratioPointY (finiteInitialPlateauRatio p s ε) k.val = initialSimplifiedY s ε 2 by
        exact congrArg Prod.snd hkPoint]
    simpa [orientedArea] using hareaSimple
  refine ⟨selectedTripleEmbedding i j k hij hjk, ?_⟩
  rw [initialToeplitzExtra_minor_eq_area hε hij hjk]
  exact ne_of_gt (mul_pos
    (mul_pos
      (mul_pos
        (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) (i.val + 2))
        (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) (j.val + 2)))
      (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) (k.val + 2))) hareaRaw)

/-- With a terminal plateau, the terminal vertical edge supplies a positive basis. -/
theorem initialToeplitzExtra_hasFullRowRank {N p q : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hε : IsAdmissibleSynthesisEpsilon s ε) :
    HasFullRowRank (rankThreeToeplitz (initialCoefficientVectorExtra p q s ε)) := by
  let i : Fin (p + N + 1 + q) := ⟨p - 1, by omega⟩
  let j : Fin (p + N + 1 + q) := ⟨p + N, by omega⟩
  let k : Fin (p + N + 1 + q) := ⟨p + N + 1, by omega⟩
  have hij : i < j := Fin.mk_lt_mk.mpr (by omega)
  have hjk : j < k := Fin.mk_lt_mk.mpr (by omega)
  have hv := finiteInitialPlateauRatio_terminalVertical (p := p) hε
  have hx : 0 < ratioPointX (finiteInitialPlateauRatio p s ε) (p + N) -
      ratioPointX (finiteInitialPlateauRatio p s ε) (p - 1) := by
    have hiPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := p - 1) (by omega)
    rw [if_pos (by omega)] at hiPoint
    have hiX : ratioPointX (finiteInitialPlateauRatio p s ε) (p - 1) = ε := by
      simpa [initialSimplifiedX] using congrArg Prod.fst hiPoint
    rw [hiX, ratioPointX, finiteInitialPlateauRatio_eq p s ε (by omega),
      show p + N + 1 = p + (N + 1) by omega, initialPlateauRatio_add]
    have hlt : synthesizedRatio s ε 0 < synthesizedRatio s ε (N + 1) :=
      synthesizedRatio_strictMonoOn hε (by omega) (by omega)
    simpa using hlt
  have harea : 0 < orientedArea (ratioPointX (finiteInitialPlateauRatio p s ε))
      (ratioPointY (finiteInitialPlateauRatio p s ε)) (p - 1) (p + N) (p + N + 1) := by
    rw [orientedArea, hv.1]
    have hpArea := mul_pos hx (sub_pos.mpr hv.2)
    nlinarith
  refine ⟨selectedTripleEmbedding i j k hij hjk, ?_⟩
  rw [initialToeplitzExtra_minor_eq_area hε hij hjk]
  exact ne_of_gt (mul_pos
    (mul_pos
      (mul_pos
        (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) (i.val + 2))
        (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) (j.val + 2)))
      (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) (k.val + 2)))
    (by simpa [i, j, k] using harea))

theorem exists_noLoop_initialPlateau_singletonTerminal {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : 1 < D.initialParallelSize)
    (hq : D.terminalParallelSize = 1) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧ HasFullRowRank (rankThreeToeplitz a) := by
  let s := CompatibleBoundaryTargets.afterLeftProtection D
  have hs := CompatibleBoundaryTargets.afterLeftProtection_isPositiveMonotone D
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hN : 1 ≤ D.simplifiedSize - 2 := by
    have hm := D.simplifiedSize_ge_three
    omega
  have hmatrixSize : 3 ≤ D.initialParallelSize + (D.simplifiedSize - 2) + 1 := by omega
  have hsize : D.initialParallelSize + (D.simplifiedSize - 2) + 1 = n := by
    have hg := D.groundSize_eq
    omega
  let a₀ := initialCoefficientVectorExtra D.initialParallelSize 0 s ε
  let a : Fin (n + 2) → ℝ := castRankThreeCoefficients hsize a₀
  refine ⟨a, ?_, ?_⟩
  · rw [show rankThreeToeplitz a = castColumnCount hsize (rankThreeToeplitz a₀) by
      exact rankThreeToeplitz_castRankThreeCoefficients hsize a₀]
    exact TotallyNonnegative.castColumnCount
      (initialToeplitzExtra_totallyNonnegative hmatrixSize hε hs)
  · rw [show rankThreeToeplitz a = castColumnCount hsize (rankThreeToeplitz a₀) by
      exact rankThreeToeplitz_castRankThreeCoefficients hsize a₀]
    exact HasFullRowRank.castColumnCount
      (initialToeplitz_hasFullRowRank hN hp.le hε)

theorem exists_noLoop_bothEndpointPlateaux {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : 1 < D.initialParallelSize)
    (hq : 1 < D.terminalParallelSize) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧ HasFullRowRank (rankThreeToeplitz a) := by
  let s := CompatibleBoundaryTargets.betweenProtectedEndpoints D
  have hs := CompatibleBoundaryTargets.betweenProtectedEndpoints_isPositiveMonotone D
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hmatrixSize : 3 ≤ D.initialParallelSize + (D.simplifiedSize - 3) + 1 +
      D.terminalParallelSize := by omega
  have hsize : D.initialParallelSize + (D.simplifiedSize - 3) + 1 +
      D.terminalParallelSize = n := by
    have hg := D.groundSize_eq
    have hm := D.simplifiedSize_ge_three
    omega
  let a₀ := initialCoefficientVectorExtra D.initialParallelSize D.terminalParallelSize s ε
  let a : Fin (n + 2) → ℝ := castRankThreeCoefficients hsize a₀
  refine ⟨a, ?_, ?_⟩
  · rw [show rankThreeToeplitz a = castColumnCount hsize (rankThreeToeplitz a₀) by
      exact rankThreeToeplitz_castRankThreeCoefficients hsize a₀]
    exact TotallyNonnegative.castColumnCount
      (initialToeplitzExtra_totallyNonnegative hmatrixSize hε hs)
  · rw [show rankThreeToeplitz a = castColumnCount hsize (rankThreeToeplitz a₀) by
      exact rankThreeToeplitz_castRankThreeCoefficients hsize a₀]
    exact HasFullRowRank.castColumnCount
      (initialToeplitzExtra_hasFullRowRank hp.le hq.le hε)

/-- All four loop-free endpoint-class combinations have the endpoint-aware TNN full-rank
Toeplitz construction. -/
theorem exists_noLoop_endpointAware_realization {n : ℕ} (D : CompatibleRankThreeData n)
    (hleft : D.leftLoopCount = 0) (hright : D.rightLoopCount = 0) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧ HasFullRowRank (rankThreeToeplitz a) := by
  have hpLe : 1 ≤ D.initialParallelSize := D.initialParallelSize_pos
  have hqLe : 1 ≤ D.terminalParallelSize := D.terminalParallelSize_pos
  rcases hpLe.eq_or_lt with hp | hp
  · rcases hqLe.eq_or_lt with hq | hq
    · have hcount : (D.simplifiedSize - 1) + 1 = n := by
        have hg := D.groundSize_eq
        have hm := D.simplifiedSize_ge_three
        omega
      obtain ⟨a₀, htnn, hrank⟩ := exists_simplifiedPositiveCoreRealization D
      let a : Fin (n + 2) → ℝ := castRankThreeCoefficients hcount a₀
      refine ⟨a, ?_, ?_⟩
      · rw [show rankThreeToeplitz a = castColumnCount hcount (rankThreeToeplitz a₀) by
          exact rankThreeToeplitz_castRankThreeCoefficients hcount a₀]
        exact TotallyNonnegative.castColumnCount htnn
      · rw [show rankThreeToeplitz a = castColumnCount hcount (rankThreeToeplitz a₀) by
          exact rankThreeToeplitz_castRankThreeCoefficients hcount a₀]
        exact HasFullRowRank.castColumnCount hrank
    · exact exists_noLoop_singletonInitial_terminalPlateau D hleft hright hp.symm hq
  · rcases hqLe.eq_or_lt with hq | hq
    · exact exists_noLoop_initialPlateau_singletonTerminal D hleft hright hp hq.symm
    · exact exists_noLoop_bothEndpointPlateaux D hleft hright hp hq

namespace CompatibleSlopePattern

/-- Every adjacent comparison needed between vertices `i` and `k` is prescribed. -/
def AllPrescribedBetween {n : ℕ} (D : CompatibleRankThreeData n) (i k : ℕ) : Prop :=
  ∀ t : ℕ, i ≤ t → t + 2 ≤ k → IsPrescribedEquality D t

/-- One prescribed interval supplies every comparison between any two of its vertices. -/
theorem allPrescribedBetween_of_interval {n : ℕ} (D : CompatibleRankThreeData n)
    {i k : ℕ} {H : SimplifiedInterval D.simplifiedSize} (hH : H ∈ D.intervals)
    (hi : H.left.val ≤ i) (hk : k ≤ H.right.val) :
    AllPrescribedBetween D i k := by
  intro t hit htk
  exact ⟨H, hH, hi.trans hit, htk.trans hk⟩

/-- A consecutive chain of prescribed comparisons belongs to one compatible interval. -/
theorem exists_interval_of_allPrescribedBetween {n : ℕ} (D : CompatibleRankThreeData n)
    {i k : ℕ} (hik : i + 2 ≤ k) (hkSize : k < D.simplifiedSize)
    (hall : AllPrescribedBetween D i k) :
    ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val := by
  classical
  obtain ⟨H₀, hH₀, hleft₀, hright₀⟩ := hall i le_rfl (by omega)
  have hreach : ∀ u : ℕ, i ≤ u → u + 2 ≤ k →
      ∃ H ∈ D.intervals, H = H₀ ∧ H.left.val ≤ i ∧ u + 2 ≤ H.right.val := by
    intro u hiu huk
    induction u, hiu using Nat.le_induction with
    | base => exact ⟨H₀, hH₀, rfl, hleft₀, hright₀⟩
    | succ u hiu ih =>
        obtain ⟨Hprev, hHprev, hprevEq, hprevLeft, hprevRight⟩ := ih (by omega)
        obtain ⟨Hnext, hHnext, hnextLeft, hnextRight⟩ := hall (u + 1) (by omega) (by omega)
        let x : Fin D.simplifiedSize := ⟨u + 1, by omega⟩
        let y : Fin D.simplifiedSize := ⟨u + 2, by omega⟩
        have hxPrev : x ∈ Hprev.points := by
          rw [SimplifiedInterval.mem_points]
          change Hprev.left.val ≤ u + 1 ∧ u + 1 ≤ Hprev.right.val
          omega
        have hyPrev : y ∈ Hprev.points := by
          rw [SimplifiedInterval.mem_points]
          change Hprev.left.val ≤ u + 2 ∧ u + 2 ≤ Hprev.right.val
          omega
        have hxNext : x ∈ Hnext.points := by
          rw [SimplifiedInterval.mem_points]
          change Hnext.left.val ≤ u + 1 ∧ u + 1 ≤ Hnext.right.val
          omega
        have hyNext : y ∈ Hnext.points := by
          rw [SimplifiedInterval.mem_points]
          change Hnext.left.val ≤ u + 2 ∧ u + 2 ≤ Hnext.right.val
          omega
        have hEq := D.interval_eq_of_two_common hHprev hHnext (by simp [x, y])
          hxPrev hxNext hyPrev hyNext
        have hleft : Hnext.left.val ≤ i := by
          rw [← hEq]
          exact hprevLeft
        exact ⟨Hnext, hHnext, hEq.symm.trans hprevEq, hleft, hnextRight⟩
  obtain ⟨H, hH, hEq, hleft, hright⟩ := hreach (k - 2) (by omega) (by omega)
  exact ⟨H, hH, hleft, by omega⟩

/-- Prescribed comparisons are equivalent to containment in one compatible interval. -/
theorem allPrescribedBetween_iff_interval {n : ℕ} (D : CompatibleRankThreeData n)
    {i k : ℕ} (hik : i + 2 ≤ k) (hkSize : k < D.simplifiedSize) :
    AllPrescribedBetween D i k ↔
      ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val := by
  constructor
  · exact exists_interval_of_allPrescribedBetween D hik hkSize
  · rintro ⟨H, hH, hi, hk⟩
    exact allPrescribedBetween_of_interval D hH hi hk

end CompatibleSlopePattern

end

end ToeplitzPositroids.RankThree
