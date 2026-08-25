import ToeplitzPositroids.RankThree.OneSidedExactSupportTheorem
import Mathlib.Tactic

/-!
# Exact support for an initial endpoint plateau

This file identifies the zero oriented areas and the ordered compatible nonbases for the
loop-free construction with a nontrivial initial parallel class and singleton terminal class.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- The protected initial simplified chain has zero area exactly on one of the compatible
collinear intervals. -/
theorem initialProtected_area_eq_zero_iff_interval {n : ℕ}
    (D : CompatibleRankThreeData n) (hp : 1 < D.initialParallelSize)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.afterLeftProtection D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < D.simplifiedSize) :
    orientedArea
        (initialSimplifiedX (CompatibleBoundaryTargets.afterLeftProtection D) ε)
        (initialSimplifiedY (CompatibleBoundaryTargets.afterLeftProtection D) ε) i j k = 0 ↔
      ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val := by
  let s := CompatibleBoundaryTargets.afterLeftProtection D
  have hs := CompatibleBoundaryTargets.afterLeftProtection_isPositiveMonotone D
  have hx : StrictlyIncreasingUpTo (initialSimplifiedX s ε)
      (D.simplifiedSize - 2 + 2) := initialSimplifiedX_strict hε
  have hslopes : SlopesMonotoneUpTo (initialSimplifiedX s ε)
      (initialSimplifiedY s ε) (D.simplifiedSize - 2 + 2) :=
    initialSimplified_slopesMonotone hε hs
  rw [orientedArea_eq_zero_iff_slopesConstantBetween _ _ hx hslopes hij hjk (by omega),
    ratioSlopesConstantBetween_iff_adjacent]
  have hnoZero : ¬CompatibleSlopePattern.IsPrescribedEquality D 0 := by
    rintro ⟨H, hH, hleft, _⟩
    apply D.initial_endpoint_protected (Or.inr hp) H hH
    omega
  have hcomparisons : AdjacentSlopesEqualBetween
      (initialSimplifiedX s ε) (initialSimplifiedY s ε) i k ↔
      CompatibleSlopePattern.AllPrescribedBetween D i k := by
    constructor
    · intro h t hit htk
      by_cases ht : t = 0
      · subst t
        have heq := h 0 hit htk
        have hN : 0 < D.simplifiedSize - 2 := by
          have := D.simplifiedSize_ge_three
          omega
        rw [initialSimplified_edgeSlope_zero hε,
          initialSimplified_edgeSlope_succ hε ⟨0, hN⟩] at heq
        have hsmall := hε.2 ⟨0, hN⟩
        have hεpos := hε.1
        exfalso
        dsimp [s, CompatibleBoundaryTargets.afterLeftProtection] at heq hsmall
        nlinarith
      · have htPos : 0 < t := Nat.pos_of_ne_zero ht
        have htN : t < D.simplifiedSize - 2 := by omega
        have htPrevN : t - 1 < D.simplifiedSize - 2 := by omega
        have htEq : t - 1 + 1 = t := by omega
        have heq := h t hit htk
        have hleftSlope : edgeSlope (initialSimplifiedX s ε)
            (initialSimplifiedY s ε) t = s ⟨t - 1, htPrevN⟩ := by
          calc
            edgeSlope (initialSimplifiedX s ε) (initialSimplifiedY s ε) t =
                edgeSlope (initialSimplifiedX s ε) (initialSimplifiedY s ε)
                  (t - 1 + 1) := by rw [htEq]
            _ = s ⟨t - 1, htPrevN⟩ :=
              initialSimplified_edgeSlope_succ hε ⟨t - 1, htPrevN⟩
        have hrightSlope : edgeSlope (initialSimplifiedX s ε)
            (initialSimplifiedY s ε) (t + 1) = s ⟨t, htN⟩ :=
          initialSimplified_edgeSlope_succ hε ⟨t, htN⟩
        rw [hleftSlope, hrightSlope] at heq
        let u : Fin (D.simplifiedSize - 2) := ⟨t, htN⟩
        apply (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D u).mp
        simpa [s, CompatibleBoundaryTargets.afterLeftProtection, htEq,
          CompatibleSlopePattern.comparisonLeft,
          CompatibleSlopePattern.comparisonRight, u] using heq
    · intro h t hit htk
      by_cases ht : t = 0
      · subst t
        exact (hnoZero (h 0 hit htk)).elim
      · have htPos : 0 < t := Nat.pos_of_ne_zero ht
        have htN : t < D.simplifiedSize - 2 := by omega
        have htPrevN : t - 1 < D.simplifiedSize - 2 := by omega
        have htEq : t - 1 + 1 = t := by omega
        let u : Fin (D.simplifiedSize - 2) := ⟨t, htN⟩
        have heq := (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D u).mpr
          (h t hit htk)
        have hleftSlope : edgeSlope (initialSimplifiedX s ε)
            (initialSimplifiedY s ε) t = s ⟨t - 1, htPrevN⟩ := by
          calc
            edgeSlope (initialSimplifiedX s ε) (initialSimplifiedY s ε) t =
                edgeSlope (initialSimplifiedX s ε) (initialSimplifiedY s ε)
                  (t - 1 + 1) := by rw [htEq]
            _ = s ⟨t - 1, htPrevN⟩ :=
              initialSimplified_edgeSlope_succ hε ⟨t - 1, htPrevN⟩
        have hrightSlope : edgeSlope (initialSimplifiedX s ε)
            (initialSimplifiedY s ε) (t + 1) = s ⟨t, htN⟩ :=
          initialSimplified_edgeSlope_succ hε ⟨t, htN⟩
        rw [hleftSlope, hrightSlope]
        simpa [s, CompatibleBoundaryTargets.afterLeftProtection, htEq,
          CompatibleSlopePattern.comparisonLeft,
          CompatibleSlopePattern.comparisonRight, u] using heq
  rw [hcomparisons,
    CompatibleSlopePattern.allPrescribedBetween_iff_interval D (by omega) hk]

/-- For three increasing raw indices in the initial-plateau chart, zero area means either that
the first two indices belong to the repeated initial point or that their three distinct
simplified indices lie in one compatible interval. -/
theorem initialPlateau_area_eq_zero_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (hp : 1 < D.initialParallelSize)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.afterLeftProtection D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k)
    (hk : k < D.initialParallelSize + (D.simplifiedSize - 2) + 1) :
    orientedArea
        (ratioPointX (finiteInitialPlateauRatio D.initialParallelSize
          (CompatibleBoundaryTargets.afterLeftProtection D) ε))
        (ratioPointY (finiteInitialPlateauRatio D.initialParallelSize
          (CompatibleBoundaryTargets.afterLeftProtection D) ε)) i j k = 0 ↔
      j < D.initialParallelSize ∨
        ∃ H ∈ D.intervals,
          H.left.val ≤ (if i < D.initialParallelSize then 0
            else i - D.initialParallelSize + 1) ∧
          k - D.initialParallelSize + 1 ≤ H.right.val := by
  let p := D.initialParallelSize
  let s := CompatibleBoundaryTargets.afterLeftProtection D
  change orientedArea
      (ratioPointX (finiteInitialPlateauRatio p s ε))
      (ratioPointY (finiteInitialPlateauRatio p s ε)) i j k = 0 ↔
    j < p ∨ ∃ H ∈ D.intervals,
      H.left.val ≤ (if i < p then 0 else i - p + 1) ∧
      k - p + 1 ≤ H.right.val
  by_cases hjp : j < p
  · have hip : i < p := hij.trans hjp
    have hiPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := i) (by omega)
    have hjPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := j) (by omega)
    rw [if_pos hip] at hiPoint
    rw [if_pos hjp] at hjPoint
    have hx := congrArg Prod.fst (hiPoint.trans hjPoint.symm)
    have hy := congrArg Prod.snd (hiPoint.trans hjPoint.symm)
    change ratioPointX (finiteInitialPlateauRatio p s ε) i =
      ratioPointX (finiteInitialPlateauRatio p s ε) j at hx
    change ratioPointY (finiteInitialPlateauRatio p s ε) i =
      ratioPointY (finiteInitialPlateauRatio p s ε) j at hy
    rw [orientedArea, hx, hy]
    simp [hjp]
  · have hjge : p ≤ j := Nat.le_of_not_gt hjp
    have hkge : p ≤ k := hjge.trans hjk.le
    let I := if i < p then 0 else i - p + 1
    let J := j - p + 1
    let K := k - p + 1
    have hiPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := i) (by omega)
    have hjPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := j) (by omega)
    have hkPoint := finiteInitialPlateauRatio_point_eq_simplified
      (p := p) (s := s) (ε := ε) (j := k) (by omega)
    rw [if_neg hjp] at hjPoint
    rw [if_neg (not_lt_of_ge hkge)] at hkPoint
    have hiPointI :
        (ratioPointX (finiteInitialPlateauRatio p s ε) i,
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
    have hK : K < D.simplifiedSize := by dsimp [K, p]; omega
    have harea : orientedArea
        (ratioPointX (finiteInitialPlateauRatio p s ε))
        (ratioPointY (finiteInitialPlateauRatio p s ε)) i j k =
        orientedArea (initialSimplifiedX s ε) (initialSimplifiedY s ε) I J K := by
      rw [orientedArea]
      rw [show ratioPointX (finiteInitialPlateauRatio p s ε) i =
          initialSimplifiedX s ε I by exact congrArg Prod.fst hiPointI,
        show ratioPointY (finiteInitialPlateauRatio p s ε) i =
          initialSimplifiedY s ε I by exact congrArg Prod.snd hiPointI,
        show ratioPointX (finiteInitialPlateauRatio p s ε) j =
          initialSimplifiedX s ε J by exact congrArg Prod.fst hjPoint,
        show ratioPointY (finiteInitialPlateauRatio p s ε) j =
          initialSimplifiedY s ε J by exact congrArg Prod.snd hjPoint,
        show ratioPointX (finiteInitialPlateauRatio p s ε) k =
          initialSimplifiedX s ε K by exact congrArg Prod.fst hkPoint,
        show ratioPointY (finiteInitialPlateauRatio p s ε) k =
          initialSimplifiedY s ε K by exact congrArg Prod.snd hkPoint]
      rfl
    rw [harea, initialProtected_area_eq_zero_iff_interval D hp hε hIJ hJK hK]
    simp [hjp, I, K]

/-- Numeric simplification map in the initial-plateau, singleton-terminal case. -/
theorem simplifiedIndexNat_initialPlateau {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hq : D.terminalParallelSize = 1)
    (j : Fin n) :
    D.simplifiedIndexNat j =
      if j.val < D.initialParallelSize then 0
      else j.val - D.initialParallelSize + 1 := by
  have hg := D.groundSize_eq
  have hm := D.simplifiedSize_ge_three
  unfold CompatibleRankThreeData.simplifiedIndexNat
  simp only [CompatibleRankThreeData.middleStart,
    CompatibleRankThreeData.terminalStart, hleft, zero_add]
  split_ifs <;> omega

/-- In the loop-free initial-plateau case, the ordered compatible nonbasis condition has the
same numeric description as `initialPlateau_area_eq_zero_iff`. -/
theorem orderedCompatibleNonbasis_initialPlateau_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hq : D.terminalParallelSize = 1)
    (cols : Fin 3 ↪o Fin n) :
    OrderedCompatibleNonbasis D cols ↔
      (cols 1).val < D.initialParallelSize ∨
        ∃ H ∈ D.intervals,
          H.left.val ≤ (if (cols 0).val < D.initialParallelSize then 0
            else (cols 0).val - D.initialParallelSize + 1) ∧
          (cols 2).val - D.initialParallelSize + 1 ≤ H.right.val := by
  have hrightStart : D.rightLoopStart = n := by
    have h := D.rightLoopStart_add_rightLoopCount
    rw [hright, add_zero] at h
    exact h
  have hloop : ∀ j : Fin n, ¬D.IsLoop j := by
    intro j
    unfold CompatibleRankThreeData.IsLoop CompatibleRankThreeData.IsLeftLoop
      CompatibleRankThreeData.IsRightLoop
    rw [hrightStart]
    simp [hleft]
  have hinit_iff : ∀ j : Fin n,
      D.IsInitialParallel j ↔ j.val < D.initialParallelSize := by
    intro j
    unfold CompatibleRankThreeData.IsInitialParallel CompatibleRankThreeData.middleStart
    simp [hleft]
  have htermPair : ∀ {a b : Fin n}, a ≠ b →
      ¬(D.IsTerminalParallel a ∧ D.IsTerminalParallel b) := by
    intro a b hab hpairs
    have hterminalEnd : D.rightLoopStart = D.terminalStart + 1 := by
      unfold CompatibleRankThreeData.rightLoopStart
      rw [hq]
    unfold CompatibleRankThreeData.IsTerminalParallel at hpairs
    rw [hterminalEnd] at hpairs
    apply hab
    apply Fin.ext
    omega
  have hidx : ∀ j : Fin n, D.simplifiedIndexNat j =
      if j.val < D.initialParallelSize then 0
      else j.val - D.initialParallelSize + 1 :=
    simplifiedIndexNat_initialPlateau D hleft hright hq
  have h01 : cols 0 ≠ cols 1 := ne_of_lt (cols.strictMono (by decide))
  have h02 : cols 0 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  have h12 : cols 1 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  unfold OrderedCompatibleNonbasis
  simp only [hloop, false_or, htermPair h01, htermPair h02, htermPair h12]
  constructor
  · rintro (hinit | hcoll)
    · left
      rcases hinit with h | h | h
      · exact (hinit_iff _).mp h.2
      · exact (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).trans
          ((hinit_iff _).mp h.2)
      · exact (hinit_iff _).mp h.1
    · rcases hcoll with ⟨h01', h02', h12', H, hH, h0, _, h2⟩
      have h1After : D.initialParallelSize ≤ (cols 1).val := by
        by_contra hbefore
        have h0Before : (cols 0).val < D.initialParallelSize :=
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).trans
            (Nat.lt_of_not_ge hbefore)
        apply h01'
        apply Fin.ext
        change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 1)
        rw [hidx, hidx, if_pos h0Before,
          if_pos (Nat.lt_of_not_ge hbefore)]
      have h2After : D.initialParallelSize ≤ (cols 2).val :=
        h1After.trans
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le
      right
      refine ⟨H, hH, ?_, ?_⟩
      · rw [SimplifiedInterval.mem_points] at h0
        have hv := Fin.mk_le_mk.mp h0.1
        change H.left.val ≤ D.simplifiedIndexNat (cols 0) at hv
        rw [hidx] at hv
        exact hv
      · rw [SimplifiedInterval.mem_points] at h2
        have hv := Fin.mk_le_mk.mp h2.2
        change D.simplifiedIndexNat (cols 2) ≤ H.right.val at hv
        rw [hidx, if_neg (not_lt_of_ge h2After)] at hv
        exact hv
  · rintro (hinit | ⟨H, hH, hL, hR⟩)
    · left
      left
      exact ⟨(hinit_iff _).2
          ((Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).trans hinit),
        (hinit_iff _).2 hinit⟩
    · by_cases h1Before : (cols 1).val < D.initialParallelSize
      · left
        left
        exact ⟨(hinit_iff _).2
            ((Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).trans
              h1Before),
          (hinit_iff _).2 h1Before⟩
      · right
        have h1After : D.initialParallelSize ≤ (cols 1).val :=
          Nat.le_of_not_gt h1Before
        have h2After : D.initialParallelSize ≤ (cols 2).val :=
          h1After.trans
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le
        let I := if (cols 0).val < D.initialParallelSize then 0
          else (cols 0).val - D.initialParallelSize + 1
        let J := (cols 1).val - D.initialParallelSize + 1
        let K := (cols 2).val - D.initialParallelSize + 1
        have h01val : (cols 0).val < (cols 1).val :=
          Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))
        have h12val : (cols 1).val < (cols 2).val :=
          Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))
        have hIJ : I < J := by
          by_cases h0Before : (cols 0).val < D.initialParallelSize
          · simp only [I, J, if_pos h0Before]
            exact Nat.zero_lt_succ _
          · have h0After : D.initialParallelSize ≤ (cols 0).val :=
              Nat.le_of_not_gt h0Before
            simp only [I, J, if_neg h0Before]
            exact Nat.add_lt_add_right
              ((Nat.sub_lt_sub_iff_right h0After).mpr h01val) 1
        have hJK : J < K := by
          dsimp [J, K]
          exact Nat.add_lt_add_right
            ((Nat.sub_lt_sub_iff_right h1After).mpr h12val) 1
        have hIK : I < K := hIJ.trans hJK
        refine ⟨?_, ?_, ?_, H, hH, ?_, ?_, ?_⟩
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 1) at hv
          rw [hidx, hidx, if_neg h1Before] at hv
          change I = J at hv
          exact (ne_of_lt hIJ) hv
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 2) at hv
          rw [hidx, hidx, if_neg (not_lt_of_ge h2After)] at hv
          change I = K at hv
          exact (ne_of_lt hIK) hv
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 1) = D.simplifiedIndexNat (cols 2) at hv
          rw [hidx, hidx, if_neg h1Before,
            if_neg (not_lt_of_ge h2After)] at hv
          change J = K at hv
          exact (ne_of_lt hJK) hv
        all_goals rw [SimplifiedInterval.mem_points]
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 0)
            rw [hidx]
            exact hL
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 0) ≤ H.right.val
            rw [hidx]
            exact hIK.le.trans hR
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 1)
            rw [hidx, if_neg h1Before]
            exact hL.trans hIJ.le
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 1) ≤ H.right.val
            rw [hidx, if_neg h1Before]
            exact hJK.le.trans hR
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 2)
            rw [hidx, if_neg (not_lt_of_ge h2After)]
            exact hL.trans hIK.le
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 2) ≤ H.right.val
            rw [hidx, if_neg (not_lt_of_ge h2After)]
            exact hR

end

end ToeplitzPositroids.RankThree
