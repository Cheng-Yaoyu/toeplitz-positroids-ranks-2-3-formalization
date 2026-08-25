import ToeplitzPositroids.RankThree.InitialPlateauSupport
import ToeplitzPositroids.RankThree.BothPlateauxSupport
import ToeplitzPositroids.RankThree.LeftLoopSupport
import ToeplitzPositroids.RankThree.ReversedCompatibleData
import Mathlib.Tactic

/-!
# Exact one-sided realization

This file completes the endpoint-plateau and loop-boundary support instances.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- In the terminal-protected slice, finite slope constancy is still exactly the compatible
interval condition away from the protected final vertex. -/
theorem beforeRight_area_eq_zero_iff_interval {n : ℕ} (D : CompatibleRankThreeData n)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.beforeRightProtection D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k + 1 < D.simplifiedSize) :
    orientedArea
        (ratioPointX (finiteSynthesizedRatio
          (CompatibleBoundaryTargets.beforeRightProtection D) ε))
        (ratioPointY (finiteSynthesizedRatio
          (CompatibleBoundaryTargets.beforeRightProtection D) ε)) i j k = 0 ↔
      ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val := by
  let s := CompatibleBoundaryTargets.beforeRightProtection D
  have hs := CompatibleBoundaryTargets.beforeRightProtection_isPositiveMonotone D
  have hx : StrictlyIncreasingUpTo
      (ratioPointX (finiteSynthesizedRatio s ε)) (D.simplifiedSize - 2 + 1) := by
    intro a b hab hb
    exact finiteSynthesizedRatio_pointX_strict hε hab hb
  have hmono : SlopesMonotoneUpTo
      (ratioPointX (finiteSynthesizedRatio s ε))
      (ratioPointY (finiteSynthesizedRatio s ε)) (D.simplifiedSize - 2 + 1) := by
    intro a b hab hb
    exact finiteSynthesizedRatio_slopesMonotone hε hs.2 hab hb
  rw [orientedArea_eq_zero_iff_slopesConstantBetween _ _ hx hmono hij hjk (by omega),
    ratioSlopesConstantBetween_iff_adjacent]
  have hcomparisons : AdjacentSlopesEqualBetween
      (ratioPointX (finiteSynthesizedRatio s ε))
      (ratioPointY (finiteSynthesizedRatio s ε)) i k ↔
      CompatibleSlopePattern.AllPrescribedBetween D i k := by
    constructor
    · intro h t hit htk
      have ht0 : t < D.simplifiedSize - 2 := by omega
      have ht1 : t + 1 < D.simplifiedSize - 2 := by omega
      have heq := h t hit htk
      rw [finiteSynthesizedRatio_edgeSlope hε ⟨t, ht0⟩,
        finiteSynthesizedRatio_edgeSlope hε ⟨t + 1, ht1⟩] at heq
      let u : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
      exact (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D u).mp (by
        simpa [s, CompatibleBoundaryTargets.beforeRightProtection,
          CompatibleSlopePattern.comparisonLeft,
          CompatibleSlopePattern.comparisonRight, u] using heq)
    · intro h t hit htk
      have ht0 : t < D.simplifiedSize - 2 := by omega
      have ht1 : t + 1 < D.simplifiedSize - 2 := by omega
      let u : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
      have heq := (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D u).mpr
        (h t hit htk)
      rw [finiteSynthesizedRatio_edgeSlope hε ⟨t, ht0⟩,
        finiteSynthesizedRatio_edgeSlope hε ⟨t + 1, ht1⟩]
      simpa [s, CompatibleBoundaryTargets.beforeRightProtection,
        CompatibleSlopePattern.comparisonLeft,
        CompatibleSlopePattern.comparisonRight, u] using heq
  rw [hcomparisons,
    CompatibleSlopePattern.allPrescribedBetween_iff_interval D (by omega) (by omega)]

/-- A terminal plateau contributes zeros only through repeated terminal classes; triples with one
terminal point have strictly positive area. -/
theorem terminalPlateau_area_eq_zero_iff {n : ℕ} (D : CompatibleRankThreeData n)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.beforeRightProtection D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    orientedArea
        (ratioPointX (finiteSynthesizedRatio
          (CompatibleBoundaryTargets.beforeRightProtection D) ε))
        (ratioPointY (finiteSynthesizedRatio
          (CompatibleBoundaryTargets.beforeRightProtection D) ε)) i j k = 0 ↔
      D.simplifiedSize - 1 ≤ j ∨
      (k < D.simplifiedSize - 1 ∧
        ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val) := by
  let s := CompatibleBoundaryTargets.beforeRightProtection D
  let N := D.simplifiedSize - 2
  have hm := D.simplifiedSize_ge_three
  have hcut : N + 1 = D.simplifiedSize - 1 := by dsimp [N]; omega
  by_cases hjTerm : N + 1 ≤ j
  · have hjPoint := finiteSynthesizedRatio_terminalPoint_eq s ε (j := j) hjTerm
    have hkPoint := finiteSynthesizedRatio_terminalPoint_eq s ε (j := k) (by omega)
    have hx := congrArg Prod.fst (hjPoint.trans hkPoint.symm)
    have hy := congrArg Prod.snd (hjPoint.trans hkPoint.symm)
    change ratioPointX (finiteSynthesizedRatio s ε) j =
      ratioPointX (finiteSynthesizedRatio s ε) k at hx
    change ratioPointY (finiteSynthesizedRatio s ε) j =
      ratioPointY (finiteSynthesizedRatio s ε) k at hy
    rw [orientedArea, hx, hy]
    constructor
    · intro _
      left
      omega
    · intro _
      ring
  · have hjBase : j ≤ N := by omega
    by_cases hkTerm : N + 1 ≤ k
    · have hkPoint := finiteSynthesizedRatio_terminalPoint_eq s ε (j := k) hkTerm
      have hsPoint := finiteSynthesizedRatio_terminalPoint_eq s ε (j := N + 1) le_rfl
      have hkx := congrArg Prod.fst (hkPoint.trans hsPoint.symm)
      have hky := congrArg Prod.snd (hkPoint.trans hsPoint.symm)
      change ratioPointX (finiteSynthesizedRatio s ε) k =
        ratioPointX (finiteSynthesizedRatio s ε) (N + 1) at hkx
      change ratioPointY (finiteSynthesizedRatio s ε) k =
        ratioPointY (finiteSynthesizedRatio s ε) (N + 1) at hky
      have hvertical := finiteSynthesizedRatio_terminalVertical hε
      have hbase : 0 ≤ orientedArea (ratioPointX (finiteSynthesizedRatio s ε))
          (ratioPointY (finiteSynthesizedRatio s ε)) i j N := by
        by_cases hjN : j = N
        · subst j
          simp [orientedArea]
        · exact finiteSynthesizedRatio_areasNonnegative hε
            (CompatibleBoundaryTargets.beforeRightProtection_isPositiveMonotone D).2
            hij (by omega) (by omega)
      have hrect : 0 <
          (ratioPointX (finiteSynthesizedRatio s ε) j -
            ratioPointX (finiteSynthesizedRatio s ε) i) *
          (ratioPointY (finiteSynthesizedRatio s ε) (N + 1) -
            ratioPointY (finiteSynthesizedRatio s ε) N) :=
        mul_pos
          (sub_pos.mpr (finiteSynthesizedRatio_pointX_strict hε hij (by omega)))
          (sub_pos.mpr hvertical.2)
      have hpositive : 0 < orientedArea (ratioPointX (finiteSynthesizedRatio s ε))
          (ratioPointY (finiteSynthesizedRatio s ε)) i j k := by
        rw [orientedArea, hkx, hky, ← orientedArea,
          orientedArea_vertical_replace _ _ hvertical.1.symm]
        linarith
      constructor
      · intro hz
        exact (ne_of_gt hpositive hz).elim
      · rintro (h | ⟨hk', H, hH, hL, hR⟩)
        · omega
        · omega
    · have hkBase : k < N + 1 := by omega
      rw [beforeRight_area_eq_zero_iff_interval D hε hij hjk (by omega)]
      constructor
      · intro h
        right
        exact ⟨by omega, h⟩
      · rintro (h | ⟨_, h⟩)
        · omega
        · exact h

/-- Numeric simplification map in the singleton-initial/terminal-plateau case. -/
theorem simplifiedIndexNat_terminalPlateau {n : ℕ} (D : CompatibleRankThreeData n)
    (hleft : D.leftLoopCount = 0) (hp : D.initialParallelSize = 1)
    (j : Fin n) :
    D.simplifiedIndexNat j =
      if j.val < D.simplifiedSize - 1 then j.val else D.simplifiedSize - 1 := by
  unfold CompatibleRankThreeData.simplifiedIndexNat
  simp only [CompatibleRankThreeData.middleStart, CompatibleRankThreeData.terminalStart,
    hleft, hp, zero_add]
  have hm := D.simplifiedSize_ge_three
  split_ifs <;> omega

/-- Ordered compatible support in the terminal-plateau case. -/
theorem orderedCompatibleNonbasis_terminalPlateau_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : D.initialParallelSize = 1)
    (hq : 1 < D.terminalParallelSize) (cols : Fin 3 ↪o Fin n) :
    OrderedCompatibleNonbasis D cols ↔
      D.simplifiedSize - 1 ≤ (cols 1).val ∨
      ((cols 2).val < D.simplifiedSize - 1 ∧
        ∃ H ∈ D.intervals,
          H.left.val ≤ (cols 0).val ∧ (cols 2).val ≤ H.right.val) := by
  have hqone : D.terminalParallelSize ≠ 1 := by omega
  have hm := D.simplifiedSize_ge_three
  have hn : n = D.simplifiedSize - 1 + D.terminalParallelSize := by
    have hg := D.groundSize_eq
    have hm := D.simplifiedSize_ge_three
    omega
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
  have hinitPair : ∀ {a b : Fin n}, a ≠ b →
      ¬(D.IsInitialParallel a ∧ D.IsInitialParallel b) := by
    intro a b hab hpairs
    unfold CompatibleRankThreeData.IsInitialParallel CompatibleRankThreeData.middleStart at hpairs
    simp [hleft, hp] at hpairs
    apply hab
    apply Fin.ext
    omega
  have hterm_iff : ∀ j : Fin n,
      D.IsTerminalParallel j ↔ D.simplifiedSize - 1 ≤ j.val := by
    intro j
    change (D.terminalStart ≤ j.val ∧ j.val < D.rightLoopStart) ↔ _
    rw [hrightStart]
    unfold CompatibleRankThreeData.terminalStart CompatibleRankThreeData.middleStart
    simp [hleft, hp]
    omega
  have hidx : ∀ j : Fin n, D.simplifiedIndexNat j =
      if j.val < D.simplifiedSize - 1 then j.val else D.simplifiedSize - 1 :=
    simplifiedIndexNat_terminalPlateau D hleft hp
  have h01 : cols 0 ≠ cols 1 := ne_of_lt (cols.strictMono (by decide))
  have h02 : cols 0 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  have h12 : cols 1 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  unfold OrderedCompatibleNonbasis
  simp only [hloop, false_or, hinitPair h01, hinitPair h02, hinitPair h12]
  constructor
  · rintro (hterm | hcoll)
    · left
      rcases hterm with h | h | h
      · exact (hterm_iff _).mp h.2
      · exact ((hterm_iff _).mp h.1).trans
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).le
      · exact (hterm_iff _).mp h.1
    · rcases hcoll with ⟨h01', h02', h12', H, hH, h0, h1, h2⟩
      have hkBefore : (cols 2).val < D.simplifiedSize - 1 := by
        by_contra hk
        have hlast : D.simplifiedIndexNat (cols 2) = D.simplifiedSize - 1 := by
          rw [hidx]
          simp [Nat.le_of_not_gt hk]
        have hcontainsLast : H.right.val + 1 = D.simplifiedSize := by
          rw [SimplifiedInterval.mem_points] at h2
          have hv := Fin.mk_le_mk.mp h2.2
          rw [hlast] at hv
          have hrBound := H.right.isLt
          have heq : H.right.val = D.simplifiedSize - 1 :=
            le_antisymm (Nat.le_sub_one_of_lt hrBound) hv
          omega
        exact (D.terminal_endpoint_protected (Or.inr hq) H hH) hcontainsLast
      right
      refine ⟨hkBefore, H, hH, ?_, ?_⟩
      · rw [SimplifiedInterval.mem_points] at h0
        have hv := Fin.mk_le_mk.mp h0.1
        change H.left.val ≤ D.simplifiedIndexNat (cols 0) at hv
        have h0Before : (cols 0).val < D.simplifiedSize - 1 :=
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).trans hkBefore
        rw [hidx] at hv
        rw [if_pos h0Before] at hv
        exact hv
      · rw [SimplifiedInterval.mem_points] at h2
        have hv := Fin.mk_le_mk.mp h2.2
        change D.simplifiedIndexNat (cols 2) ≤ H.right.val at hv
        rw [hidx] at hv
        rw [if_pos hkBefore] at hv
        exact hv
  · rintro (hterm | ⟨hkBefore, H, hH, hL, hR⟩)
    · left
      right
      right
      exact ⟨(hterm_iff _).2 hterm, (hterm_iff _).2
        (hterm.trans (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le)⟩
    · right
      have h0Before : (cols 0).val < D.simplifiedSize - 1 :=
        (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).trans hkBefore
      have h1Before : (cols 1).val < D.simplifiedSize - 1 :=
        (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).trans hkBefore
      refine ⟨?_, ?_, ?_, H, hH, ?_, ?_, ?_⟩
      · intro heq
        apply h01
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 1) at hv
        rw [hidx, hidx] at hv
        rw [if_pos h0Before, if_pos h1Before] at hv
        exact hv
      · intro heq
        apply h02
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 2) at hv
        rw [hidx, hidx] at hv
        rw [if_pos h0Before, if_pos hkBefore] at hv
        exact hv
      · intro heq
        apply h12
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change D.simplifiedIndexNat (cols 1) = D.simplifiedIndexNat (cols 2) at hv
        rw [hidx, hidx] at hv
        rw [if_pos h1Before, if_pos hkBefore] at hv
        exact hv
      all_goals rw [SimplifiedInterval.mem_points]
      · apply And.intro
        · apply Fin.mk_le_mk.mpr
          change H.left.val ≤ D.simplifiedIndexNat (cols 0)
          rw [hidx, if_pos h0Before]
          exact hL
        · apply Fin.mk_le_mk.mpr
          change D.simplifiedIndexNat (cols 0) ≤ H.right.val
          rw [hidx, if_pos h0Before]
          exact (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).le.trans hR
      · apply And.intro
        · apply Fin.mk_le_mk.mpr
          change H.left.val ≤ D.simplifiedIndexNat (cols 1)
          rw [hidx, if_pos h1Before]
          exact hL.trans
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).le
        · apply Fin.mk_le_mk.mpr
          change D.simplifiedIndexNat (cols 1) ≤ H.right.val
          rw [hidx, if_pos h1Before]
          exact (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le.trans hR
      · apply And.intro
        · apply Fin.mk_le_mk.mpr
          change H.left.val ≤ D.simplifiedIndexNat (cols 2)
          rw [hidx, if_pos hkBefore]
          exact hL.trans
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).le
        · apply Fin.mk_le_mk.mpr
          change D.simplifiedIndexNat (cols 2) ≤ H.right.val
          rw [hidx, if_pos hkBefore]
          exact hR

/-- Exact support for the singleton-initial, terminal-plateau constructor. -/
theorem exists_exactSupport_terminalPlateau {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : D.initialParallelSize = 1)
    (hq : 1 < D.terminalParallelSize) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      RealizesCompatibleSupport D (rankThreeToeplitz a) := by
  let s := CompatibleBoundaryTargets.beforeRightProtection D
  have hs := CompatibleBoundaryTargets.beforeRightProtection_isPositiveMonotone D
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hN : 1 ≤ D.simplifiedSize - 2 := by
    have hm := D.simplifiedSize_ge_three
    omega
  have hsizeMatrix : 3 ≤ (D.simplifiedSize - 2) + 1 + D.terminalParallelSize := by omega
  have hcount : (D.simplifiedSize - 2) + 1 + D.terminalParallelSize = n := by
    have hg := D.groundSize_eq
    have hm := D.simplifiedSize_ge_three
    omega
  let a₀ := positiveCoefficientVectorExtra D.terminalParallelSize s ε
  let a : Fin (n + 2) → ℝ := castRankThreeCoefficients hcount a₀
  have hmatrix : rankThreeToeplitz a = castColumnCount hcount (rankThreeToeplitz a₀) :=
    rankThreeToeplitz_castRankThreeCoefficients hcount a₀
  have htnn₀ := positiveToeplitzExtra_totallyNonnegative hsizeMatrix hε hs.2
  have hrank₀ := positiveToeplitzExtra_hasFullRowRank hN hq.le hε
  refine ⟨a, hmatrix ▸ TotallyNonnegative.castColumnCount htnn₀,
    hmatrix ▸ HasFullRowRank.castColumnCount hrank₀, ?_⟩
  intro cols
  let cols₀ := pullbackOrderEmbedding hcount cols
  have h01 : cols₀ 0 < cols₀ 1 := cols₀.strictMono (by decide)
  have h12 : cols₀ 1 < cols₀ 2 := cols₀.strictMono (by decide)
  rw [hmatrix, orderedMinor_castColumnCount]
  change orderedMinor (rankThreeToeplitz a₀) (allRows 3) cols₀ = 0 ↔
    D.TripleNonbasis (selectedTripleFinset cols)
  rw [← selectedTripleEmbedding_eq cols₀,
    positiveToeplitzExtra_minor_eq_area hε h01 h12]
  have htop : positiveCoefficientVectorExtra D.terminalParallelSize s ε (cols₀ 0).succ.succ *
      positiveCoefficientVectorExtra D.terminalParallelSize s ε (cols₀ 1).succ.succ *
      positiveCoefficientVectorExtra D.terminalParallelSize s ε (cols₀ 2).succ.succ ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (recoveredCoefficient_pos (finiteSynthesizedRatio_pos hε) _).ne'
        (recoveredCoefficient_pos (finiteSynthesizedRatio_pos hε) _).ne')
      (recoveredCoefficient_pos (finiteSynthesizedRatio_pos hε) _).ne'
  rw [mul_eq_zero]
  rw [terminalPlateau_area_eq_zero_iff D hε h01 h12,
    tripleNonbasis_selectedTriple_iff_ordered,
    orderedCompatibleNonbasis_terminalPlateau_iff D hleft hright hp hq]
  rw [or_iff_right htop]
  rfl

/- The former local copies of the initial-plateau support lemmas are retained below only as
historical proof development.  Their checked public versions live in `InitialPlateauSupport`. -/
/-
/-- The simplified initial-plateau chain has zero area exactly on prescribed intervals. -/
theorem initialSimplified_area_eq_zero_iff_interval {n : ℕ}
    (D : CompatibleRankThreeData n) {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.afterLeftProtection D) ε)
    (hp : 1 < D.initialParallelSize)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < D.simplifiedSize) :
    orientedArea (initialSimplifiedX (CompatibleBoundaryTargets.afterLeftProtection D) ε)
        (initialSimplifiedY (CompatibleBoundaryTargets.afterLeftProtection D) ε) i j k = 0 ↔
      ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val := by
  let s := CompatibleBoundaryTargets.afterLeftProtection D
  have hs := CompatibleBoundaryTargets.afterLeftProtection_isPositiveMonotone D
  have hx : StrictlyIncreasingUpTo (initialSimplifiedX s ε) D.simplifiedSize := by
    intro a b hab hb
    exact initialSimplifiedX_strict hε hab (by omega)
  have hmono : SlopesMonotoneUpTo (initialSimplifiedX s ε)
      (initialSimplifiedY s ε) D.simplifiedSize := by
    intro a b hab hb
    exact initialSimplified_slopesMonotone hε hs hab (by omega)
  rw [orientedArea_eq_zero_iff_slopesConstantBetween _ _ hx hmono hij hjk hk,
    ratioSlopesConstantBetween_iff_adjacent]
  by_cases hi0 : i = 0
  · subst i
    have hnotAdjacent : ¬AdjacentSlopesEqualBetween
        (initialSimplifiedX s ε) (initialSimplifiedY s ε) 0 k := by
      intro h
      have heq := h 0 le_rfl (by omega)
      rw [initialSimplified_edgeSlope_zero hε,
        initialSimplified_edgeSlope_succ hε ⟨0, by omega⟩] at heq
      have hsmall := hε.2 ⟨0, by omega⟩
      have hNnonneg : (0 : ℝ) ≤ D.simplifiedSize := Nat.cast_nonneg _
      nlinarith [hε.1]
    constructor
    · intro h
      exact (hnotAdjacent h).elim
    · rintro ⟨H, hH, hleft, hright⟩
      have hleftZero : H.left.val = 0 := by omega
      exact ((D.initial_endpoint_protected (Or.inr hp) H hH) hleftZero).elim
  · have hiPos : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have hcomp : AdjacentSlopesEqualBetween (initialSimplifiedX s ε)
        (initialSimplifiedY s ε) i k ↔
        CompatibleSlopePattern.AllPrescribedBetween D i k := by
      constructor
      · intro h t hit htk
        have htPos : 1 ≤ t := hiPos.trans hit
        let u : Fin (D.simplifiedSize - 2) := ⟨t - 1, by omega⟩
        have heq := h t hit htk
        rw [show t = u.val + 1 by simp [u]; omega,
          initialSimplified_edgeSlope_succ hε u] at heq
        have htNext : t < D.simplifiedSize - 2 := by omega
        let v : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
        rw [show u.val + 1 + 1 = v.val + 1 by simp [u, v]; omega,
          initialSimplified_edgeSlope_succ hε v] at heq
        let c : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
        exact (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D c).mp (by
          simpa [s, CompatibleBoundaryTargets.afterLeftProtection,
            CompatibleSlopePattern.comparisonLeft,
            CompatibleSlopePattern.comparisonRight, u, v, c,
            Nat.sub_add_cancel htPos] using heq)
      · intro h t hit htk
        have htPos : 1 ≤ t := hiPos.trans hit
        let u : Fin (D.simplifiedSize - 2) := ⟨t - 1, by omega⟩
        let v : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
        let c : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
        have heq := (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D c).mpr
          (h t hit htk)
        rw [show t = u.val + 1 by simp [u]; omega,
          initialSimplified_edgeSlope_succ hε u,
          show u.val + 1 + 1 = v.val + 1 by simp [u, v]; omega,
          initialSimplified_edgeSlope_succ hε v]
        simpa [s, CompatibleBoundaryTargets.afterLeftProtection,
          CompatibleSlopePattern.comparisonLeft,
          CompatibleSlopePattern.comparisonRight, u, v, c,
          Nat.sub_add_cancel htPos] using heq
    rw [hcomp,
      CompatibleSlopePattern.allPrescribedBetween_iff_interval D (by omega) hk]

/-- Raw initial-plateau area zeros are exactly repeated initial points or compatible intervals of
three distinct simplified images. -/
theorem initialPlateau_area_eq_zero_iff {n : ℕ} (D : CompatibleRankThreeData n)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.afterLeftProtection D) ε)
    (hp : 1 < D.initialParallelSize) {i j k : ℕ}
    (hij : i < j) (hjk : j < k)
    (hk : k < D.initialParallelSize + (D.simplifiedSize - 2) + 1) :
    orientedArea
        (ratioPointX (finiteInitialPlateauRatio D.initialParallelSize
          (CompatibleBoundaryTargets.afterLeftProtection D) ε))
        (ratioPointY (finiteInitialPlateauRatio D.initialParallelSize
          (CompatibleBoundaryTargets.afterLeftProtection D) ε)) i j k = 0 ↔
      j < D.initialParallelSize ∨
      ∃ H ∈ D.intervals,
        H.left.val ≤ (if i < D.initialParallelSize then 0 else i - D.initialParallelSize + 1) ∧
        k - D.initialParallelSize + 1 ≤ H.right.val := by
  let p := D.initialParallelSize
  let s := CompatibleBoundaryTargets.afterLeftProtection D
  by_cases hjp : j < p
  · have hip : i < p := hij.trans hjp
    change orientedArea (ratioPointX (finiteInitialPlateauRatio p s ε))
      (ratioPointY (finiteInitialPlateauRatio p s ε)) i j k = 0 ↔
        j < p ∨ ∃ H ∈ D.intervals,
          H.left.val ≤ (if i < p then 0 else i - p + 1) ∧
          k - p + 1 ≤ H.right.val
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
    constructor
    · intro _
      exact Or.inl hjp
    · intro _
      ring
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
    have hiPointI : (ratioPointX (finiteInitialPlateauRatio p s ε) i,
        ratioPointY (finiteInitialPlateauRatio p s ε) i) =
          (initialSimplifiedX s ε I, initialSimplifiedY s ε I) := by
      by_cases hip : i < p
      · simpa [I, hip] using hiPoint
      · simpa [I, hip] using hiPoint
    rw [show j - p + 1 = J by rfl] at hjPoint
    rw [show k - p + 1 = K by rfl] at hkPoint
    have hareaEq : orientedArea (ratioPointX (finiteInitialPlateauRatio p s ε))
        (ratioPointY (finiteInitialPlateauRatio p s ε)) i j k =
      orientedArea (initialSimplifiedX s ε) (initialSimplifiedY s ε) I J K := by
      rw [orientedArea, orientedArea,
        show ratioPointX (finiteInitialPlateauRatio p s ε) i = initialSimplifiedX s ε I by
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
    rw [hareaEq, initialSimplified_area_eq_zero_iff_interval D hε hp
      (by dsimp [I, J]; split_ifs <;> omega) (by dsimp [J, K]; omega) (by dsimp [K]; omega)]
    simp [hjp, I, K, p]

theorem simplifiedIndexNat_initialPlateau {n : ℕ} (D : CompatibleRankThreeData n)
    (hleft : D.leftLoopCount = 0) (hright : D.rightLoopCount = 0)
    (hq : D.terminalParallelSize = 1) (j : Fin n) :
    D.simplifiedIndexNat j =
      if j.val < D.initialParallelSize then 0 else j.val - D.initialParallelSize + 1 := by
  unfold CompatibleRankThreeData.simplifiedIndexNat
  simp only [CompatibleRankThreeData.middleStart, CompatibleRankThreeData.terminalStart,
    hleft, zero_add]
  have hm := D.simplifiedSize_ge_three
  have hg := D.groundSize_eq
  split_ifs <;> omega

/-- Ordered compatible support in the initial-plateau/singleton-terminal case. -/
theorem orderedCompatibleNonbasis_initialPlateau_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : 1 < D.initialParallelSize)
    (hq : D.terminalParallelSize = 1) (cols : Fin 3 ↪o Fin n) :
    OrderedCompatibleNonbasis D cols ↔
      (cols 1).val < D.initialParallelSize ∨
      ∃ H ∈ D.intervals,
        H.left.val ≤
          (if (cols 0).val < D.initialParallelSize then 0
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
  have htermPair : ∀ {a b : Fin n}, a ≠ b →
      ¬(D.IsTerminalParallel a ∧ D.IsTerminalParallel b) := by
    intro a b hab hpair
    unfold CompatibleRankThreeData.IsTerminalParallel CompatibleRankThreeData.terminalStart
      CompatibleRankThreeData.middleStart at hpair
    simp [hleft, hq] at hpair
    apply hab
    apply Fin.ext
    omega
  have hinit_iff : ∀ j : Fin n,
      D.IsInitialParallel j ↔ j.val < D.initialParallelSize := by
    intro j
    unfold CompatibleRankThreeData.IsInitialParallel CompatibleRankThreeData.middleStart
    simp [hleft]
  have hidx := simplifiedIndexNat_initialPlateau D hleft hright hq
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
    · rcases hcoll with ⟨h01', h02', h12', H, hH, h0, h1, h2⟩
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
        rw [hidx] at hv
        have h1After : D.initialParallelSize ≤ (cols 1).val := by
          by_contra hbefore
          have h0Before : (cols 0).val < D.initialParallelSize :=
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).trans
              (Nat.lt_of_not_ge hbefore)
          apply h01'
          apply Fin.ext
          change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 1)
          rw [hidx, hidx, if_pos h0Before, if_pos (Nat.lt_of_not_ge hbefore)]
        have h2After : D.initialParallelSize ≤ (cols 2).val :=
          h1After.trans
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le
        rw [if_neg (not_lt_of_ge h2After)] at hv
        exact hv
  · rintro (hinit | ⟨H, hH, hL, hR⟩)
    · left
      left
      exact ⟨(hinit_iff _).2 (by omega), (hinit_iff _).2 hinit⟩
    · right
      have h2ge : D.initialParallelSize ≤ (cols 2).val := by
        by_contra h
        have hrightWhole : H.left.val = 0 := by omega
        exact (D.initial_endpoint_protected (Or.inr hp) H hH) hrightWhole
      have h0ge : D.initialParallelSize ≤ (cols 0).val := by
        by_contra h
        have h0lt : (cols 0).val < D.initialParallelSize := Nat.lt_of_not_ge h
        have hleftZero : H.left.val = 0 := by simp [h0lt] at hL; omega
        exact (D.initial_endpoint_protected (Or.inr hp) H hH) hleftZero
      have h1ge : D.initialParallelSize ≤ (cols 1).val :=
        h0ge.trans (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).le
      refine ⟨?_, ?_, ?_, H, hH, ?_, ?_, ?_⟩
      · intro heq
        apply h01
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 1) at hv
        rw [hidx, hidx] at hv
        simp [not_lt_of_ge h0ge, not_lt_of_ge h1ge] at hv
        omega
      · intro heq
        apply h02
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 2) at hv
        rw [hidx, hidx] at hv
        simp [not_lt_of_ge h0ge, not_lt_of_ge h2ge] at hv
        omega
      · intro heq
        apply h12
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change D.simplifiedIndexNat (cols 1) = D.simplifiedIndexNat (cols 2) at hv
        rw [hidx, hidx] at hv
        simp [not_lt_of_ge h1ge, not_lt_of_ge h2ge] at hv
        omega
      · rw [SimplifiedInterval.mem_points]
        constructor
        · apply Fin.mk_le_mk.mpr
          change H.left.val ≤ D.simplifiedIndexNat (cols 0)
          rw [hidx, if_neg (not_lt_of_ge h0ge)]
          exact hL
        · apply Fin.mk_le_mk.mpr
          change D.simplifiedIndexNat (cols 0) ≤ H.right.val
          rw [hidx, if_neg (not_lt_of_ge h0ge)]
          omega
      · rw [SimplifiedInterval.mem_points]
        constructor
        · apply Fin.mk_le_mk.mpr
          change H.left.val ≤ D.simplifiedIndexNat (cols 1)
          rw [hidx, if_neg (not_lt_of_ge h1ge)]
          omega
        · apply Fin.mk_le_mk.mpr
          change D.simplifiedIndexNat (cols 1) ≤ H.right.val
          rw [hidx, if_neg (not_lt_of_ge h1ge)]
          omega
      · rw [SimplifiedInterval.mem_points]
        constructor
        · apply Fin.mk_le_mk.mpr
          change H.left.val ≤ D.simplifiedIndexNat (cols 2)
          rw [hidx, if_neg (not_lt_of_ge h2ge)]
          exact hL.trans (by
            have := Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))
            omega)
        · apply Fin.mk_le_mk.mpr
          change D.simplifiedIndexNat (cols 2) ≤ H.right.val
          rw [hidx, if_neg (not_lt_of_ge h2ge)]
          exact hR
-/

/-- Exact support for the initial-plateau, singleton-terminal constructor. -/
theorem exists_exactSupport_initialPlateau {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : 1 < D.initialParallelSize)
    (hq : D.terminalParallelSize = 1) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      RealizesCompatibleSupport D (rankThreeToeplitz a) := by
  let s := CompatibleBoundaryTargets.afterLeftProtection D
  have hs := CompatibleBoundaryTargets.afterLeftProtection_isPositiveMonotone D
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hN : 1 ≤ D.simplifiedSize - 2 := by
    have hm := D.simplifiedSize_ge_three
    omega
  have hmatrixSize : 3 ≤ D.initialParallelSize + (D.simplifiedSize - 2) + 1 := by
    omega
  have hcount : D.initialParallelSize + (D.simplifiedSize - 2) + 1 = n := by
    have hg := D.groundSize_eq
    omega
  let a₀ := initialCoefficientVectorExtra D.initialParallelSize 0 s ε
  let a : Fin (n + 2) → ℝ := castRankThreeCoefficients hcount a₀
  have hmatrix : rankThreeToeplitz a = castColumnCount hcount (rankThreeToeplitz a₀) :=
    rankThreeToeplitz_castRankThreeCoefficients hcount a₀
  have htnn₀ := initialToeplitzExtra_totallyNonnegative (p := D.initialParallelSize)
    (q := 0) hmatrixSize hε hs
  have hrank₀ := initialToeplitz_hasFullRowRank hN hp.le hε
  refine ⟨a, hmatrix ▸ TotallyNonnegative.castColumnCount htnn₀,
    hmatrix ▸ HasFullRowRank.castColumnCount hrank₀, ?_⟩
  intro cols
  let cols₀ := pullbackOrderEmbedding hcount cols
  have h01 : cols₀ 0 < cols₀ 1 := cols₀.strictMono (by decide)
  have h12 : cols₀ 1 < cols₀ 2 := cols₀.strictMono (by decide)
  have hk : (cols₀ 2).val < D.initialParallelSize + (D.simplifiedSize - 2) + 1 :=
    (cols₀ 2).isLt
  rw [hmatrix, orderedMinor_castColumnCount]
  change orderedMinor (rankThreeToeplitz a₀) (allRows 3) cols₀ = 0 ↔
    D.TripleNonbasis (selectedTripleFinset cols)
  rw [← selectedTripleEmbedding_eq cols₀,
    initialToeplitzExtra_minor_eq_area hε h01 h12]
  have htop : initialCoefficientVectorExtra D.initialParallelSize 0 s ε
          (cols₀ 0).succ.succ *
        initialCoefficientVectorExtra D.initialParallelSize 0 s ε
          (cols₀ 1).succ.succ *
        initialCoefficientVectorExtra D.initialParallelSize 0 s ε
          (cols₀ 2).succ.succ ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) _).ne'
        (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) _).ne')
      (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) _).ne'
  rw [mul_eq_zero, initialPlateau_area_eq_zero_iff D hp hε h01 h12 hk,
    tripleNonbasis_selectedTriple_iff_ordered,
    orderedCompatibleNonbasis_initialPlateau_iff D hleft hright hq]
  rw [or_iff_right htop]
  rfl

/-- The simplified chain between two protected endpoints has a zero area exactly on a prescribed
interval that avoids both protected endpoints. -/
theorem betweenProtected_area_eq_zero_iff_interval {n : ℕ}
    (D : CompatibleRankThreeData n) (hp : 1 < D.initialParallelSize)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k + 1 < D.simplifiedSize) :
    orientedArea
        (initialSimplifiedX (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε)
        (initialSimplifiedY (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε) i j k = 0 ↔
      ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val := by
  let s := CompatibleBoundaryTargets.betweenProtectedEndpoints D
  have hs := CompatibleBoundaryTargets.betweenProtectedEndpoints_isPositiveMonotone D
  have hx : StrictlyIncreasingUpTo (initialSimplifiedX s ε)
      (D.simplifiedSize - 3 + 2) := initialSimplifiedX_strict hε
  have hslopes : SlopesMonotoneUpTo (initialSimplifiedX s ε)
      (initialSimplifiedY s ε) (D.simplifiedSize - 3 + 2) :=
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
        have hN : 0 < D.simplifiedSize - 3 := by
          have hm := D.simplifiedSize_ge_three
          have hkLower : 2 ≤ k := by omega
          omega
        rw [initialSimplified_edgeSlope_zero hε,
          initialSimplified_edgeSlope_succ hε ⟨0, hN⟩] at heq
        have hsmall := hε.2 ⟨0, hN⟩
        have hεpos := hε.1
        exfalso
        dsimp [s, CompatibleBoundaryTargets.betweenProtectedEndpoints] at heq hsmall
        nlinarith
      · have htPos : 0 < t := Nat.pos_of_ne_zero ht
        have htN : t < D.simplifiedSize - 3 := by omega
        have htPrevN : t - 1 < D.simplifiedSize - 3 := by omega
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
        let u : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
        apply (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D u).mp
        simpa [s, CompatibleBoundaryTargets.betweenProtectedEndpoints, htEq,
          CompatibleSlopePattern.comparisonLeft,
          CompatibleSlopePattern.comparisonRight, u] using heq
    · intro h t hit htk
      by_cases ht : t = 0
      · subst t
        exact (hnoZero (h 0 hit htk)).elim
      · have htPos : 0 < t := Nat.pos_of_ne_zero ht
        have htN : t < D.simplifiedSize - 3 := by omega
        have htPrevN : t - 1 < D.simplifiedSize - 3 := by omega
        have htEq : t - 1 + 1 = t := by omega
        let u : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
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
        simpa [s, CompatibleBoundaryTargets.betweenProtectedEndpoints, htEq,
          CompatibleSlopePattern.comparisonLeft,
          CompatibleSlopePattern.comparisonRight, u] using heq
  rw [hcomparisons,
    CompatibleSlopePattern.allPrescribedBetween_iff_interval D (by omega) (by omega)]

/-- Before the repeated terminal point, the both-plateaux chart has zeros exactly from the
initial repeated point or a compatible interval. -/
theorem bothPlateaux_base_area_eq_zero_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (hp : 1 < D.initialParallelSize)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k)
    (hk : k < D.initialParallelSize + (D.simplifiedSize - 3) + 1) :
    orientedArea
        (ratioPointX (finiteInitialPlateauRatio D.initialParallelSize
          (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε))
        (ratioPointY (finiteInitialPlateauRatio D.initialParallelSize
          (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε)) i j k = 0 ↔
      j < D.initialParallelSize ∨
        ∃ H ∈ D.intervals,
          H.left.val ≤ (if i < D.initialParallelSize then 0
            else i - D.initialParallelSize + 1) ∧
          k - D.initialParallelSize + 1 ≤ H.right.val := by
  let p := D.initialParallelSize
  let s := CompatibleBoundaryTargets.betweenProtectedEndpoints D
  change orientedArea (ratioPointX (finiteInitialPlateauRatio p s ε))
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
      (p := p) (s := s) (ε := ε) (j := k) hk
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
    have hK : K + 1 < D.simplifiedSize := by dsimp [K, p]; omega
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
    rw [harea, betweenProtected_area_eq_zero_iff_interval D hp hε hIJ hJK hK]
    simp [hjp, I, K]

/-- In the complete two-plateau chart, a zero area comes exactly from a repeated endpoint point or
from three distinct simplified points contained in a compatible interval. -/
theorem bothPlateaux_area_eq_zero_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (hp : 1 < D.initialParallelSize)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    orientedArea
        (ratioPointX (finiteInitialPlateauRatio D.initialParallelSize
          (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε))
        (ratioPointY (finiteInitialPlateauRatio D.initialParallelSize
          (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε)) i j k = 0 ↔
      j < D.initialParallelSize ∨
        D.initialParallelSize + (D.simplifiedSize - 3) + 1 ≤ j ∨
        (k < D.initialParallelSize + (D.simplifiedSize - 3) + 1 ∧
          ∃ H ∈ D.intervals,
            H.left.val ≤ (if i < D.initialParallelSize then 0
              else i - D.initialParallelSize + 1) ∧
            k - D.initialParallelSize + 1 ≤ H.right.val) := by
  let p := D.initialParallelSize
  let N := D.simplifiedSize - 3
  let s := CompatibleBoundaryTargets.betweenProtectedEndpoints D
  let C := p + N + 1
  change orientedArea (ratioPointX (finiteInitialPlateauRatio p s ε))
      (ratioPointY (finiteInitialPlateauRatio p s ε)) i j k = 0 ↔
    j < p ∨ C ≤ j ∨
      (k < C ∧ ∃ H ∈ D.intervals,
        H.left.val ≤ (if i < p then 0 else i - p + 1) ∧
        k - p + 1 ≤ H.right.val)
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
  · by_cases hjTerminal : C ≤ j
    · have hjPoint := finiteInitialPlateauRatio_terminalPoint_eq (p := p) s ε
        (j := j) (by simpa [C] using hjTerminal)
      have hkPoint := finiteInitialPlateauRatio_terminalPoint_eq (p := p) s ε
        (j := k) (by dsimp [C] at hjTerminal ⊢; omega)
      have hx := congrArg Prod.fst (hjPoint.trans hkPoint.symm)
      have hy := congrArg Prod.snd (hjPoint.trans hkPoint.symm)
      change ratioPointX (finiteInitialPlateauRatio p s ε) j =
        ratioPointX (finiteInitialPlateauRatio p s ε) k at hx
      change ratioPointY (finiteInitialPlateauRatio p s ε) j =
        ratioPointY (finiteInitialPlateauRatio p s ε) k at hy
      rw [orientedArea, hx, hy]
      simp [hjp, hjTerminal]
    · have hjBefore : j < C := Nat.lt_of_not_ge hjTerminal
      by_cases hkBefore : k < C
      · rw [bothPlateaux_base_area_eq_zero_iff D hp hε hij hjk
          (by simpa [C, p, N] using hkBefore)]
        simp [hjp, hjTerminal, hkBefore, p]
      · have hkTerminal : C ≤ k := Nat.le_of_not_gt hkBefore
        have hkPoint := finiteInitialPlateauRatio_terminalPoint_eq (p := p) s ε
          (j := k) (by simpa [C] using hkTerminal)
        have hCPoint := finiteInitialPlateauRatio_terminalPoint_eq (p := p) s ε
          (j := p + N + 1) le_rfl
        have hkx := congrArg Prod.fst (hkPoint.trans hCPoint.symm)
        have hky := congrArg Prod.snd (hkPoint.trans hCPoint.symm)
        change ratioPointX (finiteInitialPlateauRatio p s ε) k =
          ratioPointX (finiteInitialPlateauRatio p s ε) (p + N + 1) at hkx
        change ratioPointY (finiteInitialPlateauRatio p s ε) k =
          ratioPointY (finiteInitialPlateauRatio p s ε) (p + N + 1) at hky
        let I := if i < p then 0 else i - p + 1
        let J := j - p + 1
        have hjge : p ≤ j := Nat.le_of_not_gt hjp
        have hiPoint := finiteInitialPlateauRatio_point_eq_simplified
          (p := p) (s := s) (ε := ε) (j := i) (by dsimp [C] at hjBefore; omega)
        have hjPoint := finiteInitialPlateauRatio_point_eq_simplified
          (p := p) (s := s) (ε := ε) (j := j) (by simpa [C] using hjBefore)
        rw [if_neg hjp] at hjPoint
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
        have hIJ : I < J := by
          dsimp [I, J]
          split_ifs <;> omega
        have hxStrict : ratioPointX (finiteInitialPlateauRatio p s ε) i <
            ratioPointX (finiteInitialPlateauRatio p s ε) j := by
          rw [show ratioPointX (finiteInitialPlateauRatio p s ε) i =
              initialSimplifiedX s ε I by exact congrArg Prod.fst hiPointI,
            show ratioPointX (finiteInitialPlateauRatio p s ε) j =
              initialSimplifiedX s ε J by exact congrArg Prod.fst hjPoint]
          exact initialSimplifiedX_strict hε hIJ (by dsimp [J, C] at *; omega)
        have hbase : 0 ≤ orientedArea
            (ratioPointX (finiteInitialPlateauRatio p s ε))
            (ratioPointY (finiteInitialPlateauRatio p s ε)) i j (p + N) := by
          by_cases hjLast : j = p + N
          · subst j
            simp [orientedArea]
          · exact finiteInitialPlateauRatio_baseAreasNonnegative hε
              (CompatibleBoundaryTargets.betweenProtectedEndpoints_isPositiveMonotone D)
              hij (by omega) (by omega)
        have hv := finiteInitialPlateauRatio_terminalVertical (p := p) hε
        have hrect : 0 <
            (ratioPointX (finiteInitialPlateauRatio p s ε) j -
              ratioPointX (finiteInitialPlateauRatio p s ε) i) *
            (ratioPointY (finiteInitialPlateauRatio p s ε) (p + N + 1) -
              ratioPointY (finiteInitialPlateauRatio p s ε) (p + N)) :=
          mul_pos (sub_pos.mpr hxStrict) (sub_pos.mpr hv.2)
        have hpositive : 0 < orientedArea
            (ratioPointX (finiteInitialPlateauRatio p s ε))
            (ratioPointY (finiteInitialPlateauRatio p s ε)) i j k := by
          rw [orientedArea, hkx, hky, ← orientedArea,
            orientedArea_vertical_replace _ _ hv.1.symm]
          linarith
        constructor
        · intro hz
          exact (ne_of_gt hpositive hz).elim
        · rintro (hinit | hterm | ⟨hk', _⟩)
          · exact (hjp hinit).elim
          · exact (hjTerminal hterm).elim
          · exact (hkBefore hk').elim

/-- Exact support for the loop-free constructor with nontrivial parallel classes at both
endpoints. -/
theorem exists_exactSupport_bothPlateaux {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : 1 < D.initialParallelSize)
    (hq : 1 < D.terminalParallelSize) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      RealizesCompatibleSupport D (rankThreeToeplitz a) := by
  let s := CompatibleBoundaryTargets.betweenProtectedEndpoints D
  have hs := CompatibleBoundaryTargets.betweenProtectedEndpoints_isPositiveMonotone D
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hmatrixSize : 3 ≤ D.initialParallelSize + (D.simplifiedSize - 3) + 1 +
      D.terminalParallelSize := by omega
  have hcount : D.initialParallelSize + (D.simplifiedSize - 3) + 1 +
      D.terminalParallelSize = n := by
    have hg := D.groundSize_eq
    have hm := D.simplifiedSize_ge_three
    omega
  let a₀ := initialCoefficientVectorExtra D.initialParallelSize D.terminalParallelSize s ε
  let a : Fin (n + 2) → ℝ := castRankThreeCoefficients hcount a₀
  have hmatrix : rankThreeToeplitz a = castColumnCount hcount (rankThreeToeplitz a₀) :=
    rankThreeToeplitz_castRankThreeCoefficients hcount a₀
  have htnn₀ := initialToeplitzExtra_totallyNonnegative hmatrixSize hε hs
  have hrank₀ := initialToeplitzExtra_hasFullRowRank hp.le hq.le hε
  refine ⟨a, hmatrix ▸ TotallyNonnegative.castColumnCount htnn₀,
    hmatrix ▸ HasFullRowRank.castColumnCount hrank₀, ?_⟩
  intro cols
  let cols₀ := pullbackOrderEmbedding hcount cols
  have h01 : cols₀ 0 < cols₀ 1 := cols₀.strictMono (by decide)
  have h12 : cols₀ 1 < cols₀ 2 := cols₀.strictMono (by decide)
  rw [hmatrix, orderedMinor_castColumnCount]
  change orderedMinor (rankThreeToeplitz a₀) (allRows 3) cols₀ = 0 ↔
    D.TripleNonbasis (selectedTripleFinset cols)
  rw [← selectedTripleEmbedding_eq cols₀,
    initialToeplitzExtra_minor_eq_area hε h01 h12]
  have htop : initialCoefficientVectorExtra D.initialParallelSize
          D.terminalParallelSize s ε (cols₀ 0).succ.succ *
        initialCoefficientVectorExtra D.initialParallelSize
          D.terminalParallelSize s ε (cols₀ 1).succ.succ *
        initialCoefficientVectorExtra D.initialParallelSize
          D.terminalParallelSize s ε (cols₀ 2).succ.succ ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) _).ne'
        (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) _).ne')
      (recoveredCoefficient_pos (finiteInitialPlateauRatio_pos hε) _).ne'
  rw [mul_eq_zero, bothPlateaux_area_eq_zero_iff D hp hε h01 h12,
    tripleNonbasis_selectedTriple_iff_ordered,
    orderedCompatibleNonbasis_bothPlateaux_iff D hleft hright hq]
  rw [or_iff_right htop]
  rfl

/-- For a protected left support boundary and singleton terminal class, the boundary-chain area
vanishes exactly on one compatible interval. -/
theorem boundaryAfterLeft_area_eq_zero_iff_interval {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : 0 < D.leftLoopCount)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.afterLeftProtection D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < D.simplifiedSize) :
    orientedArea
        (ratioPointX (finiteBoundaryRatio
          (CompatibleBoundaryTargets.afterLeftProtection D) ε))
        (ratioPointY (finiteBoundaryRatio
          (CompatibleBoundaryTargets.afterLeftProtection D) ε)) i j k = 0 ↔
      ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val := by
  let s := CompatibleBoundaryTargets.afterLeftProtection D
  have hs := CompatibleBoundaryTargets.afterLeftProtection_isPositiveMonotone D
  have hx : StrictlyIncreasingUpTo (ratioPointX (finiteBoundaryRatio s ε))
      (D.simplifiedSize - 2 + 2) := finiteBoundaryRatio_pointX_strict hε
  have hslopes : SlopesMonotoneUpTo (ratioPointX (finiteBoundaryRatio s ε))
      (ratioPointY (finiteBoundaryRatio s ε)) (D.simplifiedSize - 2 + 2) :=
    finiteBoundaryRatio_slopesMonotone hε hs
  rw [orientedArea_eq_zero_iff_slopesConstantBetween _ _ hx hslopes hij hjk (by omega),
    ratioSlopesConstantBetween_iff_adjacent]
  have hnoZero : ¬CompatibleSlopePattern.IsPrescribedEquality D 0 := by
    rintro ⟨H, hH, hfirst, _⟩
    apply D.initial_endpoint_protected (Or.inl hleft) H hH
    omega
  have hcomparisons : AdjacentSlopesEqualBetween
      (ratioPointX (finiteBoundaryRatio s ε))
      (ratioPointY (finiteBoundaryRatio s ε)) i k ↔
      CompatibleSlopePattern.AllPrescribedBetween D i k := by
    constructor
    · intro h t hit htk
      by_cases ht : t = 0
      · subst t
        have heq := h 0 hit htk
        have hN : 0 < D.simplifiedSize - 2 := by
          have hm := D.simplifiedSize_ge_three
          omega
        have hfirst := leftSupportBoundary_firstSlope (finiteBoundaryRatio s ε)
          (finiteBoundaryRatio_zero s ε) (finiteBoundaryRatio_one s ε)
          (by simpa using hε.1)
        rw [hfirst.1, finiteBoundaryRatio_edgeSlope hε ⟨0, hN⟩] at heq
        exact (ne_of_gt (hs.1 ⟨0, hN⟩) heq.symm).elim
      · have htPos : 0 < t := Nat.pos_of_ne_zero ht
        have htN : t < D.simplifiedSize - 2 := by omega
        have htPrevN : t - 1 < D.simplifiedSize - 2 := by omega
        have htEq : t - 1 + 1 = t := by omega
        have heq := h t hit htk
        have hleftSlope : edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
            (ratioPointY (finiteBoundaryRatio s ε)) t = s ⟨t - 1, htPrevN⟩ := by
          calc
            edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
                (ratioPointY (finiteBoundaryRatio s ε)) t =
              edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
                (ratioPointY (finiteBoundaryRatio s ε)) (t - 1 + 1) := by rw [htEq]
            _ = s ⟨t - 1, htPrevN⟩ :=
              finiteBoundaryRatio_edgeSlope hε ⟨t - 1, htPrevN⟩
        have hrightSlope : edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
            (ratioPointY (finiteBoundaryRatio s ε)) (t + 1) = s ⟨t, htN⟩ :=
          finiteBoundaryRatio_edgeSlope hε ⟨t, htN⟩
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
        have hleftSlope : edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
            (ratioPointY (finiteBoundaryRatio s ε)) t = s ⟨t - 1, htPrevN⟩ := by
          calc
            edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
                (ratioPointY (finiteBoundaryRatio s ε)) t =
              edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
                (ratioPointY (finiteBoundaryRatio s ε)) (t - 1 + 1) := by rw [htEq]
            _ = s ⟨t - 1, htPrevN⟩ :=
              finiteBoundaryRatio_edgeSlope hε ⟨t - 1, htPrevN⟩
        have hrightSlope : edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
            (ratioPointY (finiteBoundaryRatio s ε)) (t + 1) = s ⟨t, htN⟩ :=
          finiteBoundaryRatio_edgeSlope hε ⟨t, htN⟩
        rw [hleftSlope, hrightSlope]
        simpa [s, CompatibleBoundaryTargets.afterLeftProtection, htEq,
          CompatibleSlopePattern.comparisonLeft,
          CompatibleSlopePattern.comparisonRight, u] using heq
  rw [hcomparisons,
    CompatibleSlopePattern.allPrescribedBetween_iff_interval D (by omega) hk]

/-- Between two protected endpoints, the finite part of the boundary chain has precisely the
compatible interval zeros. -/
theorem boundaryBetween_area_eq_zero_iff_interval {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : 0 < D.leftLoopCount)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k + 1 < D.simplifiedSize) :
    orientedArea
        (ratioPointX (finiteBoundaryRatio
          (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε))
        (ratioPointY (finiteBoundaryRatio
          (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε)) i j k = 0 ↔
      ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val := by
  let s := CompatibleBoundaryTargets.betweenProtectedEndpoints D
  have hs := CompatibleBoundaryTargets.betweenProtectedEndpoints_isPositiveMonotone D
  have hx : StrictlyIncreasingUpTo (ratioPointX (finiteBoundaryRatio s ε))
      (D.simplifiedSize - 3 + 2) := finiteBoundaryRatio_pointX_strict hε
  have hslopes : SlopesMonotoneUpTo (ratioPointX (finiteBoundaryRatio s ε))
      (ratioPointY (finiteBoundaryRatio s ε)) (D.simplifiedSize - 3 + 2) :=
    finiteBoundaryRatio_slopesMonotone hε hs
  rw [orientedArea_eq_zero_iff_slopesConstantBetween _ _ hx hslopes hij hjk (by omega),
    ratioSlopesConstantBetween_iff_adjacent]
  have hnoZero : ¬CompatibleSlopePattern.IsPrescribedEquality D 0 := by
    rintro ⟨H, hH, hfirst, _⟩
    apply D.initial_endpoint_protected (Or.inl hleft) H hH
    omega
  have hcomparisons : AdjacentSlopesEqualBetween
      (ratioPointX (finiteBoundaryRatio s ε))
      (ratioPointY (finiteBoundaryRatio s ε)) i k ↔
      CompatibleSlopePattern.AllPrescribedBetween D i k := by
    constructor
    · intro h t hit htk
      by_cases ht : t = 0
      · subst t
        have heq := h 0 hit htk
        have hN : 0 < D.simplifiedSize - 3 := by
          have hm := D.simplifiedSize_ge_three
          have hkLower : 2 ≤ k := by omega
          omega
        have hfirst := leftSupportBoundary_firstSlope (finiteBoundaryRatio s ε)
          (finiteBoundaryRatio_zero s ε) (finiteBoundaryRatio_one s ε)
          (by simpa using hε.1)
        rw [hfirst.1, finiteBoundaryRatio_edgeSlope hε ⟨0, hN⟩] at heq
        exact (ne_of_gt (hs.1 ⟨0, hN⟩) heq.symm).elim
      · have htPos : 0 < t := Nat.pos_of_ne_zero ht
        have htN : t < D.simplifiedSize - 3 := by omega
        have htPrevN : t - 1 < D.simplifiedSize - 3 := by omega
        have htEq : t - 1 + 1 = t := by omega
        have heq := h t hit htk
        have hleftSlope : edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
            (ratioPointY (finiteBoundaryRatio s ε)) t = s ⟨t - 1, htPrevN⟩ := by
          calc
            edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
                (ratioPointY (finiteBoundaryRatio s ε)) t =
              edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
                (ratioPointY (finiteBoundaryRatio s ε)) (t - 1 + 1) := by rw [htEq]
            _ = s ⟨t - 1, htPrevN⟩ :=
              finiteBoundaryRatio_edgeSlope hε ⟨t - 1, htPrevN⟩
        have hrightSlope : edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
            (ratioPointY (finiteBoundaryRatio s ε)) (t + 1) = s ⟨t, htN⟩ :=
          finiteBoundaryRatio_edgeSlope hε ⟨t, htN⟩
        rw [hleftSlope, hrightSlope] at heq
        let u : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
        apply (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D u).mp
        simpa [s, CompatibleBoundaryTargets.betweenProtectedEndpoints, htEq,
          CompatibleSlopePattern.comparisonLeft,
          CompatibleSlopePattern.comparisonRight, u] using heq
    · intro h t hit htk
      by_cases ht : t = 0
      · subst t
        exact (hnoZero (h 0 hit htk)).elim
      · have htPos : 0 < t := Nat.pos_of_ne_zero ht
        have htN : t < D.simplifiedSize - 3 := by omega
        have htPrevN : t - 1 < D.simplifiedSize - 3 := by omega
        have htEq : t - 1 + 1 = t := by omega
        let u : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
        have heq := (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D u).mpr
          (h t hit htk)
        have hleftSlope : edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
            (ratioPointY (finiteBoundaryRatio s ε)) t = s ⟨t - 1, htPrevN⟩ := by
          calc
            edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
                (ratioPointY (finiteBoundaryRatio s ε)) t =
              edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
                (ratioPointY (finiteBoundaryRatio s ε)) (t - 1 + 1) := by rw [htEq]
            _ = s ⟨t - 1, htPrevN⟩ :=
              finiteBoundaryRatio_edgeSlope hε ⟨t - 1, htPrevN⟩
        have hrightSlope : edgeSlope (ratioPointX (finiteBoundaryRatio s ε))
            (ratioPointY (finiteBoundaryRatio s ε)) (t + 1) = s ⟨t, htN⟩ :=
          finiteBoundaryRatio_edgeSlope hε ⟨t, htN⟩
        rw [hleftSlope, hrightSlope]
        simpa [s, CompatibleBoundaryTargets.betweenProtectedEndpoints, htEq,
          CompatibleSlopePattern.comparisonLeft,
          CompatibleSlopePattern.comparisonRight, u] using heq
  rw [hcomparisons,
    CompatibleSlopePattern.allPrescribedBetween_iff_interval D (by omega) (by omega)]

/-- Adding the terminal plateau to a left-boundary chain introduces exactly the repeated-terminal
zeros and no others. -/
theorem boundaryTerminalPlateau_area_eq_zero_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : 0 < D.leftLoopCount)
    {ε : ℝ} (hε : IsAdmissibleSynthesisEpsilon
      (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    orientedArea
        (ratioPointX (finiteBoundaryRatio
          (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε))
        (ratioPointY (finiteBoundaryRatio
          (CompatibleBoundaryTargets.betweenProtectedEndpoints D) ε)) i j k = 0 ↔
      D.simplifiedSize - 1 ≤ j ∨
        (k < D.simplifiedSize - 1 ∧
          ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val) := by
  let s := CompatibleBoundaryTargets.betweenProtectedEndpoints D
  let N := D.simplifiedSize - 3
  have hm := D.simplifiedSize_ge_three
  have hcut : N + 2 = D.simplifiedSize - 1 := by dsimp [N]; omega
  by_cases hjTerminal : N + 2 ≤ j
  · have hjPoint := finiteBoundaryRatio_terminalPoint_eq s ε hjTerminal
    have hkPoint := finiteBoundaryRatio_terminalPoint_eq s ε (j := k) (by omega)
    have hx := congrArg Prod.fst (hjPoint.trans hkPoint.symm)
    have hy := congrArg Prod.snd (hjPoint.trans hkPoint.symm)
    change ratioPointX (finiteBoundaryRatio s ε) j =
      ratioPointX (finiteBoundaryRatio s ε) k at hx
    change ratioPointY (finiteBoundaryRatio s ε) j =
      ratioPointY (finiteBoundaryRatio s ε) k at hy
    rw [orientedArea, hx, hy]
    constructor
    · intro _
      left
      omega
    · intro _
      ring
  · have hjBefore : j < N + 2 := Nat.lt_of_not_ge hjTerminal
    by_cases hkBefore : k < N + 2
    · rw [boundaryBetween_area_eq_zero_iff_interval D hleft hε hij hjk (by omega)]
      constructor
      · intro h
        right
        exact ⟨by omega, h⟩
      · rintro (h | ⟨_, h⟩)
        · omega
        · exact h
    · have hkTerminal : N + 2 ≤ k := Nat.le_of_not_gt hkBefore
      have hkPoint := finiteBoundaryRatio_terminalPoint_eq s ε hkTerminal
      have hstarPoint := finiteBoundaryRatio_terminalPoint_eq s ε
        (j := N + 2) le_rfl
      have hkx := congrArg Prod.fst (hkPoint.trans hstarPoint.symm)
      have hky := congrArg Prod.snd (hkPoint.trans hstarPoint.symm)
      change ratioPointX (finiteBoundaryRatio s ε) k =
        ratioPointX (finiteBoundaryRatio s ε) (N + 2) at hkx
      change ratioPointY (finiteBoundaryRatio s ε) k =
        ratioPointY (finiteBoundaryRatio s ε) (N + 2) at hky
      have hbase : 0 ≤ orientedArea (ratioPointX (finiteBoundaryRatio s ε))
          (ratioPointY (finiteBoundaryRatio s ε)) i j (N + 1) := by
        by_cases hjLast : j = N + 1
        · subst j
          simp [orientedArea]
        · exact finiteBoundaryRatio_areasNonnegative hε
            (CompatibleBoundaryTargets.betweenProtectedEndpoints_isPositiveMonotone D)
            hij (by omega) (by omega)
      have hvertical := finiteBoundaryRatio_terminalVertical hε
      have hxPositive : 0 < ratioPointX (finiteBoundaryRatio s ε) j -
          ratioPointX (finiteBoundaryRatio s ε) i :=
        sub_pos.mpr (finiteBoundaryRatio_pointX_strict hε hij (by omega))
      have hrect : 0 <
          (ratioPointX (finiteBoundaryRatio s ε) j -
            ratioPointX (finiteBoundaryRatio s ε) i) *
          (ratioPointY (finiteBoundaryRatio s ε) (N + 2) -
            ratioPointY (finiteBoundaryRatio s ε) (N + 1)) :=
        mul_pos hxPositive (sub_pos.mpr hvertical.2)
      have hpositive : 0 < orientedArea (ratioPointX (finiteBoundaryRatio s ε))
          (ratioPointY (finiteBoundaryRatio s ε)) i j k := by
        rw [orientedArea, hkx, hky, ← orientedArea,
          orientedArea_vertical_replace _ _ hvertical.1.symm]
        linarith
      constructor
      · intro hz
        exact (ne_of_gt hpositive hz).elim
      · rintro (h | ⟨hk', _⟩)
        · omega
        · omega

/-- Exact support for every loop-free compatible datum, covering all four endpoint-class
combinations. -/
theorem exists_exactSupport_noLoops {n : ℕ} (D : CompatibleRankThreeData n)
    (hleft : D.leftLoopCount = 0) (hright : D.rightLoopCount = 0) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      RealizesCompatibleSupport D (rankThreeToeplitz a) := by
  have hpLe : 1 ≤ D.initialParallelSize := D.initialParallelSize_pos
  have hqLe : 1 ≤ D.terminalParallelSize := D.terminalParallelSize_pos
  rcases hpLe.eq_or_lt with hp | hp
  · rcases hqLe.eq_or_lt with hq | hq
    · exact exists_exactSupport_singletonEndpoints D hleft hright hp.symm hq.symm
    · exact exists_exactSupport_terminalPlateau D hleft hright hp.symm hq
  · rcases hqLe.eq_or_lt with hq | hq
    · exact exists_exactSupport_initialPlateau D hleft hright hp hq.symm
    · exact exists_exactSupport_bothPlateaux D hleft hright hp hq

/-- Exact support for a nonempty initial loop block and a singleton terminal class. -/
theorem exists_exactSupport_leftLoop_singletonTerminal {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : 0 < D.leftLoopCount)
    (hright : D.rightLoopCount = 0) (hq : D.terminalParallelSize = 1) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      RealizesCompatibleSupport D (rankThreeToeplitz a) := by
  let s := CompatibleBoundaryTargets.afterLeftProtection D
  have hs := CompatibleBoundaryTargets.afterLeftProtection_isPositiveMonotone D
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hN : 1 ≤ D.simplifiedSize - 2 := by
    have hm := D.simplifiedSize_ge_three
    omega
  have hcount : D.leftLoopCount + (D.simplifiedSize - 2 + 2) = n := by
    have hp := D.initialParallel_singleton_of_leftLoops hleft
    have hg := D.groundSize_eq
    omega
  let a₀ := translatedBoundaryCoefficientVector D.leftLoopCount s ε
  let a : Fin (n + 2) → ℝ := castRankThreeCoefficients hcount a₀
  have hmatrix : rankThreeToeplitz a = castColumnCount hcount (rankThreeToeplitz a₀) :=
    rankThreeToeplitz_castRankThreeCoefficients hcount a₀
  have hmodel := translatedBoundaryToeplitz_tnn_fullRowRank hN hε hs D.leftLoopCount
  refine ⟨a, hmatrix ▸ TotallyNonnegative.castColumnCount hmodel.1,
    hmatrix ▸ HasFullRowRank.castColumnCount hmodel.2, ?_⟩
  intro cols
  let cols₀ := pullbackOrderEmbedding hcount cols
  rw [hmatrix, orderedMinor_castColumnCount]
  change orderedMinor (rankThreeToeplitz a₀) (allRows 3) cols₀ = 0 ↔
    D.TripleNonbasis (selectedTripleFinset cols)
  rw [rankThreeToeplitz_translatedBoundaryCoefficientVector,
    tripleNonbasis_selectedTriple_iff_ordered,
    orderedCompatibleNonbasis_leftLoop_singletonTerminal_iff D hleft hright hq]
  by_cases hprefix : (cols₀ 0).val < D.leftLoopCount
  · have hz := orderedMinor_prependZeroColumns_eq_zero D.leftLoopCount
      (rankThreeToeplitz (boundaryCoefficientVector s ε)) (allRows 3) cols₀ hprefix
    rw [hz]
    have hprefix' : (cols 0).val < D.leftLoopCount := hprefix
    simp [hprefix']
  · have hall : ∀ p : Fin 3, D.leftLoopCount ≤ (cols₀ p).val := by
      intro p
      exact (Nat.le_of_not_gt hprefix).trans
        (Fin.mk_le_mk.mp (cols₀.monotone (Fin.zero_le p)))
    let colsU := unshiftOrderEmbedding D.leftLoopCount cols₀ hall
    rw [orderedMinor_prependZeroColumns_unshift D.leftLoopCount
      (rankThreeToeplitz (boundaryCoefficientVector s ε)) (allRows 3) cols₀ hall]
    change orderedMinor (rankThreeToeplitz (boundaryCoefficientVector s ε))
      (allRows 3) colsU = 0 ↔ _
    have h01 : colsU 0 < colsU 1 := colsU.strictMono (by decide)
    have h12 : colsU 1 < colsU 2 := colsU.strictMono (by decide)
    rw [← selectedTripleEmbedding_eq colsU,
      boundaryToeplitz_minor_eq_area hε h01 h12]
    have hpos : ∀ u : Fin (D.simplifiedSize - 2 + 2),
        0 < boundaryCoefficientVector s ε u.succ.succ := by
      intro u
      change 0 < boundaryRecoveredCoefficient (finiteBoundaryRatio s ε) (u.val + 2)
      exact boundaryRecoveredCoefficient_pos (finiteBoundaryRatio_pos hε) _ (by omega)
    have htop : boundaryCoefficientVector s ε (colsU 0).succ.succ *
          boundaryCoefficientVector s ε (colsU 1).succ.succ *
          boundaryCoefficientVector s ε (colsU 2).succ.succ ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (hpos _).ne' (hpos _).ne') (hpos _).ne'
    rw [mul_eq_zero, boundaryAfterLeft_area_eq_zero_iff_interval D hleft hε h01 h12
      (by have := (colsU 2).isLt; omega)]
    rw [or_iff_right htop]
    have hprefix' : ¬(cols 0).val < D.leftLoopCount := hprefix
    simp only [hprefix', false_or]
    rfl

/-- Exact support for a nonempty initial loop block and a nontrivial terminal parallel class. -/
theorem exists_exactSupport_leftLoop_terminalPlateau {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : 0 < D.leftLoopCount)
    (hright : D.rightLoopCount = 0) (hq : 1 < D.terminalParallelSize) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      RealizesCompatibleSupport D (rankThreeToeplitz a) := by
  let s := CompatibleBoundaryTargets.betweenProtectedEndpoints D
  have hs := CompatibleBoundaryTargets.betweenProtectedEndpoints_isPositiveMonotone D
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hmatrixSize : 3 ≤ (D.simplifiedSize - 3) + 2 + D.terminalParallelSize := by
    have hm := D.simplifiedSize_ge_three
    omega
  have hcount : D.leftLoopCount +
      ((D.simplifiedSize - 3) + 2 + D.terminalParallelSize) = n := by
    have hp := D.initialParallel_singleton_of_leftLoops hleft
    have hg := D.groundSize_eq
    have hm := D.simplifiedSize_ge_three
    omega
  let a₀ := translatedBoundaryExtraCoefficientVector D.leftLoopCount
    D.terminalParallelSize s ε
  let a : Fin (n + 2) → ℝ := castRankThreeCoefficients hcount a₀
  have hmatrix : rankThreeToeplitz a = castColumnCount hcount (rankThreeToeplitz a₀) :=
    rankThreeToeplitz_castRankThreeCoefficients hcount a₀
  have hmodel := translatedBoundaryExtra_tnn_fullRowRank hmatrixSize hε hs D.leftLoopCount
  refine ⟨a, hmatrix ▸ TotallyNonnegative.castColumnCount hmodel.1,
    hmatrix ▸ HasFullRowRank.castColumnCount hmodel.2, ?_⟩
  intro cols
  let cols₀ := pullbackOrderEmbedding hcount cols
  rw [hmatrix, orderedMinor_castColumnCount]
  change orderedMinor (rankThreeToeplitz a₀) (allRows 3) cols₀ = 0 ↔
    D.TripleNonbasis (selectedTripleFinset cols)
  rw [rankThreeToeplitz_translatedBoundaryExtraCoefficientVector,
    tripleNonbasis_selectedTriple_iff_ordered,
    orderedCompatibleNonbasis_leftLoop_terminalPlateau_iff D hleft hright hq]
  by_cases hprefix : (cols₀ 0).val < D.leftLoopCount
  · have hz := orderedMinor_prependZeroColumns_eq_zero D.leftLoopCount
      (rankThreeToeplitz (boundaryCoefficientVectorExtra D.terminalParallelSize s ε))
      (allRows 3) cols₀ hprefix
    rw [hz]
    have hprefix' : (cols 0).val < D.leftLoopCount := hprefix
    simp [hprefix']
  · have hall : ∀ p : Fin 3, D.leftLoopCount ≤ (cols₀ p).val := by
      intro p
      exact (Nat.le_of_not_gt hprefix).trans
        (Fin.mk_le_mk.mp (cols₀.monotone (Fin.zero_le p)))
    let colsU := unshiftOrderEmbedding D.leftLoopCount cols₀ hall
    rw [orderedMinor_prependZeroColumns_unshift D.leftLoopCount
      (rankThreeToeplitz (boundaryCoefficientVectorExtra D.terminalParallelSize s ε))
      (allRows 3) cols₀ hall]
    change orderedMinor
      (rankThreeToeplitz (boundaryCoefficientVectorExtra D.terminalParallelSize s ε))
      (allRows 3) colsU = 0 ↔ _
    have h01 : colsU 0 < colsU 1 := colsU.strictMono (by decide)
    have h12 : colsU 1 < colsU 2 := colsU.strictMono (by decide)
    rw [← selectedTripleEmbedding_eq colsU,
      boundaryToeplitzExtra_minor_eq_area hε h01 h12]
    have hpos : ∀ u : Fin ((D.simplifiedSize - 3) + 2 + D.terminalParallelSize),
        0 < boundaryCoefficientVectorExtra D.terminalParallelSize s ε u.succ.succ := by
      intro u
      change 0 < boundaryRecoveredCoefficient (finiteBoundaryRatio s ε) (u.val + 2)
      exact boundaryRecoveredCoefficient_pos (finiteBoundaryRatio_pos hε) _ (by omega)
    have htop : boundaryCoefficientVectorExtra D.terminalParallelSize s ε
            (colsU 0).succ.succ *
          boundaryCoefficientVectorExtra D.terminalParallelSize s ε
            (colsU 1).succ.succ *
          boundaryCoefficientVectorExtra D.terminalParallelSize s ε
            (colsU 2).succ.succ ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (hpos _).ne' (hpos _).ne') (hpos _).ne'
    rw [mul_eq_zero, boundaryTerminalPlateau_area_eq_zero_iff D hleft hε h01 h12]
    rw [or_iff_right htop]
    have hprefix' : ¬(cols 0).val < D.leftLoopCount := hprefix
    simp only [hprefix', false_or]
    have hval : ∀ p : Fin 3,
        (colsU p).val = (cols p).val - D.leftLoopCount := by
      intro p
      rfl
    have hall' : ∀ p : Fin 3, D.leftLoopCount ≤ (cols p).val := by
      intro p
      exact hall p
    simp_rw [hval]
    constructor
    · rintro (hterm | ⟨hbefore, H, hH, hL, hR⟩)
      · left
        calc
          D.leftLoopCount + (D.simplifiedSize - 1) ≤
              D.leftLoopCount + ((cols 1).val - D.leftLoopCount) :=
            Nat.add_le_add_left hterm _
          _ = (cols 1).val := Nat.add_sub_of_le (hall' 1)
      · right
        exact ⟨(Nat.sub_lt_iff_lt_add' (hall' 2)).mp hbefore, H, hH, hL, hR⟩
    · rintro (hterm | ⟨hbefore, H, hH, hL, hR⟩)
      · left
        apply Nat.le_sub_of_add_le
        simpa [Nat.add_comm] using hterm
      · right
        exact ⟨(Nat.sub_lt_iff_lt_add' (hall' 2)).mpr hbefore, H, hH, hL, hR⟩

/-- Exact support for every compatible datum with a nonempty initial loop block and no terminal
loops. -/
theorem exists_exactSupport_leftLoop {n : ℕ} (D : CompatibleRankThreeData n)
    (hleft : 0 < D.leftLoopCount) (hright : D.rightLoopCount = 0) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      RealizesCompatibleSupport D (rankThreeToeplitz a) := by
  have hqLe : 1 ≤ D.terminalParallelSize := D.terminalParallelSize_pos
  rcases hqLe.eq_or_lt with hq | hq
  · exact exists_exactSupport_leftLoop_singletonTerminal D hleft hright hq.symm
  · exact exists_exactSupport_leftLoop_terminalPlateau D hleft hright hq

/-- Exact support for a nonempty terminal loop block, obtained by simultaneous reversal. -/
theorem exists_exactSupport_rightLoop {n : ℕ} (D : CompatibleRankThreeData n)
    (hleft : D.leftLoopCount = 0) (hright : 0 < D.rightLoopCount) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      RealizesCompatibleSupport D (rankThreeToeplitz a) := by
  have hrevLeft : 0 < (reverseCompatibleData D).leftLoopCount := by
    simpa using hright
  have hrevRight : (reverseCompatibleData D).rightLoopCount = 0 := by
    simpa using hleft
  obtain ⟨aLeft, hTN, hfull, hsupport⟩ :=
    exists_exactSupport_leftLoop (reverseCompatibleData D) hrevLeft hrevRight
  let a : Fin (n + 2) → ℝ := aLeft ∘ Fin.rev
  have hmatrix : rankThreeToeplitz a = reverseMatrix (rankThreeToeplitz aLeft) := by
    simpa [a, reverseMatrix] using (rankThreeToeplitz_submatrix_rev aLeft).symm
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [hmatrix]
    exact hTN.reverseMatrix
  · rw [hmatrix]
    exact (hasFullRowRank_reverseMatrix_iff _).2 hfull
  · rw [hmatrix]
    intro cols
    rw [orderedMinor_reverseMatrix, reverseOrderEmbedding_allRows]
    have hrev := hsupport (reverseOrderEmbedding cols)
    rw [tripleNonbasis_selectedTriple_iff_ordered] at hrev ⊢
    exact hrev.trans (orderedCompatibleNonbasis_reverse_iff D cols)

end

end ToeplitzPositroids.RankThree
