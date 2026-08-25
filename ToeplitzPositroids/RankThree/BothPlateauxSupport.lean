import ToeplitzPositroids.RankThree.InitialPlateauSupport
import Mathlib.Tactic

/-!
# Compatible support with two endpoint plateaux

This file gives the numeric simplification map and ordered nonbasis condition for the
loop-free construction with nontrivial initial and terminal parallel classes.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- Numeric simplification map for a loop-free datum with both endpoint plateaux. -/
theorem simplifiedIndexNat_bothPlateaux {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (j : Fin n) :
    D.simplifiedIndexNat j =
      if j.val < D.initialParallelSize then 0
      else if j.val < D.initialParallelSize + (D.simplifiedSize - 3) + 1 then
        j.val - D.initialParallelSize + 1
      else D.simplifiedSize - 1 := by
  have hm := D.simplifiedSize_ge_three
  unfold CompatibleRankThreeData.simplifiedIndexNat
  simp only [CompatibleRankThreeData.middleStart,
    CompatibleRankThreeData.terminalStart, hleft, zero_add]
  split_ifs <;> omega

/-- With no loops and endpoint plateaux on both sides, the ordered compatible condition is
exactly an initial repeated pair, a terminal repeated pair, or interval containment before the
terminal plateau. -/
theorem orderedCompatibleNonbasis_bothPlateaux_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hq : 1 < D.terminalParallelSize)
    (cols : Fin 3 ↪o Fin n) :
    OrderedCompatibleNonbasis D cols ↔
      (cols 1).val < D.initialParallelSize ∨
      D.initialParallelSize + (D.simplifiedSize - 3) + 1 ≤ (cols 1).val ∨
      ((cols 2).val < D.initialParallelSize + (D.simplifiedSize - 3) + 1 ∧
        ∃ H ∈ D.intervals,
          H.left.val ≤ (if (cols 0).val < D.initialParallelSize then 0
            else (cols 0).val - D.initialParallelSize + 1) ∧
          (cols 2).val - D.initialParallelSize + 1 ≤ H.right.val) := by
  let terminalCutoff := D.initialParallelSize + (D.simplifiedSize - 3) + 1
  have hm := D.simplifiedSize_ge_three
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
  have hterm_iff : ∀ j : Fin n,
      D.IsTerminalParallel j ↔ terminalCutoff ≤ j.val := by
    intro j
    change (D.terminalStart ≤ j.val ∧ j.val < D.rightLoopStart) ↔ _
    rw [hrightStart]
    unfold CompatibleRankThreeData.terminalStart CompatibleRankThreeData.middleStart
    simp only [hleft, zero_add]
    dsimp [terminalCutoff]
    omega
  have hidx : ∀ j : Fin n, D.simplifiedIndexNat j =
      if j.val < D.initialParallelSize then 0
      else if j.val < terminalCutoff then j.val - D.initialParallelSize + 1
      else D.simplifiedSize - 1 := by
    intro j
    simpa [terminalCutoff] using simplifiedIndexNat_bothPlateaux D hleft j
  have h01 : cols 0 ≠ cols 1 := ne_of_lt (cols.strictMono (by decide))
  have h02 : cols 0 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  have h12 : cols 1 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  unfold OrderedCompatibleNonbasis
  simp only [hloop, false_or]
  constructor
  · rintro (hinit | hterm | hcoll)
    · left
      rcases hinit with h | h | h
      · exact (hinit_iff _).mp h.2
      · exact (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).trans
          ((hinit_iff _).mp h.2)
      · exact (hinit_iff _).mp h.1
    · right
      left
      rcases hterm with h | h | h
      · exact (hterm_iff _).mp h.1 |>.trans
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).le
      · exact (hterm_iff _).mp h.1 |>.trans
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).le
      · exact (hterm_iff _).mp h.1
    · rcases hcoll with ⟨h01simp, _, _, H, hH, h0, _, h2mem⟩
      have h1AfterInitial : D.initialParallelSize ≤ (cols 1).val := by
        by_contra hbefore
        have h0Before : (cols 0).val < D.initialParallelSize :=
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).trans
            (Nat.lt_of_not_ge hbefore)
        apply h01simp
        apply Fin.ext
        change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 1)
        have h0BeforeTerminal : (cols 0).val < terminalCutoff := by
          dsimp [terminalCutoff]
          omega
        have h1BeforeTerminal : (cols 1).val < terminalCutoff := by
          dsimp [terminalCutoff]
          omega
        rw [hidx, hidx, if_pos h0BeforeTerminal, if_pos h1BeforeTerminal,
          if_pos h0Before, if_pos (Nat.lt_of_not_ge hbefore)]
      have h2AfterInitial : D.initialParallelSize ≤ (cols 2).val :=
        h1AfterInitial.trans
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le
      have h2Before : (cols 2).val < terminalCutoff := by
        by_contra hnotBefore
        have h2After : terminalCutoff ≤ (cols 2).val := Nat.le_of_not_gt hnotBefore
        have h2NotInitial : ¬(cols 2).val < D.initialParallelSize :=
          not_lt_of_ge h2AfterInitial
        have hlast : D.simplifiedIndexNat (cols 2) = D.simplifiedSize - 1 := by
          rw [hidx, if_neg h2NotInitial, if_neg (not_lt_of_ge h2After)]
        have hcontainsLast : H.right.val + 1 = D.simplifiedSize := by
          rw [SimplifiedInterval.mem_points] at h2mem
          have hv := Fin.mk_le_mk.mp h2mem.2
          change D.simplifiedIndexNat (cols 2) ≤ H.right.val at hv
          rw [hlast] at hv
          have hrBound := H.right.isLt
          omega
        exact (D.terminal_endpoint_protected (Or.inr hq) H hH) hcontainsLast
      right
      right
      refine ⟨h2Before, H, hH, ?_, ?_⟩
      · rw [SimplifiedInterval.mem_points] at h0
        have hv := Fin.mk_le_mk.mp h0.1
        change H.left.val ≤ D.simplifiedIndexNat (cols 0) at hv
        have h0BeforeTerminal : (cols 0).val < terminalCutoff :=
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).trans
            h2Before
        rw [hidx, if_pos h0BeforeTerminal] at hv
        exact hv
      · rw [SimplifiedInterval.mem_points] at h2mem
        have hv := Fin.mk_le_mk.mp h2mem.2
        change D.simplifiedIndexNat (cols 2) ≤ H.right.val at hv
        have h2NotInitial : ¬(cols 2).val < D.initialParallelSize :=
          not_lt_of_ge h2AfterInitial
        rw [hidx, if_neg h2NotInitial, if_pos h2Before] at hv
        exact hv
  · rintro (hinit | hterm | ⟨h2Before, H, hH, hL, hR⟩)
    · left
      left
      exact ⟨(hinit_iff _).2
          ((Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).trans hinit),
        (hinit_iff _).2 hinit⟩
    · right
      left
      right
      right
      exact ⟨(hterm_iff _).2 hterm,
        (hterm_iff _).2
          (hterm.trans
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le)⟩
    · by_cases h1Before : (cols 1).val < D.initialParallelSize
      · left
        left
        exact ⟨(hinit_iff _).2
            ((Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).trans
              h1Before),
          (hinit_iff _).2 h1Before⟩
      · right
        right
        have h1After : D.initialParallelSize ≤ (cols 1).val :=
          Nat.le_of_not_gt h1Before
        have h2NotInitial : ¬(cols 2).val < D.initialParallelSize := by
          exact not_lt_of_ge
            (h1After.trans
              (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le)
        have h0BeforeTerminal : (cols 0).val < terminalCutoff :=
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).trans
            h2Before
        have h1BeforeTerminal : (cols 1).val < terminalCutoff :=
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).trans
            h2Before
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
          rw [hidx, hidx, if_pos h0BeforeTerminal, if_neg h1Before,
            if_pos h1BeforeTerminal] at hv
          change I = J at hv
          exact (ne_of_lt hIJ) hv
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 2) at hv
          rw [hidx, hidx, if_pos h0BeforeTerminal, if_neg h2NotInitial,
            if_pos h2Before] at hv
          change I = K at hv
          exact (ne_of_lt hIK) hv
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 1) = D.simplifiedIndexNat (cols 2) at hv
          rw [hidx, hidx, if_neg h1Before, if_pos h1BeforeTerminal,
            if_neg h2NotInitial, if_pos h2Before] at hv
          change J = K at hv
          exact (ne_of_lt hJK) hv
        all_goals rw [SimplifiedInterval.mem_points]
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 0)
            rw [hidx, if_pos h0BeforeTerminal]
            exact hL
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 0) ≤ H.right.val
            rw [hidx, if_pos h0BeforeTerminal]
            exact hIK.le.trans hR
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 1)
            rw [hidx, if_neg h1Before, if_pos h1BeforeTerminal]
            exact hL.trans hIJ.le
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 1) ≤ H.right.val
            rw [hidx, if_neg h1Before, if_pos h1BeforeTerminal]
            exact hJK.le.trans hR
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 2)
            rw [hidx, if_neg h2NotInitial, if_pos h2Before]
            exact hL.trans hIK.le
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 2) ≤ H.right.val
            rw [hidx, if_neg h2NotInitial, if_pos h2Before]
            exact hR

end

end ToeplitzPositroids.RankThree
