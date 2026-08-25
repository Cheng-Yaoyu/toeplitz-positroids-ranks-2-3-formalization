import ToeplitzPositroids.RankThree.OneSidedExactSupportTheorem
import Mathlib.Tactic

/-!
# Compatible support with an initial loop block

This file gives the numeric simplification maps and ordered nonbasis conditions for compatible
data with a nonempty initial loop block and no terminal loops.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- With initial loops, the simplification index is zero through the first nonloop and then
increases by raw distance until the terminal class. -/
theorem simplifiedIndexNat_leftLoop {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : 0 < D.leftLoopCount)
    (j : Fin n) :
    D.simplifiedIndexNat j =
      if j.val < D.leftLoopCount then 0
      else if j.val < D.leftLoopCount + (D.simplifiedSize - 1) then
        j.val - D.leftLoopCount
      else D.simplifiedSize - 1 := by
  have hp := D.initialParallel_singleton_of_leftLoops hleft
  have hm := D.simplifiedSize_ge_three
  unfold CompatibleRankThreeData.simplifiedIndexNat
  simp only [CompatibleRankThreeData.middleStart,
    CompatibleRankThreeData.terminalStart, hp]
  split_ifs <;> omega

/-- If the terminal class is a singleton and there are no terminal loops, every nonloop's
simplification index is its distance from the left loop block. -/
theorem simplifiedIndexNat_leftLoop_singletonTerminal {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : 0 < D.leftLoopCount)
    (hright : D.rightLoopCount = 0) (hq : D.terminalParallelSize = 1)
    (j : Fin n) :
    D.simplifiedIndexNat j =
      if j.val < D.leftLoopCount then 0 else j.val - D.leftLoopCount := by
  have hp := D.initialParallel_singleton_of_leftLoops hleft
  have hg := D.groundSize_eq
  have hm := D.simplifiedSize_ge_three
  unfold CompatibleRankThreeData.simplifiedIndexNat
  simp only [CompatibleRankThreeData.middleStart,
    CompatibleRankThreeData.terminalStart, hp]
  split_ifs <;> omega

/-- With initial loops and a singleton terminal class, an ordered triple is a nonbasis exactly
when it meets the loop prefix or its three nonloop simplified indices lie in one compatible
interval. -/
theorem orderedCompatibleNonbasis_leftLoop_singletonTerminal_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : 0 < D.leftLoopCount)
    (hright : D.rightLoopCount = 0) (hq : D.terminalParallelSize = 1)
    (cols : Fin 3 ↪o Fin n) :
    OrderedCompatibleNonbasis D cols ↔
      (cols 0).val < D.leftLoopCount ∨
        ∃ H ∈ D.intervals,
          H.left.val ≤ (cols 0).val - D.leftLoopCount ∧
          (cols 2).val - D.leftLoopCount ≤ H.right.val := by
  have hp := D.initialParallel_singleton_of_leftLoops hleft
  have hrightStart : D.rightLoopStart = n := by
    have h := D.rightLoopStart_add_rightLoopCount
    rw [hright, add_zero] at h
    exact h
  have hloop_iff : ∀ j : Fin n, D.IsLoop j ↔ j.val < D.leftLoopCount := by
    intro j
    unfold CompatibleRankThreeData.IsLoop CompatibleRankThreeData.IsLeftLoop
      CompatibleRankThreeData.IsRightLoop
    rw [hrightStart]
    simp
  have hinitPair : ∀ {a b : Fin n}, a ≠ b →
      ¬(D.IsInitialParallel a ∧ D.IsInitialParallel b) := by
    intro a b hab hpairs
    unfold CompatibleRankThreeData.IsInitialParallel CompatibleRankThreeData.middleStart at hpairs
    rw [hp] at hpairs
    apply hab
    apply Fin.ext
    omega
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
      if j.val < D.leftLoopCount then 0 else j.val - D.leftLoopCount :=
    simplifiedIndexNat_leftLoop_singletonTerminal D hleft hright hq
  have h01 : cols 0 ≠ cols 1 := ne_of_lt (cols.strictMono (by decide))
  have h02 : cols 0 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  have h12 : cols 1 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  unfold OrderedCompatibleNonbasis
  simp only [hinitPair h01, hinitPair h02, hinitPair h12,
    htermPair h01, htermPair h02, htermPair h12, false_or]
  constructor
  · rintro (h0 | h1 | h2 | hcoll)
    · exact Or.inl ((hloop_iff _).mp h0)
    · exact Or.inl
        ((Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).trans
          ((hloop_iff _).mp h1))
    · exact Or.inl
        ((Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).trans
          ((hloop_iff _).mp h2))
    · by_cases h0Loop : (cols 0).val < D.leftLoopCount
      · exact Or.inl h0Loop
      · right
        rcases hcoll with ⟨_, _, _, H, hH, h0mem, _, h2mem⟩
        have h2Nonloop : ¬(cols 2).val < D.leftLoopCount := by
          exact not_lt_of_ge
            ((Nat.le_of_not_gt h0Loop).trans
              (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).le)
        refine ⟨H, hH, ?_, ?_⟩
        · rw [SimplifiedInterval.mem_points] at h0mem
          have hv := Fin.mk_le_mk.mp h0mem.1
          change H.left.val ≤ D.simplifiedIndexNat (cols 0) at hv
          rw [hidx, if_neg h0Loop] at hv
          exact hv
        · rw [SimplifiedInterval.mem_points] at h2mem
          have hv := Fin.mk_le_mk.mp h2mem.2
          change D.simplifiedIndexNat (cols 2) ≤ H.right.val at hv
          rw [hidx, if_neg h2Nonloop] at hv
          exact hv
  · rintro (hloop | ⟨H, hH, hL, hR⟩)
    · exact Or.inl ((hloop_iff _).mpr hloop)
    · by_cases h0Loop : (cols 0).val < D.leftLoopCount
      · exact Or.inl ((hloop_iff _).mpr h0Loop)
      · right
        right
        right
        have h0Nonloop : D.leftLoopCount ≤ (cols 0).val := Nat.le_of_not_gt h0Loop
        have h1Nonloop : D.leftLoopCount ≤ (cols 1).val :=
          h0Nonloop.trans
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).le
        have h2Nonloop : D.leftLoopCount ≤ (cols 2).val :=
          h1Nonloop.trans
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le
        have h01idx : (cols 0).val - D.leftLoopCount <
            (cols 1).val - D.leftLoopCount :=
          (Nat.sub_lt_sub_iff_right h0Nonloop).mpr
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1)))
        have h12idx : (cols 1).val - D.leftLoopCount <
            (cols 2).val - D.leftLoopCount :=
          (Nat.sub_lt_sub_iff_right h1Nonloop).mpr
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2)))
        have h02idx := h01idx.trans h12idx
        refine ⟨?_, ?_, ?_, H, hH, ?_, ?_, ?_⟩
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 1) at hv
          rw [hidx, hidx, if_neg h0Loop, if_neg (not_lt_of_ge h1Nonloop)] at hv
          exact (ne_of_lt h01idx) hv
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 2) at hv
          rw [hidx, hidx, if_neg h0Loop, if_neg (not_lt_of_ge h2Nonloop)] at hv
          exact (ne_of_lt h02idx) hv
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 1) = D.simplifiedIndexNat (cols 2) at hv
          rw [hidx, hidx, if_neg (not_lt_of_ge h1Nonloop),
            if_neg (not_lt_of_ge h2Nonloop)] at hv
          exact (ne_of_lt h12idx) hv
        all_goals rw [SimplifiedInterval.mem_points]
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 0)
            rw [hidx, if_neg h0Loop]
            exact hL
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 0) ≤ H.right.val
            rw [hidx, if_neg h0Loop]
            exact h02idx.le.trans hR
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 1)
            rw [hidx, if_neg (not_lt_of_ge h1Nonloop)]
            exact hL.trans h01idx.le
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 1) ≤ H.right.val
            rw [hidx, if_neg (not_lt_of_ge h1Nonloop)]
            exact h12idx.le.trans hR
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 2)
            rw [hidx, if_neg (not_lt_of_ge h2Nonloop)]
            exact hL.trans h02idx.le
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 2) ≤ H.right.val
            rw [hidx, if_neg (not_lt_of_ge h2Nonloop)]
            exact hR

/-- With initial loops and a nontrivial terminal class, nonbases are exactly loop-prefix
triples, terminal repeated pairs, or compatible interval triples before the terminal class. -/
theorem orderedCompatibleNonbasis_leftLoop_terminalPlateau_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : 0 < D.leftLoopCount)
    (hright : D.rightLoopCount = 0) (hq : 1 < D.terminalParallelSize)
    (cols : Fin 3 ↪o Fin n) :
    OrderedCompatibleNonbasis D cols ↔
      (cols 0).val < D.leftLoopCount ∨
      D.leftLoopCount + (D.simplifiedSize - 1) ≤ (cols 1).val ∨
      ((cols 2).val < D.leftLoopCount + (D.simplifiedSize - 1) ∧
        ∃ H ∈ D.intervals,
          H.left.val ≤ (cols 0).val - D.leftLoopCount ∧
          (cols 2).val - D.leftLoopCount ≤ H.right.val) := by
  let terminalCutoff := D.leftLoopCount + (D.simplifiedSize - 1)
  have hp := D.initialParallel_singleton_of_leftLoops hleft
  have hg := D.groundSize_eq
  have hm := D.simplifiedSize_ge_three
  have hrightStart : D.rightLoopStart = n := by
    have h := D.rightLoopStart_add_rightLoopCount
    rw [hright, add_zero] at h
    exact h
  have hloop_iff : ∀ j : Fin n, D.IsLoop j ↔ j.val < D.leftLoopCount := by
    intro j
    unfold CompatibleRankThreeData.IsLoop CompatibleRankThreeData.IsLeftLoop
      CompatibleRankThreeData.IsRightLoop
    rw [hrightStart]
    simp
  have hinitPair : ∀ {a b : Fin n}, a ≠ b →
      ¬(D.IsInitialParallel a ∧ D.IsInitialParallel b) := by
    intro a b hab hpairs
    unfold CompatibleRankThreeData.IsInitialParallel CompatibleRankThreeData.middleStart at hpairs
    rw [hp] at hpairs
    apply hab
    apply Fin.ext
    omega
  have hterm_iff : ∀ j : Fin n,
      D.IsTerminalParallel j ↔ terminalCutoff ≤ j.val := by
    intro j
    change (D.terminalStart ≤ j.val ∧ j.val < D.rightLoopStart) ↔ _
    rw [hrightStart]
    unfold CompatibleRankThreeData.terminalStart CompatibleRankThreeData.middleStart
    rw [hp]
    dsimp [terminalCutoff]
    omega
  have hidx : ∀ j : Fin n, D.simplifiedIndexNat j =
      if j.val < D.leftLoopCount then 0
      else if j.val < terminalCutoff then j.val - D.leftLoopCount
      else D.simplifiedSize - 1 := by
    intro j
    simpa [terminalCutoff] using simplifiedIndexNat_leftLoop D hleft j
  have h01 : cols 0 ≠ cols 1 := ne_of_lt (cols.strictMono (by decide))
  have h02 : cols 0 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  have h12 : cols 1 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  unfold OrderedCompatibleNonbasis
  simp only [hinitPair h01, hinitPair h02, hinitPair h12, false_or]
  constructor
  · rintro (h0 | h1 | h2 | hterm | hcoll)
    · exact Or.inl ((hloop_iff _).mp h0)
    · exact Or.inl
        ((Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).trans
          ((hloop_iff _).mp h1))
    · exact Or.inl
        ((Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).trans
          ((hloop_iff _).mp h2))
    · right
      left
      rcases hterm with h | h | h
      · exact (hterm_iff _).mp h.1 |>.trans
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).le
      · exact (hterm_iff _).mp h.1 |>.trans
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).le
      · exact (hterm_iff _).mp h.1
    · by_cases h0Loop : (cols 0).val < D.leftLoopCount
      · exact Or.inl h0Loop
      · rcases hcoll with ⟨_, _, _, H, hH, h0mem, _, h2mem⟩
        have h2Before : (cols 2).val < terminalCutoff := by
          by_contra h2not
          have h2After : terminalCutoff ≤ (cols 2).val := Nat.le_of_not_gt h2not
          have h2Nonloop : ¬(cols 2).val < D.leftLoopCount := by
            exact not_lt_of_ge
              ((Nat.le_of_not_gt h0Loop).trans
                (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).le)
          have hlast : D.simplifiedIndexNat (cols 2) = D.simplifiedSize - 1 := by
            rw [hidx, if_neg h2Nonloop, if_neg (not_lt_of_ge h2After)]
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
        · rw [SimplifiedInterval.mem_points] at h0mem
          have hv := Fin.mk_le_mk.mp h0mem.1
          change H.left.val ≤ D.simplifiedIndexNat (cols 0) at hv
          have h0Before : (cols 0).val < terminalCutoff :=
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).trans h2Before
          rw [hidx, if_neg h0Loop, if_pos h0Before] at hv
          exact hv
        · rw [SimplifiedInterval.mem_points] at h2mem
          have hv := Fin.mk_le_mk.mp h2mem.2
          change D.simplifiedIndexNat (cols 2) ≤ H.right.val at hv
          have h2Nonloop : ¬(cols 2).val < D.leftLoopCount := by
            exact not_lt_of_ge
              ((Nat.le_of_not_gt h0Loop).trans
                (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).le)
          rw [hidx, if_neg h2Nonloop, if_pos h2Before] at hv
          exact hv
  · rintro (hloop | hterm | ⟨h2Before, H, hH, hL, hR⟩)
    · exact Or.inl ((hloop_iff _).mpr hloop)
    · right
      right
      right
      left
      right
      right
      exact ⟨(hterm_iff _).2 hterm,
        (hterm_iff _).2
          (hterm.trans
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le)⟩
    · by_cases h0Loop : (cols 0).val < D.leftLoopCount
      · exact Or.inl ((hloop_iff _).mpr h0Loop)
      · right
        right
        right
        right
        have h0Nonloop : D.leftLoopCount ≤ (cols 0).val := Nat.le_of_not_gt h0Loop
        have h1Nonloop : D.leftLoopCount ≤ (cols 1).val :=
          h0Nonloop.trans
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1))).le
        have h2Nonloop : D.leftLoopCount ≤ (cols 2).val :=
          h1Nonloop.trans
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).le
        have h0Before : (cols 0).val < terminalCutoff :=
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 2))).trans h2Before
        have h1Before : (cols 1).val < terminalCutoff :=
          (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2))).trans h2Before
        have h01idx : (cols 0).val - D.leftLoopCount <
            (cols 1).val - D.leftLoopCount :=
          (Nat.sub_lt_sub_iff_right h0Nonloop).mpr
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (0 : Fin 3) < 1)))
        have h12idx : (cols 1).val - D.leftLoopCount <
            (cols 2).val - D.leftLoopCount :=
          (Nat.sub_lt_sub_iff_right h1Nonloop).mpr
            (Fin.mk_lt_mk.mp (cols.strictMono (by decide : (1 : Fin 3) < 2)))
        have h02idx := h01idx.trans h12idx
        refine ⟨?_, ?_, ?_, H, hH, ?_, ?_, ?_⟩
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 1) at hv
          rw [hidx, hidx, if_neg h0Loop, if_pos h0Before,
            if_neg (not_lt_of_ge h1Nonloop), if_pos h1Before] at hv
          exact (ne_of_lt h01idx) hv
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 2) at hv
          rw [hidx, hidx, if_neg h0Loop, if_pos h0Before,
            if_neg (not_lt_of_ge h2Nonloop), if_pos h2Before] at hv
          exact (ne_of_lt h02idx) hv
        · intro heq
          have hv := congrArg Fin.val heq
          change D.simplifiedIndexNat (cols 1) = D.simplifiedIndexNat (cols 2) at hv
          rw [hidx, hidx, if_neg (not_lt_of_ge h1Nonloop), if_pos h1Before,
            if_neg (not_lt_of_ge h2Nonloop), if_pos h2Before] at hv
          exact (ne_of_lt h12idx) hv
        all_goals rw [SimplifiedInterval.mem_points]
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 0)
            rw [hidx, if_neg h0Loop, if_pos h0Before]
            exact hL
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 0) ≤ H.right.val
            rw [hidx, if_neg h0Loop, if_pos h0Before]
            exact h02idx.le.trans hR
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 1)
            rw [hidx, if_neg (not_lt_of_ge h1Nonloop), if_pos h1Before]
            exact hL.trans h01idx.le
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 1) ≤ H.right.val
            rw [hidx, if_neg (not_lt_of_ge h1Nonloop), if_pos h1Before]
            exact h12idx.le.trans hR
        · constructor
          · apply Fin.mk_le_mk.mpr
            change H.left.val ≤ D.simplifiedIndexNat (cols 2)
            rw [hidx, if_neg (not_lt_of_ge h2Nonloop), if_pos h2Before]
            exact hL.trans h02idx.le
          · apply Fin.mk_le_mk.mpr
            change D.simplifiedIndexNat (cols 2) ≤ H.right.val
            rw [hidx, if_neg (not_lt_of_ge h2Nonloop), if_pos h2Before]
            exact hR

end

end ToeplitzPositroids.RankThree
