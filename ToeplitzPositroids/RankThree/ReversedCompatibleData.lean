import ToeplitzPositroids.Matrix.Reversal
import ToeplitzPositroids.RankThree.OneSidedSupportBridge
import ToeplitzPositroids.RankThree.OneSidedExactSupportTheorem
import Mathlib.Tactic

/-!
# Reversal of compatible rank-three data

Simultaneous reversal exchanges the two loop blocks and the two endpoint parallel classes.
This file reverses the prescribed simplified intervals and proves that the compatible nonbasis
condition is invariant under the induced reversal of ordered triples.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- Numeric complement identity for the order-reversing involution on `Fin`. -/
theorem rev_val_add_val_succ {m : ℕ} (i : Fin m) :
    i.rev.val + i.val + 1 = m := by
  change (m - (i.val + 1)) + i.val + 1 = m
  omega

/-- Reverse a closed interval in `Fin m`. -/
def reverseSimplifiedInterval {m : ℕ} (H : SimplifiedInterval m) : SimplifiedInterval m where
  left := H.right.rev
  right := H.left.rev
  left_le_right := Fin.rev_le_rev.mpr H.left_le_right

@[simp]
theorem reverseSimplifiedInterval_left {m : ℕ} (H : SimplifiedInterval m) :
    (reverseSimplifiedInterval H).left = H.right.rev :=
  rfl

@[simp]
theorem reverseSimplifiedInterval_right {m : ℕ} (H : SimplifiedInterval m) :
    (reverseSimplifiedInterval H).right = H.left.rev :=
  rfl

@[simp]
theorem reverseSimplifiedInterval_reverse {m : ℕ} (H : SimplifiedInterval m) :
    reverseSimplifiedInterval (reverseSimplifiedInterval H) = H := by
  cases H
  simp [reverseSimplifiedInterval]

@[simp]
theorem mem_reverseSimplifiedInterval_points_iff {m : ℕ}
    (H : SimplifiedInterval m) (x : Fin m) :
    x ∈ (reverseSimplifiedInterval H).points ↔ x.rev ∈ H.points := by
  simp only [SimplifiedInterval.mem_points, reverseSimplifiedInterval_left,
    reverseSimplifiedInterval_right]
  constructor
  · rintro ⟨hleft, hright⟩
    exact ⟨Fin.le_rev_iff.mpr hright, Fin.rev_le_iff.mpr hleft⟩
  · rintro ⟨hleft, hright⟩
    exact ⟨Fin.rev_le_iff.mp hright, Fin.le_rev_iff.mp hleft⟩

/-- Reverse all ordered data, including the family of simplified rank-two intervals. -/
def reverseCompatibleData {n : ℕ} (D : CompatibleRankThreeData n) :
    CompatibleRankThreeData n where
  leftLoopCount := D.rightLoopCount
  rightLoopCount := D.leftLoopCount
  initialParallelSize := D.terminalParallelSize
  terminalParallelSize := D.initialParallelSize
  simplifiedSize := D.simplifiedSize
  initialParallelSize_pos := D.terminalParallelSize_pos
  terminalParallelSize_pos := D.initialParallelSize_pos
  simplifiedSize_ge_three := D.simplifiedSize_ge_three
  groundSize_eq := by
    have := D.groundSize_eq
    omega
  initialParallel_singleton_of_leftLoops := D.terminalParallel_singleton_of_rightLoops
  terminalParallel_singleton_of_rightLoops := D.initialParallel_singleton_of_leftLoops
  intervals := D.intervals.image reverseSimplifiedInterval
  interval_large := by
    intro H hH
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
    have hlarge := D.interval_large K hK
    have hleftBound := K.left.isLt
    have hrightBound := K.right.isLt
    have hleftRev := rev_val_add_val_succ K.left
    have hrightRev := rev_val_add_val_succ K.right
    simp only [reverseSimplifiedInterval_left, reverseSimplifiedInterval_right]
    change (K.right.rev).val + 2 ≤ (K.left.rev).val
    omega
  intervals_separated := by
    intro H hH K hK hne
    obtain ⟨H₀, hH₀, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨K₀, hK₀, rfl⟩ := Finset.mem_image.mp hK
    have hne₀ : H₀ ≠ K₀ := by
      intro heq
      exact hne (congrArg reverseSimplifiedInterval heq)
    rcases D.intervals_separated H₀ hH₀ K₀ hK₀ hne₀ with
        hsep | hsep | htouch | htouch
    · exact Or.inr (Or.inl (Fin.rev_lt_rev.mpr hsep))
    · exact Or.inl (Fin.rev_lt_rev.mpr hsep)
    · exact Or.inr (Or.inr (Or.inr (congrArg Fin.rev htouch).symm))
    · exact Or.inr (Or.inr (Or.inl (congrArg Fin.rev htouch).symm))
  initial_endpoint_protected := by
    intro hprotected H hH
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
    have hright := D.terminal_endpoint_protected hprotected K hK
    have hrev := rev_val_add_val_succ K.right
    simp only [reverseSimplifiedInterval_left]
    intro hzero
    apply hright
    have hbound := K.right.isLt
    change (K.right.rev).val = 0 at hzero
    omega
  terminal_endpoint_protected := by
    intro hprotected H hH
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
    have hleft := D.initial_endpoint_protected hprotected K hK
    have hrev := rev_val_add_val_succ K.left
    simp only [reverseSimplifiedInterval_right]
    intro hlast
    apply hleft
    have hbound := K.left.isLt
    change (K.left.rev).val + 1 = D.simplifiedSize at hlast
    omega
  interval_not_whole := by
    intro H hH
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
    rcases D.interval_not_whole K hK with hleft | hright
    · right
      have hrev := rev_val_add_val_succ K.left
      simp only [reverseSimplifiedInterval_right]
      intro hlast
      apply hleft
      have hbound := K.left.isLt
      change (K.left.rev).val + 1 = D.simplifiedSize at hlast
      omega
    · left
      have hrev := rev_val_add_val_succ K.right
      simp only [reverseSimplifiedInterval_left]
      intro hzero
      apply hright
      have hbound := K.right.isLt
      change (K.right.rev).val = 0 at hzero
      omega

@[simp]
theorem reverseCompatibleData_leftLoopCount {n : ℕ} (D : CompatibleRankThreeData n) :
    (reverseCompatibleData D).leftLoopCount = D.rightLoopCount :=
  rfl

@[simp]
theorem reverseCompatibleData_rightLoopCount {n : ℕ} (D : CompatibleRankThreeData n) :
    (reverseCompatibleData D).rightLoopCount = D.leftLoopCount :=
  rfl

@[simp]
theorem reverseCompatibleData_initialParallelSize {n : ℕ}
    (D : CompatibleRankThreeData n) :
    (reverseCompatibleData D).initialParallelSize = D.terminalParallelSize :=
  rfl

@[simp]
theorem reverseCompatibleData_terminalParallelSize {n : ℕ}
    (D : CompatibleRankThreeData n) :
    (reverseCompatibleData D).terminalParallelSize = D.initialParallelSize :=
  rfl

@[simp]
theorem reverseCompatibleData_simplifiedSize {n : ℕ} (D : CompatibleRankThreeData n) :
    (reverseCompatibleData D).simplifiedSize = D.simplifiedSize :=
  rfl

@[simp]
theorem reverseCompatibleData_intervals {n : ℕ} (D : CompatibleRankThreeData n) :
    (reverseCompatibleData D).intervals =
      D.intervals.image reverseSimplifiedInterval :=
  rfl

/-- Reversal exchanges loop membership. -/
@[simp]
theorem reverseCompatibleData_isLoop_rev {n : ℕ}
    (D : CompatibleRankThreeData n) (j : Fin n) :
    (reverseCompatibleData D).IsLoop j.rev ↔ D.IsLoop j := by
  have hg := D.groundSize_eq
  have hjrev := rev_val_add_val_succ j
  unfold CompatibleRankThreeData.IsLoop CompatibleRankThreeData.IsLeftLoop
    CompatibleRankThreeData.IsRightLoop CompatibleRankThreeData.rightLoopStart
    CompatibleRankThreeData.terminalStart CompatibleRankThreeData.middleStart
  dsimp [reverseCompatibleData]
  omega

/-- Reversal sends the initial endpoint class to the terminal endpoint class. -/
@[simp]
theorem reverseCompatibleData_isInitialParallel_rev {n : ℕ}
    (D : CompatibleRankThreeData n) (j : Fin n) :
    (reverseCompatibleData D).IsInitialParallel j.rev ↔ D.IsTerminalParallel j := by
  have hg := D.groundSize_eq
  have hjrev := rev_val_add_val_succ j
  unfold CompatibleRankThreeData.IsInitialParallel
    CompatibleRankThreeData.IsTerminalParallel CompatibleRankThreeData.rightLoopStart
    CompatibleRankThreeData.terminalStart CompatibleRankThreeData.middleStart
  dsimp [reverseCompatibleData]
  omega

/-- Reversal sends the terminal endpoint class to the initial endpoint class. -/
@[simp]
theorem reverseCompatibleData_isTerminalParallel_rev {n : ℕ}
    (D : CompatibleRankThreeData n) (j : Fin n) :
    (reverseCompatibleData D).IsTerminalParallel j.rev ↔ D.IsInitialParallel j := by
  have hg := D.groundSize_eq
  have hjrev := rev_val_add_val_succ j
  unfold CompatibleRankThreeData.IsInitialParallel
    CompatibleRankThreeData.IsTerminalParallel CompatibleRankThreeData.rightLoopStart
    CompatibleRankThreeData.terminalStart CompatibleRankThreeData.middleStart
  dsimp [reverseCompatibleData]
  omega

/-- The numeric simplification map is reversed on the simplified ground set. -/
@[simp]
theorem reverseCompatibleData_simplifiedIndex_rev {n : ℕ}
    (D : CompatibleRankThreeData n) (j : Fin n) :
    (reverseCompatibleData D).simplifiedIndex j.rev = (D.simplifiedIndex j).rev := by
  apply Fin.ext
  have hg := D.groundSize_eq
  have hm := D.simplifiedSize_ge_three
  have hjrev := rev_val_add_val_succ j
  have hsrev := rev_val_add_val_succ (D.simplifiedIndex j)
  change (D.simplifiedIndex j).rev.val + D.simplifiedIndexNat j + 1 =
      D.simplifiedSize at hsrev
  unfold CompatibleRankThreeData.simplifiedIndex
  unfold CompatibleRankThreeData.simplifiedIndexNat at hsrev ⊢
  simp only [CompatibleRankThreeData.middleStart,
    CompatibleRankThreeData.terminalStart]
  dsimp [reverseCompatibleData]
  split_ifs at hsrev ⊢ <;> omega

/-- Reversing interval containment of three simplified points is equivalent to containment in
an original prescribed interval. -/
theorem exists_reverseInterval_three_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (x y z : Fin D.simplifiedSize) :
    (∃ H ∈ (reverseCompatibleData D).intervals,
      x.rev ∈ H.points ∧ y.rev ∈ H.points ∧ z.rev ∈ H.points) ↔
      ∃ K ∈ D.intervals, x ∈ K.points ∧ y ∈ K.points ∧ z ∈ K.points := by
  constructor
  · rintro ⟨H, hH, hx, hy, hz⟩
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
    refine ⟨K, hK, ?_, ?_, ?_⟩
    · simpa using (mem_reverseSimplifiedInterval_points_iff K x.rev).mp hx
    · simpa using (mem_reverseSimplifiedInterval_points_iff K y.rev).mp hy
    · simpa using (mem_reverseSimplifiedInterval_points_iff K z.rev).mp hz
  · rintro ⟨K, hK, hx, hy, hz⟩
    refine ⟨reverseSimplifiedInterval K, Finset.mem_image.mpr ⟨K, hK, rfl⟩, ?_, ?_, ?_⟩
    · apply (mem_reverseSimplifiedInterval_points_iff K x.rev).mpr
      simpa using hx
    · apply (mem_reverseSimplifiedInterval_points_iff K y.rev).mpr
      simpa using hy
    · apply (mem_reverseSimplifiedInterval_points_iff K z.rev).mpr
      simpa using hz

/-- The explicit ordered compatible nonbasis condition is invariant under reversing the raw
ground set and the compatible data. -/
theorem orderedCompatibleNonbasis_reverse_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (cols : Fin 3 ↪o Fin n) :
    OrderedCompatibleNonbasis (reverseCompatibleData D) (reverseOrderEmbedding cols) ↔
      OrderedCompatibleNonbasis D cols := by
  have hrev0 : (0 : Fin 3).rev = 2 := by decide
  have hrev1 : (1 : Fin 3).rev = 1 := by decide
  have hrev2 : (2 : Fin 3).rev = 0 := by decide
  unfold OrderedCompatibleNonbasis
  simp only [reverseOrderEmbedding_apply, hrev0, hrev1, hrev2,
    reverseCompatibleData_isLoop_rev, reverseCompatibleData_isInitialParallel_rev,
    reverseCompatibleData_isTerminalParallel_rev, reverseCompatibleData_simplifiedIndex_rev]
  have hE := exists_reverseInterval_three_iff D (D.simplifiedIndex (cols 2))
    (D.simplifiedIndex (cols 1)) (D.simplifiedIndex (cols 0))
  constructor
  · rintro (h2 | h1 | h0 | hterm | hinit | hcol)
    · right
      right
      exact Or.inl h2
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h0
    · right
      right
      right
      right
      left
      rcases hterm with h | h | h
      · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
      · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      · exact Or.inl ⟨h.2, h.1⟩
    · right
      right
      right
      left
      rcases hinit with h | h | h
      · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
      · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      · exact Or.inl ⟨h.2, h.1⟩
    · right
      right
      right
      right
      right
      rcases hcol with ⟨h21, h20, h10, hinterval⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h01
        exact h10 (congrArg Fin.rev h01.symm)
      · intro h02
        exact h20 (congrArg Fin.rev h02.symm)
      · intro h12
        exact h21 (congrArg Fin.rev h12.symm)
      · obtain ⟨H, hH, h2H, h1H, h0H⟩ := hE.mp hinterval
        exact ⟨H, hH, h0H, h1H, h2H⟩
  · rintro (h0 | h1 | h2 | hinit | hterm | hcol)
    · right
      right
      exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h2
    · right
      right
      right
      right
      left
      rcases hinit with h | h | h
      · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
      · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      · exact Or.inl ⟨h.2, h.1⟩
    · right
      right
      right
      left
      rcases hterm with h | h | h
      · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
      · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      · exact Or.inl ⟨h.2, h.1⟩
    · right
      right
      right
      right
      right
      rcases hcol with ⟨h01, h02, h12, hinterval⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h21
        exact h12 (Fin.rev_injective h21).symm
      · intro h20
        exact h02 (Fin.rev_injective h20).symm
      · intro h10
        exact h01 (Fin.rev_injective h10).symm
      · apply hE.mpr
        obtain ⟨H, hH, h0H, h1H, h2H⟩ := hinterval
        exact ⟨H, hH, h2H, h1H, h0H⟩

/-- Exact-support predicates are invariant under simultaneous reversal. -/
theorem realizesCompatibleSupport_reverse_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (A : Matrix (Fin 3) (Fin n) ℝ) :
    RealizesCompatibleSupport (reverseCompatibleData D) (reverseMatrix A) ↔
      RealizesCompatibleSupport D A := by
  constructor
  · intro h cols
    have hrev := h (reverseOrderEmbedding cols)
    rw [orderedMinor_reverseMatrix, reverseOrderEmbedding_allRows,
      reverseOrderEmbedding_reverseOrderEmbedding] at hrev
    rw [tripleNonbasis_selectedTriple_iff_ordered] at hrev ⊢
    exact hrev.trans (orderedCompatibleNonbasis_reverse_iff D cols)
  · intro h cols
    rw [orderedMinor_reverseMatrix, reverseOrderEmbedding_allRows]
    have hrev := h (reverseOrderEmbedding cols)
    rw [tripleNonbasis_selectedTriple_iff_ordered] at hrev ⊢
    have hcompat := orderedCompatibleNonbasis_reverse_iff D
      (reverseOrderEmbedding cols)
    simp only [reverseOrderEmbedding_reverseOrderEmbedding] at hcompat
    exact hrev.trans hcompat.symm

end

end ToeplitzPositroids.RankThree
