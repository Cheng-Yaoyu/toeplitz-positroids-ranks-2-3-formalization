import ToeplitzPositroids.RankThree.OneSidedSupportBridge
import Mathlib.Tactic

/-!
# Exact one-sided support theorem

This file instantiates the ordered support bridge for the endpoint-aware constructors.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- Adjacent equality throughout an edge interval. -/
def AdjacentSlopesEqualBetween (x y : ℕ → ℝ) (i k : ℕ) : Prop :=
  ∀ t : ℕ, i ≤ t → t + 2 ≤ k → edgeSlope x y t = edgeSlope x y (t + 1)

/-- A constant slope run is equivalent to all its adjacent comparisons being equal. -/
theorem ratioSlopesConstantBetween_iff_adjacent {x y : ℕ → ℝ} {i k : ℕ} :
    SlopesConstantBetween x y i k ↔ AdjacentSlopesEqualBetween x y i k := by
  constructor
  · intro h t hit htk
    exact (h hit (by omega)).trans (h (by omega) (by omega)).symm
  · intro h t hit htk
    induction t, hit using Nat.le_induction with
    | base => rfl
    | succ t hit ih =>
        exact (h t hit (by omega)).symm.trans (ih (by omega))

/-- On the canonical positive core, constant slopes are exactly prescribed comparisons. -/
theorem finiteSynthesized_slopesConstant_iff_allPrescribed {n : ℕ}
    (D : CompatibleRankThreeData n) {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon (CompatibleSlopePattern.targetSlope D) ε)
    {i k : ℕ} (hik : i < k) (hk : k < D.simplifiedSize) :
    SlopesConstantBetween
        (ratioPointX (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε))
        (ratioPointY (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε)) i k ↔
      CompatibleSlopePattern.AllPrescribedBetween D i k := by
  rw [ratioSlopesConstantBetween_iff_adjacent]
  constructor
  · intro h t hit htk
    have ht₀ : t < D.simplifiedSize - 1 := by omega
    have ht₁ : t + 1 < D.simplifiedSize - 1 := by omega
    have heq := h t hit htk
    rw [finiteSynthesizedRatio_edgeSlope hε ⟨t, ht₀⟩,
      finiteSynthesizedRatio_edgeSlope hε ⟨t + 1, ht₁⟩] at heq
    let u : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
    exact (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D u).mp (by
      simpa [CompatibleSlopePattern.comparisonLeft,
        CompatibleSlopePattern.comparisonRight, u] using heq)
  · intro h t hit htk
    have ht₀ : t < D.simplifiedSize - 1 := by omega
    have ht₁ : t + 1 < D.simplifiedSize - 1 := by omega
    let u : Fin (D.simplifiedSize - 2) := ⟨t, by omega⟩
    have heq := (CompatibleSlopePattern.targetSlope_castSucc_eq_succ_iff D u).mpr
      (h t hit htk)
    rw [finiteSynthesizedRatio_edgeSlope hε ⟨t, ht₀⟩,
      finiteSynthesizedRatio_edgeSlope hε ⟨t + 1, ht₁⟩]
    simpa [CompatibleSlopePattern.comparisonLeft,
      CompatibleSlopePattern.comparisonRight, u] using heq

/-- For three distinct simplified vertices, the core area vanishes exactly when the vertices lie
in one prescribed interval. -/
theorem finiteSynthesized_area_eq_zero_iff_interval {n : ℕ}
    (D : CompatibleRankThreeData n) {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon (CompatibleSlopePattern.targetSlope D) ε)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < D.simplifiedSize) :
    orientedArea
        (ratioPointX (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε))
        (ratioPointY (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε))
        i j k = 0 ↔
      ∃ H ∈ D.intervals, H.left.val ≤ i ∧ k ≤ H.right.val := by
  have hsize : D.simplifiedSize - 1 + 1 = D.simplifiedSize := by
    exact Nat.sub_add_cancel (by omega)
  have hx : StrictlyIncreasingUpTo
      (ratioPointX (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε))
      D.simplifiedSize := by
    intro a b hab hb
    apply finiteSynthesizedRatio_pointX_strict hε hab
    rwa [hsize]
  have hs : SlopesMonotoneUpTo
      (ratioPointX (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε))
      (ratioPointY (finiteSynthesizedRatio (CompatibleSlopePattern.targetSlope D) ε))
      D.simplifiedSize := by
    intro a b hab hb
    apply finiteSynthesizedRatio_slopesMonotone hε
      (CompatibleSlopePattern.targetSlope_monotone D) hab
    rwa [hsize]
  rw [orientedArea_eq_zero_iff_slopesConstantBetween _ _ hx hs hij hjk hk,
    finiteSynthesized_slopesConstant_iff_allPrescribed D hε (hij.trans hjk) hk,
    CompatibleSlopePattern.allPrescribedBetween_iff_interval D (by omega) hk]

/-- With no loops and singleton endpoint classes, the compatible simplification index is the raw
index. -/
theorem simplifiedIndexNat_eq_val_of_singletonEndpoints {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : D.initialParallelSize = 1)
    (hq : D.terminalParallelSize = 1) (j : Fin n) :
    D.simplifiedIndexNat j = j.val := by
  have hn : n = D.simplifiedSize := by
    have hg := D.groundSize_eq
    have hm := D.simplifiedSize_ge_three
    omega
  unfold CompatibleRankThreeData.simplifiedIndexNat
  simp only [CompatibleRankThreeData.middleStart, CompatibleRankThreeData.terminalStart,
    hleft, hp, zero_add]
  have hm := D.simplifiedSize_ge_three
  have hjBound := j.isLt
  have hterminal : 1 + (D.simplifiedSize - 2) = D.simplifiedSize - 1 := by omega
  split_ifs <;> omega

/-- In the singleton-endpoint loop-free case the ordered compatible condition is exactly
containment of the three raw indices in one prescribed interval. -/
theorem orderedCompatibleNonbasis_iff_interval_singletonEndpoints {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : D.initialParallelSize = 1)
    (hq : D.terminalParallelSize = 1) (cols : Fin 3 ↪o Fin n) :
    OrderedCompatibleNonbasis D cols ↔
      ∃ H ∈ D.intervals, H.left.val ≤ (cols 0).val ∧ (cols 2).val ≤ H.right.val := by
  have hn : n = D.simplifiedSize := by
    have hg := D.groundSize_eq
    have hm := D.simplifiedSize_ge_three
    omega
  have hloop : ∀ j : Fin n, ¬D.IsLoop j := by
    intro j
    have hrs := D.rightLoopStart_add_rightLoopCount
    rw [hright, add_zero] at hrs
    unfold CompatibleRankThreeData.IsLoop CompatibleRankThreeData.IsLeftLoop
      CompatibleRankThreeData.IsRightLoop
    simp [hleft]
    omega
  have hinitPair : ∀ {i j : Fin n}, i ≠ j →
      ¬(D.IsInitialParallel i ∧ D.IsInitialParallel j) := by
    intro i j hij hpair
    unfold CompatibleRankThreeData.IsInitialParallel CompatibleRankThreeData.middleStart at hpair
    simp [hleft, hp] at hpair
    apply hij
    apply Fin.ext
    omega
  have htermPair : ∀ {i j : Fin n}, i ≠ j →
      ¬(D.IsTerminalParallel i ∧ D.IsTerminalParallel j) := by
    intro i j hij hpair
    unfold CompatibleRankThreeData.IsTerminalParallel CompatibleRankThreeData.terminalStart
      CompatibleRankThreeData.rightLoopStart CompatibleRankThreeData.middleStart at hpair
    simp [hleft, hp, hq] at hpair
    apply hij
    apply Fin.ext
    omega
  have h01 : cols 0 ≠ cols 1 := ne_of_lt (cols.strictMono (by decide))
  have h02 : cols 0 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  have h12 : cols 1 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  unfold OrderedCompatibleNonbasis
  simp only [hloop, false_or, hinitPair h01, hinitPair h02, hinitPair h12,
    htermPair h01, htermPair h02, htermPair h12]
  have hsimpNat : ∀ j : Fin n, D.simplifiedIndexNat j = j.val := by
    intro j
    exact simplifiedIndexNat_eq_val_of_singletonEndpoints D hleft hright hp hq j
  constructor
  · rintro ⟨h01', h02', h12', H, hH, h0, h1, h2⟩
    rw [SimplifiedInterval.mem_points] at h0 h2
    refine ⟨H, hH, ?_, ?_⟩
    · have hv := Fin.mk_le_mk.mp h0.1
      rw [hsimpNat (cols 0)] at hv
      exact hv
    · have hv := Fin.mk_le_mk.mp h2.2
      rw [hsimpNat (cols 2)] at hv
      exact hv
  · rintro ⟨H, hH, h0, h2⟩
    refine ⟨?_, ?_, ?_, H, hH, ?_, ?_, ?_⟩
    · intro heq
      apply h01
      apply Fin.ext
      have hv := congrArg Fin.val heq
      change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 1) at hv
      rw [hsimpNat (cols 0), hsimpNat (cols 1)] at hv
      exact hv
    · intro heq
      apply h02
      apply Fin.ext
      have hv := congrArg Fin.val heq
      change D.simplifiedIndexNat (cols 0) = D.simplifiedIndexNat (cols 2) at hv
      rw [hsimpNat (cols 0), hsimpNat (cols 2)] at hv
      exact hv
    · intro heq
      apply h12
      apply Fin.ext
      have hv := congrArg Fin.val heq
      change D.simplifiedIndexNat (cols 1) = D.simplifiedIndexNat (cols 2) at hv
      rw [hsimpNat (cols 1), hsimpNat (cols 2)] at hv
      exact hv
    · rw [SimplifiedInterval.mem_points]
      constructor
      · apply Fin.mk_le_mk.mpr
        change H.left.val ≤ D.simplifiedIndexNat (cols 0)
        rw [hsimpNat (cols 0)]
        exact h0
      · apply Fin.mk_le_mk.mpr
        change D.simplifiedIndexNat (cols 0) ≤ H.right.val
        rw [hsimpNat (cols 0)]
        have h02le : (cols 0).val ≤ (cols 2).val :=
          (cols.strictMono (by decide : (0 : Fin 3) < 2)).le
        exact h02le.trans h2
    · rw [SimplifiedInterval.mem_points]
      constructor
      · apply Fin.mk_le_mk.mpr
        change H.left.val ≤ D.simplifiedIndexNat (cols 1)
        rw [hsimpNat (cols 1)]
        have h01le : (cols 0).val ≤ (cols 1).val :=
          (cols.strictMono (by decide : (0 : Fin 3) < 1)).le
        exact h0.trans h01le
      · apply Fin.mk_le_mk.mpr
        change D.simplifiedIndexNat (cols 1) ≤ H.right.val
        rw [hsimpNat (cols 1)]
        have h12le : (cols 1).val ≤ (cols 2).val :=
          (cols.strictMono (by decide : (1 : Fin 3) < 2)).le
        exact h12le.trans h2
    · rw [SimplifiedInterval.mem_points]
      constructor
      · apply Fin.mk_le_mk.mpr
        change H.left.val ≤ D.simplifiedIndexNat (cols 2)
        rw [hsimpNat (cols 2)]
        have h02le : (cols 0).val ≤ (cols 2).val :=
          (cols.strictMono (by decide : (0 : Fin 3) < 2)).le
        exact h0.trans h02le
      · apply Fin.mk_le_mk.mpr
        change D.simplifiedIndexNat (cols 2) ≤ H.right.val
        rw [hsimpNat (cols 2)]
        exact h2

/-- Exact maximal-minor support realization of compatible data. -/
def RealizesCompatibleSupport {n : ℕ} (D : CompatibleRankThreeData n)
    (A : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  ∀ cols : Fin 3 ↪o Fin n,
    orderedMinor A (allRows 3) cols = 0 ↔ D.TripleNonbasis (selectedTripleFinset cols)

/-- Pull an ordered embedding back along an equality of cardinalities. -/
def pullbackOrderEmbedding {k n₁ n₂ : ℕ} (h : n₁ = n₂)
    (cols : Fin k ↪o Fin n₂) : Fin k ↪o Fin n₁ :=
  OrderEmbedding.ofStrictMono (fun i ↦ ⟨(cols i).val, by omega⟩) <| by
    intro i j hij
    exact Fin.mk_lt_mk.mpr (cols.strictMono hij)

theorem orderedMinor_castColumnCount {m n₁ n₂ k : ℕ} (h : n₁ = n₂)
    (A : Matrix (Fin m) (Fin n₁) ℝ) (rows : Fin k ↪o Fin m)
    (cols : Fin k ↪o Fin n₂) :
    orderedMinor (castColumnCount h A) rows cols =
      orderedMinor A rows (pullbackOrderEmbedding h cols) := by
  apply congrArg Matrix.det
  ext i j
  rfl

/-- The positive core has exactly the compatible support in the unprotected singleton-endpoint
case. -/
theorem exists_exactSupport_singletonEndpoints {n : ℕ}
    (D : CompatibleRankThreeData n) (hleft : D.leftLoopCount = 0)
    (hright : D.rightLoopCount = 0) (hp : D.initialParallelSize = 1)
    (hq : D.terminalParallelSize = 1) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      RealizesCompatibleSupport D (rankThreeToeplitz a) := by
  obtain ⟨ε, hε, htnn₀, hrank₀, hpattern⟩ :=
    exists_simplifiedPositiveCoreRealization_withPattern D
  have hcount : (D.simplifiedSize - 1) + 1 = n := by
    have hg := D.groundSize_eq
    have hm := D.simplifiedSize_ge_three
    omega
  let a₀ := synthesizedCoefficientVector (CompatibleSlopePattern.targetSlope D) ε
  let a : Fin (n + 2) → ℝ := castRankThreeCoefficients hcount a₀
  have hmatrix : rankThreeToeplitz a = castColumnCount hcount (rankThreeToeplitz a₀) :=
    rankThreeToeplitz_castRankThreeCoefficients hcount a₀
  refine ⟨a, hmatrix ▸ TotallyNonnegative.castColumnCount htnn₀,
    hmatrix ▸ HasFullRowRank.castColumnCount hrank₀, ?_⟩
  intro cols
  let cols₀ := pullbackOrderEmbedding hcount cols
  have h01 : cols₀ 0 < cols₀ 1 := cols₀.strictMono (by decide)
  have h12 : cols₀ 1 < cols₀ 2 := cols₀.strictMono (by decide)
  rw [hmatrix, orderedMinor_castColumnCount]
  change orderedMinor (rankThreeToeplitz a₀) (allRows 3) cols₀ = 0 ↔
    D.TripleNonbasis (selectedTripleFinset cols)
  rw [← selectedTripleEmbedding_eq cols₀]
  rw [synthesizedToeplitz_minor_eq_area hε h01 h12]
  have htop : synthesizedCoefficientVector (CompatibleSlopePattern.targetSlope D) ε
        (cols₀ 0).succ.succ *
      synthesizedCoefficientVector (CompatibleSlopePattern.targetSlope D) ε
        (cols₀ 1).succ.succ *
      synthesizedCoefficientVector (CompatibleSlopePattern.targetSlope D) ε
        (cols₀ 2).succ.succ ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (synthesizedCoefficientVector_pos hε _).ne'
        (synthesizedCoefficientVector_pos hε _).ne')
      (synthesizedCoefficientVector_pos hε _).ne'
  rw [mul_eq_zero]
  simp only [htop, false_or]
  have hk : (cols₀ 2).val < D.simplifiedSize := by
    have hm := D.simplifiedSize_ge_three
    have := (cols₀ 2).isLt
    omega
  rw [finiteSynthesized_area_eq_zero_iff_interval D hε h01 h12 hk]
  rw [tripleNonbasis_selectedTriple_iff_ordered,
    orderedCompatibleNonbasis_iff_interval_singletonEndpoints D hleft hright hp hq]
  rfl

end

end ToeplitzPositroids.RankThree
