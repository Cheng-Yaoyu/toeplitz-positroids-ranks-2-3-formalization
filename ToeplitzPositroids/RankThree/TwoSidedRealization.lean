import ToeplitzPositroids.RankThree.ArbitraryZeroPattern
import ToeplitzPositroids.RankThree.StrictCount
import ToeplitzPositroids.RankThree.TwoSidedCombinatorics
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Two-sided rank-three realizations

This file assembles Proposition 21.  Prescribed protected collinear intervals
are converted to interior consecutive-determinant zero runs, realized by the
sine perturbation theorem, and then translated back to the raw ground set with
both loop blocks.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids Matrix Set

noncomputable section

/-- The all-one coefficient vector in an arbitrary band degree. -/
def unitBandCoefficients (d : ℕ) : Fin (d + 1) → ℝ := fun _ ↦ 1

theorem unitBand_degree_zero_strict {d : ℕ} (hd : d = 0) :
    StrictlyLogConcaveWithZeroBoundary (unitBandCoefficients d) := by
  subst d
  simpa [unitBandCoefficients, degreeZeroUnitCoefficients] using
    degreeZero_strictlyLogConcave

theorem unitBand_degree_one_strict {d : ℕ} (hd : d = 1) :
    StrictlyLogConcaveWithZeroBoundary (unitBandCoefficients d) := by
  subst d
  simpa [unitBandCoefficients, degreeOneUnitCoefficients] using
    degreeOne_strictlyLogConcave

theorem unitBand_degree_zero_tnn_full {d : ℕ} (hd : d = 0) :
    TotallyNonnegative (bandedMatrix (unitBandCoefficients d)) ∧
      HasFullRowRank (bandedMatrix (unitBandCoefficients d)) ∧
      ∀ cols : Fin 3 ↪o Fin (d + 3),
        orderedMinor (bandedMatrix (unitBandCoefficients d)) (allRows 3) cols ≠ 0 := by
  subst d
  simpa [unitBandCoefficients, degreeZeroUnitCoefficients] using degreeZero_tnn_fullRowRank

theorem unitBand_degree_one_tnn_full {d : ℕ} (hd : d = 1) :
    TotallyNonnegative (bandedMatrix (unitBandCoefficients d)) ∧
      HasFullRowRank (bandedMatrix (unitBandCoefficients d)) ∧
      ∀ cols : Fin 3 ↪o Fin (d + 3),
        orderedMinor (bandedMatrix (unitBandCoefficients d)) (allRows 3) cols ≠ 0 := by
  subst d
  simpa [unitBandCoefficients, degreeOneUnitCoefficients] using degreeOne_tnn_fullRowRank

namespace CompatibleRankThreeData

variable {n : ℕ} (D : CompatibleRankThreeData n)

/-- The target zero set with the endpoint shift removed, in the coordinate type
used by `arbitraryZeroPattern`. -/
def targetZeroSetFin : Set (Fin (twoSidedBandDegree D - 1)) :=
  {i | i.val + 1 ∈ targetZeroSet D}

@[simp]
theorem mem_targetZeroSetFin_iff {i : Fin (twoSidedBandDegree D - 1)} :
    i ∈ targetZeroSetFin D ↔ i.val + 1 ∈ targetZeroSet D :=
  Iff.rfl

/-- A whole consecutive determinant run is prescribed exactly when its two
extreme vertices lie in one prescribed interval. -/
theorem targetZeroSet_run_iff {u v : ℕ} (huv : u + 2 ≤ v)
    (hv : v < D.simplifiedSize) :
    (∀ t : ℕ, u ≤ t → t + 2 ≤ v → t ∈ targetZeroSet D) ↔
      ∃ H ∈ D.intervals, H.left.val ≤ u ∧ v ≤ H.right.val := by
  constructor
  · intro hall
    obtain ⟨H₀, hH₀, hleft₀, hright₀⟩ :=
      (mem_targetZeroSet_iff D).mp (hall u le_rfl huv)
    have hreach : ∀ q : ℕ, u ≤ q → q + 2 ≤ v → q + 2 ≤ H₀.right.val := by
      intro q huq
      induction q, huq using Nat.le_induction with
      | base =>
          intro _
          exact hright₀
      | succ q huq ih =>
          intro hqv
          have ih' := ih (by omega)
          obtain ⟨H, hH, hleft, hright⟩ :=
            (mem_targetZeroSet_iff D).mp (hall (q + 1) (by omega) hqv)
          let x : Fin D.simplifiedSize := ⟨q + 1, by omega⟩
          let y : Fin D.simplifiedSize := ⟨q + 2, by omega⟩
          have hxy : x ≠ y := by
            intro h
            have hv := congrArg Fin.val h
            change q + 1 = q + 2 at hv
            omega
          have hx₀ : x ∈ H₀.points := by
            rw [SimplifiedInterval.mem_points]
            change H₀.left.val ≤ q + 1 ∧ q + 1 ≤ H₀.right.val
            omega
          have hy₀ : y ∈ H₀.points := by
            rw [SimplifiedInterval.mem_points]
            change H₀.left.val ≤ q + 2 ∧ q + 2 ≤ H₀.right.val
            omega
          have hxH : x ∈ H.points := by
            rw [SimplifiedInterval.mem_points]
            change H.left.val ≤ q + 1 ∧ q + 1 ≤ H.right.val
            omega
          have hyH : y ∈ H.points := by
            rw [SimplifiedInterval.mem_points]
            change H.left.val ≤ q + 2 ∧ q + 2 ≤ H.right.val
            omega
          have hEq : H₀ = H := D.interval_eq_of_two_common hH₀ hH hxy hx₀ hxH hy₀ hyH
          rw [hEq]
          exact hright
    have hfinal := hreach (v - 2) (by omega) (by omega)
    refine ⟨H₀, hH₀, hleft₀, ?_⟩
    omega
  · rintro ⟨H, hH, hleft, hright⟩ t hut htv
    apply (mem_targetZeroSet_iff D).mpr
    exact ⟨H, hH, hleft.trans hut, htv.trans hright⟩

/-- Canonical order isomorphism between band columns and simplified vertices. -/
def bandColumnOrderIso : Fin (twoSidedBandDegree D + 3) ≃o Fin D.simplifiedSize :=
  Fin.castOrderIso (twoSidedBandDegree_add_three D)

/-- The increasing reindexing from simplified vertices back to band columns. -/
def simplifiedToBandEmbedding :
    Fin D.simplifiedSize ↪o Fin (twoSidedBandDegree D + 3) :=
  (bandColumnOrderIso D).symm.toOrderEmbedding

/-- A banded matrix reindexed by the compatible simplified ground set. -/
def simplifiedBandedMatrix
  (b : Fin (twoSidedBandDegree D + 1) → ℝ) :
    Matrix (Fin 3) (Fin D.simplifiedSize) ℝ :=
  (bandedMatrix b).submatrix (allRows 3) (simplifiedToBandEmbedding D)

/-- Reindexing preserves every selected maximal minor. -/
theorem simplifiedBandedMatrix_minor
    (b : Fin (twoSidedBandDegree D + 1) → ℝ)
    (cols : Fin 3 ↪o Fin D.simplifiedSize) :
    orderedMinor (simplifiedBandedMatrix D b) (allRows 3) cols =
      orderedMinor (bandedMatrix b) (allRows 3)
        (cols.trans (simplifiedToBandEmbedding D)) := by
  rw [simplifiedBandedMatrix]
  rw [orderedMinor_submatrix (bandedMatrix b) (allRows 3)
    (simplifiedToBandEmbedding D) (allRows 3) cols]
  have hrows : (allRows 3).trans (allRows 3) = allRows 3 := by
    apply RelEmbedding.ext
    intro i
    rfl
  rw [hrows]

/-- Total nonnegativity passes through the canonical column reindexing. -/
theorem simplifiedBandedMatrix_totallyNonnegative
    {b : Fin (twoSidedBandDegree D + 1) → ℝ}
    (h : TotallyNonnegative (bandedMatrix b)) :
    TotallyNonnegative (simplifiedBandedMatrix D b) :=
  h.submatrix (allRows 3) (simplifiedToBandEmbedding D)

/-- A positive left endpoint determinant gives full row rank after reindexing. -/
theorem simplifiedBandedMatrix_hasFullRowRank
    {b : Fin (twoSidedBandDegree D + 1) → ℝ}
    (hb : PositiveBandCoefficients b) :
    HasFullRowRank (simplifiedBandedMatrix D b) := by
  have hm : 3 ≤ D.simplifiedSize := D.simplifiedSize_ge_three
  let i : Fin D.simplifiedSize := ⟨0, by omega⟩
  let j : Fin D.simplifiedSize := ⟨1, by omega⟩
  let k : Fin D.simplifiedSize := ⟨2, by omega⟩
  let cols : Fin 3 ↪o Fin D.simplifiedSize :=
    selectedTripleEmbedding i j k (by simp [i, j]) (by simp [j, k])
  refine ⟨cols, ?_⟩
  rw [simplifiedBandedMatrix_minor]
  let z₀ : Fin (twoSidedBandDegree D + 3) := ⟨0, by omega⟩
  let z₁ : Fin (twoSidedBandDegree D + 3) := ⟨1, by omega⟩
  let z₂ : Fin (twoSidedBandDegree D + 3) := ⟨2, by omega⟩
  have h₀₁ : z₀ < z₁ := Fin.mk_lt_mk.mpr (by omega)
  have h₁₂ : z₁ < z₂ := Fin.mk_lt_mk.mpr (by omega)
  have hembed : cols.trans (simplifiedToBandEmbedding D) =
      selectedTripleEmbedding z₀ z₁ z₂ h₀₁ h₁₂ := by
    apply RelEmbedding.ext
    intro t
    fin_cases t <;> apply Fin.ext <;> rfl
  rw [hembed, orderedMinor_selectedTriple_eq_threeColumnMatrix_det]
  change consecutiveDeterminant b 0 ≠ 0
  rw [consecutiveDeterminant_zero]
  exact (pow_pos (hb 0) 3).ne'

/-- An exact interior target pattern extends to all consecutive determinants,
because the two boundary determinants are strictly positive. -/
theorem consecutiveDeterminant_zero_iff_target
    (hTwo : HasTwoSidedLoops D)
    {b : Fin (twoSidedBandDegree D + 1) → ℝ}
    (hb : PositiveBandCoefficients b)
    (hpattern : ∀ i : Fin (twoSidedBandDegree D - 1),
      consecutiveDeterminant b ⟨i + 1, by omega⟩ = 0 ↔
        i ∈ targetZeroSetFin D)
    (t : Fin (twoSidedBandDegree D + 1)) :
    consecutiveDeterminant b t = 0 ↔ t.val ∈ targetZeroSet D := by
  by_cases ht0 : t.val = 0
  · have ht : t = 0 := Fin.ext ht0
    subst t
    rw [consecutiveDeterminant_zero]
    constructor
    · intro h
      exact ((pow_ne_zero _ (hb 0).ne') h).elim
    · intro h
      have hi := targetZeroSet_interior D hTwo h
      omega
  by_cases htd : t.val = twoSidedBandDegree D
  · have ht : t = Fin.last (twoSidedBandDegree D) := Fin.ext htd
    subst t
    rw [consecutiveDeterminant_last]
    constructor
    · intro h
      exact ((pow_ne_zero _ (hb _).ne') h).elim
    · intro h
      have hi := targetZeroSet_interior D hTwo h
      omega
  · let i : Fin (twoSidedBandDegree D - 1) := ⟨t.val - 1, by omega⟩
    have hindex : (⟨i + 1, by omega⟩ : Fin (twoSidedBandDegree D + 1)) = t := by
      apply Fin.ext
      simp [i]
      omega
    rw [← hindex, hpattern]
    exact Iff.rfl

/-- For the realized band, a selected triple is dependent exactly when its
three vertices lie in one prescribed compatible interval. -/
theorem bandedMatrix_triple_zero_iff_interval
    (hTwo : HasTwoSidedLoops D)
    (hd : 2 ≤ twoSidedBandDegree D)
    {b : Fin (twoSidedBandDegree D + 1) → ℝ}
    (hb : StrictlyLogConcaveWithZeroBoundary b)
    (hTNN : TotallyNonnegative (bandedMatrix b))
    (hpattern : ∀ i : Fin (twoSidedBandDegree D - 1),
      consecutiveDeterminant b ⟨i + 1, by omega⟩ = 0 ↔
        i ∈ targetZeroSetFin D)
    {p q r : Fin (twoSidedBandDegree D + 3)} (hpq : p < q) (hqr : q < r) :
    orderedMinor (bandedMatrix b) (allRows 3)
        (selectedTripleEmbedding p q r hpq hqr) = 0 ↔
      ∃ H ∈ D.intervals,
        H.left.val ≤ p.val ∧ r.val ≤ H.right.val := by
  have hTN₂ := bandedMatrix_tnUpTo_two_of_strictLogConcave hb
  have hsimple := bandedMatrix_isSimpleNonloopConfiguration hd hb
  have hslopes : SlopesMonotoneUpTo
      (matrixMomentU (bandedMatrix b)) (matrixMomentV (bandedMatrix b))
      (twoSidedBandDegree D + 3) :=
    (totallyNonnegative_iff_momentSlopesMonotone hTN₂ hsimple).mp hTNN
  rw [orderedMinor_selectedTriple_eq_zero_iff_slopesConstantBetween
    hTN₂ hsimple hslopes hpq hqr]
  change
    (SlopesConstantBetween (matrixMomentU (bandedMatrix b))
      (matrixMomentV (bandedMatrix b)) p.val r.val) ↔ _
  rw [show SlopesConstantBetween (matrixMomentU (bandedMatrix b))
      (matrixMomentV (bandedMatrix b)) p.val r.val ↔
        ∀ {t : ℕ}, p.val ≤ t → t + 1 < r.val →
          edgeSlope (matrixMomentU (bandedMatrix b)) (matrixMomentV (bandedMatrix b)) t =
            edgeSlope (matrixMomentU (bandedMatrix b)) (matrixMomentV (bandedMatrix b)) (t + 1) by
    exact slopesConstantBetween_iff_adjacent]
  have hrun := targetZeroSet_run_iff D (u := p.val) (v := r.val)
    (by omega) (by
      have hr := r.isLt
      have hsize := twoSidedBandDegree_add_three D
      omega)
  rw [← hrun]
  constructor
  · intro hs t hpt htr
    let tt : Fin (twoSidedBandDegree D + 1) := ⟨t, by omega⟩
    have heq : consecutiveDeterminant b tt = 0 := by
      apply (consecutiveDeterminant_eq_zero_iff_slope_eq hb hsimple tt).mpr
      rw [bandMomentSlope_eq_edgeSlope, bandMomentSlope_eq_edgeSlope]
      simpa [tt, consecutiveSlopeIndex] using hs hpt (by omega)
    exact (consecutiveDeterminant_zero_iff_target D hTwo hb.1 hpattern tt).mp heq
  · intro hz t hpt htr
    let tt : Fin (twoSidedBandDegree D + 1) := ⟨t, by omega⟩
    have hdet : consecutiveDeterminant b tt = 0 :=
      (consecutiveDeterminant_zero_iff_target D hTwo hb.1 hpattern tt).mpr
        (hz t hpt (by omega))
    have heq := (consecutiveDeterminant_eq_zero_iff_slope_eq hb hsimple tt).mp hdet
    rw [bandMomentSlope_eq_edgeSlope, bandMomentSlope_eq_edgeSlope] at heq
    simpa [tt, consecutiveSlopeIndex] using heq

/-- The same exact triple criterion after reindexing the band by simplified
vertices. -/
theorem simplifiedBandedMatrix_triple_zero_iff_interval
    (hTwo : HasTwoSidedLoops D) (hd : 2 ≤ twoSidedBandDegree D)
    {b : Fin (twoSidedBandDegree D + 1) → ℝ}
    (hb : StrictlyLogConcaveWithZeroBoundary b)
    (hTNN : TotallyNonnegative (bandedMatrix b))
    (hpattern : ∀ i : Fin (twoSidedBandDegree D - 1),
      consecutiveDeterminant b ⟨i + 1, by omega⟩ = 0 ↔
        i ∈ targetZeroSetFin D)
    {p q r : Fin D.simplifiedSize} (hpq : p < q) (hqr : q < r) :
    orderedMinor (simplifiedBandedMatrix D b) (allRows 3)
        (selectedTripleEmbedding p q r hpq hqr) = 0 ↔
      ∃ H ∈ D.intervals,
        p ∈ H.points ∧ q ∈ H.points ∧ r ∈ H.points := by
  let p' := simplifiedToBandEmbedding D p
  let q' := simplifiedToBandEmbedding D q
  let r' := simplifiedToBandEmbedding D r
  have hpq' : p' < q' := (simplifiedToBandEmbedding D).strictMono hpq
  have hqr' : q' < r' := (simplifiedToBandEmbedding D).strictMono hqr
  rw [simplifiedBandedMatrix_minor]
  have hembed :
      (selectedTripleEmbedding p q r hpq hqr).trans (simplifiedToBandEmbedding D) =
        selectedTripleEmbedding p' q' r' hpq' hqr' := by
    apply RelEmbedding.ext
    intro i
    fin_cases i <;> rfl
  rw [hembed, bandedMatrix_triple_zero_iff_interval D hTwo hd hb hTNN hpattern hpq' hqr']
  constructor
  · rintro ⟨H, hH, hleft, hright⟩
    refine ⟨H, hH, ?_, ?_, ?_⟩
    · rw [SimplifiedInterval.mem_points]
      have hpr : p.val ≤ r.val := by simpa using (hpq.trans hqr).le
      exact ⟨hleft, hpr.trans hright⟩
    · rw [SimplifiedInterval.mem_points]
      have hpq' : p.val ≤ q.val := by simpa using hpq.le
      have hqr' : q.val ≤ r.val := by simpa using hqr.le
      exact ⟨hleft.trans hpq', hqr'.trans hright⟩
    · rw [SimplifiedInterval.mem_points]
      exact ⟨hleft.trans (by simpa using (hpq.trans hqr).le), hright⟩
  · rintro ⟨H, hH, hpH, hqH, hrH⟩
    rw [SimplifiedInterval.mem_points] at hpH hrH
    exact ⟨H, hH, hpH.1, hrH.2⟩

/-- A complete realization of the simplified two-sided configuration. -/
structure TwoSidedCoreRealization where
  b : Fin (twoSidedBandDegree D + 1) → ℝ
  strict : StrictlyLogConcaveWithZeroBoundary b
  totallyNonnegative : TotallyNonnegative (simplifiedBandedMatrix D b)
  fullRowRank : HasFullRowRank (simplifiedBandedMatrix D b)
  triple_zero_iff : ∀ {p q r : Fin D.simplifiedSize} (hpq : p < q) (hqr : q < r),
    orderedMinor (simplifiedBandedMatrix D b) (allRows 3)
        (selectedTripleEmbedding p q r hpq hqr) = 0 ↔
      ∃ H ∈ D.intervals,
        p ∈ H.points ∧ q ∈ H.points ∧ r ∈ H.points

/-- The arbitrary-zero-pattern theorem realizes every two-sided datum of
degree at least two on its simplified ground set. -/
theorem exists_coreRealization_of_two_le_degree
    (hTwo : HasTwoSidedLoops D) (hd : 2 ≤ twoSidedBandDegree D) :
    Nonempty (TwoSidedCoreRealization D) := by
  obtain ⟨b, hb, hclose, hpattern, hTN₂, hTNN, hfull, hnonstruct⟩ :=
    arbitraryZeroPattern hd (targetZeroSetFin D) (epsilon := 1) zero_lt_one
  refine ⟨⟨b, hb, simplifiedBandedMatrix_totallyNonnegative D hTNN,
    simplifiedBandedMatrix_hasFullRowRank D hb.1, ?_⟩⟩
  intro p q r hpq hqr
  exact simplifiedBandedMatrix_triple_zero_iff_interval D hTwo hd hb hTNN hpattern hpq hqr

/-- The explicit identity band realizes the exceptional degree-zero case. -/
theorem exists_coreRealization_of_degree_zero
    (hTwo : HasTwoSidedLoops D) (hd : twoSidedBandDegree D = 0) :
    Nonempty (TwoSidedCoreRealization D) := by
  let b := unitBandCoefficients (twoSidedBandDegree D)
  have hb := unitBand_degree_zero_strict hd
  have hband := (unitBand_degree_zero_tnn_full hd).1
  have hnonzero := (unitBand_degree_zero_tnn_full hd).2.2
  have hEmpty : D.intervals = ∅ :=
    intervals_eq_empty_of_degree_le_one D hTwo (by omega)
  refine ⟨⟨b, hb, simplifiedBandedMatrix_totallyNonnegative D hband,
    simplifiedBandedMatrix_hasFullRowRank D hb.1, ?_⟩⟩
  intro p q r hpq hqr
  let cols : Fin 3 ↪o Fin D.simplifiedSize := selectedTripleEmbedding p q r hpq hqr
  rw [simplifiedBandedMatrix_minor]
  have hne := hnonzero (cols.trans (simplifiedToBandEmbedding D))
  constructor
  · exact fun hzero ↦ (hne hzero).elim
  · rintro ⟨H, hH, _⟩
    rw [hEmpty] at hH
    simp at hH

/-- The explicit staircase band realizes the exceptional degree-one case. -/
theorem exists_coreRealization_of_degree_one
    (hTwo : HasTwoSidedLoops D) (hd : twoSidedBandDegree D = 1) :
    Nonempty (TwoSidedCoreRealization D) := by
  let b := unitBandCoefficients (twoSidedBandDegree D)
  have hb := unitBand_degree_one_strict hd
  have hband := (unitBand_degree_one_tnn_full hd).1
  have hnonzero := (unitBand_degree_one_tnn_full hd).2.2
  have hEmpty : D.intervals = ∅ :=
    intervals_eq_empty_of_degree_le_one D hTwo (by omega)
  refine ⟨⟨b, hb, simplifiedBandedMatrix_totallyNonnegative D hband,
    simplifiedBandedMatrix_hasFullRowRank D hb.1, ?_⟩⟩
  intro p q r hpq hqr
  let cols : Fin 3 ↪o Fin D.simplifiedSize := selectedTripleEmbedding p q r hpq hqr
  rw [simplifiedBandedMatrix_minor]
  have hne := hnonzero (cols.trans (simplifiedToBandEmbedding D))
  constructor
  · exact fun hzero ↦ (hne hzero).elim
  · rintro ⟨H, hH, _⟩
    rw [hEmpty] at hH
    simp at hH

/-- Every compatible datum with two loop boundaries has a simplified core
realization, including the exceptional degrees zero and one. -/
theorem exists_twoSidedCoreRealization (hTwo : HasTwoSidedLoops D) :
    Nonempty (TwoSidedCoreRealization D) := by
  rcases Nat.eq_zero_or_pos (twoSidedBandDegree D) with hd0 | hdpos
  · exact exists_coreRealization_of_degree_zero D hTwo hd0
  by_cases hd1 : twoSidedBandDegree D = 1
  · exact exists_coreRealization_of_degree_one D hTwo hd1
  · exact exists_coreRealization_of_two_le_degree D hTwo (by omega)

/-! ## Translation to the raw ground set -/

theorem initialParallelSize_eq_one (hTwo : HasTwoSidedLoops D) :
    D.initialParallelSize = 1 :=
  D.initialParallel_singleton_of_leftLoops hTwo.1

theorem terminalParallelSize_eq_one (hTwo : HasTwoSidedLoops D) :
    D.terminalParallelSize = 1 :=
  D.terminalParallel_singleton_of_rightLoops hTwo.2

/-- With two loop boundaries the nonloop raw interval has exactly the
simplified size. -/
theorem groundSize_twoSided (hTwo : HasTwoSidedLoops D) :
    D.leftLoopCount + D.simplifiedSize + D.rightLoopCount = n := by
  have hground := D.groundSize_eq
  rw [initialParallelSize_eq_one D hTwo, terminalParallelSize_eq_one D hTwo] at hground
  have hm := D.simplifiedSize_ge_three
  omega

/-- Insert a band coefficient vector after the initial loop block and pad both
sides by zeros. -/
def translatedBandCoefficient (_hTwo : HasTwoSidedLoops D)
    (b : Fin (twoSidedBandDegree D + 1) → ℝ) : Fin (n + 2) → ℝ :=
  fun k ↦
    if h : D.leftLoopCount + 2 ≤ k.val ∧
        k.val < D.leftLoopCount + 2 + (twoSidedBandDegree D + 1) then
      b ⟨k.val - (D.leftLoopCount + 2), by omega⟩
    else 0

/-- The increasing embedding of simplified core columns into the raw ground
set, immediately after the initial loops. -/
def rawCoreEmbedding (hTwo : HasTwoSidedLoops D) : Fin D.simplifiedSize ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun j ↦ ⟨D.leftLoopCount + j.val, by
      have hground := groundSize_twoSided D hTwo
      omega⟩)
    (by intro i j hij; simp only [Fin.mk_lt_mk]; omega)

@[simp]
theorem rawCoreEmbedding_val (hTwo : HasTwoSidedLoops D) (j : Fin D.simplifiedSize) :
    (rawCoreEmbedding D hTwo j).val = D.leftLoopCount + j.val :=
  rfl

/-- Restricting the translated Toeplitz matrix to its nonloop core recovers the
canonically reindexed banded matrix. -/
theorem translatedBand_core
    (hTwo : HasTwoSidedLoops D)
    (b : Fin (twoSidedBandDegree D + 1) → ℝ) :
    (rankThreeToeplitz (translatedBandCoefficient D hTwo b)).submatrix
        (allRows 3) (rawCoreEmbedding D hTwo) = simplifiedBandedMatrix D b := by
  ext i j
  simp only [Matrix.submatrix_apply, allRows, OrderIso.coe_toOrderEmbedding,
    OrderIso.coe_refl, id_eq, rankThreeToeplitz_apply, simplifiedBandedMatrix,
    rawCoreEmbedding_val]
  rw [bandedMatrix_apply]
  unfold translatedBandCoefficient bandCoefficient simplifiedToBandEmbedding
  simp only [bandColumnOrderIso, OrderIso.coe_toOrderEmbedding]
  have hsize := twoSidedBandDegree_add_three D
  have hjcast : ((Fin.castOrderIso (twoSidedBandDegree_add_three D)).symm j).val = j.val := rfl
  have htoNat :
      ((((Fin.castOrderIso (twoSidedBandDegree_add_three D)).symm j : Fin
          (twoSidedBandDegree D + 3)) : ℤ) - (i : ℤ)).toNat = j.val - i.val := by
    rw [Int.toNat_sub]
    simp only [hjcast]
  split_ifs with h₁ h₂
  · congr 1
    apply Fin.ext
    change D.leftLoopCount + j.val + (2 - i.val) - (D.leftLoopCount + 2) =
      ((((Fin.castOrderIso (twoSidedBandDegree_add_three D)).symm j : Fin
        (twoSidedBandDegree D + 3)) : ℤ) - (i : ℤ)).toNat
    rw [htoNat]
    omega
  · exfalso
    apply h₂
    constructor <;> omega
  · exfalso
    apply h₁
    constructor <;> omega
  · rfl

/-- In the two-sided case the raw nonloop interval begins at the left loop
count and ends after exactly `simplifiedSize` columns. -/
theorem rightLoopStart_eq_left_add_simplified (hTwo : HasTwoSidedLoops D) :
    D.rightLoopStart = D.leftLoopCount + D.simplifiedSize := by
  unfold CompatibleRankThreeData.rightLoopStart CompatibleRankThreeData.terminalStart
    CompatibleRankThreeData.middleStart
  rw [initialParallelSize_eq_one D hTwo, terminalParallelSize_eq_one D hTwo]
  have hm := D.simplifiedSize_ge_three
  omega

/-- On a nonloop, the compatible simplification index is just translation by
the left loop count. -/
theorem simplifiedIndexNat_eq_sub_left (hTwo : HasTwoSidedLoops D)
    {j : Fin n} (hj : D.IsNonloop j) :
    D.simplifiedIndexNat j = j.val - D.leftLoopCount := by
  unfold CompatibleRankThreeData.simplifiedIndexNat
  unfold CompatibleRankThreeData.middleStart CompatibleRankThreeData.terminalStart
  rw [initialParallelSize_eq_one D hTwo]
  split_ifs with h₁ h₂
  · omega
  · omega
  · have hright := rightLoopStart_eq_left_add_simplified D hTwo
    have hinitial := initialParallelSize_eq_one D hTwo
    have hterminal := terminalParallelSize_eq_one D hTwo
    unfold CompatibleRankThreeData.rightLoopStart CompatibleRankThreeData.terminalStart
      CompatibleRankThreeData.middleStart at hright
    rw [hinitial, hterminal] at hright
    have hmiddle : D.middleStart = D.leftLoopCount + 1 := by
      unfold CompatibleRankThreeData.middleStart
      rw [hinitial]
    have hterminalStart :
        D.terminalStart = D.leftLoopCount + D.simplifiedSize - 1 := by
      unfold CompatibleRankThreeData.terminalStart
      rw [hmiddle]
      have hm := D.simplifiedSize_ge_three
      omega
    rw [hmiddle] at h₂
    unfold CompatibleRankThreeData.IsNonloop at hj
    rw [rightLoopStart_eq_left_add_simplified D hTwo] at hj
    change D.simplifiedSize - 1 = j.val - D.leftLoopCount
    omega

/-- Embedding the simplified image of a raw nonloop recovers that raw column. -/
theorem rawCoreEmbedding_simplifiedIndex (hTwo : HasTwoSidedLoops D)
    {j : Fin n} (hj : D.IsNonloop j) :
    rawCoreEmbedding D hTwo (D.simplifiedIndex j) = j := by
  apply Fin.ext
  rw [rawCoreEmbedding_val]
  change D.leftLoopCount + D.simplifiedIndexNat j = j.val
  rw [simplifiedIndexNat_eq_sub_left D hTwo hj]
  have hjleft := hj.1
  omega

/-- Every prescribed loop column of the translated Toeplitz matrix is zero. -/
theorem translatedBand_isLoop_of_dataLoop
    (hTwo : HasTwoSidedLoops D)
    (b : Fin (twoSidedBandDegree D + 1) → ℝ)
    {j : Fin n} (hj : D.IsLoop j) :
    ToeplitzPositroids.IsLoop
      (rankThreeToeplitz (translatedBandCoefficient D hTwo b)) j := by
  rw [isLoop_iff_entry_eq_zero]
  intro i
  rw [rankThreeToeplitz_apply]
  unfold translatedBandCoefficient
  rw [dif_neg]
  intro hsupport
  have hi := i.isLt
  change D.leftLoopCount + 2 ≤ j.val + (2 - i.val) ∧
    j.val + (2 - i.val) <
      D.leftLoopCount + 2 + (twoSidedBandDegree D + 1) at hsupport
  rcases hj with hleft | hright
  · unfold CompatibleRankThreeData.IsLeftLoop at hleft
    omega
  · unfold CompatibleRankThreeData.IsRightLoop at hright
    have hstart := rightLoopStart_eq_left_add_simplified D hTwo
    have hsize := twoSidedBandDegree_add_three D
    omega

/-- Every compatible nonloop column is nonzero when the band coefficients are
positive. -/
theorem translatedBand_not_isLoop_of_dataNonloop
    (hTwo : HasTwoSidedLoops D)
    {b : Fin (twoSidedBandDegree D + 1) → ℝ} (hb : PositiveBandCoefficients b)
    {j : Fin n} (hj : D.IsNonloop j) :
    ¬ToeplitzPositroids.IsLoop
      (rankThreeToeplitz (translatedBandCoefficient D hTwo b)) j := by
  have hcol : (rankThreeToeplitz (translatedBandCoefficient D hTwo b)).col j =
      (simplifiedBandedMatrix D b).col (D.simplifiedIndex j) := by
    funext i
    have hentry := congrFun (congrFun (translatedBand_core D hTwo b) i)
      (D.simplifiedIndex j)
    change rankThreeToeplitz (translatedBandCoefficient D hTwo b) (allRows 3 i)
        (rawCoreEmbedding D hTwo (D.simplifiedIndex j)) =
      simplifiedBandedMatrix D b i (D.simplifiedIndex j) at hentry
    rw [rawCoreEmbedding_simplifiedIndex D hTwo hj] at hentry
    exact hentry
  intro hloop
  rw [ToeplitzPositroids.IsLoop, hcol] at hloop
  let s : Fin (twoSidedBandDegree D + 3) :=
    simplifiedToBandEmbedding D (D.simplifiedIndex j)
  by_cases hs : s.val ≤ twoSidedBandDegree D
  · have hpos : 0 < bandedMatrix b 0 s := by
      rw [bandedMatrix_apply, bandCoefficient_pos_iff hb]
      constructor <;> omega
    have hzero := congrFun hloop (0 : Fin 3)
    exact hpos.ne' hzero
  · by_cases hs₁ : s.val ≤ twoSidedBandDegree D + 1
    · have hpos : 0 < bandedMatrix b 1 s := by
        rw [bandedMatrix_apply, bandCoefficient_pos_iff hb]
        change (0 : ℤ) ≤ (s.val : ℤ) - 1 ∧
          (s.val : ℤ) - 1 ≤ twoSidedBandDegree D
        constructor <;> omega
      have hzero := congrFun hloop (1 : Fin 3)
      exact hpos.ne' hzero
    · have hpos : 0 < bandedMatrix b 2 s := by
        rw [bandedMatrix_apply, bandCoefficient_pos_iff hb]
        have hslt := s.isLt
        change (0 : ℤ) ≤ (s.val : ℤ) - 2 ∧
          (s.val : ℤ) - 2 ≤ twoSidedBandDegree D
        constructor <;> omega
      have hzero := congrFun hloop (2 : Fin 3)
      exact hpos.ne' hzero

/-- Matrix entries of a compatible nonloop agree with the corresponding core
column. -/
theorem translatedBand_entry_nonloop
    (hTwo : HasTwoSidedLoops D)
    (b : Fin (twoSidedBandDegree D + 1) → ℝ)
    {j : Fin n} (hj : D.IsNonloop j) (i : Fin 3) :
    rankThreeToeplitz (translatedBandCoefficient D hTwo b) i j =
      simplifiedBandedMatrix D b i (D.simplifiedIndex j) := by
  have hentry := congrFun (congrFun (translatedBand_core D hTwo b) i)
    (D.simplifiedIndex j)
  change rankThreeToeplitz (translatedBandCoefficient D hTwo b) (allRows 3 i)
      (rawCoreEmbedding D hTwo (D.simplifiedIndex j)) =
    simplifiedBandedMatrix D b i (D.simplifiedIndex j) at hentry
  rw [rawCoreEmbedding_simplifiedIndex D hTwo hj] at hentry
  exact hentry

/-- Every translated matrix entry is nonnegative. -/
theorem translatedBand_entry_nonneg
    (hTwo : HasTwoSidedLoops D)
    {b : Fin (twoSidedBandDegree D + 1) → ℝ} (hb : PositiveBandCoefficients b)
    (i : Fin 3) (j : Fin n) :
    0 ≤ rankThreeToeplitz (translatedBandCoefficient D hTwo b) i j := by
  rw [rankThreeToeplitz_apply]
  unfold translatedBandCoefficient
  split_ifs
  · exact (hb _).le
  · exact le_rfl

/-- Simplification is strictly order preserving on raw nonloops. -/
theorem simplifiedIndex_lt
    (hTwo : HasTwoSidedLoops D) {i j : Fin n}
    (hi : D.IsNonloop i) (hj : D.IsNonloop j) (hij : i < j) :
    D.simplifiedIndex i < D.simplifiedIndex j := by
  apply Fin.mk_lt_mk.mpr
  change D.simplifiedIndexNat i < D.simplifiedIndexNat j
  rw [simplifiedIndexNat_eq_sub_left D hTwo hi,
    simplifiedIndexNat_eq_sub_left D hTwo hj]
  have hiLeft := hi.1
  exact Nat.sub_lt_sub_right hiLeft hij

/-- The translated matrix is totally nonnegative through order two. -/
theorem translatedBand_tnUpTo_two
    (hTwo : HasTwoSidedLoops D) (R : TwoSidedCoreRealization D) :
    TNUpTo (rankThreeToeplitz (translatedBandCoefficient D hTwo R.b)) 2 := by
  intro l hl rows cols
  interval_cases l
  · simp
  · rw [orderedMinor_one]
    exact translatedBand_entry_nonneg D hTwo R.strict.1 _ _
  · have hcols : cols 0 < cols 1 := cols.strictMono (by decide)
    by_cases hloop₀ : D.IsLoop (cols 0)
    · have hz := isLoop_iff_entry_eq_zero.mp
        (translatedBand_isLoop_of_dataLoop D hTwo R.b hloop₀)
      rw [orderedMinor_two, hz (rows 0), hz (rows 1)]
      ring_nf
      exact le_rfl
    by_cases hloop₁ : D.IsLoop (cols 1)
    · have hz := isLoop_iff_entry_eq_zero.mp
        (translatedBand_isLoop_of_dataLoop D hTwo R.b hloop₁)
      rw [orderedMinor_two, hz (rows 0), hz (rows 1)]
      ring_nf
      exact le_rfl
    have hn₀ : D.IsNonloop (cols 0) := (D.isNonloop_iff_not_isLoop _).mpr hloop₀
    have hn₁ : D.IsNonloop (cols 1) := (D.isNonloop_iff_not_isLoop _).mpr hloop₁
    have hsimp : D.simplifiedIndex (cols 0) < D.simplifiedIndex (cols 1) :=
      simplifiedIndex_lt D hTwo hn₀ hn₁ hcols
    let coreCols : Fin 2 ↪o Fin D.simplifiedSize :=
      selectedPairEmbedding (D.simplifiedIndex (cols 0)) (D.simplifiedIndex (cols 1)) hsimp
    have hminor := R.totallyNonnegative.orderedMinor_nonneg rows coreCols
    rw [orderedMinor_two] at hminor ⊢
    simp only [coreCols, selectedPairEmbedding_zero, selectedPairEmbedding_one] at hminor
    rw [translatedBand_entry_nonloop D hTwo R.b hn₀,
      translatedBand_entry_nonloop D hTwo R.b hn₁,
      translatedBand_entry_nonloop D hTwo R.b hn₀,
      translatedBand_entry_nonloop D hTwo R.b hn₁]
    exact hminor

/-- Every translated maximal minor is nonnegative. -/
theorem translatedBand_maximalMinorsNonnegative
    (hTwo : HasTwoSidedLoops D) (R : TwoSidedCoreRealization D) :
    MaximalMinorsNonnegative
      (rankThreeToeplitz (translatedBandCoefficient D hTwo R.b)) := by
  intro cols
  have h₀₁ : cols 0 < cols 1 := cols.strictMono (by decide)
  have h₁₂ : cols 1 < cols 2 := cols.strictMono (by decide)
  by_cases hloop₀ : D.IsLoop (cols 0)
  · rw [orderedMinor]
    have hzdet : ((rankThreeToeplitz (translatedBandCoefficient D hTwo R.b)).submatrix
        (allRows 3) cols).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero 0
      intro i
      exact (isLoop_iff_entry_eq_zero.mp
        (translatedBand_isLoop_of_dataLoop D hTwo R.b hloop₀)) (allRows 3 i)
    rw [hzdet]
  by_cases hloop₁ : D.IsLoop (cols 1)
  · rw [orderedMinor]
    have hzdet : ((rankThreeToeplitz (translatedBandCoefficient D hTwo R.b)).submatrix
        (allRows 3) cols).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero 1
      intro i
      exact (isLoop_iff_entry_eq_zero.mp
        (translatedBand_isLoop_of_dataLoop D hTwo R.b hloop₁)) (allRows 3 i)
    rw [hzdet]
  by_cases hloop₂ : D.IsLoop (cols 2)
  · rw [orderedMinor]
    have hzdet : ((rankThreeToeplitz (translatedBandCoefficient D hTwo R.b)).submatrix
        (allRows 3) cols).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero 2
      intro i
      exact (isLoop_iff_entry_eq_zero.mp
        (translatedBand_isLoop_of_dataLoop D hTwo R.b hloop₂)) (allRows 3 i)
    rw [hzdet]
  have hn₀ := (D.isNonloop_iff_not_isLoop (cols 0)).mpr hloop₀
  have hn₁ := (D.isNonloop_iff_not_isLoop (cols 1)).mpr hloop₁
  have hn₂ := (D.isNonloop_iff_not_isLoop (cols 2)).mpr hloop₂
  have hs₀₁ := simplifiedIndex_lt D hTwo hn₀ hn₁ h₀₁
  have hs₁₂ := simplifiedIndex_lt D hTwo hn₁ hn₂ h₁₂
  let coreCols : Fin 3 ↪o Fin D.simplifiedSize :=
    selectedTripleEmbedding (D.simplifiedIndex (cols 0))
      (D.simplifiedIndex (cols 1)) (D.simplifiedIndex (cols 2)) hs₀₁ hs₁₂
  have hminor := R.totallyNonnegative.orderedMinor_nonneg (allRows 3) coreCols
  rw [orderedMinor_three] at hminor ⊢
  simp only [coreCols, selectedTripleEmbedding_zero, selectedTripleEmbedding_one,
    selectedTripleEmbedding_two] at hminor
  simp_rw [translatedBand_entry_nonloop D hTwo R.b hn₀,
    translatedBand_entry_nonloop D hTwo R.b hn₁,
    translatedBand_entry_nonloop D hTwo R.b hn₂]
  exact hminor

/-- The translated raw Toeplitz matrix is totally nonnegative. -/
theorem translatedBand_totallyNonnegative
    (hTwo : HasTwoSidedLoops D) (R : TwoSidedCoreRealization D) :
    TotallyNonnegative (rankThreeToeplitz (translatedBandCoefficient D hTwo R.b)) :=
  (totallyNonnegative_fin_three_iff _).mpr
    ⟨translatedBand_tnUpTo_two D hTwo R,
      translatedBand_maximalMinorsNonnegative D hTwo R⟩

/-- Full row rank of the core survives insertion of loop columns. -/
theorem translatedBand_hasFullRowRank
    (hTwo : HasTwoSidedLoops D) (R : TwoSidedCoreRealization D) :
    HasFullRowRank (rankThreeToeplitz (translatedBandCoefficient D hTwo R.b)) := by
  obtain ⟨cols, hcols⟩ := R.fullRowRank
  refine ⟨cols.trans (rawCoreEmbedding D hTwo), ?_⟩
  have hminor := orderedMinor_submatrix
    (rankThreeToeplitz (translatedBandCoefficient D hTwo R.b))
      (allRows 3) (rawCoreEmbedding D hTwo) (allRows 3) cols
  rw [translatedBand_core D hTwo R.b] at hminor
  have hrows : (allRows 3).trans (allRows 3) = allRows 3 := by
    apply RelEmbedding.ext
    intro i
    rfl
  rw [hrows] at hminor
  rw [← hminor]
  exact hcols

/-- Two-sided loop compatibility makes the initial endpoint class a singleton,
so no triple can contain an initial parallel pair. -/
theorem not_containsInitialParallelPair
    (hTwo : HasTwoSidedLoops D) (J : Finset (Fin n)) :
    ¬D.ContainsInitialParallelPair J := by
  intro hpair
  have hle : (J.filter D.IsInitialParallel).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    apply Fin.ext
    unfold CompatibleRankThreeData.IsInitialParallel at ha hb
    unfold CompatibleRankThreeData.middleStart at ha hb
    rw [initialParallelSize_eq_one D hTwo] at ha hb
    omega
  unfold CompatibleRankThreeData.ContainsInitialParallelPair at hpair
  omega

/-- Likewise, the terminal endpoint class is a singleton. -/
theorem not_containsTerminalParallelPair
    (hTwo : HasTwoSidedLoops D) (J : Finset (Fin n)) :
    ¬D.ContainsTerminalParallelPair J := by
  intro hpair
  have hle : (J.filter D.IsTerminalParallel).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    apply Fin.ext
    unfold CompatibleRankThreeData.IsTerminalParallel at ha hb
    have hterminal := terminalParallelSize_eq_one D hTwo
    unfold CompatibleRankThreeData.rightLoopStart at ha hb
    rw [hterminal] at ha hb
    omega
  unfold CompatibleRankThreeData.ContainsTerminalParallelPair at hpair
  omega

/-- The simplified images of three nonloops are exactly their three compatible
simplification indices. -/
theorem simplifiedImages_triple
    {i j k : Fin n} (hi : D.IsNonloop i) (hj : D.IsNonloop j) (hk : D.IsNonloop k) :
    D.simplifiedImages {i, j, k} =
      {D.simplifiedIndex i, D.simplifiedIndex j, D.simplifiedIndex k} := by
  classical
  ext x
  simp [CompatibleRankThreeData.simplifiedImages,
    CompatibleRankThreeData.simplifiedIndex?_eq_some D hi,
    CompatibleRankThreeData.simplifiedIndex?_eq_some D hj,
    CompatibleRankThreeData.simplifiedIndex?_eq_some D hk]
  tauto

/-- Exact maximal-minor support after both loop translations. -/
theorem translatedBand_triple_zero_iff_nonbasis
    (hTwo : HasTwoSidedLoops D) (R : TwoSidedCoreRealization D)
    {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    orderedMinor (rankThreeToeplitz (translatedBandCoefficient D hTwo R.b))
        (allRows 3) (selectedTripleEmbedding i j k hij hjk) = 0 ↔
      D.TripleNonbasis {i, j, k} := by
  have hcard : ({i, j, k} : Finset (Fin n)).card = 3 := by
    simp [hij.ne, hjk.ne, (hij.trans hjk).ne]
  by_cases hloopi : D.IsLoop i
  · constructor
    · intro _
      refine ⟨hcard, Or.inl ⟨i, by simp, hloopi⟩⟩
    · intro _
      rw [orderedMinor]
      apply Matrix.det_eq_zero_of_column_eq_zero 0
      intro r
      exact (isLoop_iff_entry_eq_zero.mp
        (translatedBand_isLoop_of_dataLoop D hTwo R.b hloopi)) (allRows 3 r)
  by_cases hloopj : D.IsLoop j
  · constructor
    · intro _
      refine ⟨hcard, Or.inl ⟨j, by simp, hloopj⟩⟩
    · intro _
      rw [orderedMinor]
      apply Matrix.det_eq_zero_of_column_eq_zero 1
      intro r
      exact (isLoop_iff_entry_eq_zero.mp
        (translatedBand_isLoop_of_dataLoop D hTwo R.b hloopj)) (allRows 3 r)
  by_cases hloopk : D.IsLoop k
  · constructor
    · intro _
      refine ⟨hcard, Or.inl ⟨k, by simp, hloopk⟩⟩
    · intro _
      rw [orderedMinor]
      apply Matrix.det_eq_zero_of_column_eq_zero 2
      intro r
      exact (isLoop_iff_entry_eq_zero.mp
        (translatedBand_isLoop_of_dataLoop D hTwo R.b hloopk)) (allRows 3 r)
  have hi : D.IsNonloop i := (D.isNonloop_iff_not_isLoop i).mpr hloopi
  have hj : D.IsNonloop j := (D.isNonloop_iff_not_isLoop j).mpr hloopj
  have hk : D.IsNonloop k := (D.isNonloop_iff_not_isLoop k).mpr hloopk
  have hpq := simplifiedIndex_lt D hTwo hi hj hij
  have hqr := simplifiedIndex_lt D hTwo hj hk hjk
  let coreCols : Fin 3 ↪o Fin D.simplifiedSize :=
    selectedTripleEmbedding (D.simplifiedIndex i) (D.simplifiedIndex j)
      (D.simplifiedIndex k) hpq hqr
  have hminorEq :
      orderedMinor (rankThreeToeplitz (translatedBandCoefficient D hTwo R.b))
          (allRows 3) (selectedTripleEmbedding i j k hij hjk) =
        orderedMinor (simplifiedBandedMatrix D R.b) (allRows 3) coreCols := by
    rw [orderedMinor_three, orderedMinor_three]
    simp only [coreCols, selectedTripleEmbedding_zero, selectedTripleEmbedding_one,
      selectedTripleEmbedding_two]
    simp_rw [translatedBand_entry_nonloop D hTwo R.b hi,
      translatedBand_entry_nonloop D hTwo R.b hj,
      translatedBand_entry_nonloop D hTwo R.b hk]
  rw [hminorEq, R.triple_zero_iff hpq hqr]
  have himages := simplifiedImages_triple D hi hj hk
  have hMeets : ¬D.MeetsLoops {i, j, k} := by
    rintro ⟨x, hx, hloopx⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hloopi hloopx
    · exact hloopj hloopx
    · exact hloopk hloopx
  have hInitial := not_containsInitialParallelPair D hTwo {i, j, k}
  have hTerminal := not_containsTerminalParallelPair D hTwo {i, j, k}
  constructor
  · rintro ⟨H, hH, hpH, hqH, hrH⟩
    refine ⟨hcard, Or.inr (Or.inr (Or.inr ?_))⟩
    constructor
    · rw [himages]
      simp [hpq.ne, hqr.ne, (hpq.trans hqr).ne]
    · refine ⟨H, hH, ?_⟩
      rw [himages]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hpH
      · exact hqH
      · exact hrH
  · rintro ⟨_, hcases⟩
    rcases hcases with hloops | hinitial | hterminal | hlast
    · exact (hMeets hloops).elim
    · exact (hInitial hinitial).elim
    · exact (hTerminal hterminal).elim
    · obtain ⟨hdistinct, hcoll⟩ := hlast
      obtain ⟨H, hH, hsub⟩ := hcoll
      rw [himages] at hsub
      exact ⟨H, hH, hsub (by simp), hsub (by simp), hsub (by simp)⟩

/-- A full raw Toeplitz realization of compatible two-sided data. -/
structure TwoSidedRealization (hTwo : HasTwoSidedLoops D) where
  coefficients : Fin (n + 2) → ℝ
  totallyNonnegative : TotallyNonnegative (rankThreeToeplitz coefficients)
  fullRowRank : HasFullRowRank (rankThreeToeplitz coefficients)
  loop_iff : ∀ j : Fin n,
    ToeplitzPositroids.IsLoop (rankThreeToeplitz coefficients) j ↔ D.IsLoop j
  maximalMinor_zero_iff : ∀ cols : Fin 3 ↪o Fin n,
    orderedMinor (rankThreeToeplitz coefficients) (allRows 3) cols = 0 ↔
      D.TripleNonbasis {cols 0, cols 1, cols 2}

/-- Proposition 21: every compatible datum with both loop boundaries has a
full-row-rank totally nonnegative Toeplitz realization with exactly the
prescribed triple nonbases. -/
theorem exists_twoSidedRealization (hTwo : HasTwoSidedLoops D) :
    Nonempty (TwoSidedRealization D hTwo) := by
  obtain ⟨R⟩ := exists_twoSidedCoreRealization D hTwo
  let a := translatedBandCoefficient D hTwo R.b
  refine ⟨⟨a, translatedBand_totallyNonnegative D hTwo R,
    translatedBand_hasFullRowRank D hTwo R, ?_, ?_⟩⟩
  · intro j
    constructor
    · intro hloop
      by_contra hj
      have hnonloop : D.IsNonloop j := (D.isNonloop_iff_not_isLoop j).mpr hj
      exact (translatedBand_not_isLoop_of_dataNonloop D hTwo R.strict.1 hnonloop) hloop
    · exact translatedBand_isLoop_of_dataLoop D hTwo R.b
  · intro cols
    have h₀₁ : cols 0 < cols 1 := cols.strictMono (by decide)
    have h₁₂ : cols 1 < cols 2 := cols.strictMono (by decide)
    rw [← selectedTripleEmbedding_eq cols]
    exact translatedBand_triple_zero_iff_nonbasis D hTwo R h₀₁ h₁₂

/-- The exact support statement in existential form, convenient for the final
classification theorem. -/
theorem propositionTwentyOne (hTwo : HasTwoSidedLoops D) :
    ∃ a : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      (∀ j : Fin n, ToeplitzPositroids.IsLoop (rankThreeToeplitz a) j ↔ D.IsLoop j) ∧
      ∀ cols : Fin 3 ↪o Fin n,
        orderedMinor (rankThreeToeplitz a) (allRows 3) cols = 0 ↔
          D.TripleNonbasis {cols 0, cols 1, cols 2} := by
  obtain ⟨R⟩ := exists_twoSidedRealization D hTwo
  exact ⟨R.coefficients, R.totallyNonnegative, R.fullRowRank,
    R.loop_iff, R.maximalMinor_zero_iff⟩

end CompatibleRankThreeData

end

end ToeplitzPositroids.RankThree
