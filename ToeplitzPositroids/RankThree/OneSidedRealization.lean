import ToeplitzPositroids.Matrix.Reversal
import ToeplitzPositroids.RankThree.CompatibleData
import ToeplitzPositroids.RankThree.ConvexChainCriterion
import ToeplitzPositroids.RankThree.SlopeSynthesis
import Mathlib.Tactic

/-!
# Endpoint-aware one-sided slope constructions

This file develops the fully quantified endpoint modifications used in the
one-sided realization argument.  The statements make the smallness hypotheses
which are implicit in Lemma 15 explicit, and separate the affine slope facts
from the later coefficient-index bookkeeping.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- The normalized ratio point associated with consecutive ratios `r_j,r_(j+1)`. -/
def ratioPointX (r : ℕ → ℝ) (j : ℕ) : ℝ := r (j + 1)

/-- The second coordinate of the normalized ratio point. -/
def ratioPointY (r : ℕ → ℝ) (j : ℕ) : ℝ := r j * r (j + 1)

/-- The exact finite-slope formula in the positive Toeplitz chart. -/
theorem ratioPoint_edgeSlope (r : ℕ → ℝ) (j : ℕ) :
    edgeSlope (ratioPointX r) (ratioPointY r) j =
      r (j + 1) * (r (j + 2) - r j) / (r (j + 2) - r (j + 1)) := by
  simp only [edgeSlope, chordSlope, ratioPointX, ratioPointY]
  congr 1
  ring

/-- Add an initial ratio plateau of length `p + 1` to a regular synthesized tail.  The raw
columns indexed `1,...,p` then represent one projective class. -/
def initialPlateauRatio {N : ℕ} (p : ℕ) (s : Fin N → ℝ) (ε : ℝ) (j : ℕ) : ℝ :=
  if j ≤ p then ε else synthesizedRatio s ε (j - p)

@[simp]
theorem initialPlateauRatio_of_le {N : ℕ} (p : ℕ) (s : Fin N → ℝ) (ε : ℝ)
    {j : ℕ} (hj : j ≤ p) :
    initialPlateauRatio p s ε j = ε := by
  simp [initialPlateauRatio, hj]

@[simp]
theorem initialPlateauRatio_succ {N : ℕ} (p : ℕ) (s : Fin N → ℝ) (ε : ℝ) :
    initialPlateauRatio p s ε (p + 1) = 2 * ε := by
  simp [initialPlateauRatio]

/-- Shifting past the plateau recovers the original synthesized ratio sequence. -/
theorem initialPlateauRatio_add {N : ℕ} (p : ℕ) (s : Fin N → ℝ) (ε : ℝ) (j : ℕ) :
    initialPlateauRatio p s ε (p + j) = synthesizedRatio s ε j := by
  cases j with
  | zero => simp [initialPlateauRatio]
  | succ j => simp [initialPlateauRatio]

/-- Every point belonging to the initial plateau equals `(ε,ε²)`. -/
theorem initialPlateau_point_eq {N : ℕ} {p : ℕ}
    (s : Fin N → ℝ) (ε : ℝ) {j : ℕ} (hj : j < p) :
    (ratioPointX (initialPlateauRatio p s ε) j,
      ratioPointY (initialPlateauRatio p s ε) j) = (ε, ε ^ 2) := by
  have hjp : j ≤ p := by omega
  have hj1p : j + 1 ≤ p := by omega
  simp [ratioPointX, ratioPointY, initialPlateauRatio_of_le, hjp, hj1p, pow_two]

/-- After collapsing the initial plateau, its first outgoing edge has slope exactly `ε`. -/
theorem initialPlateau_firstSimplifiedSlope {N : ℕ} {p : ℕ}
    (s : Fin N → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (ratioPointY (initialPlateauRatio p s ε) p - ε ^ 2) /
        (ratioPointX (initialPlateauRatio p s ε) p - ε) = ε := by
  rw [ratioPointX, ratioPointY, initialPlateauRatio_succ,
    initialPlateauRatio_of_le p s ε le_rfl]
  field_simp [hε.ne']

/-- Subsequent edges after an initial plateau realize exactly the target slopes. -/
theorem initialPlateau_subsequentSlope {N p : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : Fin N) :
    edgeSlope (ratioPointX (initialPlateauRatio p s ε))
        (ratioPointY (initialPlateauRatio p s ε)) (p + j.val) = s j := by
  rw [ratioPoint_edgeSlope]
  rw [show p + j.val + 1 = p + (j.val + 1) by omega,
    show p + j.val + 2 = p + (j.val + 2) by omega,
    initialPlateauRatio_add, initialPlateauRatio_add, initialPlateauRatio_add]
  rw [← ratioPoint_edgeSlope (synthesizedRatio s ε) j.val]
  exact synthesizedPoint_edgeSlope hε j

/-- Freeze a ratio sequence after index `k`; this is the terminal plateau construction. -/
def terminalPlateauRatio (r : ℕ → ℝ) (k : ℕ) (j : ℕ) : ℝ :=
  if j ≤ k then r j else r k

@[simp]
theorem terminalPlateauRatio_of_le (r : ℕ → ℝ) (k : ℕ) {j : ℕ} (hj : j ≤ k) :
    terminalPlateauRatio r k j = r j := by
  simp [terminalPlateauRatio, hj]

@[simp]
theorem terminalPlateauRatio_of_lt (r : ℕ → ℝ) (k : ℕ) {j : ℕ} (hj : k < j) :
    terminalPlateauRatio r k j = r k := by
  simp [terminalPlateauRatio, not_le.mpr hj]

/-- Every raw point strictly after the terminal cutoff equals `(r_k,r_k²)`. -/
theorem terminalPlateau_point_eq (r : ℕ → ℝ) (k : ℕ) {j : ℕ} (hkj : k ≤ j) :
    (ratioPointX (terminalPlateauRatio r k) j,
      ratioPointY (terminalPlateauRatio r k) j) = (r k, (r k) ^ 2) := by
  have hkj1 : k < j + 1 := by omega
  by_cases hEq : k = j
  · subst j
    simp [ratioPointX, ratioPointY, terminalPlateauRatio, pow_two]
  · have hkj' : k < j := lt_of_le_of_ne hkj hEq
    simp [ratioPointX, ratioPointY, terminalPlateauRatio_of_lt, hkj', hkj1, pow_two]

/-- If `r_(k-1) < r_k`, the last distinct point and the terminal projective class form an
upward vertical edge.  This replaces the manuscript's informal `+∞` slope. -/
theorem terminalPlateau_verticalEdge (r : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hrPos : 0 < r k) (hr : r (k - 1) < r k) :
    ratioPointX (terminalPlateauRatio r k) (k - 1) =
        ratioPointX (terminalPlateauRatio r k) k ∧
      ratioPointY (terminalPlateauRatio r k) (k - 1) <
        ratioPointY (terminalPlateauRatio r k) k := by
  have hkm1 : k - 1 ≤ k := by omega
  have hk1 : k < k + 1 := by omega
  simp only [ratioPointX, ratioPointY, show k - 1 + 1 = k by omega,
    terminalPlateauRatio_of_le _ _ hkm1, terminalPlateauRatio_of_le _ _ le_rfl,
    terminalPlateauRatio_of_lt _ _ hk1]
  constructor
  · trivial
  · exact mul_lt_mul_of_pos_right hr hrPos

/-- The projective points at a left support boundary begin at `(0,0)` and `(r₂,0)`. -/
theorem leftSupportBoundary_firstPoints (r : ℕ → ℝ) (h0 : r 0 = 0) (h1 : r 1 = 0) :
    (ratioPointX r 0, ratioPointY r 0) = (0, 0) ∧
      (ratioPointX r 1, ratioPointY r 1) = (r 2, 0) := by
  simp [ratioPointX, ratioPointY, h0, h1]

/-- If the second post-boundary ratio is positive, the first simplified edge is horizontal and
nondegenerate. -/
theorem leftSupportBoundary_firstSlope (r : ℕ → ℝ) (h0 : r 0 = 0) (h1 : r 1 = 0)
    (h2 : 0 < r 2) :
    edgeSlope (ratioPointX r) (ratioPointY r) 0 = 0 ∧
      ratioPointX r 0 < ratioPointX r 1 := by
  constructor
  · simp [edgeSlope, chordSlope, ratioPointX, ratioPointY, h0, h1]
  · simpa [ratioPointX, h1] using h2

namespace CompatibleSlopePattern

/-- A comparison between edges `t` and `t+1` is prescribed to be an equality exactly when both
edges belong to one of the interval blocks from the compatible datum. -/
def IsPrescribedEquality {n : ℕ} (D : CompatibleRankThreeData n) (t : ℕ) : Prop :=
  ∃ H ∈ D.intervals, H.left.val ≤ t ∧ t + 2 ≤ H.right.val

instance isPrescribedEqualityDecidable {n : ℕ} (D : CompatibleRankThreeData n) (t : ℕ) :
    Decidable (IsPrescribedEquality D t) :=
  Classical.dec _

/-- Count the strict slope breaks before edge `i`. -/
def breakCount {n : ℕ} (D : CompatibleRankThreeData n) (i : ℕ) : ℕ :=
  ((Finset.range i).filter fun t ↦ ¬IsPrescribedEquality D t).card

/-- Canonical positive target slopes whose adjacent equality pattern is the compatible interval
pattern. -/
def targetSlope {n : ℕ} (D : CompatibleRankThreeData n) :
    Fin (D.simplifiedSize - 1) → ℝ :=
  fun i ↦ 1 + breakCount D i.val

/-- The edge on the left of a consecutive edge comparison. -/
def comparisonLeft {n : ℕ} (D : CompatibleRankThreeData n)
    (i : Fin (D.simplifiedSize - 2)) : Fin (D.simplifiedSize - 1) :=
  ⟨i.val, by omega⟩

/-- The edge on the right of a consecutive edge comparison. -/
def comparisonRight {n : ℕ} (D : CompatibleRankThreeData n)
    (i : Fin (D.simplifiedSize - 2)) : Fin (D.simplifiedSize - 1) :=
  ⟨i.val + 1, by omega⟩

/-- Adding one edge either preserves the break count or increments it by one. -/
theorem breakCount_succ {n : ℕ} (D : CompatibleRankThreeData n) (i : ℕ) :
    breakCount D (i + 1) =
      if IsPrescribedEquality D i then breakCount D i else breakCount D i + 1 := by
  classical
  simp only [breakCount, Finset.card_filter, Finset.sum_range_succ]
  by_cases hi : IsPrescribedEquality D i <;> simp [hi]

/-- The target slopes are strictly positive. -/
theorem targetSlope_pos {n : ℕ} (D : CompatibleRankThreeData n)
    (i : Fin (D.simplifiedSize - 1)) :
    0 < targetSlope D i := by
  unfold targetSlope
  positivity

/-- At a consecutive edge comparison, the target slope stays constant exactly for a prescribed
interval continuation. -/
theorem targetSlope_castSucc_eq_succ_iff {n : ℕ} (D : CompatibleRankThreeData n)
    (i : Fin (D.simplifiedSize - 2)) :
    targetSlope D (comparisonLeft D i) = targetSlope D (comparisonRight D i) ↔
      IsPrescribedEquality D i.val := by
  classical
  rw [targetSlope, targetSlope, comparisonLeft, comparisonRight, breakCount_succ]
  by_cases hi : IsPrescribedEquality D i.val
  · simp [hi]
  · simp [hi]

/-- The canonical compatible target slopes are weakly increasing. -/
theorem targetSlope_monotone {n : ℕ} (D : CompatibleRankThreeData n) :
    Monotone (targetSlope D) := by
  classical
  intro i j hij
  simp only [targetSlope]
  gcongr
  exact Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.range_mono (show i.val ≤ j.val from hij)))

/-- The compatible interval family therefore supplies a positive monotone slope family for the
finite synthesis theorem. -/
theorem targetSlope_isPositiveMonotone {n : ℕ} (D : CompatibleRankThreeData n) :
    IsPositiveMonotoneSlopeFamily (targetSlope D) :=
  ⟨targetSlope_pos D, targetSlope_monotone D⟩

/-- Applying finite-slope synthesis to the canonical compatible edge pattern. -/
theorem exists_compatibleSlopeSynthesis {n : ℕ} (D : CompatibleRankThreeData n) :
    ∃ ε : ℝ,
      IsAdmissibleSynthesisEpsilon (targetSlope D) ε ∧
        StrictlyIncreasingUpTo (synthesizedRatio (targetSlope D) ε)
          (D.simplifiedSize - 1 + 2) ∧
        (∀ i : Fin (D.simplifiedSize - 1),
          edgeSlope (synthesizedPointX (targetSlope D) ε)
            (synthesizedPointY (targetSlope D) ε) i.val = targetSlope D i) := by
  obtain ⟨ε, hε, hstrict, hpos, hx, hedge, hmono⟩ :=
    exists_finiteSlopeSynthesis (targetSlope D) (targetSlope_isPositiveMonotone D)
  exact ⟨ε, hε, hstrict, hedge⟩

end CompatibleSlopePattern

/-- Reversing both matrix axes preserves the two properties needed by one-sided realization. -/
theorem reverseMatrix_tnn_fullRowRank {n : ℕ} {A : Matrix (Fin 3) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (hrank : HasFullRowRank A) :
    TotallyNonnegative (reverseMatrix A) ∧ HasFullRowRank (reverseMatrix A) := by
  exact ⟨hA.reverseMatrix, (hasFullRowRank_reverseMatrix_iff A).2 hrank⟩

end

end ToeplitzPositroids.RankThree
