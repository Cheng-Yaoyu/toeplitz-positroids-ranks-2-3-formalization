import ToeplitzPositroids.RankThree.Banded
import ToeplitzPositroids.RankThree.CompatibleData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Combinatorics for the two-sided rank-three realization

This file isolates the finite combinatorics used in Proposition 21 from the inverse-function
argument.  It handles the exceptional degrees `d = 0` and `d = 1`, identifies the general band
degree as `simplifiedSize - 3`, and translates protected collinear vertex intervals into interior
runs of zero consecutive determinants.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids Matrix

noncomputable section

/-- The unique coefficient of the `d = 0` band. -/
def degreeZeroUnitCoefficients : Fin 1 → ℝ :=
  fun _ ↦ 1

/-- The two coefficients of the `d = 1` band. -/
def degreeOneUnitCoefficients : Fin 2 → ℝ :=
  fun _ ↦ 1

/-- The degree-zero band is the identity matrix. -/
theorem degreeZeroBandedMatrix_eq_identity :
    bandedMatrix degreeZeroUnitCoefficients = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bandedMatrix, toeplitzMatrix, bandCoefficient, degreeZeroUnitCoefficients,
      Matrix.one_apply]

/-- The degree-one band is the four-column staircase matrix from Proposition 21. -/
theorem degreeOneBandedMatrix_eq :
    bandedMatrix degreeOneUnitCoefficients =
      !![(1 : ℝ), 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bandedMatrix, toeplitzMatrix, bandCoefficient, degreeOneUnitCoefficients]

/-- Both short unit sequences satisfy strict log-concavity with the zero boundary convention. -/
theorem degreeZero_strictlyLogConcave :
    StrictlyLogConcaveWithZeroBoundary degreeZeroUnitCoefficients := by
  constructor
  · intro t
    fin_cases t
    norm_num [degreeZeroUnitCoefficients]
  · intro t
    fin_cases t
    norm_num [bandCoefficient, degreeZeroUnitCoefficients]

theorem degreeOne_strictlyLogConcave :
    StrictlyLogConcaveWithZeroBoundary degreeOneUnitCoefficients := by
  constructor
  · intro t
    fin_cases t <;> norm_num [degreeOneUnitCoefficients]
  · intro t
    fin_cases t <;> norm_num [bandCoefficient, degreeOneUnitCoefficients]

/-- Every maximal minor of the degree-zero band equals one. -/
theorem degreeZero_maximalMinor_eq_one (cols : Fin 3 ↪o Fin 3) :
    orderedMinor (bandedMatrix degreeZeroUnitCoefficients) (allRows 3) cols = 1 := by
  rw [degreeZeroBandedMatrix_eq_identity, finThree_orderEmbedding_eq_allRows cols]
  simp [orderedMinor, allRows]

/-- Every maximal minor of the degree-one band equals one. -/
theorem degreeOne_maximalMinor_eq_one (cols : Fin 3 ↪o Fin 4) :
    orderedMinor (bandedMatrix degreeOneUnitCoefficients) (allRows 3) cols = 1 := by
  rw [orderedMinor_three, degreeOneBandedMatrix_eq]
  have h₀₁ : cols 0 < cols 1 := cols.strictMono (by decide)
  have h₁₂ : cols 1 < cols 2 := cols.strictMono (by decide)
  have hcases :
      ((cols 0).val = 0 ∧ (cols 1).val = 1 ∧ (cols 2).val = 2) ∨
      ((cols 0).val = 0 ∧ (cols 1).val = 1 ∧ (cols 2).val = 3) ∨
      ((cols 0).val = 0 ∧ (cols 1).val = 2 ∧ (cols 2).val = 3) ∨
      ((cols 0).val = 1 ∧ (cols 1).val = 2 ∧ (cols 2).val = 3) := by
    omega
  rcases hcases with h | h | h | h
  · rcases h with ⟨h0, h1, h2⟩
    have e0 : cols 0 = 0 := Fin.ext h0
    have e1 : cols 1 = 1 := Fin.ext h1
    have e2 : cols 2 = 2 := Fin.ext h2
    rw [e0, e1, e2]
    norm_num [allRows, Matrix.cons_val_two, Matrix.cons_val_three]
  · rcases h with ⟨h0, h1, h2⟩
    have e0 : cols 0 = 0 := Fin.ext h0
    have e1 : cols 1 = 1 := Fin.ext h1
    have e2 : cols 2 = 3 := Fin.ext h2
    rw [e0, e1, e2]
    norm_num [allRows, Matrix.cons_val_two, Matrix.cons_val_three]
  · rcases h with ⟨h0, h1, h2⟩
    have e0 : cols 0 = 0 := Fin.ext h0
    have e1 : cols 1 = 2 := Fin.ext h1
    have e2 : cols 2 = 3 := Fin.ext h2
    rw [e0, e1, e2]
    norm_num [allRows, Matrix.cons_val_two, Matrix.cons_val_three]
  · rcases h with ⟨h0, h1, h2⟩
    have e0 : cols 0 = 1 := Fin.ext h0
    have e1 : cols 1 = 2 := Fin.ext h1
    have e2 : cols 2 = 3 := Fin.ext h2
    rw [e0, e1, e2]
    norm_num [allRows, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The identity band is totally nonnegative and full row rank, with its unique maximal minor
nonzero. -/
theorem degreeZero_tnn_fullRowRank :
    TotallyNonnegative (bandedMatrix degreeZeroUnitCoefficients) ∧
      HasFullRowRank (bandedMatrix degreeZeroUnitCoefficients) ∧
      ∀ cols : Fin 3 ↪o Fin 3,
        orderedMinor (bandedMatrix degreeZeroUnitCoefficients) (allRows 3) cols ≠ 0 := by
  have htwo := bandedMatrix_tnUpTo_two_of_strictLogConcave degreeZero_strictlyLogConcave
  have hmax : MaximalMinorsNonnegative (bandedMatrix degreeZeroUnitCoefficients) :=
    fun cols ↦ by rw [degreeZero_maximalMinor_eq_one]; norm_num
  have hTNN := (totallyNonnegative_fin_three_iff _).mpr ⟨htwo, hmax⟩
  refine ⟨hTNN, ⟨allRows 3, ?_⟩, ?_⟩
  · rw [degreeZero_maximalMinor_eq_one]
    norm_num
  · intro cols
    rw [degreeZero_maximalMinor_eq_one]
    norm_num

/-- The four-column staircase band is totally nonnegative and full row rank, and all four of its
maximal minors are nonzero. -/
theorem degreeOne_tnn_fullRowRank :
    TotallyNonnegative (bandedMatrix degreeOneUnitCoefficients) ∧
      HasFullRowRank (bandedMatrix degreeOneUnitCoefficients) ∧
      ∀ cols : Fin 3 ↪o Fin 4,
        orderedMinor (bandedMatrix degreeOneUnitCoefficients) (allRows 3) cols ≠ 0 := by
  have htwo := bandedMatrix_tnUpTo_two_of_strictLogConcave degreeOne_strictlyLogConcave
  have hmax : MaximalMinorsNonnegative (bandedMatrix degreeOneUnitCoefficients) :=
    fun cols ↦ by rw [degreeOne_maximalMinor_eq_one]; norm_num
  have hTNN := (totallyNonnegative_fin_three_iff _).mpr ⟨htwo, hmax⟩
  let cols : Fin 3 ↪o Fin 4 := selectedTripleEmbedding 0 1 2 (by decide) (by decide)
  refine ⟨hTNN, ⟨cols, ?_⟩, ?_⟩
  · rw [degreeOne_maximalMinor_eq_one]
    norm_num
  · intro J
    rw [degreeOne_maximalMinor_eq_one]
    norm_num

/-! ## Protected intervals and determinant runs -/

/-- The band degree attached to a simplified configuration of size `m` is `m - 3`. -/
def twoSidedBandDegree {n : ℕ} (D : CompatibleRankThreeData n) : ℕ :=
  D.simplifiedSize - 3

/-- The band has exactly as many columns as there are simplified vertices. -/
theorem twoSidedBandDegree_add_three {n : ℕ} (D : CompatibleRankThreeData n) :
    twoSidedBandDegree D + 3 = D.simplifiedSize := by
  unfold twoSidedBandDegree
  exact Nat.sub_add_cancel D.simplifiedSize_ge_three

/-- Both loop blocks are nonempty. -/
def HasTwoSidedLoops {n : ℕ} (D : CompatibleRankThreeData n) : Prop :=
  0 < D.leftLoopCount ∧ 0 < D.rightLoopCount

/-- A collinear vertex interval protected from both endpoints. -/
structure ProtectedCollinearInterval (m : ℕ) where
  interval : SimplifiedInterval m
  large : interval.left.val + 2 ≤ interval.right.val
  left_pos : 0 < interval.left.val
  right_strict : interval.right.val + 1 < m

/-- A nonempty run of interior consecutive-determinant indices. -/
structure InteriorDeterminantRun (d : ℕ) where
  left : ℕ
  right : ℕ
  left_le_right : left ≤ right
  left_pos : 1 ≤ left
  right_lt_degree : right < d

namespace InteriorDeterminantRun

/-- The finite set of determinant indices in a run. -/
def indices {d : ℕ} (R : InteriorDeterminantRun d) : Finset ℕ :=
  Finset.Icc R.left R.right

@[simp]
theorem mem_indices {d : ℕ} {R : InteriorDeterminantRun d} {t : ℕ} :
    t ∈ R.indices ↔ R.left ≤ t ∧ t ≤ R.right :=
  Finset.mem_Icc

end InteriorDeterminantRun

/-- A protected vertex interval `[u,v]` maps to the determinant run `[u,v-2]`. -/
def protectedIntervalToRun {m : ℕ} (hm : 3 ≤ m) (P : ProtectedCollinearInterval m) :
    InteriorDeterminantRun (m - 3) where
  left := P.interval.left.val
  right := P.interval.right.val - 2
  left_le_right := Nat.le_sub_of_add_le P.large
  left_pos := P.left_pos
  right_lt_degree := by
    have hlarge := P.large
    have hright := P.right_strict
    have hr : (P.interval.right.val - 2) + 2 = P.interval.right.val := by
      exact Nat.sub_add_cancel (by omega)
    have hm' : (m - 3) + 3 = m := Nat.sub_add_cancel hm
    omega

/-- An interior determinant run `[u,w]` maps back to the vertex interval `[u,w+2]`. -/
def zeroRunToProtectedInterval (m : ℕ) (hm : 3 ≤ m)
    (R : InteriorDeterminantRun (m - 3)) : ProtectedCollinearInterval m where
  interval :=
    { left := ⟨R.left, by
          have hlr := R.left_le_right
          have hr := R.right_lt_degree
          have hm' : (m - 3) + 3 = m := Nat.sub_add_cancel hm
          omega⟩
      right := ⟨R.right + 2, by
          have hr := R.right_lt_degree
          have hm' : (m - 3) + 3 = m := Nat.sub_add_cancel hm
          omega⟩
      left_le_right := by
        have hlr := R.left_le_right
        change R.left ≤ R.right + 2
        omega }
  large := by
    have hlr := R.left_le_right
    change R.left + 2 ≤ R.right + 2
    omega
  left_pos := R.left_pos
  right_strict := by
    have hr := R.right_lt_degree
    have hm' : (m - 3) + 3 = m := Nat.sub_add_cancel hm
    change R.right + 2 + 1 < m
    omega

@[simp]
theorem protectedIntervalToRun_left {m : ℕ} (hm : 3 ≤ m)
    (P : ProtectedCollinearInterval m) :
    (protectedIntervalToRun hm P).left = P.interval.left.val :=
  rfl

@[simp]
theorem protectedIntervalToRun_right {m : ℕ} (hm : 3 ≤ m)
    (P : ProtectedCollinearInterval m) :
    (protectedIntervalToRun hm P).right = P.interval.right.val - 2 :=
  rfl

@[simp]
theorem zeroRunToProtectedInterval_left {m : ℕ} (hm : 3 ≤ m)
    (R : InteriorDeterminantRun (m - 3)) :
    (zeroRunToProtectedInterval m hm R).interval.left.val = R.left :=
  rfl

@[simp]
theorem zeroRunToProtectedInterval_right {m : ℕ} (hm : 3 ≤ m)
    (R : InteriorDeterminantRun (m - 3)) :
    (zeroRunToProtectedInterval m hm R).interval.right.val = R.right + 2 :=
  rfl

/-- Mapping a protected interval to a run and back recovers both vertex endpoint values. -/
theorem protectedInterval_run_roundTrip {m : ℕ} (hm : 3 ≤ m)
    (P : ProtectedCollinearInterval m) :
    (zeroRunToProtectedInterval m hm (protectedIntervalToRun hm P)).interval.left.val =
        P.interval.left.val ∧
      (zeroRunToProtectedInterval m hm (protectedIntervalToRun hm P)).interval.right.val =
        P.interval.right.val := by
  constructor
  · rfl
  · change (P.interval.right.val - 2) + 2 = P.interval.right.val
    have hlarge := P.large
    exact Nat.sub_add_cancel (by omega)

/-- Mapping a run to a protected interval and back recovers its numeric endpoints. -/
theorem zeroRun_interval_roundTrip {m : ℕ} (hm : 3 ≤ m)
    (R : InteriorDeterminantRun (m - 3)) :
    (protectedIntervalToRun hm (zeroRunToProtectedInterval m hm R)).left = R.left ∧
      (protectedIntervalToRun hm (zeroRunToProtectedInterval m hm R)).right = R.right := by
  constructor
  · rfl
  · change (R.right + 2) - 2 = R.right
    omega

namespace CompatibleRankThreeData

variable {n : ℕ} (D : CompatibleRankThreeData n)

/-- In the two-sided case every prescribed interval is protected at both endpoints. -/
def protectedIntervalOfMem (hTwo : HasTwoSidedLoops D)
    (H : SimplifiedInterval D.simplifiedSize) (hH : H ∈ D.intervals) :
    ProtectedCollinearInterval D.simplifiedSize where
  interval := H
  large := D.interval_large H hH
  left_pos := by
    have hne := D.initial_endpoint_protected (Or.inl hTwo.1) H hH
    omega
  right_strict := by
    have hne := D.terminal_endpoint_protected (Or.inl hTwo.2) H hH
    have hlt := H.right.isLt
    omega

/-- The determinant-index run belonging to a prescribed two-sided collinear interval. -/
def intervalZeroRun (hTwo : HasTwoSidedLoops D)
    (H : SimplifiedInterval D.simplifiedSize) (hH : H ∈ D.intervals) :
    InteriorDeterminantRun (twoSidedBandDegree D) :=
  protectedIntervalToRun D.simplifiedSize_ge_three (protectedIntervalOfMem D hTwo H hH)

/-- The raw finite run `[left,right-2]` attached to any simplified interval. -/
def intervalZeroIndices (H : SimplifiedInterval D.simplifiedSize) : Finset ℕ :=
  Finset.Icc H.left.val (H.right.val - 2)

/-- Membership in an interval's zero run is precisely the manuscript inequality
`left ≤ t` and `t+2 ≤ right`. -/
theorem mem_intervalZeroIndices_iff {H : SimplifiedInterval D.simplifiedSize}
    (hH : H ∈ D.intervals) {t : ℕ} :
    t ∈ intervalZeroIndices D H ↔ H.left.val ≤ t ∧ t + 2 ≤ H.right.val := by
  rw [intervalZeroIndices, Finset.mem_Icc]
  have hlarge := D.interval_large H hH
  omega

/-- The target zero set `Z`: the union of all prescribed determinant runs. -/
def targetZeroSet : Finset ℕ :=
  D.intervals.biUnion (intervalZeroIndices D)

/-- Exact membership criterion for the target zero set. -/
theorem mem_targetZeroSet_iff {t : ℕ} :
    t ∈ targetZeroSet D ↔
      ∃ H ∈ D.intervals, H.left.val ≤ t ∧ t + 2 ≤ H.right.val := by
  classical
  rw [targetZeroSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨H, hH, ht⟩
    exact ⟨H, hH, (mem_intervalZeroIndices_iff D hH).mp ht⟩
  · rintro ⟨H, hH, ht⟩
    exact ⟨H, hH, (mem_intervalZeroIndices_iff D hH).mpr ht⟩

/-- Endpoint protection places every target determinant index in `1, …, d-1`. -/
theorem targetZeroSet_interior (hTwo : HasTwoSidedLoops D) {t : ℕ}
    (ht : t ∈ targetZeroSet D) :
    1 ≤ t ∧ t < twoSidedBandDegree D := by
  obtain ⟨H, hH, hleft, hright⟩ := (mem_targetZeroSet_iff D).mp ht
  let P := protectedIntervalOfMem D hTwo H hH
  have hPleft := P.left_pos
  have hPright := P.right_strict
  dsimp only [P, protectedIntervalOfMem] at hPleft hPright
  unfold twoSidedBandDegree
  omega

/-- Degree zero is exactly simplified size three. -/
theorem twoSidedBandDegree_eq_zero_iff :
    twoSidedBandDegree D = 0 ↔ D.simplifiedSize = 3 := by
  have hsize := twoSidedBandDegree_add_three D
  constructor <;> intro h
  · omega
  · omega

/-- Degree one is exactly simplified size four. -/
theorem twoSidedBandDegree_eq_one_iff :
    twoSidedBandDegree D = 1 ↔ D.simplifiedSize = 4 := by
  have hsize := twoSidedBandDegree_add_three D
  constructor <;> intro h
  · omega
  · omega

/-- With both loop boundaries and at most four simplified vertices, compatibility permits no
collinear interval of size three. -/
theorem intervals_eq_empty_of_simplifiedSize_le_four (hTwo : HasTwoSidedLoops D)
    (hm : D.simplifiedSize ≤ 4) :
    D.intervals = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro H hH
  let P := protectedIntervalOfMem D hTwo H hH
  have hlarge := P.large
  have hleft := P.left_pos
  have hright := P.right_strict
  dsimp only [P, protectedIntervalOfMem] at hlarge hleft hright
  omega

/-- Consequently, the exceptional degrees zero and one have no prescribed collinear interval;
the short matrices above therefore have exactly the compatible maximal-minor supports. -/
theorem intervals_eq_empty_of_degree_le_one (hTwo : HasTwoSidedLoops D)
    (hd : twoSidedBandDegree D ≤ 1) :
    D.intervals = ∅ := by
  apply intervals_eq_empty_of_simplifiedSize_le_four D hTwo
  have hsize := twoSidedBandDegree_add_three D
  omega

/-- If two prescribed vertex intervals meet at one endpoint, their determinant runs are separated
by exactly one index, and that intervening determinant is not in the target zero set. -/
theorem touchingIntervals_zeroRuns_separated (hTwo : HasTwoSidedLoops D)
    (H K : SimplifiedInterval D.simplifiedSize) (hH : H ∈ D.intervals)
    (hK : K ∈ D.intervals) (htouch : H.right = K.left) :
    let RH := intervalZeroRun D hTwo H hH
    let RK := intervalZeroRun D hTwo K hK
    RH.right + 2 = RK.left ∧
      RH.right + 1 = H.right.val - 1 ∧
        H.right.val - 1 ∉ targetZeroSet D := by
  dsimp only
  have hlargeH := D.interval_large H hH
  have hlargeK := D.interval_large K hK
  have htouchVal := congrArg Fin.val htouch
  constructor
  · change (H.right.val - 2) + 2 = K.left.val
    rw [Nat.sub_add_cancel (by omega)]
    exact htouchVal
  constructor
  · change (H.right.val - 2) + 1 = H.right.val - 1
    omega
  · intro hgap
    obtain ⟨L, hL, hleftL, hrightL⟩ := (mem_targetZeroSet_iff D).mp hgap
    let x : Fin D.simplifiedSize := ⟨H.right.val - 1, by omega⟩
    let y : Fin D.simplifiedSize := H.right
    have hxy : x ≠ y := by
      intro hxy
      have hv := congrArg Fin.val hxy
      simp only [x, y] at hv
      omega
    have hxH : x ∈ H.points := by
      rw [SimplifiedInterval.mem_points]
      change H.left.val ≤ H.right.val - 1 ∧ H.right.val - 1 ≤ H.right.val
      omega
    have hyH : y ∈ H.points := by
      simpa [y] using H.right_mem_points
    have hxL : x ∈ L.points := by
      rw [SimplifiedInterval.mem_points]
      change L.left.val ≤ H.right.val - 1 ∧ H.right.val - 1 ≤ L.right.val
      omega
    have hyL : y ∈ L.points := by
      rw [SimplifiedInterval.mem_points]
      change L.left.val ≤ H.right.val ∧ H.right.val ≤ L.right.val
      omega
    have hEq : H = L := D.interval_eq_of_two_common hH hL hxy hxH hxL hyH hyL
    rw [← hEq] at hrightL
    omega

end CompatibleRankThreeData

end

end ToeplitzPositroids.RankThree
