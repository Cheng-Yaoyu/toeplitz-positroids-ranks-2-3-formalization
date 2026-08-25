import ToeplitzPositroids.RankTwo.Classification
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Boundary realizations in rank two

This file completes the constructive direction of the rank-two classification, including prefix
and suffix loops.  The first and last elements of the active interval encode the loop counts.  A
surjective monotone block map partitions that interval into consecutive parallel classes.

When the prefix is nonempty, the first projective parameter is the ray `0`; when the suffix is
nonempty, the last parameter is the ray `∞`.  The compatibility conditions require the associated
boundary blocks to be singletons.
-/

namespace ToeplitzPositroids

open Matrix Set

variable {n blocks : ℕ}

/-- Raw boundary data for a rank-two Toeplitz configuration. -/
structure RankTwoBoundaryDatum (n blocks : ℕ) where
  /-- First nonloop column; its value is the number of prefix loops. -/
  first : Fin n
  /-- Last nonloop column. -/
  last : Fin n
  first_le_last : first ≤ last
  /-- Parallel-block label on the intervening nonloop interval. -/
  block : {j : Fin n // first ≤ j ∧ j ≤ last} → Fin blocks
  block_mono : Monotone block
  block_surjective : Function.Surjective block

namespace RankTwoBoundaryDatum

/-- The subtype of active, hence nonloop, columns. -/
abbrev Active (D : RankTwoBoundaryDatum n blocks) :=
  {j : Fin n // D.first ≤ j ∧ j ≤ D.last}

/-- The first active column. -/
def firstActive (D : RankTwoBoundaryDatum n blocks) : D.Active :=
  ⟨D.first, le_rfl, D.first_le_last⟩

/-- The last active column. -/
def lastActive (D : RankTwoBoundaryDatum n blocks) : D.Active :=
  ⟨D.last, D.first_le_last, le_rfl⟩

/-- The data satisfy the full-rank and loop-boundary restrictions of Theorem 3. -/
structure Compatible (D : RankTwoBoundaryDatum n blocks) : Prop where
  two_le_blocks : 2 ≤ blocks
  left_boundary_singleton : 0 < D.first.val →
    ∀ j : D.Active, D.block j = D.block D.firstActive → j = D.firstActive
  right_boundary_singleton : D.last.val + 1 < n →
    ∀ j : D.Active, D.block j = D.block D.lastActive → j = D.lastActive

/-- There is a nonempty prefix loop interval exactly when `first` is positive. -/
def HasLeftLoops (D : RankTwoBoundaryDatum n blocks) : Prop :=
  0 < D.first.val

/-- There is a nonempty suffix loop interval exactly when `last` is not the final column. -/
def HasRightLoops (D : RankTwoBoundaryDatum n blocks) : Prop :=
  D.last.val + 1 < n

/-- First positive coefficient index. -/
def supportStart (D : RankTwoBoundaryDatum n blocks) : ℕ :=
  if D.first.val = 0 then 0 else D.first.val + 1

/-- Last positive coefficient index. -/
def supportEnd (D : RankTwoBoundaryDatum n blocks) : ℕ :=
  if D.last.val + 1 = n then n else D.last.val

/-- A positive finite parameter attached to every column.  Values outside the active interval are
irrelevant to the construction and are set to one. -/
noncomputable def finiteParameter (D : RankTwoBoundaryDatum n blocks) (j : Fin n) : ℝ :=
  if h : D.first ≤ j ∧ j ≤ D.last then (D.block ⟨j, h⟩).val + 1 else 1

/-- Natural-indexed extension of the finite parameter. -/
noncomputable def extendedFiniteParameter (D : RankTwoBoundaryDatum n blocks) (k : ℕ) : ℝ :=
  if h : k < n then D.finiteParameter ⟨k, h⟩ else 1

/-- Toeplitz coefficients with exactly the support forced by the two loop boundaries. -/
noncomputable def coefficients (D : RankTwoBoundaryDatum n blocks) (k : Fin (n + 1)) : ℝ :=
  if D.supportStart ≤ k.val ∧ k.val ≤ D.supportEnd then
    ∏ t ∈ Finset.Ico D.supportStart k.val, (D.extendedFiniteParameter t)⁻¹
  else
    0

/-- Every finite parameter is strictly positive. -/
theorem finiteParameter_pos (D : RankTwoBoundaryDatum n blocks) (j : Fin n) :
    0 < D.finiteParameter j := by
  classical
  rw [finiteParameter]
  split_ifs
  · positivity
  · positivity

/-- Every extended finite parameter is strictly positive. -/
theorem extendedFiniteParameter_pos (D : RankTwoBoundaryDatum n blocks) (k : ℕ) :
    0 < D.extendedFiniteParameter k := by
  classical
  rw [extendedFiniteParameter]
  split_ifs
  · exact D.finiteParameter_pos _
  · positivity

/-- The reconstructed coefficient is positive exactly on the prescribed coefficient interval. -/
theorem coefficients_pos_iff (D : RankTwoBoundaryDatum n blocks) (k : Fin (n + 1)) :
    0 < D.coefficients k ↔ D.supportStart ≤ k.val ∧ k.val ≤ D.supportEnd := by
  classical
  rw [coefficients]
  split_ifs with hk
  · exact ⟨fun _ ↦ hk, fun _ ↦ Finset.prod_pos fun t _ ↦ inv_pos.mpr
      (D.extendedFiniteParameter_pos t)⟩
  · simp [hk]

/-- Coefficients outside the prescribed support vanish. -/
theorem coefficients_eq_zero_iff (D : RankTwoBoundaryDatum n blocks) (k : Fin (n + 1)) :
    D.coefficients k = 0 ↔ ¬(D.supportStart ≤ k.val ∧ k.val ≤ D.supportEnd) := by
  classical
  rw [coefficients]
  split_ifs with hk
  · constructor
    · intro hzero
      have hpos : 0 < ∏ t ∈ Finset.Ico D.supportStart k.val,
          (D.extendedFiniteParameter t)⁻¹ :=
        Finset.prod_pos fun t _ ↦ inv_pos.mpr (D.extendedFiniteParameter_pos t)
      exact False.elim (hpos.ne' hzero)
    · exact fun h ↦ False.elim (h hk)
  · simp [hk]

/-- Every reconstructed coefficient is nonnegative. -/
theorem coefficients_nonneg (D : RankTwoBoundaryDatum n blocks) (k : Fin (n + 1)) :
    0 ≤ D.coefficients k := by
  by_cases hk : D.supportStart ≤ k.val ∧ k.val ≤ D.supportEnd
  · exact (D.coefficients_pos_iff k).mpr hk |>.le
  · rw [(D.coefficients_eq_zero_iff k).mpr hk]

/-- Block zero, available for compatible data. -/
def Compatible.zeroBlock {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) : Fin blocks :=
  ⟨0, by have := hD.two_le_blocks; omega⟩

/-- Block one, available for compatible data. -/
def Compatible.oneBlock {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) : Fin blocks :=
  ⟨1, by have := hD.two_le_blocks; omega⟩

/-- An active representative of block zero. -/
noncomputable def Compatible.zeroRepresentative {D : RankTwoBoundaryDatum n blocks}
    (hD : D.Compatible) : D.Active :=
  Classical.choose (D.block_surjective hD.zeroBlock)

/-- An active representative of block one. -/
noncomputable def Compatible.oneRepresentative {D : RankTwoBoundaryDatum n blocks}
    (hD : D.Compatible) : D.Active :=
  Classical.choose (D.block_surjective hD.oneBlock)

@[simp]
theorem Compatible.block_zeroRepresentative {D : RankTwoBoundaryDatum n blocks}
    (hD : D.Compatible) : D.block hD.zeroRepresentative = hD.zeroBlock :=
  Classical.choose_spec (D.block_surjective hD.zeroBlock)

@[simp]
theorem Compatible.block_oneRepresentative {D : RankTwoBoundaryDatum n blocks}
    (hD : D.Compatible) : D.block hD.oneRepresentative = hD.oneBlock :=
  Classical.choose_spec (D.block_surjective hD.oneBlock)

/-- Compatible full-rank data contain at least two active columns. -/
theorem Compatible.zeroRepresentative_lt_oneRepresentative
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) :
    hD.zeroRepresentative < hD.oneRepresentative := by
  by_contra hnot
  have hblock := D.block_mono (not_lt.mp hnot)
  rw [hD.block_oneRepresentative, hD.block_zeroRepresentative] at hblock
  change (1 : ℕ) ≤ 0 at hblock
  omega

/-- In particular, the active interval has distinct endpoints. -/
theorem Compatible.first_lt_last {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) :
    D.first < D.last := by
  have hz := hD.zeroRepresentative.property
  have ho := hD.oneRepresentative.property
  have hzo := hD.zeroRepresentative_lt_oneRepresentative
  change D.first.val < D.last.val
  change hD.zeroRepresentative.val < hD.oneRepresentative.val at hzo
  omega

/-- The support start is a valid coefficient index. -/
theorem supportStart_le_n (D : RankTwoBoundaryDatum n blocks) : D.supportStart ≤ n := by
  rw [supportStart]
  split_ifs <;> omega

/-- The support end is a valid coefficient index. -/
theorem supportEnd_le_n (D : RankTwoBoundaryDatum n blocks) : D.supportEnd ≤ n := by
  rw [supportEnd]
  split_ifs <;> omega

/-- Compatibility makes the reconstructed coefficient support nonempty. -/
theorem Compatible.supportStart_le_supportEnd
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) :
    D.supportStart ≤ D.supportEnd := by
  rw [supportStart, supportEnd]
  split_ifs with hfirst hlast
  · omega
  · omega
  · omega
  · have hfl := hD.first_lt_last
    omega

/-- Consecutive positive coefficients obey the prescribed finite-parameter recurrence. -/
theorem coefficients_succ (D : RankTwoBoundaryDatum n blocks) (j : Fin n)
    (hstart : D.supportStart ≤ j.val) (hend : j.val < D.supportEnd) :
    D.coefficients j.succ = D.coefficients j.castSucc / D.finiteParameter j := by
  classical
  have hjend : j.val + 1 ≤ D.supportEnd := by omega
  have hupper : D.supportStart ≤ j.succ.val ∧ j.succ.val ≤ D.supportEnd := by
    simpa using ⟨Nat.le_trans hstart (Nat.le_succ _), hjend⟩
  have hlower : D.supportStart ≤ j.castSucc.val ∧
      j.castSucc.val ≤ D.supportEnd := by
    simpa using ⟨hstart, hend.le⟩
  rw [coefficients, coefficients, if_pos hupper, if_pos hlower]
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [Finset.prod_Ico_succ_top hstart]
  have hext : D.extendedFiniteParameter j.val = D.finiteParameter j := by
    simp [extendedFiniteParameter, j.isLt]
  rw [hext]
  simp [div_eq_mul_inv]

/-- A column meets the positive coefficient support exactly when it belongs to the active
interval. -/
theorem Compatible.adjacent_support_iff_active
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) (j : Fin n) :
    ((D.supportStart ≤ j.succ.val ∧ j.succ.val ≤ D.supportEnd) ∨
      (D.supportStart ≤ j.castSucc.val ∧ j.castSucc.val ≤ D.supportEnd)) ↔
      D.first ≤ j ∧ j ≤ D.last := by
  have hfl := hD.first_lt_last
  rw [supportStart, supportEnd]
  split_ifs with hfirst hlast <;>
    simp only [Fin.val_succ, Fin.val_castSucc] <;> constructor <;> intro h <;> omega

/-- The nonloop columns are exactly the prescribed intervening interval. -/
theorem Compatible.not_isLoop_iff_active
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) (j : Fin n) :
    ¬IsLoop (rankTwoToeplitz D.coefficients) j ↔ D.first ≤ j ∧ j ≤ D.last := by
  rw [rankTwoToeplitz_not_isLoop_iff D.coefficients D.coefficients_nonneg,
    D.coefficients_pos_iff, D.coefficients_pos_iff]
  exact hD.adjacent_support_iff_active j

/-- Equivalently, the loops are exactly the prefix and suffix outside the active interval. -/
theorem Compatible.isLoop_iff_not_active
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) (j : Fin n) :
    IsLoop (rankTwoToeplitz D.coefficients) j ↔ ¬(D.first ≤ j ∧ j ≤ D.last) := by
  constructor
  · intro hloop hactive
    exact (hD.not_isLoop_iff_active j).mpr hactive hloop
  · intro hnot
    by_contra hnonloop
    exact hnot ((hD.not_isLoop_iff_active j).mp hnonloop)

@[simp]
theorem finiteParameter_active (D : RankTwoBoundaryDatum n blocks) (j : D.Active) :
    D.finiteParameter j = (D.block j).val + 1 := by
  classical
  simp [finiteParameter, j.property]

/-- The active column is the structural `0` ray at a nonempty left loop boundary. -/
def IsLeftBoundary (D : RankTwoBoundaryDatum n blocks) (j : D.Active) : Prop :=
  D.HasLeftLoops ∧ j.val.val = D.first.val

/-- The active column is the structural `∞` ray at a nonempty right loop boundary. -/
def IsRightBoundary (D : RankTwoBoundaryDatum n blocks) (j : D.Active) : Prop :=
  D.HasRightLoops ∧ j.val.val = D.last.val

/-- For an active column, its lower coefficient lies in the positive support unless it is the
structural zero at a nonempty left loop boundary. -/
theorem Compatible.active_lower_support_iff
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) (j : D.Active) :
    (D.supportStart ≤ j.val.val ∧ j.val.val ≤ D.supportEnd) ↔
      ¬D.IsLeftBoundary j := by
  have hj := j.property
  have hfl := hD.first_lt_last
  rw [supportStart, supportEnd, IsLeftBoundary, HasLeftLoops]
  split_ifs <;> omega

/-- For an active column, its upper coefficient lies in the positive support unless it is the
structural zero at a nonempty right loop boundary. -/
theorem Compatible.active_upper_support_iff
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) (j : D.Active) :
    (D.supportStart ≤ j.val.val + 1 ∧ j.val.val + 1 ≤ D.supportEnd) ↔
      ¬D.IsRightBoundary j := by
  have hj := j.property
  have hfl := hD.first_lt_last
  rw [supportStart, supportEnd, IsRightBoundary, HasRightLoops]
  split_ifs <;> omega

/-- The projective parameter prescribed by the datum, including the two boundary rays. -/
noncomputable def boundaryParameter (D : RankTwoBoundaryDatum n blocks) (j : D.Active) :
    WithTop ℝ := by
  classical
  exact if D.IsLeftBoundary j then 0
    else if D.IsRightBoundary j then ⊤
    else ((D.block j).val + 1 : ℝ)

/-- The reconstructed columns have exactly the prescribed finite and infinite projective
parameters. -/
theorem Compatible.projectiveParameter_eq_boundaryParameter
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) (j : D.Active) :
    rankTwoProjectiveParameterWithTop D.coefficients j.val = D.boundaryParameter j := by
  classical
  let lower : Fin (n + 1) := j.val.castSucc
  let upper : Fin (n + 1) := j.val.succ
  by_cases hleft : D.IsLeftBoundary j
  · have hlower : D.coefficients lower = 0 := by
      apply (D.coefficients_eq_zero_iff lower).mpr
      intro hsupp
      exact ((hD.active_lower_support_iff j).mp (by simpa [lower] using hsupp)) hleft
    have hrightNot : ¬D.IsRightBoundary j := by
      intro hright
      have hleft' := hleft
      have hright' := hright
      rw [IsLeftBoundary] at hleft'
      rw [IsRightBoundary] at hright'
      have hfl := hD.first_lt_last
      omega
    have hupper : 0 < D.coefficients upper := by
      apply (D.coefficients_pos_iff upper).mpr
      simpa [upper] using (hD.active_upper_support_iff j).mpr hrightNot
    have hlower' : D.coefficients j.val.castSucc = 0 := by simpa [lower] using hlower
    have hupper' : D.coefficients j.val.succ ≠ 0 := by simpa [upper] using hupper.ne'
    rw [rankTwoProjectiveParameterWithTop, if_neg hupper', hlower', zero_div]
    simp [boundaryParameter, hleft]
  · by_cases hright : D.IsRightBoundary j
    · have hupper : D.coefficients upper = 0 := by
        apply (D.coefficients_eq_zero_iff upper).mpr
        intro hsupp
        exact ((hD.active_upper_support_iff j).mp (by simpa [upper] using hsupp)) hright
      have hupper' : D.coefficients j.val.succ = 0 := by simpa [upper] using hupper
      rw [rankTwoProjectiveParameterWithTop, if_pos hupper']
      simp only [boundaryParameter, if_neg hleft, if_pos hright]
    · have hlower : 0 < D.coefficients lower := by
        apply (D.coefficients_pos_iff lower).mpr
        simpa [lower] using (hD.active_lower_support_iff j).mpr hleft
      have hupper : 0 < D.coefficients upper := by
        apply (D.coefficients_pos_iff upper).mpr
        simpa [upper] using (hD.active_upper_support_iff j).mpr hright
      have hstart : D.supportStart ≤ j.val.val :=
        ((hD.active_lower_support_iff j).mpr hleft).1
      have hend : j.val.val < D.supportEnd := by
        have hu := (hD.active_upper_support_iff j).mpr hright
        omega
      have hrec := D.coefficients_succ j.val hstart hend
      have hfinite : D.finiteParameter j.val = (D.block j).val + 1 :=
        D.finiteParameter_active j
      have hparampos : 0 < D.finiteParameter j.val := D.finiteParameter_pos _
      have hlowerne : D.coefficients j.val.castSucc ≠ 0 := by
        simpa [lower] using hlower.ne'
      have hratio : D.coefficients lower / D.coefficients upper = D.finiteParameter j.val := by
        change D.coefficients j.val.castSucc / D.coefficients j.val.succ = _
        rw [hrec]
        field_simp [hparampos.ne', hlowerne]
      have hupperne : D.coefficients j.val.succ ≠ 0 := by
        simpa [upper] using hupper.ne'
      rw [rankTwoProjectiveParameterWithTop, if_neg hupperne]
      change (D.coefficients lower / D.coefficients upper : ℝ) = D.boundaryParameter j
      rw [hratio, hfinite]
      simp [boundaryParameter, hleft, hright]

/-- Finite parameters inherit monotonicity from the block map on active columns. -/
theorem finiteParameter_mono_active (D : RankTwoBoundaryDatum n blocks)
    {i j : D.Active} (hij : i ≤ j) :
    D.finiteParameter i ≤ D.finiteParameter j := by
  rw [D.finiteParameter_active, D.finiteParameter_active]
  have hblock := D.block_mono hij
  exact_mod_cast Nat.add_le_add_right hblock 1

/-- Away from the two structural boundary rays, lower coefficient equals upper coefficient times
the finite projective parameter. -/
theorem Compatible.coefficients_castSucc_eq_succ_mul_parameter
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) (j : D.Active)
    (hleft : ¬D.IsLeftBoundary j) (hright : ¬D.IsRightBoundary j) :
    D.coefficients j.val.castSucc =
      D.coefficients j.val.succ * D.finiteParameter j.val := by
  have hstart : D.supportStart ≤ j.val.val :=
    ((hD.active_lower_support_iff j).mpr hleft).1
  have hend : j.val.val < D.supportEnd := by
    have hu := (hD.active_upper_support_iff j).mpr hright
    omega
  rw [D.coefficients_succ j.val hstart hend]
  field_simp [D.finiteParameter_pos j.val |>.ne']

/-- Every increasingly ordered pair of active columns has nonnegative determinant. -/
theorem Compatible.active_pairMinor_nonneg
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible)
    (i j : D.Active) (hij : i < j) :
    0 ≤ orderedPairMinor (rankTwoToeplitz D.coefficients) i.val j.val := by
  by_cases hleft : D.IsLeftBoundary i
  · have hlower : D.coefficients i.val.castSucc = 0 := by
      apply (D.coefficients_eq_zero_iff i.val.castSucc).mpr
      intro hsupp
      exact ((hD.active_lower_support_iff i).mp (by simpa using hsupp)) hleft
    rw [orderedPairMinor_rankTwoToeplitz, hlower, mul_zero, sub_zero]
    exact mul_nonneg (D.coefficients_nonneg _) (D.coefficients_nonneg _)
  · by_cases hright : D.IsRightBoundary j
    · have hupper : D.coefficients j.val.succ = 0 := by
        apply (D.coefficients_eq_zero_iff j.val.succ).mpr
        intro hsupp
        exact ((hD.active_upper_support_iff j).mp (by simpa using hsupp)) hright
      rw [orderedPairMinor_rankTwoToeplitz, hupper, zero_mul, sub_zero]
      exact mul_nonneg (D.coefficients_nonneg _) (D.coefficients_nonneg _)
    · have hright_i : ¬D.IsRightBoundary i := by
        intro hi
        rw [IsRightBoundary] at hi
        have hjle := j.property.2
        change i.val.val < j.val.val at hij
        change j.val.val ≤ D.last.val at hjle
        omega
      have hleft_j : ¬D.IsLeftBoundary j := by
        intro hj
        rw [IsLeftBoundary] at hj
        have hile := i.property.1
        change i.val.val < j.val.val at hij
        change D.first.val ≤ i.val.val at hile
        omega
      rw [orderedPairMinor_rankTwoToeplitz,
        hD.coefficients_castSucc_eq_succ_mul_parameter i hleft hright_i,
        hD.coefficients_castSucc_eq_succ_mul_parameter j hleft_j hright]
      have hp := D.finiteParameter_mono_active hij.le
      nlinarith [mul_nonneg (D.coefficients_nonneg i.val.succ)
        (D.coefficients_nonneg j.val.succ)]

/-- The boundary construction is totally nonnegative in every minor order. -/
theorem Compatible.realization_totallyNonnegative
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) :
    TotallyNonnegative (rankTwoToeplitz D.coefficients) := by
  intro k rows cols
  cases k with
  | zero => simp
  | succ k =>
      cases k with
      | zero =>
          rw [orderedMinor_one]
          exact D.coefficients_nonneg _
      | succ k =>
          cases k with
          | zero =>
              have hrows : rows 0 < rows 1 := rows.strictMono (by decide)
              have hcols : cols 0 < cols 1 := cols.strictMono (by decide)
              have hrow₀ : rows 0 = 0 := by apply Fin.ext; omega
              have hrow₁ : rows 1 = 1 := by apply Fin.ext; omega
              rw [orderedMinor_two, hrow₀, hrow₁]
              change 0 ≤ orderedPairMinor (rankTwoToeplitz D.coefficients) (cols 0) (cols 1)
              by_cases hi : D.first ≤ cols 0 ∧ cols 0 ≤ D.last
              · by_cases hj : D.first ≤ cols 1 ∧ cols 1 ≤ D.last
                · exact hD.active_pairMinor_nonneg ⟨cols 0, hi⟩ ⟨cols 1, hj⟩ hcols
                · have hloop := (hD.isLoop_iff_not_active (cols 1)).mpr hj
                  rw [isLoop_iff_entry_eq_zero] at hloop
                  have h₀ := hloop (0 : Fin 2)
                  have h₁ := hloop (1 : Fin 2)
                  simp only [rankTwoToeplitz_row_zero] at h₀
                  simp only [rankTwoToeplitz_row_one] at h₁
                  rw [orderedPairMinor_rankTwoToeplitz, h₀, h₁]
                  simp
              · have hloop := (hD.isLoop_iff_not_active (cols 0)).mpr hi
                rw [isLoop_iff_entry_eq_zero] at hloop
                have h₀ := hloop (0 : Fin 2)
                have h₁ := hloop (1 : Fin 2)
                simp only [rankTwoToeplitz_row_zero] at h₀
                simp only [rankTwoToeplitz_row_one] at h₁
                rw [orderedPairMinor_rankTwoToeplitz, h₀, h₁]
                simp
          | succ k =>
              exfalso
              have hcard := Fintype.card_le_of_injective rows rows.injective
              simp only [Fintype.card_fin] at hcard
              omega

/-- The boundary projective parameters have exactly the prescribed block fibers. -/
theorem Compatible.boundaryParameter_eq_iff_block_eq
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) (i j : D.Active) :
    D.boundaryParameter i = D.boundaryParameter j ↔ D.block i = D.block j := by
  classical
  constructor
  · intro hq
    by_cases hiL : D.IsLeftBoundary i
    · by_cases hjL : D.IsLeftBoundary j
      · have hii : i = D.firstActive := by
          apply Subtype.ext
          apply Fin.ext
          exact hiL.2
        have hjj : j = D.firstActive := by
          apply Subtype.ext
          apply Fin.ext
          exact hjL.2
        rw [hii, hjj]
      · by_cases hjR : D.IsRightBoundary j
        · simp only [boundaryParameter, if_pos hiL, if_neg hjL, if_pos hjR] at hq
          exact False.elim (WithTop.coe_ne_top hq)
        · have hbad : (0 : WithTop ℝ) = ((D.block j).val + 1 : ℝ) := by
            simpa only [boundaryParameter, if_pos hiL, if_neg hjL, if_neg hjR] using hq
          have hpos : (0 : ℝ) < (D.block j).val + 1 := by positivity
          have hzero : (0 : ℝ) = (D.block j).val + 1 := by exact_mod_cast hbad
          exact False.elim (hpos.ne' hzero.symm)
    · by_cases hiR : D.IsRightBoundary i
      · by_cases hjR : D.IsRightBoundary j
        · have hii : i = D.lastActive := by
            apply Subtype.ext
            apply Fin.ext
            exact hiR.2
          have hjj : j = D.lastActive := by
            apply Subtype.ext
            apply Fin.ext
            exact hjR.2
          rw [hii, hjj]
        · by_cases hjL : D.IsLeftBoundary j
          · simp only [boundaryParameter, if_neg hiL, if_pos hiR, if_pos hjL] at hq
            exact False.elim (WithTop.coe_ne_top hq.symm)
          · simp only [boundaryParameter, if_neg hiL, if_pos hiR, if_neg hjL,
              if_neg hjR] at hq
            exact False.elim (WithTop.coe_ne_top hq.symm)
      · by_cases hjL : D.IsLeftBoundary j
        · have hbad : (((D.block i).val + 1 : ℝ) : WithTop ℝ) = 0 := by
            simpa only [boundaryParameter, if_neg hiL, if_neg hiR, if_pos hjL] using hq
          have hpos : (0 : ℝ) < (D.block i).val + 1 := by positivity
          have hzero : ((D.block i).val + 1 : ℝ) = 0 := by exact_mod_cast hbad
          exact False.elim (hpos.ne' hzero)
        · by_cases hjR : D.IsRightBoundary j
          · simp only [boundaryParameter, if_neg hiL, if_neg hiR, if_neg hjL,
              if_pos hjR] at hq
            exact False.elim (WithTop.coe_ne_top hq)
          · have hreal : (((D.block i).val + 1 : ℝ) : WithTop ℝ) =
                ((D.block j).val + 1 : ℝ) := by
              simpa only [boundaryParameter, if_neg hiL, if_neg hiR, if_neg hjL,
                if_neg hjR] using hq
            apply Fin.ext
            have hnat : (D.block i).val + 1 = (D.block j).val + 1 := by
              exact_mod_cast (WithTop.coe_eq_coe.mp hreal)
            exact Nat.add_right_cancel hnat
  · intro hblock
    by_cases hiL : D.IsLeftBoundary i
    · have hii : i = D.firstActive := by
        apply Subtype.ext
        apply Fin.ext
        exact hiL.2
      have hjblock : D.block j = D.block D.firstActive := by
        rw [← hii]
        exact hblock.symm
      have hjj := hD.left_boundary_singleton hiL.1 j hjblock
      rw [hii, hjj]
    · by_cases hjL : D.IsLeftBoundary j
      · have hjj : j = D.firstActive := by
          apply Subtype.ext
          apply Fin.ext
          exact hjL.2
        have hiblock : D.block i = D.block D.firstActive := by simpa [hjj] using hblock
        have hii := hD.left_boundary_singleton hjL.1 i hiblock
        exact False.elim (hiL (by
          rw [hii, IsLeftBoundary]
          exact ⟨hjL.1, rfl⟩))
      · by_cases hiR : D.IsRightBoundary i
        · have hii : i = D.lastActive := by
            apply Subtype.ext
            apply Fin.ext
            exact hiR.2
          have hjblock : D.block j = D.block D.lastActive := by
            rw [← hii]
            exact hblock.symm
          have hjj := hD.right_boundary_singleton hiR.1 j hjblock
          rw [hii, hjj]
        · by_cases hjR : D.IsRightBoundary j
          · have hjj : j = D.lastActive := by
              apply Subtype.ext
              apply Fin.ext
              exact hjR.2
            have hiblock : D.block i = D.block D.lastActive := by simpa [hjj] using hblock
            have hii := hD.right_boundary_singleton hjR.1 i hiblock
            exact False.elim (hiR (by
              rw [hii, IsRightBoundary]
              exact ⟨hjR.1, rfl⟩))
          · simp only [boundaryParameter, if_neg hiL, if_neg hiR, if_neg hjL,
              if_neg hjR]
            rw [hblock]

/-- Positive parallelism among active reconstructed columns is exactly equality of block labels. -/
theorem Compatible.columnsPositivelyParallel_iff_block_eq
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) (i j : D.Active) :
    ColumnsPositivelyParallel (rankTwoToeplitz D.coefficients) i.val j.val ↔
      D.block i = D.block j := by
  have hTN := hD.realization_totallyNonnegative
  have hi : ¬IsLoop (rankTwoToeplitz D.coefficients) i.val :=
    (hD.not_isLoop_iff_active i.val).mpr i.property
  have hj : ¬IsLoop (rankTwoToeplitz D.coefficients) j.val :=
    (hD.not_isLoop_iff_active j.val).mpr j.property
  calc
    ColumnsPositivelyParallel (rankTwoToeplitz D.coefficients) i.val j.val ↔
        rankTwoProjectiveParameterWithTop D.coefficients i.val =
          rankTwoProjectiveParameterWithTop D.coefficients j.val :=
      (rankTwoProjectiveParameterWithTop_eq_iff_columnsPositivelyParallel
        D.coefficients hTN hi hj).symm
    _ ↔ D.boundaryParameter i = D.boundaryParameter j := by
      rw [hD.projectiveParameter_eq_boundaryParameter,
        hD.projectiveParameter_eq_boundaryParameter]
    _ ↔ D.block i = D.block j := hD.boundaryParameter_eq_iff_block_eq i j

/-- The representatives of blocks zero and one give a nonzero maximal minor. -/
theorem Compatible.realization_hasFullRowRank
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) :
    HasFullRowRank (rankTwoToeplitz D.coefficients) := by
  let i := hD.zeroRepresentative
  let j := hD.oneRepresentative
  have hij : i.val < j.val := hD.zeroRepresentative_lt_oneRepresentative
  refine ⟨pairOrderEmbedding i.val j.val hij, ?_⟩
  rw [orderedMinor_two]
  change orderedPairMinor (rankTwoToeplitz D.coefficients) i.val j.val ≠ 0
  intro hzero
  have hi : ¬IsLoop (rankTwoToeplitz D.coefficients) i.val :=
    (hD.not_isLoop_iff_active i.val).mpr i.property
  have hj : ¬IsLoop (rankTwoToeplitz D.coefficients) j.val :=
    (hD.not_isLoop_iff_active j.val).mpr j.property
  have hparallel := columnsPositivelyParallel_of_orderedPairMinor_eq_zero
    (i := i.val) (j := j.val) (fun r k ↦ D.coefficients_nonneg _)
    hi hj hzero
  have hblock := (hD.columnsPositivelyParallel_iff_block_eq i j).mp hparallel
  rw [hD.block_zeroRepresentative, hD.block_oneRepresentative] at hblock
  have hval := congrArg Fin.val hblock
  simp [Compatible.zeroBlock, Compatible.oneBlock] at hval

/-- A coefficient vector realizes the exact loops and block fibers of the datum. -/
def Realizes (D : RankTwoBoundaryDatum n blocks) (a : Fin (n + 1) → ℝ) : Prop :=
  (∀ j : Fin n, IsLoop (rankTwoToeplitz a) j ↔
    ¬(D.first ≤ j ∧ j ≤ D.last)) ∧
  ∀ i j : D.Active,
    ColumnsPositivelyParallel (rankTwoToeplitz a) i.val j.val ↔ D.block i = D.block j

/-- The constructed coefficient vector realizes the datum exactly. -/
theorem Compatible.coefficients_realize
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) :
    D.Realizes D.coefficients :=
  ⟨hD.isLoop_iff_not_active, hD.columnsPositivelyParallel_iff_block_eq⟩

/-- Sufficiency for every compatible boundary datum. -/
theorem Compatible.exists_realization
    {D : RankTwoBoundaryDatum n blocks} (hD : D.Compatible) :
    ∃ a : Fin (n + 1) → ℝ,
      D.Realizes a ∧ TotallyNonnegative (rankTwoToeplitz a) ∧
        HasFullRowRank (rankTwoToeplitz a) :=
  ⟨D.coefficients, hD.coefficients_realize, hD.realization_totallyNonnegative,
    hD.realization_hasFullRowRank⟩

/-- Full rank and total nonnegativity force exactly the compatibility conditions imposed on raw
boundary data.  This is the necessity half, transported through an exact realization. -/
theorem compatible_of_exists_realization (D : RankTwoBoundaryDatum n blocks)
    (h : ∃ a : Fin (n + 1) → ℝ,
      D.Realizes a ∧ TotallyNonnegative (rankTwoToeplitz a) ∧
        HasFullRowRank (rankTwoToeplitz a)) :
    D.Compatible := by
  obtain ⟨a, hreal, hTN, hfull⟩ := h
  have hnecessary := rankTwo_classification_necessity a hTN hfull
  have htwo : 2 ≤ blocks := by
    by_contra hnot
    have hblocks : blocks ≤ 1 := by omega
    obtain ⟨i, j, hij, hi, hj, hnonparallel⟩ := hnecessary.two_distinct_classes
    have hiactive : D.first ≤ i ∧ i ≤ D.last := by
      by_contra hiactive
      exact hi ((hreal.1 i).mpr hiactive)
    have hjactive : D.first ≤ j ∧ j ≤ D.last := by
      by_contra hjactive
      exact hj ((hreal.1 j).mpr hjactive)
    let ii : D.Active := ⟨i, hiactive⟩
    let jj : D.Active := ⟨j, hjactive⟩
    have hblock : D.block ii = D.block jj := by
      apply Fin.ext
      have hiBound := (D.block ii).isLt
      have hjBound := (D.block jj).isLt
      omega
    exact hnonparallel ((hreal.2 ii jj).mpr hblock)
  refine ⟨htwo, ?_, ?_⟩
  · intro hleft j hblock
    let prev : Fin n := ⟨D.first.val - 1, by omega⟩
    have hprev : IsLoop (rankTwoToeplitz a) prev := by
      apply (hreal.1 prev).mpr
      intro hactive
      have := hactive.1
      change D.first.val ≤ prev.val at this
      simp [prev] at this
      omega
    have hfirst : ¬IsLoop (rankTwoToeplitz a) D.first := by
      intro hloop
      exact (hreal.1 D.first).mp hloop ⟨le_rfl, D.first_le_last⟩
    have hparallel : ColumnsPositivelyParallel (rankTwoToeplitz a) D.first j.val :=
      (hreal.2 D.firstActive j).mpr hblock.symm
    have heq := (hnecessary.initialClass_singleton D.first hleft
      (by simpa [prev] using hprev) hfirst j.val).mp hparallel
    apply Subtype.ext
    exact heq
  · intro hright j hblock
    let next : Fin n := ⟨D.last.val + 1, hright⟩
    have hnext : IsLoop (rankTwoToeplitz a) next := by
      apply (hreal.1 next).mpr
      intro hactive
      have := hactive.2
      change next.val ≤ D.last.val at this
      simp [next] at this
    have hlast : ¬IsLoop (rankTwoToeplitz a) D.last := by
      intro hloop
      exact (hreal.1 D.last).mp hloop ⟨D.first_le_last, le_rfl⟩
    have hparallel : ColumnsPositivelyParallel (rankTwoToeplitz a) D.last j.val :=
      (hreal.2 D.lastActive j).mpr hblock.symm
    have heq := (hnecessary.terminalClass_singleton D.last hright
      (by simpa [next] using hnext) hlast j.val).mp hparallel
    apply Subtype.ext
    exact heq

/-- Complete boundary-data classification: a raw datum has a full-row-rank totally nonnegative
Toeplitz realization with exactly its loops and parallel fibers if and only if it is compatible. -/
theorem exists_realization_iff_compatible (D : RankTwoBoundaryDatum n blocks) :
    (∃ a : Fin (n + 1) → ℝ,
      D.Realizes a ∧ TotallyNonnegative (rankTwoToeplitz a) ∧
        HasFullRowRank (rankTwoToeplitz a)) ↔ D.Compatible :=
  ⟨D.compatible_of_exists_realization, fun hD ↦ hD.exists_realization⟩

end RankTwoBoundaryDatum

end ToeplitzPositroids
