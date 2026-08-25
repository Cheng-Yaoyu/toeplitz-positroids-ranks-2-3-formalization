import ToeplitzPositroids.Matrix.Positroid
import ToeplitzPositroids.RankTwo.BoundaryRealization
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Matroid-level rank-two classification

This file packages Theorem 3 at the level of genuine column matroids.  The existing boundary
construction proves the matrix-level classification.  Here we add the two missing bridges:

* a canonical ordered support datum extracted from every full-row-rank totally nonnegative
  rank-two Toeplitz matrix;
* the fact that loops and positive-parallel classes determine every basis of a rank-two column
  matroid.
-/

namespace ToeplitzPositroids

open Matrix Set

noncomputable section

/-- Ordered rank-two support data before compressing the projective parameters to finite block
labels.  The parameter fibers are the prescribed parallel classes. -/
structure RankTwoMatroidDatum (n : ℕ) where
  first : Fin n
  last : Fin n
  first_le_last : first ≤ last
  parameter : {j : Fin n // first ≤ j ∧ j ≤ last} → WithTop ℝ
  parameter_mono : Monotone parameter

namespace RankTwoMatroidDatum

variable {n : ℕ} (D : RankTwoMatroidDatum n)

abbrev Active := {j : Fin n // D.first ≤ j ∧ j ≤ D.last}

def firstActive : D.Active := ⟨D.first, le_rfl, D.first_le_last⟩

def lastActive : D.Active := ⟨D.last, D.first_le_last, le_rfl⟩

/-- The intrinsic compatibility conditions in Theorem 3. -/
structure Compatible : Prop where
  two_distinct : ∃ i j : D.Active, D.parameter i ≠ D.parameter j
  left_boundary_singleton : 0 < D.first.val →
    ∀ j : D.Active, D.parameter j = D.parameter D.firstActive → j = D.firstActive
  right_boundary_singleton : D.last.val + 1 < n →
    ∀ j : D.Active, D.parameter j = D.parameter D.lastActive → j = D.lastActive

/-- Exact matrix realization of the loop interval and projective-parameter fibers. -/
def Realizes (a : Fin (n + 1) → ℝ) : Prop :=
  (∀ j : Fin n, IsLoop (rankTwoToeplitz a) j ↔
    ¬(D.first ≤ j ∧ j ≤ D.last)) ∧
  ∀ i j : D.Active,
    ColumnsPositivelyParallel (rankTwoToeplitz a) i.val j.val ↔
      D.parameter i = D.parameter j

/-- The pair of raw indices is a basis pair exactly when both indices are active and their
projective parameters are distinct. -/
def IsBasisPair (i j : Fin n) : Prop :=
  ∃ hi : D.first ≤ i ∧ i ≤ D.last,
    ∃ hj : D.first ≤ j ∧ j ≤ D.last,
      D.parameter ⟨i, hi⟩ ≠ D.parameter ⟨j, hj⟩

/-- The finite set of projective values occurring in the datum. -/
def parameterValues : Finset (WithTop ℝ) :=
  Finset.univ.image D.parameter

/-- The number of parallel classes. -/
def blockCount : ℕ := D.parameterValues.card

/-- Increasing enumeration of the occurring projective values. -/
def parameterEmbedding : Fin D.blockCount ↪o WithTop ℝ :=
  D.parameterValues.orderEmbOfFin rfl

theorem parameter_mem_values (j : D.Active) : D.parameter j ∈ D.parameterValues := by
  simp [parameterValues]

theorem exists_parameterIndex (j : D.Active) :
    ∃ k : Fin D.blockCount, D.parameterEmbedding k = D.parameter j := by
  have hj : D.parameter j ∈ (D.parameterValues : Set (WithTop ℝ)) :=
    D.parameter_mem_values j
  rw [← Finset.range_orderEmbOfFin D.parameterValues rfl] at hj
  exact hj

/-- Compressed finite block label of an active index. -/
def block (j : D.Active) : Fin D.blockCount :=
  Classical.choose (D.exists_parameterIndex j)

@[simp]
theorem parameterEmbedding_block (j : D.Active) :
    D.parameterEmbedding (D.block j) = D.parameter j :=
  Classical.choose_spec (D.exists_parameterIndex j)

theorem block_eq_iff_parameter_eq (i j : D.Active) :
    D.block i = D.block j ↔ D.parameter i = D.parameter j := by
  constructor
  · intro h
    rw [← D.parameterEmbedding_block i, ← D.parameterEmbedding_block j, h]
  · intro h
    apply D.parameterEmbedding.injective
    rw [D.parameterEmbedding_block, D.parameterEmbedding_block, h]

theorem block_mono : Monotone D.block := by
  intro i j hij
  apply le_of_not_gt
  intro hji
  have hparam : D.parameter j < D.parameter i := by
    rw [← D.parameterEmbedding_block j, ← D.parameterEmbedding_block i]
    exact D.parameterEmbedding.strictMono hji
  exact (not_lt_of_ge (D.parameter_mono hij)) hparam

theorem block_surjective : Function.Surjective D.block := by
  intro k
  have hk : D.parameterEmbedding k ∈ D.parameterValues :=
    Finset.orderEmbOfFin_mem D.parameterValues rfl k
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hk
  refine ⟨j, ?_⟩
  apply D.parameterEmbedding.injective
  rw [D.parameterEmbedding_block]
  exact hj

/-- Compression to the finite block datum used by the constructive matrix theorem. -/
def toBoundaryDatum : RankTwoBoundaryDatum n D.blockCount where
  first := D.first
  last := D.last
  first_le_last := D.first_le_last
  block := D.block
  block_mono := D.block_mono
  block_surjective := D.block_surjective

theorem Compatible.two_le_blockCount (hD : D.Compatible) : 2 ≤ D.blockCount := by
  obtain ⟨i, j, hij⟩ := hD.two_distinct
  have hi := D.parameter_mem_values i
  have hj := D.parameter_mem_values j
  have hcard : 1 < D.parameterValues.card :=
    Finset.one_lt_card.mpr ⟨D.parameter i, hi, D.parameter j, hj, hij⟩
  simpa [blockCount] using hcard

theorem Compatible.toBoundaryDatum_compatible (hD : D.Compatible) :
    D.toBoundaryDatum.Compatible := by
  refine ⟨hD.two_le_blockCount, ?_, ?_⟩
  · intro hleft j hblock
    apply hD.left_boundary_singleton hleft j
    exact (D.block_eq_iff_parameter_eq j D.firstActive).mp hblock
  · intro hright j hblock
    apply hD.right_boundary_singleton hright j
    exact (D.block_eq_iff_parameter_eq j D.lastActive).mp hblock

/-- Every compatible ordered support datum has a full-row-rank totally nonnegative Toeplitz
realization with exactly its loops and projective fibers. -/
theorem Compatible.exists_realization (hD : D.Compatible) :
    ∃ a : Fin (n + 1) → ℝ,
      D.Realizes a ∧ TotallyNonnegative (rankTwoToeplitz a) ∧
        HasFullRowRank (rankTwoToeplitz a) := by
  let B := D.toBoundaryDatum
  have hB : B.Compatible := hD.toBoundaryDatum_compatible
  obtain ⟨a, hreal, hTN, hfull⟩ := hB.exists_realization
  refine ⟨a, ?_, hTN, hfull⟩
  constructor
  · intro j
    simpa [B, toBoundaryDatum] using hreal.1 j
  · intro i j
    have hparallel := hreal.2 i j
    rw [hparallel]
    exact D.block_eq_iff_parameter_eq i j

end RankTwoMatroidDatum

/-! ## Canonical data extracted from a matrix -/

variable {n : ℕ}

def rankTwoNonloopIndices (a : Fin (n + 1) → ℝ) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun j ↦ ¬IsLoop (rankTwoToeplitz a) j

@[simp]
theorem mem_rankTwoNonloopIndices {a : Fin (n + 1) → ℝ} {j : Fin n} :
    j ∈ rankTwoNonloopIndices a ↔ ¬IsLoop (rankTwoToeplitz a) j := by
  simp [rankTwoNonloopIndices]

theorem rankTwoNonloopIndices_nonempty {a : Fin (n + 1) → ℝ}
    (hfull : HasFullRowRank (rankTwoToeplitz a)) :
    (rankTwoNonloopIndices a).Nonempty := by
  obtain ⟨i, -, -, hi, -, -⟩ := hasFullRowRank_exists_nonparallel_columns hfull
  exact ⟨i, mem_rankTwoNonloopIndices.mpr hi⟩

def firstRankTwoNonloop (a : Fin (n + 1) → ℝ)
    (hfull : HasFullRowRank (rankTwoToeplitz a)) : Fin n :=
  (rankTwoNonloopIndices a).min' (rankTwoNonloopIndices_nonempty hfull)

def lastRankTwoNonloop (a : Fin (n + 1) → ℝ)
    (hfull : HasFullRowRank (rankTwoToeplitz a)) : Fin n :=
  (rankTwoNonloopIndices a).max' (rankTwoNonloopIndices_nonempty hfull)

theorem firstRankTwoNonloop_nonloop {a : Fin (n + 1) → ℝ}
    (hfull : HasFullRowRank (rankTwoToeplitz a)) :
    ¬IsLoop (rankTwoToeplitz a) (firstRankTwoNonloop a hfull) :=
  mem_rankTwoNonloopIndices.mp
    ((rankTwoNonloopIndices a).min'_mem (rankTwoNonloopIndices_nonempty hfull))

theorem lastRankTwoNonloop_nonloop {a : Fin (n + 1) → ℝ}
    (hfull : HasFullRowRank (rankTwoToeplitz a)) :
    ¬IsLoop (rankTwoToeplitz a) (lastRankTwoNonloop a hfull) :=
  mem_rankTwoNonloopIndices.mp
    ((rankTwoNonloopIndices a).max'_mem (rankTwoNonloopIndices_nonempty hfull))

theorem firstRankTwoNonloop_le_last {a : Fin (n + 1) → ℝ}
    (hfull : HasFullRowRank (rankTwoToeplitz a)) :
    firstRankTwoNonloop a hfull ≤ lastRankTwoNonloop a hfull := by
  exact Finset.min'_le _ _
    ((rankTwoNonloopIndices a).max'_mem (rankTwoNonloopIndices_nonempty hfull))

theorem rankTwo_nonloop_iff_between {a : Fin (n + 1) → ℝ}
    (hTN : TotallyNonnegative (rankTwoToeplitz a))
    (hfull : HasFullRowRank (rankTwoToeplitz a)) (j : Fin n) :
    ¬IsLoop (rankTwoToeplitz a) j ↔
      firstRankTwoNonloop a hfull ≤ j ∧ j ≤ lastRankTwoNonloop a hfull := by
  constructor
  · intro hj
    exact ⟨Finset.min'_le _ _ (mem_rankTwoNonloopIndices.mpr hj),
      Finset.le_max' _ _ (mem_rankTwoNonloopIndices.mpr hj)⟩
  · rintro ⟨hfirst, hlast⟩
    exact (Set.ordConnected_def.mp (rankTwoToeplitz_nonloop_ordConnected a hTN))
      (firstRankTwoNonloop_nonloop hfull) (lastRankTwoNonloop_nonloop hfull) ⟨hfirst, hlast⟩

/-- Canonical ordered support datum extracted from a full-rank totally nonnegative Toeplitz
matrix. -/
def canonicalRankTwoMatroidDatum (a : Fin (n + 1) → ℝ)
    (hTN : TotallyNonnegative (rankTwoToeplitz a))
    (hfull : HasFullRowRank (rankTwoToeplitz a)) : RankTwoMatroidDatum n where
  first := firstRankTwoNonloop a hfull
  last := lastRankTwoNonloop a hfull
  first_le_last := firstRankTwoNonloop_le_last hfull
  parameter j := rankTwoProjectiveParameterWithTop a j.val
  parameter_mono := by
    intro i j hij
    exact rankTwoProjectiveParameterWithTop_mono a hTN hij
      ((rankTwo_nonloop_iff_between hTN hfull i).mpr i.property)
      ((rankTwo_nonloop_iff_between hTN hfull j).mpr j.property)

theorem canonicalRankTwoMatroidDatum_compatible {a : Fin (n + 1) → ℝ}
    (hTN : TotallyNonnegative (rankTwoToeplitz a))
    (hfull : HasFullRowRank (rankTwoToeplitz a)) :
    (canonicalRankTwoMatroidDatum a hTN hfull).Compatible := by
  let D := canonicalRankTwoMatroidDatum a hTN hfull
  have hactive : ∀ {j : Fin n}, ¬IsLoop (rankTwoToeplitz a) j →
      D.first ≤ j ∧ j ≤ D.last := by
    intro j hj
    exact (rankTwo_nonloop_iff_between hTN hfull j).mp hj
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨i, j, -, hi, hj, hnonparallel⟩ :=
      hasFullRowRank_exists_nonparallel_columns hfull
    let ii : D.Active := ⟨i, hactive hi⟩
    let jj : D.Active := ⟨j, hactive hj⟩
    refine ⟨ii, jj, ?_⟩
    intro heq
    apply hnonparallel
    exact (rankTwoProjectiveParameterWithTop_eq_iff_columnsPositivelyParallel
      a hTN hi hj).mp heq
  · intro hleft j hparam
    let prev : Fin n := ⟨D.first.val - 1, by omega⟩
    have hprev : IsLoop (rankTwoToeplitz a) prev := by
      by_contra hnonloop
      have hle := Finset.min'_le (rankTwoNonloopIndices a) prev
        (mem_rankTwoNonloopIndices.mpr hnonloop)
      have hleval : (firstRankTwoNonloop a hfull).val ≤ prev.val := hle
      have hprevVal : prev.val = (firstRankTwoNonloop a hfull).val - 1 := by
        simp [prev, D, canonicalRankTwoMatroidDatum]
      have hfirstPos : 0 < (firstRankTwoNonloop a hfull).val := by
        simpa [D, canonicalRankTwoMatroidDatum] using hleft
      rw [hprevVal] at hleval
      omega
    have hfirst : ¬IsLoop (rankTwoToeplitz a) D.first := by
      exact firstRankTwoNonloop_nonloop hfull
    have hpar : ColumnsPositivelyParallel (rankTwoToeplitz a) D.first j.val :=
      (rankTwoProjectiveParameterWithTop_eq_iff_columnsPositivelyParallel
        a hTN hfirst ((rankTwo_nonloop_iff_between hTN hfull j).mpr j.property)).mp hparam.symm
    have hj := (rankTwoToeplitz_initial_parallel_class_singleton a hTN D.first hleft
      (by simpa [prev] using hprev) hfirst j.val).mp hpar
    apply Subtype.ext
    exact hj
  · intro hright j hparam
    let next : Fin n := ⟨D.last.val + 1, hright⟩
    have hnext : IsLoop (rankTwoToeplitz a) next := by
      by_contra hnonloop
      have hle := Finset.le_max' (rankTwoNonloopIndices a) next
        (mem_rankTwoNonloopIndices.mpr hnonloop)
      have hleval : next.val ≤ (lastRankTwoNonloop a hfull).val := hle
      have hnextVal : next.val = (lastRankTwoNonloop a hfull).val + 1 := by
        simp [next, D, canonicalRankTwoMatroidDatum]
      rw [hnextVal] at hleval
      omega
    have hlast : ¬IsLoop (rankTwoToeplitz a) D.last := by
      exact lastRankTwoNonloop_nonloop hfull
    have hpar : ColumnsPositivelyParallel (rankTwoToeplitz a) D.last j.val :=
      (rankTwoProjectiveParameterWithTop_eq_iff_columnsPositivelyParallel
        a hTN hlast ((rankTwo_nonloop_iff_between hTN hfull j).mpr j.property)).mp hparam.symm
    have hj := (rankTwoToeplitz_terminal_parallel_class_singleton a hTN D.last hright
      (by simpa [next] using hnext) hlast j.val).mp hpar
    apply Subtype.ext
    exact hj

theorem canonicalRankTwoMatroidDatum_realizes {a : Fin (n + 1) → ℝ}
    (hTN : TotallyNonnegative (rankTwoToeplitz a))
    (hfull : HasFullRowRank (rankTwoToeplitz a)) :
    (canonicalRankTwoMatroidDatum a hTN hfull).Realizes a := by
  let D := canonicalRankTwoMatroidDatum a hTN hfull
  constructor
  · intro j
    rw [← not_iff_not]
    simpa [D] using rankTwo_nonloop_iff_between hTN hfull j
  · intro i j
    exact (rankTwoProjectiveParameterWithTop_eq_iff_columnsPositivelyParallel a hTN
      ((rankTwo_nonloop_iff_between hTN hfull i).mpr i.property)
      ((rankTwo_nonloop_iff_between hTN hfull j).mpr j.property)).symm

/-! ## Basis support and matroid classification -/

namespace RankTwoMatroidDatum

variable {D : RankTwoMatroidDatum n} {a : Fin (n + 1) → ℝ}

theorem Realizes.columnMatroid_isBase_range_iff (R : D.Realizes a)
    (hTN : TotallyNonnegative (rankTwoToeplitz a)) (cols : Fin 2 ↪o Fin n) :
    (columnMatroid (rankTwoToeplitz a)).IsBase (Set.range cols) ↔
      D.IsBasisPair (cols 0) (cols 1) := by
  rw [ToeplitzPositroids.columnMatroid_isBase_range_iff, orderedMinor_two]
  change orderedPairMinor (rankTwoToeplitz a) (cols 0) (cols 1) ≠ 0 ↔ _
  constructor
  · intro hminor
    have hi : ¬IsLoop (rankTwoToeplitz a) (cols 0) := by
      intro hloop
      rw [isLoop_iff_entry_eq_zero] at hloop
      have hzero := hloop (0 : Fin 2)
      have hone := hloop (1 : Fin 2)
      rw [rankTwoToeplitz_row_zero] at hzero
      rw [rankTwoToeplitz_row_one] at hone
      apply hminor
      rw [orderedPairMinor_rankTwoToeplitz, hzero, hone]
      ring
    have hj : ¬IsLoop (rankTwoToeplitz a) (cols 1) := by
      intro hloop
      rw [isLoop_iff_entry_eq_zero] at hloop
      have hzero := hloop (0 : Fin 2)
      have hone := hloop (1 : Fin 2)
      rw [rankTwoToeplitz_row_zero] at hzero
      rw [rankTwoToeplitz_row_one] at hone
      apply hminor
      rw [orderedPairMinor_rankTwoToeplitz, hzero, hone]
      ring
    have hiActive : D.first ≤ cols 0 ∧ cols 0 ≤ D.last := by
      by_contra hbad
      exact hi ((R.1 (cols 0)).mpr hbad)
    have hjActive : D.first ≤ cols 1 ∧ cols 1 ≤ D.last := by
      by_contra hbad
      exact hj ((R.1 (cols 1)).mpr hbad)
    refine ⟨hiActive, hjActive, ?_⟩
    intro hparam
    have hparallel := (R.2 ⟨cols 0, hiActive⟩ ⟨cols 1, hjActive⟩).mpr hparam
    obtain ⟨c, -, hcol⟩ := hparallel
    exact hminor (orderedPairMinor_eq_zero_of_column_eq_smul _ _ _ c hcol)
  · rintro ⟨hiActive, hjActive, hparam⟩ hminor
    have hi : ¬IsLoop (rankTwoToeplitz a) (cols 0) := by
      intro hloop
      exact ((R.1 (cols 0)).mp hloop) hiActive
    have hj : ¬IsLoop (rankTwoToeplitz a) (cols 1) := by
      intro hloop
      exact ((R.1 (cols 1)).mp hloop) hjActive
    have hparallel := columnsPositivelyParallel_of_orderedPairMinor_eq_zero
      (fun r k ↦ hTN.entry_nonneg r k) hi hj hminor
    exact hparam ((R.2 ⟨cols 0, hiActive⟩ ⟨cols 1, hjActive⟩).mp hparallel)

/-- A matroid has exactly the rank-two basis support encoded by `D`. -/
structure CompatibleSupportRealization (D : RankTwoMatroidDatum n)
    (M : Matroid (Fin n)) : Prop where
  ground_eq : M.E = Set.univ
  isBase_range_iff : ∀ cols : Fin 2 ↪o Fin n,
    M.IsBase (Set.range cols) ↔ D.IsBasisPair (cols 0) (cols 1)

theorem Realizes.compatibleSupportRealization (R : D.Realizes a)
    (hTN : TotallyNonnegative (rankTwoToeplitz a)) :
    CompatibleSupportRealization D (columnMatroid (rankTwoToeplitz a)) where
  ground_eq := columnMatroid_ground _
  isBase_range_iff := R.columnMatroid_isBase_range_iff hTN

theorem Compatible.exists_basisPair {D : RankTwoMatroidDatum n} (hD : D.Compatible) :
    ∃ cols : Fin 2 ↪o Fin n, D.IsBasisPair (cols 0) (cols 1) := by
  obtain ⟨i, j, hij⟩ := hD.two_distinct
  have hijRaw : i.val ≠ j.val := by
    intro h
    have : i = j := Subtype.ext h
    exact hij (this ▸ rfl)
  rcases lt_or_gt_of_ne hijRaw with hlt | hgt
  · let cols := pairOrderEmbedding i.val j.val hlt
    refine ⟨cols, i.property, j.property, ?_⟩
    simpa [cols, pairOrderEmbedding_zero, pairOrderEmbedding_one] using hij
  · let cols := pairOrderEmbedding j.val i.val hgt
    refine ⟨cols, j.property, i.property, ?_⟩
    simpa [cols, pairOrderEmbedding_zero, pairOrderEmbedding_one] using hij.symm

theorem CompatibleSupportRealization.base_ncard_eq_two
    {D : RankTwoMatroidDatum n} {M : Matroid (Fin n)}
    (hD : D.Compatible) (R : CompatibleSupportRealization D M)
    {B : Set (Fin n)} (hB : M.IsBase B) : B.ncard = 2 := by
  obtain ⟨cols, hpair⟩ := hD.exists_basisPair
  have hbase : M.IsBase (Set.range cols) := (R.isBase_range_iff cols).mpr hpair
  rw [hB.ncard_eq_ncard_of_isBase hbase, Set.ncard_range_of_injective cols.injective]
  simp

theorem matroid_eq_of_compatibleSupportRealizations
    {D : RankTwoMatroidDatum n} {M N : Matroid (Fin n)}
    (hD : D.Compatible) (RM : CompatibleSupportRealization D M)
    (RN : CompatibleSupportRealization D N) : M = N := by
  apply Matroid.ext_isBase (RM.ground_eq.trans RN.ground_eq.symm)
  intro B _
  constructor
  · intro hB
    let hBfin : B.Finite := Set.toFinite B
    let s : Finset (Fin n) := hBfin.toFinset
    have hsCard : s.card = 2 := by
      rw [← Set.ncard_eq_toFinset_card B hBfin]
      exact RM.base_ncard_eq_two hD hB
    let cols : Fin 2 ↪o Fin n := s.orderEmbOfFin hsCard
    have hrange : Set.range cols = B := by
      dsimp only [cols, s]
      rw [Finset.range_orderEmbOfFin]
      exact hBfin.coe_toFinset
    have hpair : D.IsBasisPair (cols 0) (cols 1) :=
      (RM.isBase_range_iff cols).mp (hrange.symm ▸ hB)
    exact hrange ▸ (RN.isBase_range_iff cols).mpr hpair
  · intro hB
    let hBfin : B.Finite := Set.toFinite B
    let s : Finset (Fin n) := hBfin.toFinset
    have hsCard : s.card = 2 := by
      rw [← Set.ncard_eq_toFinset_card B hBfin]
      exact RN.base_ncard_eq_two hD hB
    let cols : Fin 2 ↪o Fin n := s.orderEmbOfFin hsCard
    have hrange : Set.range cols = B := by
      dsimp only [cols, s]
      rw [Finset.range_orderEmbOfFin]
      exact hBfin.coe_toFinset
    have hpair : D.IsBasisPair (cols 0) (cols 1) :=
      (RN.isBase_range_iff cols).mp (hrange.symm ▸ hB)
    exact hrange ▸ (RM.isBase_range_iff cols).mpr hpair

end RankTwoMatroidDatum

/-- A rank-two matroid has a strong Toeplitz representation when it is the column matroid of a
full-row-rank all-minor totally nonnegative rank-two Toeplitz section. -/
def HasTNNRankTwoToeplitzRepresentation (M : Matroid (Fin n)) : Prop :=
  ∃ a : Fin (n + 1) → ℝ,
    TotallyNonnegative (rankTwoToeplitz a) ∧
      HasFullRowRank (rankTwoToeplitz a) ∧ columnMatroid (rankTwoToeplitz a) = M

/-- Intrinsic compatible rank-two support. -/
def HasCompatibleRankTwoSupport (M : Matroid (Fin n)) : Prop :=
  ∃ D : RankTwoMatroidDatum n,
    D.Compatible ∧ D.CompatibleSupportRealization M

/-- Theorem 3 at the level of genuine matroids. -/
theorem hasTNNRankTwoToeplitzRepresentation_iff_hasCompatibleRankTwoSupport
    {M : Matroid (Fin n)} :
    HasTNNRankTwoToeplitzRepresentation M ↔ HasCompatibleRankTwoSupport M := by
  constructor
  · rintro ⟨a, hTN, hfull, hmatroid⟩
    let D := canonicalRankTwoMatroidDatum a hTN hfull
    have hD : D.Compatible := canonicalRankTwoMatroidDatum_compatible hTN hfull
    have hreal : D.Realizes a := canonicalRankTwoMatroidDatum_realizes hTN hfull
    refine ⟨D, hD, ?_⟩
    rw [← hmatroid]
    exact hreal.compatibleSupportRealization hTN
  · rintro ⟨D, hD, hM⟩
    obtain ⟨a, hreal, hTN, hfull⟩ := hD.exists_realization
    have hmatrix := hreal.compatibleSupportRealization hTN
    exact ⟨a, hTN, hfull,
      RankTwoMatroidDatum.matroid_eq_of_compatibleSupportRealizations hD hmatrix hM⟩

end

end ToeplitzPositroids
