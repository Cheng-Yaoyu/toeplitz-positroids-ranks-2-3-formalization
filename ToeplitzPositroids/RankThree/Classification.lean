import ToeplitzPositroids.RankThree.ClassificationNecessity
import ToeplitzPositroids.RankThree.PropositionSeventeen
import ToeplitzPositroids.RankThree.SupportUniqueness
import ToeplitzPositroids.RankThree.TwoSidedRealization
import Mathlib.Tactic

/-!
# Classification of rank-three Toeplitz positroid supports

This file packages the necessity, realization, and support-uniqueness results into the exact
rank-three classification.  A representation is exact when its vanishing ordered maximal
minors are precisely the triples declared to be nonbases by the compatible datum.
-/

namespace ToeplitzPositroids

open RankThree

noncomputable section

namespace CompatibleRankThreeData

variable {n : ℕ} (D : CompatibleRankThreeData n)

/-- A coefficient vector exactly represents compatible rank-three data when its Toeplitz
section is totally nonnegative, has full row rank, and has exactly the prescribed vanishing
maximal minors. -/
structure ExactToeplitzRepresentation (a : Fin (n + 2) → ℝ) : Prop where
  totallyNonnegative : TotallyNonnegative (rankThreeToeplitz a)
  fullRowRank : HasFullRowRank (rankThreeToeplitz a)
  maximalMinor_zero_iff : ∀ cols : Fin 3 ↪o Fin n,
    orderedMinor (rankThreeToeplitz a) (allRows 3) cols = 0 ↔
      D.TripleNonbasis (selectedTripleFinset cols)

namespace ExactToeplitzRepresentation

variable {D : CompatibleRankThreeData n} {a : Fin (n + 2) → ℝ}

/-- An exact representation, viewed only as the support predicate used by the one-sided
construction. -/
theorem realizesCompatibleSupport (R : D.ExactToeplitzRepresentation a) :
    RealizesCompatibleSupport D (rankThreeToeplitz a) :=
  R.maximalMinor_zero_iff

/-- Bundle an exact Toeplitz representation as the positroid representation determined by its
nonnegative maximal minors. -/
noncomputable def toPositroidRepresentation (R : D.ExactToeplitzRepresentation a) :
    PositroidRepresentation 3 n :=
  ⟨rankThreeToeplitz a,
    R.fullRowRank, R.totallyNonnegative.maximalMinorsNonnegative⟩

/-- An exact representation is a strong all-minor totally nonnegative Toeplitz
representation. -/
theorem isAllMinorTNToeplitzRepresentation (R : D.ExactToeplitzRepresentation a) :
    IsAllMinorTNToeplitzRepresentation (rankThreeToeplitz a) := by
  rw [rankThreeToeplitz_eq_finiteToeplitz,
    isAllMinorTNToeplitzRepresentation_finiteToeplitz_iff]
  exact ⟨R.fullRowRank, R.totallyNonnegative⟩

/-- The genuine column matroid of an exact representation has precisely the compatible datum's
three-element bases. -/
theorem compatibleTripleSupportRealization (R : D.ExactToeplitzRepresentation a) :
    CompatibleTripleSupportRealization D R.toPositroidRepresentation.matroid := by
  let P := R.toPositroidRepresentation
  refine ⟨P.matroid_ground, ?_, ?_⟩
  · obtain ⟨cols, hbase, _⟩ := P.exists_positive_orderedBasis
    exact ⟨Set.range cols, hbase, by simp [Set.ncard_range_of_injective cols.injective]⟩
  · intro J hJ
    let cols := J.orderEmbOfFin hJ
    have hrange : Set.range cols = (J : Set (Fin n)) := by
      simp [cols]
    rw [← hrange, P.isBase_range_iff_orderedMinor_pos]
    have hset : selectedTripleFinset cols = J := by
      rw [selectedTripleFinset_eq, ← finset_eq_three_orderEmb_values hJ]
    have hzero := R.maximalMinor_zero_iff cols
    rw [hset] at hzero
    constructor
    · intro hpos hnonbasis
      exact (ne_of_gt hpos) (hzero.mpr hnonbasis)
    · intro hnonbasis
      have hne : orderedMinor (rankThreeToeplitz a) (allRows 3) cols ≠ 0 := by
        intro hzero'
        exact hnonbasis (hzero.mp hzero')
      exact lt_of_le_of_ne
        (R.totallyNonnegative.orderedMinor_nonneg (allRows 3) cols) hne.symm

/-- The finite basis family of exactly represented data is the nonzero ordered maximal-minor
support of its Toeplitz matrix. -/
theorem mem_basisFinsets_iff (R : D.ExactToeplitzRepresentation a)
    {J : Finset (Fin n)} :
    J ∈ D.basisFinsets ↔
      ∃ hJ : J.card = 3,
        orderedMinor (rankThreeToeplitz a) (allRows 3) (J.orderEmbOfFin hJ) ≠ 0 := by
  rw [CompatibleRankThreeData.mem_basisFinsets_iff]
  constructor
  · rintro ⟨hJ, hnonbasis⟩
    refine ⟨hJ, ?_⟩
    intro hzero
    apply hnonbasis
    have hsupport := (R.maximalMinor_zero_iff (J.orderEmbOfFin hJ)).mp hzero
    rwa [selectedTripleFinset_eq, ← finset_eq_three_orderEmb_values hJ] at hsupport
  · rintro ⟨hJ, hnonzero⟩
    refine ⟨hJ, ?_⟩
    intro hnonbasis
    apply hnonzero
    apply (R.maximalMinor_zero_iff (J.orderEmbOfFin hJ)).mpr
    rwa [selectedTripleFinset_eq, ← finset_eq_three_orderEmb_values hJ]

end ExactToeplitzRepresentation

/-- The canonical compatible datum extracted from a totally nonnegative full-row-rank
rank-three Toeplitz matrix exactly describes all of its vanishing maximal minors. -/
theorem canonical_exactToeplitzRepresentation {a : Fin (n + 2) → ℝ}
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    (canonicalCompatibleRankThreeData hTN hfull).ExactToeplitzRepresentation a := by
  refine ⟨hTN, hfull, ?_⟩
  intro cols
  have hcols : cols =
      (selectedTripleFinset cols).orderEmbOfFin (selectedTripleFinset_card cols) :=
    Finset.orderEmbOfFin_unique' (selectedTripleFinset_card cols) (by
      intro i
      simp [selectedTripleFinset])
  have hcanonical := canonicalCompatibleRankThreeData_tripleNonbasis_iff hTN hfull
    (selectedTripleFinset cols) (selectedTripleFinset_card cols)
  rw [← hcols] at hcanonical
  exact hcanonical.symm

/-- Exact representation identifies the datum's finite basis family with that of the canonical
datum extracted from the same matrix. -/
theorem basisFinsets_eq_canonical {a : Fin (n + 2) → ℝ}
    (R : D.ExactToeplitzRepresentation a) :
    D.basisFinsets =
      (canonicalCompatibleRankThreeData R.totallyNonnegative R.fullRowRank).basisFinsets := by
  ext J
  rw [R.mem_basisFinsets_iff,
    mem_canonicalCompatibleRankThreeData_basisFinsets_iff]

/-- Any two compatible data exactly represented by the same Toeplitz matrix have the same
loop, parallel-pair, and maximal rank-two-flat support. -/
theorem supportComponents_eq_of_exactRepresentations
    {E : CompatibleRankThreeData n} {a : Fin (n + 2) → ℝ}
    (RD : D.ExactToeplitzRepresentation a)
    (RE : E.ExactToeplitzRepresentation a) :
    D.supportLoops = E.supportLoops ∧
      D.supportParallelPairs = E.supportParallelPairs ∧
      D.supportRankTwoFlats = E.supportRankTwoFlats := by
  have hbasis : D.basisFinsets = E.basisFinsets := by
    ext J
    rw [RD.mem_basisFinsets_iff, RE.mem_basisFinsets_iff]
  exact D.supportComponents_eq_of_sameSupport E
    (sameCompatibleTripleSupport_of_basisFinsets_eq D E hbasis)

/-- In particular, exact representation recovers the same support components as the canonical
datum extracted from the representing matrix. -/
theorem supportComponents_eq_canonical {a : Fin (n + 2) → ℝ}
    (R : D.ExactToeplitzRepresentation a) :
    D.supportLoops =
        (canonicalCompatibleRankThreeData R.totallyNonnegative R.fullRowRank).supportLoops ∧
      D.supportParallelPairs =
        (canonicalCompatibleRankThreeData R.totallyNonnegative R.fullRowRank).supportParallelPairs ∧
      D.supportRankTwoFlats =
        (canonicalCompatibleRankThreeData R.totallyNonnegative R.fullRowRank).supportRankTwoFlats :=
  supportComponents_eq_of_exactRepresentations D R
    (canonical_exactToeplitzRepresentation R.totallyNonnegative R.fullRowRank)

/-- Proposition 21 supplies an exact representation whenever both loop boundaries are
nonempty. -/
theorem exists_exactToeplitzRepresentation_of_twoSided
    (hTwo : RankThree.HasTwoSidedLoops D) :
    ∃ a : Fin (n + 2) → ℝ, D.ExactToeplitzRepresentation a := by
  obtain ⟨a, hTN, hfull, _, hzero⟩ :=
    RankThree.CompatibleRankThreeData.propositionTwentyOne (D := D) hTwo
  refine ⟨a, hTN, hfull, ?_⟩
  intro cols
  simpa [selectedTripleFinset_eq] using hzero cols

/-- Proposition 17 and Proposition 21 together realize every compatible rank-three datum. -/
theorem exists_exactToeplitzRepresentation (D : CompatibleRankThreeData n) :
    ∃ a : Fin (n + 2) → ℝ, D.ExactToeplitzRepresentation a := by
  by_cases hleft : D.leftLoopCount = 0
  · by_cases hright : D.rightLoopCount = 0
    · obtain ⟨a, hTN, hfull, hsupport⟩ :=
        exists_exactSupport_noLoops D hleft hright
      exact ⟨a, hTN, hfull, hsupport⟩
    · have hrightPos : 0 < D.rightLoopCount := Nat.pos_of_ne_zero hright
      obtain ⟨a, hTN, hfull, hsupport⟩ :=
        exists_exactSupport_rightLoop D hleft hrightPos
      exact ⟨a, hTN, hfull, hsupport⟩
  · have hleftPos : 0 < D.leftLoopCount := Nat.pos_of_ne_zero hleft
    by_cases hright : D.rightLoopCount = 0
    · obtain ⟨a, hTN, hfull, hsupport⟩ :=
        exists_exactSupport_leftLoop D hleftPos hright
      exact ⟨a, hTN, hfull, hsupport⟩
    · have hrightPos : 0 < D.rightLoopCount := Nat.pos_of_ne_zero hright
      have hTwo : RankThree.HasTwoSidedLoops D := ⟨hleftPos, hrightPos⟩
      obtain ⟨a, hTN, hfull, _, hzero⟩ :=
        RankThree.CompatibleRankThreeData.propositionTwentyOne (D := D) hTwo
      refine ⟨a, hTN, hfull, ?_⟩
      intro cols
      simpa [selectedTripleFinset_eq] using hzero cols

/-- The canonical datum is uniquely recovered, at the level of all combinatorial support
components, from the basis support of the represented positroid. -/
theorem canonical_supportComponents_unique {a : Fin (n + 2) → ℝ}
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    (E : CompatibleRankThreeData n)
    (hbasis : (canonicalCompatibleRankThreeData hTN hfull).basisFinsets = E.basisFinsets) :
    (canonicalCompatibleRankThreeData hTN hfull).supportLoops = E.supportLoops ∧
      (canonicalCompatibleRankThreeData hTN hfull).supportParallelPairs =
        E.supportParallelPairs ∧
      (canonicalCompatibleRankThreeData hTN hfull).supportRankTwoFlats =
        E.supportRankTwoFlats :=
  canonicalCompatibleRankThreeData_support_unique hTN hfull E hbasis

/-- Two rank-three matroids realizing the same compatible triple support are equal. -/
theorem matroid_eq_of_compatibleTripleSupportRealizations
    {M N : Matroid (Fin n)}
    (RM : CompatibleTripleSupportRealization D M)
    (RN : CompatibleTripleSupportRealization D N) :
    M = N := by
  apply matroid_eq_of_sameBasisSupport (RM.ground_eq.trans RN.ground_eq.symm)
  intro B
  constructor
  · intro hB
    let hBfin : B.Finite := Set.toFinite B
    let J : Finset (Fin n) := hBfin.toFinset
    have hJcard : J.card = 3 := by
      rw [← Set.ncard_eq_toFinset_card B hBfin]
      exact RM.base_ncard_eq_three hB
    have hbaseJ : M.IsBase (J : Set (Fin n)) := by
      simpa [J, hBfin.coe_toFinset] using hB
    have hnot := (RM.isBase_iff J hJcard).mp hbaseJ
    have hbaseJN : N.IsBase (J : Set (Fin n)) := (RN.isBase_iff J hJcard).mpr hnot
    simpa [J, hBfin.coe_toFinset] using hbaseJN
  · intro hB
    let hBfin : B.Finite := Set.toFinite B
    let J : Finset (Fin n) := hBfin.toFinset
    have hJcard : J.card = 3 := by
      rw [← Set.ncard_eq_toFinset_card B hBfin]
      exact RN.base_ncard_eq_three hB
    have hbaseJ : N.IsBase (J : Set (Fin n)) := by
      simpa [J, hBfin.coe_toFinset] using hB
    have hnot := (RN.isBase_iff J hJcard).mp hbaseJ
    have hbaseJM : M.IsBase (J : Set (Fin n)) := (RM.isBase_iff J hJcard).mpr hnot
    simpa [J, hBfin.coe_toFinset] using hbaseJM

/-- Compatible data inducing the same rank-three matroid have the same loops, parallel pairs,
and maximal rank-two flats.  Thus these components are intrinsic to the positroid basis
support. -/
theorem supportComponents_eq_of_compatibleTripleSupportRealizations
    {E : CompatibleRankThreeData n} {M : Matroid (Fin n)}
    (RD : CompatibleTripleSupportRealization D M)
    (RE : CompatibleTripleSupportRealization E M) :
    D.supportLoops = E.supportLoops ∧
      D.supportParallelPairs = E.supportParallelPairs ∧
      D.supportRankTwoFlats = E.supportRankTwoFlats := by
  have hsupport : SameCompatibleTripleSupport D E := by
    intro J
    by_cases hJ : J.card = 3
    · constructor
      · intro hD
        by_contra hE
        have hbase : M.IsBase (J : Set (Fin n)) := (RE.isBase_iff J hJ).mpr hE
        exact ((RD.isBase_iff J hJ).mp hbase) hD
      · intro hE
        by_contra hD
        have hbase : M.IsBase (J : Set (Fin n)) := (RD.isBase_iff J hJ).mpr hD
        exact ((RE.isBase_iff J hJ).mp hbase) hE
    · constructor
      · intro hD
        exact (hJ hD.1).elim
      · intro hE
        exact (hJ hE.1).elim
  exact D.supportComponents_eq_of_sameSupport E hsupport

/-- Every totally nonnegative full-row-rank rank-three Toeplitz matrix yields an exact canonical
compatible datum. -/
theorem exists_exactCompatibleData_iff {a : Fin (n + 2) → ℝ} :
    TotallyNonnegative (rankThreeToeplitz a) ∧
        HasFullRowRank (rankThreeToeplitz a) ↔
      ∃ D : CompatibleRankThreeData n, D.ExactToeplitzRepresentation a := by
  constructor
  · rintro ⟨hTN, hfull⟩
    exact ⟨canonicalCompatibleRankThreeData hTN hfull,
      canonical_exactToeplitzRepresentation hTN hfull⟩
  · rintro ⟨D, R⟩
    exact ⟨R.totallyNonnegative, R.fullRowRank⟩

end CompatibleRankThreeData

/-- A rank-three matroid has a strong Toeplitz representation when it is the column matroid of
a full-row-rank, all-minor totally nonnegative rank-three Toeplitz section. -/
def HasTNNRankThreeToeplitzRepresentation {n : ℕ} (M : Matroid (Fin n)) : Prop :=
  ∃ a : Fin (n + 2) → ℝ,
    TotallyNonnegative (rankThreeToeplitz a) ∧
      HasFullRowRank (rankThreeToeplitz a) ∧
      columnMatroid (rankThreeToeplitz a) = M

/-- A rank-three matroid has compatible support when its three-element bases are exactly those
specified by some compatible datum. -/
def HasCompatibleRankThreeSupport {n : ℕ} (M : Matroid (Fin n)) : Prop :=
  ∃ D : CompatibleRankThreeData n, CompatibleTripleSupportRealization D M

/-- The necessity half of the rank-three classification, stated directly for the represented
column matroid. -/
theorem hasCompatibleRankThreeSupport_of_hasTNNRankThreeToeplitzRepresentation
    {n : ℕ} {M : Matroid (Fin n)}
    (hM : HasTNNRankThreeToeplitzRepresentation M) :
    HasCompatibleRankThreeSupport M := by
  obtain ⟨a, hTN, hfull, hmatroid⟩ := hM
  let D := canonicalCompatibleRankThreeData hTN hfull
  have R : D.ExactToeplitzRepresentation a := by
    dsimp [D]
    exact CompatibleRankThreeData.canonical_exactToeplitzRepresentation hTN hfull
  refine ⟨D, ?_⟩
  rw [← hmatroid]
  simpa [CompatibleRankThreeData.ExactToeplitzRepresentation.toPositroidRepresentation,
    PositroidRepresentation.matroid] using R.compatibleTripleSupportRealization

/-- A compatible rank-three support has a totally nonnegative Toeplitz realization whose genuine
column matroid is the prescribed matroid. -/
theorem hasTNNRankThreeToeplitzRepresentation_of_hasCompatibleRankThreeSupport
    {n : ℕ} {M : Matroid (Fin n)}
    (hM : HasCompatibleRankThreeSupport M) :
    HasTNNRankThreeToeplitzRepresentation M := by
  obtain ⟨D, hD⟩ := hM
  obtain ⟨a, R⟩ := D.exists_exactToeplitzRepresentation
  refine ⟨a, R.totallyNonnegative, R.fullRowRank, ?_⟩
  change R.toPositroidRepresentation.matroid = M
  have hmatroid := CompatibleRankThreeData.matroid_eq_of_compatibleTripleSupportRealizations
    (D := D) R.compatibleTripleSupportRealization hD
  exact hmatroid

/-- The rank-three Toeplitz classification: the represented matroids are exactly the compatible
supports. -/
theorem hasTNNRankThreeToeplitzRepresentation_iff_hasCompatibleRankThreeSupport
    {n : ℕ} {M : Matroid (Fin n)} :
    HasTNNRankThreeToeplitzRepresentation M ↔
      HasCompatibleRankThreeSupport M := by
  constructor
  · exact hasCompatibleRankThreeSupport_of_hasTNNRankThreeToeplitzRepresentation
  · exact hasTNNRankThreeToeplitzRepresentation_of_hasCompatibleRankThreeSupport

end

end ToeplitzPositroids
