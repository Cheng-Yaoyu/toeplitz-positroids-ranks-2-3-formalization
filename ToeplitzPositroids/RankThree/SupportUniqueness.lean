import ToeplitzPositroids.Matrix.Positroid
import ToeplitzPositroids.RankThree.CompatibleData
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# Uniqueness from rank-three basis support

This file formalizes the support-uniqueness argument in Section 7. For a rank-three matroid,
basis support determines loops, parallel pairs, and the subsets of rank at most two. Applied to
the column matroid of a positroid representation, equality of positive maximal-minor support
therefore determines all three kinds of degeneracy used in the classification.
-/

namespace ToeplitzPositroids

open Set

variable {α : Type*} {M N : Matroid α}

/-- A matroid has set-theoretic rank three when it has a base with three elements. -/
def MatroidHasRankThree (M : Matroid α) : Prop :=
  ∃ B, M.IsBase B ∧ B.ncard = 3

/-- In a rank-three matroid, an independent three-element set is a base. -/
theorem Matroid.Indep.isBase_of_ncard_eq_three [Finite α]
    (hM : MatroidHasRankThree M) {I : Set α} (hI : M.Indep I) (hIcard : I.ncard = 3) :
    M.IsBase I := by
  obtain ⟨B, hB, hBcard⟩ := hM
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  have hB'card : B'.ncard = 3 := (hB'.ncard_eq_ncard_of_isBase hB).trans hBcard
  have hEq : I = B' := Set.eq_of_subset_of_ncard_le hIB' (by omega) (Set.toFinite B')
  rwa [hEq]

/-- In a rank-three matroid, independence and being a base agree on three-element sets. -/
theorem indep_iff_isBase_of_ncard_eq_three [Finite α] (hM : MatroidHasRankThree M)
    {I : Set α} (hIcard : I.ncard = 3) :
    M.Indep I ↔ M.IsBase I :=
  ⟨fun hI ↦ Matroid.Indep.isBase_of_ncard_eq_three hM hI hIcard,
    Matroid.IsBase.indep⟩

/-- A finite subset has rank at most two exactly when none of its three-element subsets is a
basis. This is the all-triples rank-two-subset criterion used in Section 7. -/
theorem eRk_le_two_iff_all_triples_not_isBase [Finite α] (hM : MatroidHasRankThree M)
    (X : Set α) :
    M.eRk X ≤ 2 ↔
      ∀ T : Set α, T ⊆ X → T.ncard = 3 → ¬M.IsBase T := by
  constructor
  · intro hrank T hTX hTcard hTbase
    have hle := Matroid.eRk_le_iff.mp hrank hTX hTbase.indep
    have hTfin : T.Finite := Set.toFinite T
    rw [← hTfin.cast_ncard_eq, hTcard] at hle
    norm_num at hle
  · intro htriples
    apply Matroid.eRk_le_iff.mpr
    intro I hIX hI
    have hIfin : I.Finite := Set.toFinite I
    rw [← hIfin.cast_ncard_eq]
    norm_cast
    by_contra hcard
    have hthree : 3 ≤ I.ncard := by omega
    obtain ⟨T, hTI, hTcard⟩ := Set.exists_subset_card_eq hthree
    exact htriples T (hTI.trans hIX) hTcard
      (Matroid.Indep.isBase_of_ncard_eq_three hM (hI.subset hTI) hTcard)

/-- A nonloop pair is a two-element circuit exactly when no base contains both elements. -/
theorem pair_isCircuit_iff_forall_not_both_mem_isBase
    {e f : α} (hef : e ≠ f) (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    M.IsCircuit {e, f} ↔ ∀ B, M.IsBase B → ¬(e ∈ B ∧ f ∈ B) := by
  constructor
  · intro hcir B hB hmem
    exact hcir.not_indep (hB.indep.subset (by simpa [Set.pair_subset_iff] using hmem))
  · intro hsupport
    have hnot : ¬M.Indep {e, f} := by
      intro hpair
      obtain ⟨B, hB, hpairB⟩ := hpair.exists_isBase_superset
      exact hsupport B hB ⟨hpairB (by simp), hpairB (by simp)⟩
    rw [Matroid.isCircuit_iff_dep_forall_diff_singleton_indep]
    refine ⟨⟨hnot, ?_⟩, ?_⟩
    · intro x hx
      rcases hx with rfl | rfl
      · exact he.mem_ground
      · exact hf.mem_ground
    intro x hx
    rcases hx with rfl | rfl
    · simpa [Set.pair_diff_left hef] using hf.indep
    · simpa [Set.pair_diff_right hef] using he.indep

/-- Two matroids have the same basis support when their base predicates agree on every set. -/
def SameBasisSupport (M N : Matroid α) : Prop :=
  ∀ B, M.IsBase B ↔ N.IsBase B

/-- Equal ground sets and equal basis support determine the entire matroid. -/
theorem matroid_eq_of_sameBasisSupport (hE : M.E = N.E) (hMN : SameBasisSupport M N) :
    M = N := by
  apply Matroid.ext_isBase hE
  intro B _
  exact hMN B

/-- Equal basis support determines the loop set. -/
theorem isLoop_iff_of_sameBasisSupport (hE : M.E = N.E) (hMN : SameBasisSupport M N)
    (e : α) :
    M.IsLoop e ↔ N.IsLoop e := by
  rw [matroid_eq_of_sameBasisSupport hE hMN]

/-- Equal basis support determines all two-element circuits, hence all nonloop parallel pairs. -/
theorem pair_isCircuit_iff_of_sameBasisSupport (hE : M.E = N.E)
    (hMN : SameBasisSupport M N) (e f : α) :
    M.IsCircuit {e, f} ↔ N.IsCircuit {e, f} := by
  rw [matroid_eq_of_sameBasisSupport hE hMN]

/-- Equal basis support determines which subsets have rank at most two. -/
theorem eRk_le_two_iff_of_sameBasisSupport (hE : M.E = N.E)
    (hMN : SameBasisSupport M N) (X : Set α) :
    M.eRk X ≤ 2 ↔ N.eRk X ≤ 2 := by
  rw [matroid_eq_of_sameBasisSupport hE hMN]

section PositroidSupport

variable {n : ℕ}

/-- Equality of positive ordered maximal-minor support for two rank-three positroid
representations. -/
def SameOrderedRankThreeSupport (P Q : PositroidRepresentation 3 n) : Prop :=
  ∀ cols : Fin 3 ↪o Fin n,
    (0 < orderedMinor P.matrix (allRows 3) cols ↔
      0 < orderedMinor Q.matrix (allRows 3) cols)

/-- Equality of ordered maximal-minor support is equivalent to equality of the genuine matroid
basis supports. -/
theorem sameOrderedRankThreeSupport_iff_sameBasisSupport
    (P Q : PositroidRepresentation 3 n) :
    SameOrderedRankThreeSupport P Q ↔ SameBasisSupport P.matroid Q.matroid := by
  constructor
  · intro hsupport B
    rw [P.isBase_iff_exists_positive_orderedMinor,
      Q.isBase_iff_exists_positive_orderedMinor]
    constructor
    · rintro ⟨cols, hcols, hpos⟩
      exact ⟨cols, hcols, (hsupport cols).1 hpos⟩
    · rintro ⟨cols, hcols, hpos⟩
      exact ⟨cols, hcols, (hsupport cols).2 hpos⟩
  · intro hsupport cols
    rw [← P.isBase_range_iff_orderedMinor_pos,
      ← Q.isBase_range_iff_orderedMinor_pos]
    exact hsupport (Set.range cols)

/-- Equal positive maximal-minor support gives equal represented matroids. -/
theorem PositroidRepresentation.matroid_eq_of_sameOrderedRankThreeSupport
    (P Q : PositroidRepresentation 3 n) (hsupport : SameOrderedRankThreeSupport P Q) :
    P.matroid = Q.matroid :=
  matroid_eq_of_sameBasisSupport (by simp)
    ((sameOrderedRankThreeSupport_iff_sameBasisSupport P Q).1 hsupport)

/-- Equal positive maximal-minor support determines matrix loops. -/
theorem PositroidRepresentation.isLoop_iff_of_sameOrderedRankThreeSupport
    (P Q : PositroidRepresentation 3 n) (hsupport : SameOrderedRankThreeSupport P Q)
    (e : Fin n) :
    IsLoop P.matrix e ↔ IsLoop Q.matrix e := by
  rw [P.isLoop_iff, Q.isLoop_iff, P.matroid_eq_of_sameOrderedRankThreeSupport Q hsupport]

/-- Equal positive maximal-minor support determines nonloop parallel pairs of all-minor-TN
representations. -/
theorem columnsParallel_iff_of_sameOrderedRankThreeSupport
    {A B : Matrix (Fin 3) (Fin n) ℝ}
    (hA : IsAllMinorTNToeplitzRepresentation A)
    (hB : IsAllMinorTNToeplitzRepresentation B)
    (hsupport : SameOrderedRankThreeSupport hA.toPositroidRepresentation
      hB.toPositroidRepresentation) {e f : Fin n} (hef : e ≠ f) :
    ColumnsParallel A e f ↔ ColumnsParallel B e f := by
  rw [hA.columnsParallel_iff_pair_isCircuit hef,
    hB.columnsParallel_iff_pair_isCircuit hef]
  exact pair_isCircuit_iff_of_sameBasisSupport (by simp)
    ((sameOrderedRankThreeSupport_iff_sameBasisSupport _ _).1 hsupport) e f

end PositroidSupport

section CompatibleSupport

variable {n : ℕ}

/-- A closed ordinary interval is uniquely determined by its point set. -/
theorem SimplifiedInterval.eq_of_points_eq {m : ℕ} {H K : SimplifiedInterval m}
    (hpoints : H.points = K.points) :
    H = K := by
  have hHlK : H.left ∈ K.points := by
    rw [← hpoints]
    exact H.left_mem_points
  have hKlH : K.left ∈ H.points := by
    rw [hpoints]
    exact K.left_mem_points
  have hHrK : H.right ∈ K.points := by
    rw [← hpoints]
    exact H.right_mem_points
  have hKrH : K.right ∈ H.points := by
    rw [hpoints]
    exact K.right_mem_points
  have hleft : H.left = K.left := le_antisymm
    (SimplifiedInterval.mem_points.mp hKlH).1
    (SimplifiedInterval.mem_points.mp hHlK).1
  have hright : H.right = K.right := le_antisymm
    (SimplifiedInterval.mem_points.mp hHrK).2
    (SimplifiedInterval.mem_points.mp hKrH).2
  cases H with
  | mk hl hr hle =>
    cases K with
    | mk kl kr kle =>
      simp only at hleft hright
      subst kl
      subst kr
      rfl

/-- Equality of the induced triple nonbasis predicates of two compatible data sets. -/
def SameCompatibleTripleSupport (D E : CompatibleRankThreeData n) : Prop :=
  ∀ J : Finset (Fin n), D.TripleNonbasis J ↔ E.TripleNonbasis J

/-- Equal triple support gives the same canonical finite basis system. -/
theorem CompatibleRankThreeData.basisFinsets_eq_of_sameSupport
    (D E : CompatibleRankThreeData n) (hDE : SameCompatibleTripleSupport D E) :
    D.basisFinsets = E.basisFinsets := by
  ext J
  simp only [CompatibleRankThreeData.mem_basisFinsets_iff]
  exact and_congr_right fun _ ↦ not_congr (hDE J)

/-- A raw element is detected as a loop by triple support when every triple containing it is a
nonbasis. -/
def CompatibleRankThreeData.IsSupportLoop (D : CompatibleRankThreeData n) (e : Fin n) : Prop :=
  ∀ J : Finset (Fin n), J.card = 3 → e ∈ J → D.TripleNonbasis J

/-- Two distinct support-nonloops are detected as parallel when every triple containing the pair
is a nonbasis. -/
def CompatibleRankThreeData.IsSupportParallel (D : CompatibleRankThreeData n)
    (e f : Fin n) : Prop :=
  e ≠ f ∧ ¬D.IsSupportLoop e ∧ ¬D.IsSupportLoop f ∧
    ∀ J : Finset (Fin n), J.card = 3 → e ∈ J → f ∈ J → D.TripleNonbasis J

/-- Equal triple support determines the support-detected loop elements. -/
theorem CompatibleRankThreeData.isSupportLoop_iff_of_sameSupport
    (D E : CompatibleRankThreeData n) (hDE : SameCompatibleTripleSupport D E) (e : Fin n) :
    D.IsSupportLoop e ↔ E.IsSupportLoop e := by
  simp only [CompatibleRankThreeData.IsSupportLoop]
  constructor <;> intro h J hJcard heJ
  · exact (hDE J).1 (h J hJcard heJ)
  · exact (hDE J).2 (h J hJcard heJ)

/-- Equal triple support determines the support-detected nonloop parallel relation. -/
theorem CompatibleRankThreeData.isSupportParallel_iff_of_sameSupport
    (D E : CompatibleRankThreeData n) (hDE : SameCompatibleTripleSupport D E)
    (e f : Fin n) :
    D.IsSupportParallel e f ↔ E.IsSupportParallel e f := by
  simp only [CompatibleRankThreeData.IsSupportParallel]
  rw [D.isSupportLoop_iff_of_sameSupport E hDE e,
    D.isSupportLoop_iff_of_sameSupport E hDE f]
  constructor <;> rintro ⟨hef, he, hf, h⟩
  · exact ⟨hef, he, hf, fun J hc heJ hfJ ↦ (hDE J).1 (h J hc heJ hfJ)⟩
  · exact ⟨hef, he, hf, fun J hc heJ hfJ ↦ (hDE J).2 (h J hc heJ hfJ)⟩

/-- A support-detected rank-two subset has at least three elements and no basis triple. -/
def CompatibleRankThreeData.IsSupportRankTwoSubset
    (D : CompatibleRankThreeData n) (X : Finset (Fin n)) : Prop :=
  3 ≤ X.card ∧
    ∀ T : Finset (Fin n), T ⊆ X → T.card = 3 → D.TripleNonbasis T

/-- Equal triple support determines all support-detected rank-two subsets. -/
theorem CompatibleRankThreeData.isSupportRankTwoSubset_iff_of_sameSupport
    (D E : CompatibleRankThreeData n) (hDE : SameCompatibleTripleSupport D E)
    (X : Finset (Fin n)) :
    D.IsSupportRankTwoSubset X ↔ E.IsSupportRankTwoSubset X := by
  simp only [CompatibleRankThreeData.IsSupportRankTwoSubset]
  constructor
  · rintro ⟨hcard, hX⟩
    exact ⟨hcard, fun T hTX hTcard ↦ (hDE T).1 (hX T hTX hTcard)⟩
  · rintro ⟨hcard, hX⟩
    exact ⟨hcard, fun T hTX hTcard ↦ (hDE T).2 (hX T hTX hTcard)⟩

/-- Equal triple support determines the maximal support-detected rank-two subsets. -/
theorem CompatibleRankThreeData.maximal_supportRankTwoSubset_iff_of_sameSupport
    (D E : CompatibleRankThreeData n) (hDE : SameCompatibleTripleSupport D E)
    (X : Finset (Fin n)) :
    Maximal D.IsSupportRankTwoSubset X ↔ Maximal E.IsSupportRankTwoSubset X := by
  have hpred : D.IsSupportRankTwoSubset = E.IsSupportRankTwoSubset := by
    funext Y
    exact propext (D.isSupportRankTwoSubset_iff_of_sameSupport E hDE Y)
  rw [hpred]

/-- The finite set of loop elements recovered solely from triple support. -/
noncomputable def CompatibleRankThreeData.supportLoops
    (D : CompatibleRankThreeData n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter D.IsSupportLoop

/-- The finite set of ordered nonloop parallel pairs recovered solely from triple support. -/
noncomputable def CompatibleRankThreeData.supportParallelPairs
    (D : CompatibleRankThreeData n) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p ↦ D.IsSupportParallel p.1 p.2

/-- The finite family of maximal rank-two subsets recovered solely from triple support. -/
noncomputable def CompatibleRankThreeData.supportRankTwoFlats
    (D : CompatibleRankThreeData n) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.powerset.filter fun X ↦ Maximal D.IsSupportRankTwoSubset X

@[simp]
theorem CompatibleRankThreeData.mem_supportLoops_iff
    (D : CompatibleRankThreeData n) (e : Fin n) :
    e ∈ D.supportLoops ↔ D.IsSupportLoop e := by
  classical
  simp [CompatibleRankThreeData.supportLoops]

@[simp]
theorem CompatibleRankThreeData.mem_supportParallelPairs_iff
    (D : CompatibleRankThreeData n) (p : Fin n × Fin n) :
    p ∈ D.supportParallelPairs ↔ D.IsSupportParallel p.1 p.2 := by
  classical
  simp [CompatibleRankThreeData.supportParallelPairs]

@[simp]
theorem CompatibleRankThreeData.mem_supportRankTwoFlats_iff
    (D : CompatibleRankThreeData n) (X : Finset (Fin n)) :
    X ∈ D.supportRankTwoFlats ↔ Maximal D.IsSupportRankTwoSubset X := by
  classical
  simp [CompatibleRankThreeData.supportRankTwoFlats]

/-- Equal triple basis support uniquely determines the recovered loop set, nonloop parallel
relation, and maximal rank-two-flat family. -/
theorem CompatibleRankThreeData.supportComponents_eq_of_sameSupport
    (D E : CompatibleRankThreeData n) (hDE : SameCompatibleTripleSupport D E) :
    D.supportLoops = E.supportLoops ∧
      D.supportParallelPairs = E.supportParallelPairs ∧
      D.supportRankTwoFlats = E.supportRankTwoFlats := by
  refine ⟨?_, ?_, ?_⟩
  · ext e
    simp only [CompatibleRankThreeData.mem_supportLoops_iff]
    exact D.isSupportLoop_iff_of_sameSupport E hDE e
  · ext p
    simp only [CompatibleRankThreeData.mem_supportParallelPairs_iff]
    exact D.isSupportParallel_iff_of_sameSupport E hDE p.1 p.2
  · ext X
    simp only [CompatibleRankThreeData.mem_supportRankTwoFlats_iff]
    exact D.maximal_supportRankTwoSubset_iff_of_sameSupport E hDE X

/-- A rank-three matroid realizes compatible triple support when its ground set is the raw ground
set and its three-element bases are exactly the triples not declared nonbases. -/
structure CompatibleTripleSupportRealization
    (D : CompatibleRankThreeData n) (M : Matroid (Fin n)) : Prop where
  ground_eq : M.E = Set.univ
  rankThree : MatroidHasRankThree M
  isBase_iff : ∀ J : Finset (Fin n), J.card = 3 →
    (M.IsBase (J : Set (Fin n)) ↔ ¬D.TripleNonbasis J)

namespace CompatibleTripleSupportRealization

variable {D : CompatibleRankThreeData n} {M : Matroid (Fin n)}

/-- Every base of a realization has three elements. -/
theorem base_ncard_eq_three (R : CompatibleTripleSupportRealization D M)
    {B : Set (Fin n)} (hB : M.IsBase B) :
    B.ncard = 3 := by
  obtain ⟨B₀, hB₀, hB₀card⟩ := R.rankThree
  exact (hB.ncard_eq_ncard_of_isBase hB₀).trans hB₀card

/-- The support-detected loop predicate agrees with the actual matroid loop predicate in every
rank-three realization. -/
theorem isSupportLoop_iff_isLoop (R : CompatibleTripleSupportRealization D M) (e : Fin n) :
    D.IsSupportLoop e ↔ M.IsLoop e := by
  constructor
  · intro he
    rw [M.isLoop_iff_forall_notMem_isBase (by rw [R.ground_eq]; simp)]
    intro B hB heB
    let hBfin : B.Finite := Set.toFinite B
    let J : Finset (Fin n) := hBfin.toFinset
    have hJcard : J.card = 3 := by
      rw [← Set.ncard_eq_toFinset_card B hBfin]
      exact R.base_ncard_eq_three hB
    have heJ : e ∈ J := by
      simpa [J] using heB
    have hnonbasis : D.TripleNonbasis J := he J hJcard heJ
    have hbaseJ : M.IsBase (J : Set (Fin n)) := by
      simpa [J, hBfin.coe_toFinset] using hB
    exact (R.isBase_iff J hJcard).mp hbaseJ hnonbasis
  · intro he J hJcard heJ
    by_contra hbasis
    have hbase : M.IsBase (J : Set (Fin n)) := (R.isBase_iff J hJcard).2 hbasis
    exact he.notMem_of_indep hbase.indep (by simpa using heJ)

/-- The support-detected parallel relation agrees with two-element matroid circuits in every
rank-three realization. -/
theorem isSupportParallel_iff_pair_isCircuit
    (R : CompatibleTripleSupportRealization D M) (e f : Fin n) :
    D.IsSupportParallel e f ↔ e ≠ f ∧ M.IsCircuit {e, f} := by
  constructor
  · rintro ⟨hef, heSupport, hfSupport, hpairs⟩
    have heNotLoop : ¬M.IsLoop e := by
      rwa [← R.isSupportLoop_iff_isLoop]
    have hfNotLoop : ¬M.IsLoop f := by
      rwa [← R.isSupportLoop_iff_isLoop]
    have he : M.IsNonloop e := M.isNonloop_of_not_isLoop (by rw [R.ground_eq]; simp) heNotLoop
    have hf : M.IsNonloop f := M.isNonloop_of_not_isLoop (by rw [R.ground_eq]; simp) hfNotLoop
    refine ⟨hef, (pair_isCircuit_iff_forall_not_both_mem_isBase hef he hf).2 ?_⟩
    intro B hB hmem
    let hBfin : B.Finite := Set.toFinite B
    let J : Finset (Fin n) := hBfin.toFinset
    have hJcard : J.card = 3 := by
      rw [← Set.ncard_eq_toFinset_card B hBfin]
      exact R.base_ncard_eq_three hB
    have heJ : e ∈ J := by simpa [J] using hmem.1
    have hfJ : f ∈ J := by simpa [J] using hmem.2
    have hnonbasis := hpairs J hJcard heJ hfJ
    have hbaseJ : M.IsBase (J : Set (Fin n)) := by
      simpa [J, hBfin.coe_toFinset] using hB
    exact (R.isBase_iff J hJcard).mp hbaseJ hnonbasis
  · rintro ⟨hef, hcir⟩
    have heInd : M.Indep {e} := by
      have h := hcir.diff_singleton_indep (show f ∈ ({e, f} : Set (Fin n)) by simp)
      simpa [Set.pair_diff_right hef] using h
    have hfInd : M.Indep {f} := by
      have h := hcir.diff_singleton_indep (show e ∈ ({e, f} : Set (Fin n)) by simp)
      simpa [Set.pair_diff_left hef] using h
    have heNotSupport : ¬D.IsSupportLoop e := by
      rw [R.isSupportLoop_iff_isLoop]
      exact heInd.isNonloop.not_isLoop
    have hfNotSupport : ¬D.IsSupportLoop f := by
      rw [R.isSupportLoop_iff_isLoop]
      exact hfInd.isNonloop.not_isLoop
    refine ⟨hef, heNotSupport, hfNotSupport, ?_⟩
    intro J hJcard heJ hfJ
    by_contra hbasis
    have hbase : M.IsBase (J : Set (Fin n)) := (R.isBase_iff J hJcard).2 hbasis
    exact hcir.not_indep (hbase.indep.subset (by
      intro x hx
      rcases hx with rfl | rfl
      · simpa using heJ
      · simpa using hfJ))

/-- The support-detected all-triples condition agrees with matroid rank at most two. -/
theorem eRk_coe_le_two_iff_isSupportRankTwoSubset
    (R : CompatibleTripleSupportRealization D M) (X : Finset (Fin n))
    (hXcard : 3 ≤ X.card) :
    M.eRk (X : Set (Fin n)) ≤ 2 ↔ D.IsSupportRankTwoSubset X := by
  rw [eRk_le_two_iff_all_triples_not_isBase R.rankThree]
  constructor
  · intro hX
    refine ⟨hXcard, ?_⟩
    intro T hTX hTcard
    have hnotbase := hX (T : Set (Fin n)) (by simpa using hTX) (by simpa using hTcard)
    by_contra hnot
    exact hnotbase ((R.isBase_iff T hTcard).2 hnot)
  · rintro ⟨_, hX⟩ T hTX hTcard hTbase
    let hTfin : T.Finite := Set.toFinite T
    let J : Finset (Fin n) := hTfin.toFinset
    have hJcard : J.card = 3 := by
      rw [← Set.ncard_eq_toFinset_card T hTfin]
      exact hTcard
    have hJX : J ⊆ X := by
      intro x hx
      have hxT : x ∈ T := by simpa [J] using hx
      simpa using hTX hxT
    have hnonbasis := hX J hJX hJcard
    have hbaseJ : M.IsBase (J : Set (Fin n)) := by
      simpa [J, hTfin.coe_toFinset] using hTbase
    exact (R.isBase_iff J hJcard).mp hbaseJ hnonbasis

end CompatibleTripleSupportRealization

/-- The prescribed interval family is the unique family whose point sets are exactly the maximal
simplified rank-two-flat candidates. Thus it is determined by simplified triple support. -/
theorem CompatibleRankThreeData.intervals_eq_iff_maximal_rankTwoFlats
    (D : CompatibleRankThreeData n)
    (F : Finset (SimplifiedInterval D.simplifiedSize)) :
    D.intervals = F ↔
      ∀ X : Finset (Fin D.simplifiedSize),
        Maximal D.IsSimplifiedRankTwoFlat X ↔ ∃ H ∈ F, X = H.points := by
  constructor
  · rintro rfl X
    exact D.maximal_rankTwoFlat_iff_eq_interval
  · intro hF
    ext H
    constructor
    · intro hHD
      obtain ⟨K, hKF, hpoints⟩ := (hF H.points).1 (D.interval_isMaximal_rankTwoFlat hHD)
      have hHK : H = K := SimplifiedInterval.eq_of_points_eq hpoints
      rwa [hHK]
    · intro hHF
      have hmax : Maximal D.IsSimplifiedRankTwoFlat H.points :=
        (hF H.points).2 ⟨H, hHF, rfl⟩
      obtain ⟨K, hKD, hpoints⟩ := D.maximal_rankTwoFlat_iff_eq_interval.mp hmax
      have hHK : H = K := SimplifiedInterval.eq_of_points_eq hpoints
      rwa [hHK]

end CompatibleSupport

end ToeplitzPositroids
