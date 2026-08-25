import ToeplitzPositroids.RankThree.MomentMatrix
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Canonical simplification of three-row column configurations

For a matrix that is totally nonnegative through order two, the first Pascal
moment is monotone on the nonloop columns and its fibers are precisely the
positive-parallel classes.  This file proves that these fibers are intervals in
the induced order on nonloop indices and chooses the least index in every class
as a canonical simplification representative.
-/

namespace ToeplitzPositroids.RankThree

open Matrix Set

noncomputable section

variable {n : ℕ} {A : Matrix (Fin 3) (Fin n) ℝ}

/-- Positive parallelism preserves the property of being a loop. -/
theorem isLoop_iff_of_columnsPositivelyParallel {i j : Fin n}
    (hij : ColumnsPositivelyParallel A i j) :
    IsLoop A i ↔ IsLoop A j := by
  rcases hij with ⟨a, ha, hcol⟩
  constructor
  · intro hi
    rw [IsLoop, hcol, hi, smul_zero]
  · intro hj
    rw [IsLoop, hcol] at hj
    have ha0 : a ≠ 0 := ha.ne'
    simpa only [smul_eq_zero, ha0, false_or] using hj

/-- The first moments are weakly ordered on any weakly increasing pair of nonloop indices. -/
theorem momentU_col_mono_of_tnUpTo_two (hA : TNUpTo A 2) {i j : Fin n} (hij : i ≤ j)
    (hi : ¬IsLoop A i) (hj : ¬IsLoop A j) :
    momentU (A.col i) ≤ momentU (A.col j) := by
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · exact momentU_col_le_of_tnUpTo_two hA hij hi hj

/-- On nonloop columns of a `TN₂` matrix, equality of first moments is exactly positive
parallelism, without an ordering assumption on the two indices. -/
theorem momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two' (hA : TNUpTo A 2)
    {i j : Fin n} (hi : ¬IsLoop A i) (hj : ¬IsLoop A j) :
    momentU (A.col i) = momentU (A.col j) ↔ ColumnsPositivelyParallel A i j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two hA hij hi hj
  · simp only [columnsPositivelyParallel_refl]
  · constructor
    · intro hu
      apply columnsPositivelyParallel_symm
      exact (momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two hA hji hj hi).mp hu.symm
    · intro hpar
      have hpar' := columnsPositivelyParallel_symm hpar
      exact (momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two hA hji hj hi).mpr hpar' |>.symm

/-- A positive-parallel class is order-convex after loops have been deleted. -/
theorem columnsPositivelyParallel_interval_of_tnUpTo_two (hA : TNUpTo A 2)
    {i j k : Fin n} (hij : i ≤ j) (hjk : j ≤ k) (hi : ¬IsLoop A i)
    (hj : ¬IsLoop A j) (hk : ¬IsLoop A k) (hik : ColumnsPositivelyParallel A i k) :
    ColumnsPositivelyParallel A i j ∧ ColumnsPositivelyParallel A j k := by
  have huik : momentU (A.col i) = momentU (A.col k) :=
    (momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two' hA hi hk).mpr hik
  have huij := momentU_col_mono_of_tnUpTo_two hA hij hi hj
  have hujk := momentU_col_mono_of_tnUpTo_two hA hjk hj hk
  have huij' : momentU (A.col i) = momentU (A.col j) := by linarith
  have hujk' : momentU (A.col j) = momentU (A.col k) := by linarith
  exact ⟨(momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two' hA hi hj).mp huij',
    (momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two' hA hj hk).mp hujk'⟩

/-- The ordered subtype of indices of nonloop columns. -/
abbrev NonloopIndex (A : Matrix (Fin 3) (Fin n) ℝ) :=
  {j : Fin n // ¬IsLoop A j}

/-- The positive-parallel class of a nonloop index, viewed inside the ordered nonloop subtype. -/
def nonloopParallelClass (A : Matrix (Fin 3) (Fin n) ℝ) (i : NonloopIndex A) :
    Set (NonloopIndex A) :=
  {j | ColumnsPositivelyParallel A i.1 j.1}

/-- Positive-parallel classes are ordinary intervals in the induced order on nonloop indices. -/
theorem nonloopParallelClass_ordConnected (hA : TNUpTo A 2) (i : NonloopIndex A) :
    (nonloopParallelClass A i).OrdConnected := by
  rw [Set.ordConnected_def]
  intro j hj k hk l hl
  have hjl : j.1 ≤ l.1 := hl.1
  have hlk : l.1 ≤ k.1 := hl.2
  exact columnsPositivelyParallel_trans hj
    (columnsPositivelyParallel_interval_of_tnUpTo_two hA hjl hlk j.2 l.2 k.2
      (columnsPositivelyParallel_trans (columnsPositivelyParallel_symm hj) hk)).1

/-- A parallel class is exactly a fiber of the first moment on nonloop indices. -/
theorem nonloopParallelClass_eq_momentUFiber (hA : TNUpTo A 2) (i : NonloopIndex A) :
    nonloopParallelClass A i = {j | momentU (A.col j.1) = momentU (A.col i.1)} := by
  ext j
  change ColumnsPositivelyParallel A i.1 j.1 ↔
    momentU (A.col j.1) = momentU (A.col i.1)
  rw [eq_comm, momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two' hA i.2 j.2]

/-- The finite set of all indices positively parallel to `j`. -/
def parallelClassIndices (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun i ↦ ColumnsPositivelyParallel A i j

@[simp]
theorem mem_parallelClassIndices {i j : Fin n} :
    i ∈ parallelClassIndices A j ↔ ColumnsPositivelyParallel A i j := by
  classical
  simp [parallelClassIndices]

theorem parallelClassIndices_nonempty (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) :
    (parallelClassIndices A j).Nonempty := by
  exact ⟨j, mem_parallelClassIndices.mpr (columnsPositivelyParallel_refl A j)⟩

/-- The canonical representative of a positive-parallel class is its least index. -/
def parallelRepresentative (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) : Fin n :=
  (parallelClassIndices A j).min' (parallelClassIndices_nonempty A j)

/-- The canonical representative belongs to the positive-parallel class it represents. -/
theorem parallelRepresentative_parallel (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) :
    ColumnsPositivelyParallel A (parallelRepresentative A j) j := by
  exact mem_parallelClassIndices.mp
    ((parallelClassIndices A j).min'_mem (parallelClassIndices_nonempty A j))

/-- The canonical representative is no later than every member of its class. -/
theorem parallelRepresentative_le {i j : Fin n} (hij : ColumnsPositivelyParallel A i j) :
    parallelRepresentative A j ≤ i := by
  exact Finset.min'_le _ i (mem_parallelClassIndices.mpr hij)

/-- Two indices have the same canonical representative exactly when their columns are
positively parallel. -/
theorem parallelRepresentative_eq_iff {i j : Fin n} :
    parallelRepresentative A i = parallelRepresentative A j ↔
      ColumnsPositivelyParallel A i j := by
  constructor
  · intro hrep
    have hi := parallelRepresentative_parallel A i
    have hj := parallelRepresentative_parallel A j
    exact columnsPositivelyParallel_trans (columnsPositivelyParallel_symm hi) (hrep ▸ hj)
  · intro hij
    have hclasses : parallelClassIndices A i = parallelClassIndices A j := by
      ext k
      simp only [mem_parallelClassIndices]
      constructor
      · intro hki
        exact columnsPositivelyParallel_trans hki hij
      · intro hkj
        exact columnsPositivelyParallel_trans hkj (columnsPositivelyParallel_symm hij)
    simp only [parallelRepresentative, hclasses]

/-- A canonical representative is a loop exactly when the represented column is a loop. -/
theorem parallelRepresentative_isLoop_iff (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) :
    IsLoop A (parallelRepresentative A j) ↔ IsLoop A j :=
  isLoop_iff_of_columnsPositivelyParallel (parallelRepresentative_parallel A j)

/-- A simplification representative is the least index of a nonloop positive-parallel class. -/
def IsSimplificationRepresentative (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) : Prop :=
  ¬IsLoop A j ∧ parallelRepresentative A j = j

/-- Equivalently, a simplification representative is a nonloop column with no earlier member
of its positive-parallel class. -/
theorem isSimplificationRepresentative_iff_classStart
    (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) :
    IsSimplificationRepresentative A j ↔
      ¬IsLoop A j ∧ ∀ i : Fin n, i < j → ¬ColumnsPositivelyParallel A i j := by
  constructor
  · rintro ⟨hj, hrep⟩
    refine ⟨hj, ?_⟩
    intro i hij hipar
    have hle := parallelRepresentative_le hipar
    rw [hrep] at hle
    exact (not_le_of_gt hij) hle
  · rintro ⟨hj, hfirst⟩
    refine ⟨hj, ?_⟩
    have hle : parallelRepresentative A j ≤ j :=
      parallelRepresentative_le (columnsPositivelyParallel_refl A j)
    apply le_antisymm hle
    apply le_of_not_gt
    intro hlt
    exact hfirst _ hlt (parallelRepresentative_parallel A j)

/-- The canonical representative of a nonloop column is itself a simplification
representative. -/
theorem parallelRepresentative_isSimplificationRepresentative (A : Matrix (Fin 3) (Fin n) ℝ)
    {j : Fin n} (hj : ¬IsLoop A j) :
    IsSimplificationRepresentative A (parallelRepresentative A j) := by
  constructor
  · rwa [parallelRepresentative_isLoop_iff]
  · exact (parallelRepresentative_eq_iff.mpr (parallelRepresentative_parallel A j))

/-- The finite set of canonical nonloop class representatives. -/
def simplificationIndices (A : Matrix (Fin 3) (Fin n) ℝ) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter (IsSimplificationRepresentative A)

@[simp]
theorem mem_simplificationIndices {j : Fin n} :
    j ∈ simplificationIndices A ↔ IsSimplificationRepresentative A j := by
  classical
  simp [simplificationIndices]

/-- The number of nonloop positive-parallel classes. -/
def simplificationSize (A : Matrix (Fin 3) (Fin n) ℝ) : ℕ :=
  (simplificationIndices A).card

/-- The canonical increasing enumeration of the nonloop positive-parallel classes. -/
def simplificationEmbedding (A : Matrix (Fin 3) (Fin n) ℝ) :
    Fin (simplificationSize A) ↪o Fin n :=
  (simplificationIndices A).orderEmbOfFin rfl

/-- Every selected simplification index is a nonloop canonical representative. -/
theorem simplificationEmbedding_isRepresentative (A : Matrix (Fin 3) (Fin n) ℝ)
    (p : Fin (simplificationSize A)) :
    IsSimplificationRepresentative A (simplificationEmbedding A p) := by
  exact mem_simplificationIndices.mp
    ((simplificationIndices A).orderEmbOfFin_mem rfl p)

/-- Every selected simplification column is a nonloop. -/
theorem simplificationEmbedding_not_isLoop (A : Matrix (Fin 3) (Fin n) ℝ)
    (p : Fin (simplificationSize A)) :
    ¬IsLoop A (simplificationEmbedding A p) :=
  (simplificationEmbedding_isRepresentative A p).1

/-- Selected simplification indices are fixed by the canonical representative map. -/
theorem parallelRepresentative_simplificationEmbedding
    (A : Matrix (Fin 3) (Fin n) ℝ) (p : Fin (simplificationSize A)) :
    parallelRepresentative A (simplificationEmbedding A p) = simplificationEmbedding A p :=
  (simplificationEmbedding_isRepresentative A p).2

/-- Two selected simplification columns are positively parallel exactly when their selected
indices agree. -/
theorem simplificationEmbedding_parallel_iff
    (A : Matrix (Fin 3) (Fin n) ℝ) {p q : Fin (simplificationSize A)} :
    ColumnsPositivelyParallel A (simplificationEmbedding A p) (simplificationEmbedding A q) ↔
      p = q := by
  constructor
  · intro hpq
    have hrep := parallelRepresentative_eq_iff.mpr hpq
    rw [parallelRepresentative_simplificationEmbedding,
      parallelRepresentative_simplificationEmbedding] at hrep
    exact (simplificationEmbedding A).injective hrep
  · rintro rfl
    exact columnsPositivelyParallel_refl A _

/-- The representative of every nonloop column occurs in the simplification enumeration. -/
theorem exists_simplificationEmbedding_eq_parallelRepresentative
    (A : Matrix (Fin 3) (Fin n) ℝ) {j : Fin n} (hj : ¬IsLoop A j) :
    ∃ p : Fin (simplificationSize A),
      simplificationEmbedding A p = parallelRepresentative A j := by
  have hmem : parallelRepresentative A j ∈ simplificationIndices A :=
    mem_simplificationIndices.mpr
      (parallelRepresentative_isSimplificationRepresentative A hj)
  have hmem' : parallelRepresentative A j ∈ (simplificationIndices A : Set (Fin n)) := hmem
  rw [← Finset.range_orderEmbOfFin (simplificationIndices A) rfl] at hmem'
  exact hmem'

/-- Every nonloop column is positively parallel to a selected simplification column. -/
theorem exists_simplificationEmbedding_parallel
    (A : Matrix (Fin 3) (Fin n) ℝ) {j : Fin n} (hj : ¬IsLoop A j) :
    ∃ p : Fin (simplificationSize A),
      ColumnsPositivelyParallel A (simplificationEmbedding A p) j := by
  rcases exists_simplificationEmbedding_eq_parallelRepresentative A hj with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  rw [hp]
  exact parallelRepresentative_parallel A j

/-- Every nonloop column belongs to exactly one selected positive-parallel class. -/
theorem existsUnique_simplificationEmbedding_parallel
    (A : Matrix (Fin 3) (Fin n) ℝ) {j : Fin n} (hj : ¬IsLoop A j) :
    ∃! p : Fin (simplificationSize A),
      ColumnsPositivelyParallel A (simplificationEmbedding A p) j := by
  rcases exists_simplificationEmbedding_parallel A hj with ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact ((simplificationEmbedding_parallel_iff A (p := p) (q := q)).mp
    (columnsPositivelyParallel_trans hp (columnsPositivelyParallel_symm hq))).symm

/-- An index is nonloop exactly when it belongs to a unique selected simplification class. -/
theorem not_isLoop_iff_existsUnique_simplificationEmbedding_parallel
    (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) :
    ¬IsLoop A j ↔
      ∃! p : Fin (simplificationSize A),
        ColumnsPositivelyParallel A (simplificationEmbedding A p) j := by
  constructor
  · exact existsUnique_simplificationEmbedding_parallel A
  · rintro ⟨p, hp, _⟩ hj
    have hpLoop : IsLoop A (simplificationEmbedding A p) :=
      (isLoop_iff_of_columnsPositivelyParallel hp).mpr hj
    exact simplificationEmbedding_not_isLoop A p hpLoop

/-- The canonical class number of a nonloop column in the simplification enumeration. -/
def simplificationClassIndex (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n)
    (hj : ¬IsLoop A j) : Fin (simplificationSize A) :=
  Classical.choose (existsUnique_simplificationEmbedding_parallel A hj).exists

/-- The column selected by the canonical class number is positively parallel to the original
nonloop column. -/
theorem simplificationClassIndex_parallel
    (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) (hj : ¬IsLoop A j) :
    ColumnsPositivelyParallel A
      (simplificationEmbedding A (simplificationClassIndex A j hj)) j :=
  Classical.choose_spec (existsUnique_simplificationEmbedding_parallel A hj).exists

/-- The exact fiber characterization of the canonical simplification class number. -/
theorem simplificationClassIndex_eq_iff
    (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) (hj : ¬IsLoop A j)
    (p : Fin (simplificationSize A)) :
    simplificationClassIndex A j hj = p ↔
      ColumnsPositivelyParallel A (simplificationEmbedding A p) j := by
  constructor
  · rintro rfl
    exact simplificationClassIndex_parallel A j hj
  · intro hp
    exact (existsUnique_simplificationEmbedding_parallel A hj).unique
      (simplificationClassIndex_parallel A j hj) hp

/-- The selected column at a canonical class number is the least index in the corresponding
positive-parallel class. -/
theorem simplificationEmbedding_classIndex_eq_parallelRepresentative
    (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) (hj : ¬IsLoop A j) :
    simplificationEmbedding A (simplificationClassIndex A j hj) =
      parallelRepresentative A j := by
  have hrep := parallelRepresentative_eq_iff.mpr
    (simplificationClassIndex_parallel A j hj)
  rw [parallelRepresentative_simplificationEmbedding] at hrep
  exact hrep

/-- Under `TN₂`, the first moments of the selected simplification columns are strictly
increasing. -/
theorem momentU_simplificationEmbedding_strictMono (hA : TNUpTo A 2) :
    StrictMono fun p : Fin (simplificationSize A) ↦
      momentU (A.col (simplificationEmbedding A p)) := by
  intro p q hpq
  apply momentU_col_lt_of_tnUpTo_two_of_not_positivelyParallel hA
    ((simplificationEmbedding A).strictMono hpq)
    (simplificationEmbedding_not_isLoop A p)
    (simplificationEmbedding_not_isLoop A q)
  intro hpar
  exact hpq.ne ((simplificationEmbedding_parallel_iff A).mp hpar)

/-- The canonical simplified matrix, obtained by retaining the least nonloop representative of
each positive-parallel class. -/
def simplifiedMatrix (A : Matrix (Fin 3) (Fin n) ℝ) :
    Matrix (Fin 3) (Fin (simplificationSize A)) ℝ :=
  A.submatrix (allRows 3) (simplificationEmbedding A)

@[simp]
theorem simplifiedMatrix_apply (A : Matrix (Fin 3) (Fin n) ℝ) (i : Fin 3)
    (p : Fin (simplificationSize A)) :
    simplifiedMatrix A i p = A i (simplificationEmbedding A p) :=
  rfl

@[simp]
theorem simplifiedMatrix_col (A : Matrix (Fin 3) (Fin n) ℝ)
    (p : Fin (simplificationSize A)) :
    (simplifiedMatrix A).col p = A.col (simplificationEmbedding A p) :=
  rfl

/-- The canonical simplified matrix inherits total nonnegativity through order two. -/
theorem simplifiedMatrix_tnUpTo_two (hA : TNUpTo A 2) :
    TNUpTo (simplifiedMatrix A) 2 :=
  hA.submatrix (allRows 3) (simplificationEmbedding A)

/-- The canonical simplified matrix has no loop columns. -/
theorem simplifiedMatrix_not_isLoop
    (A : Matrix (Fin 3) (Fin n) ℝ) (p : Fin (simplificationSize A)) :
    ¬IsLoop (simplifiedMatrix A) p := by
  simpa only [IsLoop, simplifiedMatrix_col] using simplificationEmbedding_not_isLoop A p

/-- The canonical simplified matrix has no repeated positive-parallel class. -/
theorem simplifiedMatrix_columnsPositivelyParallel_iff
    (A : Matrix (Fin 3) (Fin n) ℝ) (p q : Fin (simplificationSize A)) :
    ColumnsPositivelyParallel (simplifiedMatrix A) p q ↔ p = q := by
  simpa only [ColumnsPositivelyParallel, simplifiedMatrix_col] using
    (simplificationEmbedding_parallel_iff A (p := p) (q := q))

/-- Every original nonloop column is a positive multiple of exactly one column of the
canonical simplified matrix; loop columns belong to no such fiber. -/
theorem not_isLoop_iff_existsUnique_simplifiedMatrix_positiveMultiple
    (A : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) :
    ¬IsLoop A j ↔
      ∃! p : Fin (simplificationSize A),
        ∃ a : ℝ, 0 < a ∧ A.col j = a • (simplifiedMatrix A).col p := by
  simpa only [ColumnsPositivelyParallel, simplifiedMatrix_col] using
    not_isLoop_iff_existsUnique_simplificationEmbedding_parallel A j

/-- Under `TN₂`, the first moments of the columns of the simplified matrix are strictly
increasing. -/
theorem momentU_simplifiedMatrix_strictMono (hA : TNUpTo A 2) :
    StrictMono fun p : Fin (simplificationSize A) ↦ momentU ((simplifiedMatrix A).col p) := by
  simpa only [simplifiedMatrix_col] using momentU_simplificationEmbedding_strictMono hA

end


end ToeplitzPositroids.RankThree
